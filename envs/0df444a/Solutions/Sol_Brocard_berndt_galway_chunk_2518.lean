-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:10.411461+00:00
-- url     : https://prove2.me/submissions/6e573717-fe6a-4bc1-b2cd-f1b13a026032

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 452697841 ≤ n < 452877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 452699091 1250 452697841 452697863
    0xb04060c06020744090402030406110712030609050403020c0d020418081806030402010207150203130305010e100b06160219060c03020c010201090f0b0601020717030a02190302070b07050111030f04 86
    0x361040401120003801340101c40500d0008004180000380d000100213071500d1f0364440d122140184204000c000305445031154000742094800041c04864403900078000c2a407800082200103a000562000402c100b2510069144900c0c40001c02070a4118580700100e007240c4a0441000140809014034040c030720701000c840310100040c4081c1d400b00f00c9000e4010780c080d040070018503040e1580b20168654900c1541d28003801358071b48624516155108a402ea0354031280500000340a01005e05000c0030000c0600c0200030000016409020b0401003a04a0006101e600115692813005644d40018a8401c2803102d41d500c0000e0001c55840d03e0940c0540510032041415601c1803068010a0b58800c0f691464035000e9269500124401007003507041d03104d801c1b00824880301025200391160035840095641d818080e1000742088414000043d070305c469448580002034000c41d40340c00b0b0380d4202c20013581b56045410000c1c090180440030f130842800000501001c81410b000251099014800d8160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 452700341 1250 452699091 452699183
    0x1b0102070504090c0b030c07170307020c0a0302011d041e06050109060e0a0b090621070f05070803011203021002030a06050405013807050619150b04060c060207 70
    0x2981d10302e50f0000c01001c3d90309400c0c0519410007010b55003003c00240010700700f0811b03a413420228405454603100116006c070402c80455810403113110341307940075907561105519580c000307800e41030342e01c4d443c41841080320031001541c2c4480c0e00661405500d9404004107101000c000402030041d801001d0010384a5480070414500503043c11541c1c4102400302038943d460b01420340c200341c2100510f503901900400000e0154440d40c00c86130700107141111007030300c00c1c2072034100580503884220708042800420302080020a64900c20b80741146c0e10301c04011000301141ca001c0f4207103005040120a0070f480032060009401c103503844041502c8040d0350410141e602c3d150002d0780d01d207004000d08031000c10300004c00d0244204500201c5000e442070460fa0800c41240e581c40e00b000000c131800d4540305240c0c0c0002c80407042c0c03405100241c041218000c00032509003040d81e1100d109a000e20010700039026541d104218be5941203d803200d40252640040d2503d4030312010342c1840b244d41e00b141000600c05401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 452701591 1250 452700341 452700349
    0x12031a270a0e0d0f0207030f021810140f060304110303040b0a0e131406010f110118050c040902030d1b20010906020706020318030709090b1e01270e1b01020705 70
    0x11310000740c0c2c0d0014948070b491590784501c510602101260401e03804c881302601d440c40480d0090060030701030589000241420400c44451a14200c1d06100b53381128440d8095121501101e030050703081070001d40c0008000010a02e948120b070312540901c880024081030300c030340c0003c9007000c901048580d04803d18544200c0f5013035402042c4003900048008000c21095070080c1089420a0444e040241422000c12031907821a590b200081034654009140c800c10428180415950000104c4040061035403a0700070a41e03d61110807454248451480608060000320603040e945982c49140c540800c03900708490b403400712190000d580820700c940b2000c90b4480c000300b1201c00baa000d60b4019410203001000303904000200c511aa505030060940c08503c0b1b001030700400300c10030301403c501012801c0c10030401b1803c1e40382e80021001c0c0304130f80c8018030446040f461085001400907047ca62103640a102100081041c44001039483c400c241c1e9608612400701224034082e0002d0302903810f0b003030380d0300140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 452702841 1250 452701591 452701607
    0x40906080607170603160609062006060607171305011803050d050901030b101808070e0a0c0e100f020f1b01050a11070303090312031a270a0e0d 63
    0x2d4000c20003000b4842d10300c0c1040000355030700240040c121640c140003c00440480b8015030080400107500c2c404c14040507070802c03581c0307104040c0e900e08201c5003040300300803039254240076010364450803000400200f4440181c09117040300340d001404030b07500d0b00b0b040c81000c51030041c1c1c40f03014041500e24428a001c1100000e451080300e4202014102c0300c00b1040c811115031344080100d60526a541180c420191102000c45c80e140400e83c8502800d03144010b03502e10146056400b01d982580030460500514865011780740d0000144000443e070030414034412368001e0502d0818582198142511014076036124180547d1101030760241c92000c083c48000907191181422140c089241001440105501c00c03001050610b00b646001c4ea08610446841400e08080ea8019400109004000e1080c0595240c0c2d41051400c00e0404202409055207400c0700c00d80c88030400da22481002156403051104401044036071080c0390b220314035616048401d04001e0082280100542c40b0b8540c0c0101c40c00d00039162 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 452704091 1250 452702841 452702851
    0x8031e0a230408070305031b0307050d050d020708071515030308150126011e0e0a0b03030c01060605131d01180605090a021207050f0f131a0409060806 66
    0x14203540e032500250440703252201410714509100c01000b000500540601076280914450340107140c0d180b40420341c021213030744011003c08154008008a1000610000f0320501c02612814480d4540a220300004024021201c01800301000001c591040001c0006000c50003002d103034040208847d80300c00307080303040741038000240450031410100340b68102d080c0c07030080041c01c140342900c00005862404a003050900082200e8a828000107000124101c000701d18942080076031080d03500c1c580400d00380440806040700b0781c0c3c6a81c41c001034a0310380f020b00480c1c001024046c02401103540d21003006016038450507100307814010690003c1010032085064008401d8140360300d070310781c0c0d091402c1c401080e42d60801c240050b0b0f65039140092142c5940500622940c420307500107840f801c501c00034407100700c0004d14100400c00d0401c044401c61100c2010b80d00301c10602c10720540c4540c82b9a01c94241c10a0325044480d105501070360f0700d4101c1030000c00503c16500c0840e0148107169030341c48100c0d03070341c001980c0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 452705341 1250 452704091 452704097
    0x60a030c02010524040504050f0d080103030f021c05070f0b091b040b0121020412081209060705041401090f09020405031002090f060903011812110a020a1403150108031e0a 75
    0x4e4200041c6401c3d0019500140110b007500c000201310300e08245007200c220010310204070030100400c145a04001010034905260014010181c84010045007111480d04190700340030f4046540b5003441018007075100d02d607500c0703180d481103406c003104215503030035104200c0014851a8480580d50307040c140240501c6000c10f03100d0701c62401103030b01007038030070048007455114203a801d000015803440e050520840d400c0c02070500360350b5100c00c1c4510445e180380050106506070b00030018849459806411203003194100d1220f52402c4c2031440040f0741d0910300da800810507040c101004030704d18800d54010001c40300c2c11002c503100a1101080c11059005007030000c2d60200c0ca0380c2c3c4240c114202640102002c03038000b000020880d011618204442c4a5000c0555a02080c090620412a0495151004507d030b030802040d580c03501d03074009100300754036000301c141949124200852a8a04100c45501d034114007500d907241c2d44e15503108590302c0e0031118038a109032050003a0786000a8400017218000000d5907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 452706591 1250 452705341 452705401
    0x1030204120b040317070903150209030d0e0a0320040b03120904020d06050402070f0201020f0a112e0e04060e041a090f010e0703060506030303070504030b06030c060a030c020105 78
    0x2895400b0107090080040c0c0601c07132608045880c000c05041d5141c416035107500c032050348500b9070900304d101040012507002e48500c1041440e6052b900014900c96501041c43c003245104100000715514000a50005005106030842d01c88090041012449a0001643c08010000c01e0004055680810000c072418544e001c00c54a4003a042c550010040350100c040302007074035941ea1003c1812684200b00554800741d00c02c0401d01117603410700845a1003100417000b0204a0010740b2030960065030758808521036000304280e09280030726100c072813a001d8003041c2e40c2c001420b82002c028101c4101210114840c516144001c114240c000c5852070140d0b405c0201c2d0150340c1c081903003079004448060502c0000e8400c0d00030480840c40240603402d086090000034102d03443c035514154041c0c500c05051144250014010000015030100030340b4201c0350802911207558940c200400d003041d1407414241d402c0303500042c640040d03682680140070301d0f00285e4020041c580c5c44601c0300c036965041c4019003405501503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 452707841 1250 452706591 452706593
    0x1d0d05030f010b2101060201090204050906150d0c0f1503200a0302161709030c0307030f020108070c02180411010e0303040504020d06050a0801060614030f0115200102180103020412 79
    0x1c03800b80c004410001c03131800e001c00342050800c64056090740010300507911032112004508103405007d8101c82490020012428071070441513012202001b040d0050b8038403a003100a00102e04500001030402c0b40401d4132990b00c1d01040d1b80d0082031122030001180c1031503c001d451004034032510015900c003e45072802c0920984080303019600c14404100c0301c2c0001e0031110045007505d40d1818215444840c0141e543c0010424142459401c3c12a14400d4022060800126490740101409a90309182c15107480d6250384013618007941510f00603421000d05503015462403402c0c40224043c130302501211455016070001100c9001090321100d0b0940c005101c100300f41d00385034001e00142885a1b601003040c0361101b000c0342007072566500c0000c440c3e44603541040082d800004480444804800031441c0d840c000c100c040f41c00c4018801c07404d0b0564101c0c8414aa035124501e10300344111b070b030035039a1079150302850064083d4101c10101c0d22646410040d0117510740c068801ca5044490703028151204002c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 452709091 1250 452707841 452707859
    0x110c0d0201210e010e1501030503040902071506060c1a1509102312030406170a021603171006090306050702030f1219060b0306040b131d0d05030f01 65
    0xd500b48200751000484288a1516040c0c000c1c10f1842c4040030000605103455a5440d02d043c411880181c00b0b000e40707000520125001000721015640300540140c1c2d160445c1c07504000350b0002c841c0400b421403030000041555607001c071414654034003a100703d40c0c04040305550030a4146003074a6041c0e0f8800344195104644c181400c020790f00c8060003030f10056081d0350b46131615041039200c00650b0204100c060301207051400c4203130544a1185040110b0a0501744540500721552012228032a2180d0100140c2443c103550100d070740f070a60212110f09004182c3c80d019102084001420080d0424040010180310702d0703190b08022504c003991001915840d5840f004021b010281180c021400104041745059000c1402030a0425440b03042c404a440c0c09002004004640c42140008038206502088450725680680760040811500000d15540c2c620004d100b00803002c008107045414044003060901280307002140008141d416510ba0300b0700701030300312941d20044a4a000d5610310000600400d56 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 452710341 1250 452709091 452709107
    0x31e09060a050a030f0e0a0f05011d0a05070e09031b0705040c0c12030203090d1805030a1a091b10030915060503060a05040f0f030207050303030a2735030a0c110c0d0201 74
    0x8010306c0001181c100bc050041d0700785810b910b00d030072980e21007208001000410440c00005200144001c40c07181010030f407003500d902c12001f068030455281c034032412150350184030500081000400400c000e00c80c605014000308003520301543c010540c40284001d01d802802242e1140ca403c0000e442110381e44036096034030146418182d081c10307141d100c01045e11f8604000c444141030045a01080c161641c029000004000a2840019411202000c4050484004040d414900481c0c000401d5110260101c004003103081c1c0c060440744081c900041c1140b503940c045803d88100741e003500c506a0b200c83c000b4060303a009540051504041c484032001241c280c01d01501d03c144644140c40106030b541000928603002601d102064a6417041012000c03004145048041ea241c070300d070403040a00f15220601020f810102003034130381c009000d03010350703025600000c0e1103400d07060b111003a245c4c00c004030402d008000700102c540c0850380c8038007a131100f502c0014186c0540070001382140041c82c000c1d401190a06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 452711591 1250 452710341 452710343
    0x602030301120f0b090319110316030e090103030f18051c0f0b0f07200d0318051c1704053304061b0f02031e09060a050a030f0e0a0f 58
    0x12030003c108800102d00d5400c00b4000c6040c01e00442d150620903c2d00030b40310810025090900141c030342c0c10149180048180c800030034104134011a540c1a90070300f40d0f88001d1034440b40707501c0b9090100220030950414051400b9016a68420150f40f00f0740d1b0317021500e01018024194070919400a820303440603a005544495803007100c0c1c5003c0c1e40000c1d55090b550000a41c3c01003100407061040000007544080d803110780002d4898440111905903c6054031002400d81900c01c00d925580c401111001110a0030b003021b60140403610908100c86514010040810350700e0009240642080d01860036040c0b6280102d401c00007400c0d408d407442108000043c0c2010a0711101301c0c3c1c8104603400e205079000700c2e0b8801c90040b00302003111400f1800c0000d1020b0454800414007104480c000700c4180e00100362483c07008010034a40034285843c0120f80307140184441180e000d000010218034180d40480a00702c0e900741a01c060100507a0341050b0020380300b4001076407049501c0b80a008002c1421104440116 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 452712841 1250 452711591 452711603
    0xf03080d090b1008100204031a0a150803120109020a0f11190b06100f09062604120809011b0f09150e0306090118020d0c080304060801051801060203030112 68
    0x8101c07665034144241500316401042d90300b030040100400703681800b03800051503541500318038142c01c60f650246d0460009003d050011000d10006e22025000c0d030001c610540942410100990b0b00c00d40f047c1d4079440111955100301c0030390300010b0466554006d40d080c031055911002e000040350002161031403005102d0103894414021030820185582c1034664074940a4844e14015243c46814004205003201c04c8908201c4004641c5200303680c00708449040e0703111850180303a61100c0440a0314a2108920030441203059281880308011b030a462140700c07101245c07600410f03581e40400356170883c4d614001125001401c032004805443c403800340d801f10300e00d01c1d05180c50b000f9110301c40c91003c3c0000c3d0b00d200c4041460302079038176074501d0304000b0b01d40d00220007c024001074095074a8520390582c0028000d01981c1e117000b608040200781c40921010304400d0040700d8481d665a00005d11000c42881880e0240120015071503040234000c05680c181c500d203030010b40c6140d281ca9003c06c0503140c0080c00343e904d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 452714091 1250 452712841 452712851
    0x6060c0305220909050c1005091c05011104081e030a030b040e070303090503280311150702151e0106120b060f0304140d020d03021803011401080d05040f03080d 70
    0x301501020b00d10050540748a000403000160300d03055107005400740c8900c4c891902581d46102c00d59201040700c0d28048161011140d1012034409103440e1011407000600079420030503c000703408100d070050012039100608881c000b02280741000c50303403501c6100c43c01113504200201c941d806d000380c006001d0403502030030000b540040440e003103041000e00d030412800160384010801440c0707000c00034180c002d640c0da00c190510320607201c16108021a610310050a002c1c4040c01441090300900c40c5065034801020f0794401483d1004e07000f5110a003a0a00003040301c0ca400110f0030a0645241103407001c08040b42c1007000380d003080800d0718030b00c8501c034078004c145403200840082516400301030301c401c078000a02030b5203a08141c40d0a502140804030806141c0d0b00000c640f013030711a80051170004400c810300300181d580e28500c88600034040c443c040d80790198205900c00e2103020401980c141203070360400544440ea00c41c601d00301c40a10841c86101d1035150071070414170104032000000c1840b000c0d41040020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 452715341 1250 452714091 452714137
    0x907060c08090f0a120614010b0f070f03020102130311090c03090d0e0f0409060e0705010201090807120c0b040305030402101e05030907030b0903030a0606080f0c0d0f05090c01030b0406060c0305 85
    0x43e02d1a65044601e15147c02e12980744141c240015409443d80310005170030904c035880c1c602c0c0280a100c00286c0034580741500d10f0b013418000c9d4102d4040d4042002454000c944a00b402ca00002c40c2a10b2540100424000110030740b000c40d0940e8055000303500945114610340c05e01303d0b0560340c010551540b203584c403030035103e00350369500c40c02c84101d1140c00040703124041c0001d41d60500f24203501160541e41402560000100d000e0700702c51255620040b19498003141c103504440c0c030f403403002f0010000c00b501c509001c1499044406980729900c2240c4d0306420b0110803000311507840300c2041d40414021440240c902da00d01410203158049132603021540c440b581d03510f420580141c02d03201008a5000001808091000740c054440a0885410701c60480d0400d00e2451034601c03401440c0d607218440100e6500981102500140a01001001c2c28401c0c0c1c00e00300c40ea00e481d80a500303429030100e0310300402c01d0300c41d003050700500040300c00d503443e4140344500035101654240d103c1103a2005012201c0c080e08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 452716591 1250 452715341 452715359
    0x40b03010c11120304030206010303050f070203011d06061f050703051c0501030c1203020c10170123030a02031b06040e0f0103060501091407120e070306050907060c08090f0a 76
    0x1080c0d00c1c1a0381c92440d6100e501d5641c40c00d00088040d010140d98040080002081d00081c5c4641129890715007250703140c2805040226600861070001e42c10350a107171043c4540c11a003885c54031800c560400380c50341a20781504101c1c400488440030490f40e8100401c14013060b010300051700903203001e400c0961922101d2002080140e01345150807403440c0d40c1da4014428400b8a010711380140101d50b41d44090420705880c007035918412284045c4c820720b41051445c00b0184102040c048800408000100950716522a00020899100c50f8511034081504031400c6181c0020070400b81030f009070141491840e0400070080008890724401d070066401c010009102c0c45010385035106540c0c020820805504500e8000184c0d4010b900040c0a5418102d0f000c406030385005402d0713044019418503904548a1441c45005405411090205405466800003c1c01203c3e0040c2d8420701101c4140e1300920b41b104002d403174505804071301030032100091041045030b04015201030a4194020441150165100042c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 452717841 1250 452716591 452716601
    0x106030c0e1005120108030d0b060307050d150e07170601050403150c03140c0301060e010905030d112107140d090e06150309010c030501090506061e04090606110c0301020a1d040b0301 80
    0x1078800c0d610001c1e54234a00a040d204001202c0f5044442c2417450504400050640c00380030411b60318140e40f070352045ea142c2c140425040041514050a60040c9400341002e040c40030414545608080000001005503100707104540590380d00c01904540741500c0521350008000040074a0b00b070660744e10212503860000c000e01c03480713580702e4145a40d4035814288000c1104541030402030500c40c3c40182030115940125800c0044480380c50300c0c4001d400901040c61900c0c0d0030155036445d4012801fa801032180389100280010360042c160001c6585464a01c251b4400c5020f4182c00090743c4c20006012440340019510303041000201000441d42d00e403d02d402441c0c0c020798100e02c2a0b950707460300d43e038800d405000d480d0050141800801c49880c1c2480400e01c6d0740300d55010350283d421010f0850303915a11040568001c2c084840301000034030b480c1d41014011060714000c0c0c8a55204460040c1d01614050080f90025036440e516843c1207948a0b514807407070b1032080c42c0f2951040c4c9402041416480c24415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 452719091 1250 452717841 452717849
    0x3051b03040e100e2202040b060c0a1a041a15060d020a03050f04050c19080a080912010e0a1709130f0f050903120403090b0406080a050106030c0e10051201 68
    0x1c44516400d0203c101185040c0c50340c00711194444180030000c021101e00843c0c0e40420780401c440c040c40c032203480001d004010b0310460717952084010900040202e40000c0005003544111301e0340307210320074044480042220032140188905d2804190510300140741c20001d03006180d4580194011980c000000c8a982100b00d94000d5185e01180225002ea41801002e8009101c9140700b00a41040d0302c1300343c2c8507041070204500441910a682c01c0502c1002d1b5580c1c0204180e03003c1c1e5015442c40c0c54000ea155000d1140944514160a00d804400c01d06105400c0303041030305402880c1c080b007180d4403e4103a880c4402491241d5a0902c100d987c1d6840300511030110b01c4818100044c0305d02524488070071520505800c84a080c60441000280c0000000b206c9406c00d400401d490107a81d685011204001ea54001c035003010800305000800b15040041c460007680d40b0039041c0302c0da80c4c0ba600c0c03c0701182c083c0c0440c1c000040034400302e2182410b2070440d03030b1040d2020749825851b081c10202032040502c420380c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452720341 1250 452719091 452719109
    0x105270c0307120c1d01111204090b030d021902011106070903140a0c090203060a030210022b021005070e032a03010204062703021c03090503120703051b0304 69
    0xb000031482e8081d84450414445440402c0098650303903004246241004c0360004a501182c01c41c083e80c1c0c02107030400081c0804504540e8400c05481503002941c200d0720401001d01d04007000011a881c0101e50b5100d1144103038024071695030f888010000440700d510381641400881c980044450780c0034802d40348250382136229001010b10b54a08404080756003400914039410100e40c0c403000465a90413503040300c107404000768407500d80074005071100404c0c0e4030095102940d0078549071625008200306484e90200d4901010b0030110780000180181700344014801a082292031441c800007660095801580c1854401140340c01800403134600080c083c0060750a040c0b20701a4a14403000c1c0541e0002c2e00c00980095050071f14254010f00300315055141d4200c0c462895400010100825000000558000f00701549808240c414580c8080019070290b000400b02d00c00841d95090000c0d03074101541c00f00441c03903c2c00311151000c64a540041c02e0880e028083c80901c010406000c10141016101c145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452721591 1250 452720341 452720347
    0x203031c02070204091a06030d050901110705030a0f0308130b01090207112110150312030e0d0302041d040b0c0d0608060403020f0f0705060d090809120f070503150105270c 75
    0x84200076506c3d00103180e14403d6101d40b03840040305500a0a58580d20003c0c01d2410499164042e03c90030410560011500b500c5855100f005018a928512404500a448080352a10b0f2000144001131030640007400e038121005c010413451606030f0050640030f010b402e1007000304484400140441c03078400c0c9084000a81c0c00c812946054083c00006450682c4410801400c02150740d0300041c8000da200103408445188101d0310b0040c041d4002c100842c40b02403c1d00d98440c813410000d03000b5046030080b030030240c206058407021040640d880034092038000b02c0d40d0003166905442040345034003040044910644910000495550070419140910300c2034016021003090b02c01810715104500c0c60b010f41c00d6010b02010011926401c0441c0c01100d0b0b111301c0030030362200d0fa04029026110b03103403901e5084000c100c08a5031590002c64500003c0030030b1426204038a541300b0400d6a11001d042022803101008001007003a482c1522078103810301e40305000481c0041c1300c001c0300c4400100846621103012400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452722841 1250 452721591 452721623
    0x1306050c0c010c02032a10140117010c0801051207030807141912050304031103130806100e15040605090f0403020c100519090b0403060e190203031c0207020409 70
    0x80c09910f2042c609840214100702d1018400c1c0c04043d00b100f4000c0550414010004040e0301c14411070a400d0041034050202c08090464013072114424815540029800c6825403d9803e041c001c0368070081f05c41c1c1d40c0044a03400c2c0f01c00c105c3d0702c0200d101044c407148078642c070000001792200003900c1500d001d404180b02030001c0244050400149882e180000250070503001c0005080d007103a14a00b003d149080c6071070382d0310b034039040d03074040202c46500e4414440805e54090392180255408242c400c640280d507110380751b516050044075554050b082d100e081c1030002031141021600e41c40d03009040180f0218506030b0750001b2400d00c0034107a8103441082900c40030041459010443c41502e21010742d5151541405588014201d01403080744001600f04840d100701e05030700c103074108000350005080941e42c40e41c1e20f00d404002004000a00409070003031403c1c10a08208004842e0107003a00a4091490f0503c20329804038003c0d440040c5c90a19942071011801513200c41c468410605c1c46604d44861612075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452724091 1250 452722841 452722843
    0xf060c02120303060109120201051314120d02070902250309170d12020a17240d120c0303181101031b050a03110d140117010902030c06031306050c0c 65
    0x10034080301420342e00c01c0080c03025590703200d402c0c0005c5514207405c400f69000d0318801299684a818828a0402d0003200003280580c05504007149462007150980040c0d2494174144e80c40d0440c54200b900940c0003403600b003010103016002402d4034401d000064900c0c45e4291300005e07051041071016000208002001e20084044003030442658441d440209045035514100503c803103018000c0048017030700411552020b6008003000001184154180d0403a0f1030562510106030302e14140b100401b1501101d45900ca080445000e40c416421901441e80180046020f503100350070703200b044082665501680c0d4881c0c60340155085014412800b81c00111281000101920000101d0100c0c9610030026001e4868201c0704603a026140c0e8140826003c0481505440c80d0041140a003007290800012410002c845800c0300d069415030a400b900f0307900c0744240705088401140000390598400c00705a1080e01d0302e20080c641c40704241c022204c0c4080e0310364921098900070744206205000100d151501110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452725341 1250 452724091 452724109
    0x304030f0507020f060706020705060f06042007080a090b030c04030c06051303120c05010213080111040608040b060d060f053c060609030a030c0506010e0f1f0f060c02 73
    0x12146452030900840f5000076900c24002c440480c4581302c0000d94408000322501a15010f80c0c0020580341c4a241a0101c4417001c6000c1f201c132032049260001c0c9290030707180d644200e04d5103410344a105041648036500c0d1025079014040383d000b4000c407840005000b1584100651140d12202d0805844615500e031010340020307a03400c040203021050266000e09948211804200e030b812862035a0b10308019001070f44e00042401c0301400740c0d40005080e0703034903504d0001400d04840d1058020440c00c00886068481130281b406081c0000d241c21010a012172012088140c01807001018114000c150759124821210900c03a2646092307250390070000c100c2100780501c1c005c24150000c0f104201120f519825a02c0441005907880c401d441d4003041e520744548017074407101d2170090120b6100440d00c1c00d016080c070f4503644040f1082d00c2090004038140381030041c0240201d03032004080500fa1100c030f40703510244454042004402181c140c0010b1408607809241d0020441612a0080c90b4024014030603124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452726591 1250 452725341 452725367
    0x50c0703030e1306080d0311252303030406053409060806010c0204092a150c0305090f0111120903061f0e19050115080a06081b0a0801050c030403 64
    0x1481c0080c10000000c02080004401b440340c40d0024000341000034181e090b001e40418048640e680405c9071318002002c00f110202a4001c404246e00f40000d95450706400b80702800d4151b007a01f050020070001040782c0c10058000e5003581070743e50003140024040000303682400107001990020150740da03090350000c260340060145803805108038a04100003030138100345c41134001e001d9540d480c59081403000541d10307500004540800e001c000d103003000322480c012440e40202452a2410700c00010124003030f5400ea010140d140d12000d0400c2c5000c1c08006041c410200118144080d580040b5030042c014007942441040c40f07031a107a2103448c1081403510b8948000c0c0100c40044841d5a45400c01030240390010440e80e40d149400c0c001e90b00c524660321103031030000d40d0006903810940003142d9841e080382c1c0d10a480101d0f5407101302c2d590740e5017101002e941c0c4c58032500d8a1350700b000c6400e50713074084024a80d0015200191a141d0010b6403840d40305d0841d44102c6804a40303400210a00c001c15a1010fa1501c0c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452727841 1250 452726591 452726629
    0xe062502010528020f0703020a0b070e0906040c020c150c0d0509060f0a110a0501020a0e06070b01060509120f010501030c050a030b010620030a090303090503070803030604090201050c0703030e 84
    0x2e10b881180d03d42d15184821000c095100208940b449420907034040701e0802c1d1101d0f0310280c40d03844620700699500b11007041101e40440b1100000c0300382e4421001a905114014010314440c0c8400c1d00b8000200b1040b2102c10031800358102d81c864a0721000a25010260804105692401c0c00128a410252040ba080042050400042e4015a1400c003580c3c80260031850071955132291100503221462064031482e12805a42000d030203002040d13001c0c0c0342e110442c0d1141c0240240c0d80080005174451203000510784080d487c018801103120340058409441c0160243c0e018100044405190081d1280c0c260801d1391110018000c0040c0f00344110010001550701041c45800c60791000104481401940200b182085103014203000b1009000b000c603840300309490f0b45013202d48008024201034081900410403e020000b602d0070001500c40c21104060061400c5440702c908101c06440c0d0200168100f0101f48100c840c00e07602170000d40c000b1407007515050807501d0000e080c0300c0e401e2241950002d00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452729091 1250 452727841 452727851
    0x40f061d0c0603060a052206060e13090503041a13090b0d0b04030c06020f0a090506191d060f040602060c0403021008100b0a050d140405120705010e06250201 69
    0x180d54000a207544000d404848494590350341e50040307110380559a0246901205440511103c80d9009001c0013200b00210b20601001d5150f050035900d500d8410303000c2d5081440301407074a500c0303100380d802175000302d106200303803440d255698841800080c1440440700d010000040c505203401911340b8038000a1520007802c1c03081c0c1d84000000b49224110f098054070120f40d00d0001010076228810400050341c1c4602c0c02c54a40340c1202008a041d00050401030126202960200b0140703041c8058a59032081d222252040741c0540d0001c407114080072030824540c020440b9203413115075036407015140c0c0810700d031031454555140100c000e24041b0040e100303c1419400300400d002607200d5042481084045042450040e151140140e141c05055407100700e4424001c0748c03d10515500000070003200d90124424030a410b0120240300aa41054800070400e6000603040281005848003401c1440d00410000030b0101414000c035042040849000909641c50403c8a002e40311404458085107494402088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452730341 1250 452729091 452729141
    0x20408010f0525020703151b09030203120c0a080f070c0f0806010b0f191e03051006180305010e0718090209070813020a0b030703230103022205040f06 66
    0x1c052614035042030303c00c0980084102d00c0d01d0007001500029980001009102580d61280b000103040c46491880901d00e1000c1003c0150310420205c030999030018041c100000442c0c0000300340340c1c001c1400d00045c0c068000c0000203c0c51080c06001c500300c3c81c0107001c1c0d490216140c901c000c0d846e04c3e0040d015564140074148020500010000c3c1910742100c1c0181c0e80322400300c06206580182c881d00708460030004002e1000700e0303100750840c00880b06000f5072100410040d9054058a808403415031528204690403ca03051040f401d0110408210615404050300c9840749401e64141c0401c15183d6480050100141650210740021100c0d607520204805202640054844100036101310104160f147c0403540f62003052030041b0f8010b0340103040310946c5075504c08a07009900112060b0001c01d02c0c1035000d40040641a070341c04043e454218038003105038215820004041440c0400d201c2c462786080c1c0c0b494040c034943c070885004501030042011071751710700c0c03400c0b07030980d0109000d0720161811184007038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452731591 1250 452730341 452730361
    0xb091f030b0f013b0c070615150302091e010903020306180d050702060307140d14010e070c12120204090507050910050c07090902040f020331150e0c0a0801020408010f05 74
    0x805481048030b40e1105480ba42170140d50341c0200030000d06003906d419001040000c000104a086030b034620200703c40a00103c000364100d00451916036004618541801c841030740c002c5034203070441c0050400800031500c0f42c0100340741010480d52541046401c00c8104d0080d0800c0201c5002d00042d4a4144e103400e007150b000c102c031800003900070411b1140348070347c801e6030a19100035038005d5003600c0020020800e104291a06100082c811918041140b202103410203114034100c0048a8003d180c48520124070f540807507031a282455032001d4240d0910002c1800c070310754000c050041f00d00e580c0d29078a80b0004410481c10852240300030003070000030422100d8000d00402c0000c00c80303000350303000610781c040c0e400030602034201c020030100e6003440001005440e0400c56240c01910280304d18000c81d58113010244406900c00c001d010301030102544030040003030344c10f8024880b4049458103a5814690b10008114035540e280c0211149035004030b024002d0800074031594540070f1002801340480e090102c006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452732841 1250 452731591 452731679
    0x7020712031d2b1704080a0807030c020406170f010905060711120a0f090902041d040809030105040b1b0f090d02190e10090b091f030b0f01 61
    0xd40a90000090b819000d80e01d070b28801e020712210040c0318129042d08014a0405440c41104032101c80308608104082e50030b80b02502c09444120300108080251380d00c625040ba040018101c1c10003001c10944801610b0b1402440c0003003100040c2c3c8603400c2d2003212410b080401c000d424860681c98004490049080047c5881d006070b09810400001d410048180303040c161002c0c0c54142ca4440003401005050307018486e407180040c1c170756485024940780c105550a038451071080b10360076a050103451000700880803416402a20400c001c5207803040e401c01003425901c00311400c1e40d20700b0b8200c01b01b1883d1079420b200012001c042d480c40c2c030300c2d02c14545c1a60543e801089901806214504580021511110400141040100c6007130401c503985070340c0c0ba150200200c1e0f01015031801ca40b00029100303410f014100380000e00600c40400c0d5505c84603250040807115401c411403121003a000008200481003c501444402b8002c3d02c032076040c40880c4603140d4020340301e00c100060096210800b81011440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452734091 1250 452732841 452732867
    0x3010504020906100c06060b0301060e01050403050a0b15100207080f012306150309011b0c1511040b1b0d08070c080a0519030f060b03010b07060906090503030f0702071203 75
    0x1000013460060040750810401200200b180303181c9440451207038030a10146040b0380f07083c2d954a1449400400464483c022841f0040040d800070111400062030080c2059011450450502c52601a00001903c0d040700c0608400541c11007401482100001e02411000c81e0000d0028804611140000340d52009441040840041b502e40030802656640070040c203004410391410f6220b041010b507ea0003009281449219410101400c01d503d50240d1b010030602c0d6040359003500a089005007510103801295035120481504100110b10280000c0c082c6c40036515424031450019947e10034681303032805541280c0103000b20f003420002d0384c0744d0081c03e040301c0c29804016952900c50140064401d80545049407940e611a00c1c01c103501180c1c0340d8000d0720123078420b44050046507a100303040f0113544020700811000404c2000580b0105640382c211100c042d1207244001050001d944400c3d09541050b04c0a01c000600c03c000d20401036410018400a015010491030f161401c0c0d690241c800800651 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452735341 1250 452734091 452734099
    0x60f100809010b2106060a032a09060605070201080105040e0d0c1e030f02010c08060a050f060708071a070806010e0409060b03071509080304050a060e03030d240503010504020906 78
    0x9480c21000f03402c04169440050598402d20349580d0511011049980e082c1000d449004005101442c2200d0003000300e80c0c22803201d10100e00c00c60348101814102d410401480510b600d000a0b20981510540b0024402580d4040d10780c41c8510005294101c1a44014400d504180200801d00c00104490034072040c1d504001d44415403d20f000e100340c3c01d0900584101142c1040071105054000d024612041001d5008001d00310710000140c400007829603156402c2807a4000910880c24500fa8200100800800c014101000b96a860510354000c003000c48194800460703003510700b08410203040d04604181071525545c500000004d29003c9651203062003203448010343e606010302c6a0050308601d502505942285803074180080922000300d110000160103c440018204004402d40b000e9810043c800b0000620304601111070001a251550741400200000d5244030041d1099402040c41d285400104c54020b0361080b2100c0b07034980c800c6019034101003c000042c1d0f1015081680030504072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452736591 1250 452735341 452735357
    0x1d0109050402120d030606030e0a050c0111070b0d1d0708061b04030f11120106080c12030f070302101406060d1e090605010e01060207030c06120221040308060f10 71
    0x40001840b40780c4080100b00c5901070881204c0203580c0c103030442c0c401c0e186607403400d0089006802205503284101c41002d440d13038002c60041642c6600c19240c0c41000c448060446104540b541e000100960100c508010050b6691004640210703000181d032a512042a010b421103034134002c80300f034503040020030511304000030061a0351712402c0c078005e5501942c1c00203501c24180a141c80c1001d1042c10340302c450791040300c0704248070b9000030050140784161541c0c0409030410390000002c0c02514004d00c82500b245010030b0000800c414121b50280078864000da000b400420f52603032035101100d1201203d40d141650010800505840d00005c4030300d08803200c0c1002800407128403000d010200b00000f0744c42c0c1c1d9410280180140403e80e04040d0507600058000c882d10313680d500302a0303a02c0341540f00c000c18140300c2c0d030740410020b801080095003034151010090301d0710040012034036030301002800303603c08084080180002e050b03200f4286640f14006a9205d4010030140000034090440090950204010301d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452737841 1250 452736591 452736593
    0x209090610061b0606060305060f0319030e0a17101b0503040f020a030c17010506060702030a021c08070602030405100e07152a02102618060705030604061d01090504 72
    0x4031102020b5141c00c50344c01c00015484420040c05071000b518594440d600c40c0c034101c1e640e4a0301040f581d0403088044003416805020f50707415160b0030003200c0e406900c051400400501c4502c00c44c00f002144240201402240c000c40203004202c0b09840c0502c5d80d032007030700f580c40d040058211040720303001600984107182c400071078400180c280c20b003600000c01001000030000f8000d544c60062001d54407000c8000d00c02549d9100500206006040e8041d500da84040c14034009400c1210319a08510940e40b0090b05070100f40c0c031500070652007003a01b110715650010800051010500400842c0032507a0003c1c410000c04082d1140e0310705e001c1c0035501c0d000b13440b80685c00c2c07054010024400b8018000303091669056144400407030320340c18600241d0203000d2210715860035602c078184060207042244444050003600b202c0c2e07481c0c81c800c007c0030f800d0310820030200b0440340801000001d00c60880741c3e8503642d072450004144026101503a2191440304841c007a20104900145034850640340325001c00941581c507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452739091 1250 452737841 452737877
    0x201120b0f060c0f0f01050115050309030a0c080d091a071d04111c09020103060e0f0a050c121005041d060f0a0b150d0c09150305070519020109020909061006 69
    0x4c406141ea105102c1d8401d03158000c501900801c1c1254580827400400300c1d2440360944a0348402c1301d500105420401c40507a0a50040007010009030045484506020722403082508984403000107550400c0646c01a0306941c401c038149039809025031826844166092001541c400701e0411844c0c032071500d8500810922980f40141c501d190000c2c5d9412048584008854000b0010044281e0001c1d007810400720707894141641d524050341350596125070039940d030a04440100000303003201c900755608010300031489544c07c03185070040c00c0000700d1031240c602c0d000030002250b004240607a210a10000c18040701003001c1380c21039001246900542c880d03950f05039800003e000311800254480b407900308225400c04034001070002490610400c11513901741d002c0c10340d8540b030203119044200d408501e0300b40c0300302c0c0703e5000a508503600d82001401c04a401008854000d088030010005030342d0307900030105511b0700110752601700712048041c0c2801d0405040962180c0c03a5405458140b0408007440c2003403001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452740341 1250 452739091 452739103
    0x604020910090306150b180a090218090906090307140f1203090f0307080711040902040203010b2808060121060e060306090111031303032003040201120b0f060c 70
    0x18014100341040081d150007070140c040500096424070f240400928440031a0071444d0246da9004007854200200031a0303810503030024114160700310381c400c4000610301d07101d07001a11200f03c008441c0a240e101101c1486440b071002444070525a000c241401002c060210890703c0342e942140c02001c031801c503041300c50328001c00590150724501c903000c802099010040003447c0602c081c02c0035240740d88041480c213960303400b48030340c0504001800c00c0300400142045014194804000d440440c0a0314282c0000f4201e8000340d01c00104a44001600044131400e40c0072642d8104c003005e03007101d5603d0407610003015400020004c5062001d040800701281e4041030441c1e9007014000028040305482d064403a0f003d0409454030360181c030403034010034850035041c0130380e50802207494405825540e079100400c0d045a07407900107905042e5038400300e1141150803113610342a00c008017891a070b00c0c2803030302c0014107030309800f10480c1007a0710f40044121701d5a110b0346e00d5201d4820481d4a5901c49070222060f40c2061 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452741591 1250 452740341 452740357
    0x40204080303090d080f04030f053a240905190906060609170a030513030611030714042108190e030d0309050309040c090305030c0105010e0a0e0a0308060402 69
    0xc0710100400149003800180c48022414075a51452540ca074907030340080b0048281c0d00140403540c041480800648108050716841c03000c654200914840001105620780d1000d0000c04190700303000100741d0701d0045004140c000c40110341100f030764610821107489803181601604205980314000308501c05e00c200d039421100180d11000b041000b040d481c0a030001c1205102c0c03540481c070107101c0054100103425800c8594034141d4054081100170340d9044440351f00800c2400500000248040301007106803003612196281400b44596a041418000e050030304048588070700d0341d4080106102890112201c4001c00c07030880d9120034510305916040c00b881c05031b00462401503204400b00c01a46501064010352010141c042d190b01d80f00c198821800e0310413840000d41154407c020132103070303400c00707611061314039072145410900281c43c0d985190443d0b0010600418681d15100180320031750340e400d0302541008a10804010181003900c180742c403081001c1020b01849030490000e00b5648840c0c04441c1c0103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452742841 1250 452741591 452741593
    0xd0f060b031902040f0209010c11011404060201021e09010c17120a14060118050d08040b04150305011d0412032a030e010203070c080307020a0c0e01081b011d04020408 73
    0xd0420806000c42c5403080005038811170902e040c01c4c09140040c401c55a001d001a5660084003c140d00e40300020064003101c0c504011b40c1c0700d247c000b80303800a80504041c2120303030b00242c0e072030150b405d4003501100703000d0512000c2081000b9102441e03800c090b03c00700c0395601010110b40380c243d500f11703a40140507502a0f03800000001303080114800003503100078804c0c8023410511100b5111003004542e82204c43d0700c10190207094400501241c90403d1203038800a1181e1007080c41c2640b01c0405c042c81d600a07030f00250b80d4101c0c4000c080c8031141c16003c0c40d8058404040c0b8134428250394603d28110501c080c00150400c0c459a0140422510030f4010718454500c103100d1803150025400304c0c1c0d006d1400100c080c400a03142c211540700000041c002c03070707000da8510740d555440004103844032209540040d05c407005600c0750091034400214004a280001c1226001c1121650700d002a01820a914056404d454449441300e6111581e00070660a612212112001b0742078010180814003e1003960041a01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452744091 1250 452742841 452742853
    0x60c0b0c040806040602072006030c0906040504020f0c1b130507030b03010c05030702070902090a0e1e010e0f060105270406030b04050604022403010e10050414010509070203090d0f060b03 82
    0x901590346c0041508521542a002d031170280101800c0c00440030600c281d13806038041010071040b117400f00190103040300045c50306183c030b5503a4000400b01d9020000c15802400c010036050600ca0003070010101001e01c040000e2690541900043c0e40b25820848445400f40d40303102103024030307201b42d02c1310702e401d070010707008204000307640d100038010790400c40d9080300510501002080c140480d0013607811480020708684045400d02406190040e002001400700620341d207840400400d02c000107038001d0051441e440501c0c10541c8020310440001444a4103100040102c0b80d12040e00e01005440c0300d1160026100c50344000000901410b0a580060032250700201480b05002c00882c0803402a84200d52482c3c00b40d005070303030048030418120100c0d0140da0052004000c4040345a1080c0e40c00491981842d000e243c8400020341120400b02c054500a011040188107904001032490b40100045c0000c6003048190000184001d203440c0c40104040c010503d64410840e0b1600925070031880101980c1e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452745341 1250 452744091 452744093
    0x50a05131503150b090f0603060312040905070e01050c0d110c041505040f11120a0906020f192345010509010e010804111e040b0406060c0b0c04080604 66
    0x500b4180f201c0c0f08050f1081c00002a11500c010100c4104403006454400102100e104014050304000d06032505401010004905000d02c040141701522842c00c0011f207a081c669001003101128224040c140181004203821000001664107942400f034502600c5075001c241000382891410880b8680060912290b81d8440e620000000c0a544059504201038000441c0320002c1d42c22011003912951303001c01200f001c11504485269200710758810214828400f41c1e5031008a070300c8071074030b41c13203103000032031030181400319207281c01801c0c0507501d40f0003003e5007049140810404940d071594440d80d00020f1542d0182206071707407024582500c2003003440449040720646200323600c1501d2511420040350ba06c3c500c0350300400580f40e4004042c1d49001c03044110100649003d8009001500e12100d40d4500c084191b403081010310f40703800c083c110200500c10074002e01c010f540390018582e1042d82820010312074982c6c01000954145c0e007064081c22903841e4442a100548100e4016039418052a42084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452746591 1250 452745341 452745347
    0x9181507020a1b03080304031404050303040f03061406060a03020918130b07030501080c0405040501020717040f090203040b0402010513210c090506100e030111030a050f060907050a051315 82
    0x180000340510703103031946101c1c00020100c4500f228000206035420a10108012a120341c3c0000401050b90780103d10740f5807100c1c002440d540260b0300c03442180d07082d503d0620410115000f00c010142d1948d07140350303803800c1140c00a20706000700482c0108041c1e01050002e03155650b501082c516208100d804c40641c10320900c010301000d1030050950361400410041540e040c441d1080754125103c0300064031001d0101000c110183c1000340080c0c0b03083d07400380002030118020323a9030041400e6001c85001e50341d0f0f2914529a514500303903441202024810300400000c40d060b02501940b0688c2441c10301e5a90340d5400b160030158150303800c95410344550b0710b4408030100203a452152050b005807403504d41666580325100c241c1e0011a04150000c20240c100c0012038024921116568001000071a040d020704491655540044411041c1c0a881e001440140c8010140c5690003040031344100c00030b80303000400a441842600300782d200f00a40000d035074044035100d4041002408012001d1826400110001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452747841 1250 452746591 452746603
    0xa09060303020d1407021c051b310b06070c030b040203010b0a03120c0203010e010c120f02030402150c070f0e041a07021002030414010509030406020c01030b0918150702 74
    0x118094070460003c1d84250380a40e4070000c40d140078104142c07411120303609001462081d00d60003da042c2400307040500049051203090803100100d6a10500705180d4002c014422091070b03d52800d0041008546103101a8451410446500324001103081c604103004160644645c44019000504000e8003108007e1698240390080d8021002840002a0360f42003042d410000d2100600c2d45108254a4803218083c41460358018001000005c014842e0700e00c0c242540c106252490000d07041041e281408000c600c6040010164080e0450461405078007142d21043c501250420314040410300703009110040128101a04a121039070f50f140795110940d521924040d201110303a451114070082d80c40c0c96060486208080c268000e014019078069402c009600140058031100d903819668034400e0000d010b031502407040e07107008560b40c519120000341440c1000e06414101403c20740c046070705640c3c000400c3e0f00011a0a0076800c00030140121600e0443e4049001b0341213000c0d034080040258010036070b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452749091 1250 452747841 452747843
    0x61812020a03030b0f0d03030e0109050d17010f0602070501051e1606180b01210f03050c10021606020901030213061d04060b03071b050a08041a070c060e0f0a090603 72
    0x14081d042c840d800704910480c0c4407803c5da4000a0860104010034030036003204aa41c0e1075400005406219600c8560070541d103411440c0210300380c07100c9080341c0344242400500600d62019a080301b80c0c14140c00039111803040c466141009070105410b41c41d000705248a40e002031030074804554a404410050000001042007039072040c0c0750404107000d102c442c0c241d070200310340d22114030605c1d43c0c00d1210750b0259042845001e8a08107031030f510000017441000c00022100d0098407000c0e101d4680b802014a40341313445401014440c01405452800c83c07901080001c0680d2225001d0784550010004034002e018003610700d01d220904010000d200fa03002000e04010740d11144070b0240584051043c4403d07640d00c2d2040d5024034000f0000101407511400c00500d5180d60301c1c05e11705075180203881e400d2038160758541c292258000000c0c104010031b07200615250a8050700145400c0a0098a403031745d5400e41031140c43c05011012049070810b90f81c104c08031070700101c0104040700c41c0e0344515104001b82a2408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452750341 1250 452749091 452749097
    0x160c090b06090f090703060305031309051008152d01061b0302030f09030708101b0e010e090702010b040c1d0108011208070507090f0c0f1803061812020a03 68
    0x100c406034078146002101c91001000d44240c0c0b0034206001031141c040d10042c040342c1096070f1820f0210000b00184000c04894103084041116541032403103a504540c0c0180000c1034a01005804010b03d0002042c101c0c20710700042d102c03603929910224020b421008401844220070241003804012a1840c2034060684440d980e5141c211160012610700c041990034014015070302c20301c00b50040406040003400c01000140c1074070071490799200301910300000414404000e68403805901c0344e01c800401c0101c01d0007403a291400a805044001030b250b66904096980113142420010350080d00035085100da0030b0000d0010402004c03100801440c2c400a00d0000c0b80a0106030300c42449907206220f40c5041c1c503030400c1840820311090b070302c00c80d0a0340400b004451780e0007801c00005600d0b1041c42002209021486c010461511501c0024610328441213100e0602100301000308404a90710701c60003c0e40d500c030034000b640d1009140000311040e2030f030900070440c48484d81901a11540401e128078114441d807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452751591 1250 452750341 452750351
    0xb07020d091818020d0506040b0a02120609180f0c09010f0605040510030902030d17070309030203030612072c0f07020a020d0312090623040203070e0705160c09 70
    0xa4201d400720035511500401c074410204805900a07240e0090020142c1043c0001c1016580d90116018100744d10068680c6d030050310800040c040c0300d8840070780c0001040400c508d0702d20254071007088100080d0a0f03074060f40303a810000d081246051045400d040403241210329202040d64420f5603030b01b49611140c0910085400041c0203405c5400311000e80e5240d4462a0a00e410b01c014003101141d400e0380282015228140080562014804035003035495998a44c070f05010324000768202004007130b10640405107031034a000e000c44c0e03000c0160381d000740b41164247d11180f035001c0311038074201042d080000840d0012400d1a402c86024403208000107000b4100700c0596900140419000c50484110000d6004007012000628102003d50503445c030a06002100c2c01031003101c00c040f180c80c81400c9420b0b6a8134000c41000004003c06440540e0300c10612401e40d141c29030100340c5400c214811080060040404211454080c00c2522410808162070360200001406d0003001d0b0201c61007080a410720340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452752841 1250 452751591 452751613
    0xe04090c15050415080402030a0b070c0c05190302040e0111040b09030106050d0f0201050a051603170108030918090a290606090607030e040f150302030d0512070c08090901030b0702 79
    0x80c010703602142c4c40708203800007185000e941502d1095000340120b0313150090040320000150b01e00d00c01c5025038010754400c29001036501d800340030380d0341e5074100c0c40c810910074040014110800d1b441205407039041d42c1c003040c0781c130340c0c06002400340098020038040241c005c80c0c00306d032088800f0003404c11072104a000f440b0540ea280280003140025110107811004070680d10380240d400f4000030a070007405031510350300c6c2205020601480c41801c00c8100d002a08240b244100c103080f00b004103024040b80700c05103150140900000355103100002440c000e50100c04001000c9070014006420002d40008000c64040f1465000f2010030302241a13074200c4400242c0425031138280364050700c00440300078144600d8501c2c50340701511154072090510364416107a260340c00200400d406201280d080181501903da801c5104146c100035604810b501002000c0c404103510682c41c104540c0c200c41c50b8240b4140584542c02c00080e5882070311040c503080244c5c1c20002042101400409200e20026401e0b140d41000c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452754091 1250 452752841 452752847
    0x1020c1005030f061c2405041b06030626010204030b0106180b030c071e02030316060b0312160c030605010b0c0105070c0209180307050a1209090e0601060305070e04090c15 75
    0x1030b51440700b170000414a20313040002c5122000460f00354042d8000030403040c940d0130380c5090360b004403002c030b8120003002d1034020311502c2001030030b01819846c00e0034000d0130704200e204241c00e15080d01000c0400d8100e100d0b10703142036080d81110301954012015500075a141c1202900c054020f82c081403071282c04541c00204000010107807801881c3c80d06900e480c00e2078540b00c840c0e6417004030580d40ca400e00031005460061b5010001030030803041018410303001500030b04110048071500728103980241c20801701074007000040400c9070102060150340402c541c1c55410041107a10090304001d00051420f400458528203060140000b0340650000380f09580d1001d83c12546548403650003500000c090000c20650b03441044007001c0d00e904402101c0c00e0403c29240d030762904014840950f81007004685180400b51b1019400000e000464401d0184180c001c41180d9140d01c14481e1300e08059954010030319142c4a4646005d0048000340184038004030b40c20710401508040c403925505c0084d1026084000c0c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452755341 1250 452754091 452754109
    0x106020d0311040b03041103060a05150406180509151e0105040b0a05120102160f0b060a080601030b220b010f060c05070515070503040f06080106050f0a0e01020c1005030f06 76
    0x21010b85242000d14111401c035a5801c06442101c1410420080c1340154400b041b000744520445003000c01d00e8103090101c520094400c2c00500d004506003581409003d2130304868a0745003480308400102607503048451401c180d01d42a007012408049024881030a5a0040180c8140e040d040500181d990740c10801040f210b030040510381001040101700b1061801c2c441240c5015200341c009803600180b52250b803c0b1f1954400b0448806501300746401c00d010800c0010742c0c0c00001642d40da6200b42c180000a43d0b596414440200307417802c0200041d110f0f582d051b905041e0f50104e05070702880c0b50358500d009204100b09004040400724503400c001341051144441218850f0404c002d420402d06000600c004603820040c0b00e8140c42080003c903000a008200600c010500174184208860800100810001045c6d2088007048010301c20100c0c044010400c495444505040100c5400c20400041c0e00741207140804590100c034000241d102c041d0484001c5200d0020b40402100c540c0d40c120802144007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452756591 1250 452755341 452755361
    0x91b0203190c051b3a03020c270105030d12180206031611033105060712030506040522050c090907091b0801120303020c030a200604031b0305041d0106020d03 69
    0xb01d104075a03170590900144040f40c0360300a01c140e4803490303000808540703400700c40094007005215000c403a825050300c604035a8007409044000e00500d50030860020020f8602c0203035903200c161f0b1000222004620002d038110403507405004551a842d00030700312131901509109000c08120b0050030002c82100200c01c94000c010f08000c1608100d11004004049201c202c6101c4803500c0b1090010682d0b95403c4080c00405100d03001881002c0070f02c14005082e0341020f0482030003941000113200354040d04c9c4490006000d00144030301d004050a0030103910f002070b13507204150400a8041401010a408500041030b034801c00d2042c4000c401203188164000c2c10300340001d0015042d10018090142072500b2020071500a140150a01c6101e5805c1803c5501c0030100001007000105103e08c44205180d52121450402010300349514003528050000c0400344100d2001141c4881d004042601450507a070140c422003190100f050311070310002048401c203014100152007100808600548a40201ca03250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452757841 1250 452756591 452756659
    0x521101104060f03150b09031504031d01030b100f0f0519030c020717031312050c0603091204120215040b040b1b010213091b0203190c051b 61
    0xe4036008040b911409860380000c02c141d20b507506403c81403d02c541750405406240e030f0060b81c40007182c0405180405444200200078a031200300000302c0e8000b42d54445440302300e880c44200743c80c0400103d0091120400440c1d10600c0680c8518078942d1040043c0c00c005940d031114481108803050580703482c016070201212150103030307081d03003003d600c26040b1480300f100301d00440e03070001e4803040c1241210404043c11031465002041e021a0b94402000650007800415000007604100f43c540c035884011440b0000c1c00f03100000003140c01c80d0400c00050100d602c000c5c1c03c3c1500c85840b0000041000d1808030f00342d105100c0c540405019030200d0048400700c62000034070500e02440d00c49400b81c0c0d41c001d400c140960460300c0d21404070041003800141000c0309900401503113607003014014001c442848141c0300ca0010210307080e085146d0000215000c04406401861400c40040c000b04d81c400e40000c0d00403e14000c54409a802480400e4044162407045984088200744100003076903180300c0c4207491001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452759091 1250 452757841 452757847
    0x5010b0627030712120806371707031208070c030e1306060201050604151404021b03070506010e0a05040c060809120a0509030c270a0605211011 63
    0x2600610021101c032000c00941507a6500d959010b034590074001e1480203a5241200d4074200c81c01540c007524103136200d03204450000710304905c0c107040445440000b211900140384d8104000d00741141c0032a58004000402c0780301100c4111094072919040d942c40f0440d90300700407450300103d1358080d05500c6d1140c041a40c50108600c0103031001c48243d9444d141e9a81c003c0c141c0e160b407070014101c60007000c0203002d0640010440d41404001c0c04110350404406503d04e0541c110140210407121441c000c510508030313030141c5c0b1251148076054519299040c40c42d060b100005101c010413001141c1b060480e1041c0f1162400d590315025000d00741d81d000c130340c010200994080305000442c003e540ba0354000072000101e80804184215018240d44a00000d13800703e500460480d4451034200002c13a80f0f040241d598000030710f00080c0780e50144030300702800e040e10600040081c0491000350b01082c000c04000300b010450022008080301c1044881c0e46800715030081c4020110102d000d0300074030303048000021140e0300d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452760341 1250 452759091 452759137
    0x10605032803030204050d030e0f010e03070b0a3515060d020706020903060114150f0a230304030302030a0e010b131e1104081e060604110712030905010b06 68
    0x401104010720403028075900340030100d800d0311401d58201003a4465103945204038005030401c40f2640d0b104141604020b89508006100e8501154450486034650501c079142e4991100640b2444901c0d440c4030100328202400702c000114201d0071001d05034009084c100b0b50b8586114200c10141144841a086807040055022020b01a401801003c2c003c01005050000d0580000d0406400b0f9001145982030f094001c0a60311300070001007601c01882524604d4281c07580c0d0320b0801400b035010f0a0081c090305601c80c40485c50515502140101c001040e980e0301d1400c2e14000c1c0c000e400c15a070702c4800314a480c5002680000510901410950007040004854084419080030f0308403400b0610082015595a24070b940c042c0c00b40c0a205441c201180b034640c1d0600e0845c0e454034502c0b2415101015071080da600d4502004150749401000c1510007207001c07481c3c0b0340111464414120009c00c00c60074030300071a000fa40e055100203000e620520081c8a9003040504103d0a8083c2d000a00085500c9003e010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452761591 1250 452760341 452760403
    0x414010e06040308070605011703071a041703070201050a1a03030d0515030d030509100c171308190311030118090c030606180c0903030804060e010608070f0801060503 73
    0x4202900c0003842540307000d450742e44192041e04000c1d01110b241c6d441303400502030003403980c1e030001140b24010004c1d4240300c45508c0f501c03484040381907a4020032400f0804076080c4028001586c003010040011180d0301e040440009000301400c07100c040400b0700e042000808100307644188a01c204000b0011b604220300c065290b8010000500008510010941003000340c1d00c080c09220001d2800303440004991516500c01383c1007030054908a9401450100080000c1c1d400ca503c020980341001c01949850340c03400942c15030400401c030080c0204101013420706041c500c510121080d50103965090025071051642103000c1d020a00400324051a852031141c40458154003803001c250055020b45185079503610b403c000c495031078100350001d414060031007002505c50300480f101b0041a00e058031000f461a10000e14602e80903000419040e106c41d002d81d100442500030300c0c0541f6a005c182c41c1466a220708003521100740344a028031035401c02c1400280d40c5004500301d00440300d940b51011070300448480b5a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452762841 1250 452761591 452761607
    0x108010b0c0109020a0801020c010f02120f341107180c05041203091a03040506220c08030306040c110a03030c2102040f0e1509100b13090c05041401 65
    0x402d650300d000303e2015980d0000124000d010700400140c3d580341c01c21009094440f0f810191010300c1c010440f031300681c03842402075503109004203400e0b001501c0c2d0910500d00b10b62000c1007103206c403401450003a032074218410320309089100c81d20341c202007441024106031550701c07511400088407101d44608000d802d143d0400030441c03a41c1e00d0610324040d01e070701184081c5445083c05130001228460240064118668003141271540d0303000380d5003549810317515103a68040040070f0240405104210302508200442411510b40c0d02420603011551600c80c0290350303400c1107a441e48520b0a104200b50b0721401444d00540200c0761201038000280942c80030340190146030307890300401a20754409445100807000010342c210600c440540e80d03074640000c000c10010076400980365510403034103000c00c07005601040c0c2400c6038242c0c3c0300c0181d507590029100329185c05034030544054100241c2000c0481001c1100310031380350ba02008100700140300004641c9402180190360869280c0c0c0031015042d07014000b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452764091 1250 452762841 452762857
    0x90403030b010c060203161b0809011409040203070c05010b06130e131203060f060306050102030307200f0f1b1804051c0e030f0d0c0b0414030a0f14090108010b 70
    0x4855018151381d03800b81241e1086414128101445151a80b0254401514005071400e9210b000c05070703c03036413900800c070b1080c05666418006601141c1c00d50345034842c240e03039004000038021900c3e450075032400f9009501b44a412074041d480c0207a845d10f0707442e240c4c00b9a840701c0c41c02008044924101084140c40d401c01500400e070544000c00c0c01e200049440590f107010240e60740c0c1c0850600c0c40e046150380c001090707402050601d414650244401d9900000340e80d07002d0414680100511142e084203030203800c4a9a12003814041c8082e86080f0000c00205004401c145200b10b690003c2046124100d001e01c0401740c1c2d070701074134941d180c6a40811170a905d0b50003070300840c103880c0791000018a515604009600040102d441500100c5c02c07480d090140c1380c002e80d038400c094507000e01100402015084200801852401058042024040160031b440d08a04141d0116a03490b02c4011001d8120440071171700c0300000349201024001203c00c00c007038415005060b10f8068240e424040c61144940103190 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452765341 1250 452764091 452764097
    0x510110906090d080309071d01060f18080106140a09050c040527070f020d0e0102070b0a050c03040611160602031b010e0a082101050d0201320a09080c090403030b01 72
    0x3042c076002c211800005c42c0204420002020b015150030310048a003412002c00d00d9402c2110401040a15040160100b289125146c0000d080c2001890312142d246143c000300400d40c6089000300303241b85101e1343d14485038421550070398804d40d18100103081e141c08a0303030025180824003080065040044444910fa000e99002c0b102501204005c090b091a00712071802c0062907045604402c6501409100e49410840c0b8083c2810148040043d50304c02d181e00c90000508030004440341414031030001d4a0b44107140500341e80d99180d0b5808001c100388200d016160301800360443c15108982500c6501044444640181d805c05031680fa0308200c16004502c081455522a401c1158141d0140700300a030052041001d544c9400e007080390001c0c220030083c072100156000d40018000c640d134221001d2545982480d00c50740c88107072a088982107100c0503d40420315261148008444401040a044642410f5588500540d030b5041d00f180c1e03c1556554260b00651041c020030042846a0000007070000181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452766591 1250 452765341 452765359
    0x204030503070b0415050c040303080609060d0b0a1e02030601110304031a0402060405100f02240c130f06051903020a0c110301020415080a0b0102030901021b041512051011090609 78
    0x1417880007580c40071250700c849600000380a00806030885032081c1c100b4410380d0420024505040800c011204011000c0c00f4100c080c0c0001e456884950001031189103129408038200c848154040043d41040d50380c24046500c0e404284900c07080001a10102d070f030000d0340c40ca10a55005402c0500700e1000d88240d070868010040401c1503100c20440c4a04c00d8480d603211000e2100030700c4001d08200002c00d080c004548010742d4072494880c4807c0d466000324225940f2070f070350301c0c0440030600c42651940c010314030309034043c1000404a800002030003c0e58030500c0c950040000a410440c12407180441d4000450300d0b20341d40401080100701c41044112002d0300051400e0345522000b8003000034400b1040001d4645410000d900c00d542c007034208122020b000039410719030344a0010f52250f00319440800d032001620b1200c4030759540c0c0d8021030300700c44240700c8005005840300702d5245120a240700070f4505104c3e56200032150300b290710420320b1031400700d10400d0420b0142010045140e2000c001c459003d4422 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452767841 1250 452766591 452766623
    0x80409090b070e03010b01050717040e070c031706090a090501060902030a06030c1d07180e01240e060d020c0a02090f01080d0302030f060108221407090204030503070b04 74
    0x520689180d140aa44514458a0401001043d080f0f000c0206402a41407500c2103a841c0d0b000000d640a90380d00c2606055041e4035406100c100e40155400300342c91001c42018401510303008284101b0050081da606005803061608a403030001c0b0584209400180d80e0780041e18262039a4000218648200004201d06581d0301d09035080e40c000b61800171a40c0d603101410010400121a901c2c000c0c840a84000c2d651400b034504005009002080a0103020235004004078208105019501400c040c4800d0215940c4440c41e5943d8240c411a02d100c5492450452001380c0d80030340000880502c00400d503a03d0141032a05100294200d0014403540380700d00d4201380c00581e0b408240741d104050a00d440000c42d0b143c040c5403842e0068100c0b640d010306d031041041c840c0070350000081941c000000c1c00c080c0c83c40c0c1c881d100811030300d600640d04a212050303040d01803020003480c4200d4500c51801c85044850031622501071408920807444001d090b0780c0100b1800c00012041c140342d80d4007601549480f0400208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452769091 1250 452767841 452767859
    0x1603050705100c061416020705060a050304141b040c0c0f02130e1c1b0b060f0a05040c02150903040f0e15210d0504081e2404020a121e0804 61
    0x95402c1d0b1080380441c030030081c0c6c18070340c520b84180180b07031417004081061500011650903c5802c48170400c0240000024040c0800304c03290703d0b05000c0d0201103985076007803d100d140e444001980864880ca042404141441d032083c9628a00329410101e802d40d00c0c0c18542c2008200900030580b00030032921a10010b4601c6c2e814030500003035142d0301c00407561a0340350746ca00601001403150408c10901c81014100301103405156034540c0180243c404150204000340043c0c26410075500040e40181400b107180c001c607038049811b0741404803521b84507a454480c02007440e02e9006600800c280e07064121030400020003500c1c802c1d03800111100d40403000144c6072020802c1680d020344001c0b120708041c0c09284090400700310500280e081840c20f40d05090514100540303420740f0300c03480f0801210810700700c507044d0018030034002c01c40c2286c140044140b03100c0da000358820038100c6040e8490350444900055031014074075403013041d03070b4000c0b44032000a041ca550240044400a016240c0041c00d10020500001e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452770341 1250 452769091 452769101
    0xf030e0a1a0106031b05070302100501120b0f0105030a0206090f0909062e03020d05010b19050f040207030507020108071101290a05060d0f110403060204081603050705100c06 76
    0x20144192406040c840350307441c10000300c1a802001007616200a410002001c0003010200e104140303401682c80036a81002c0345400300758241601e03c80c2c54803000040c0f45894842140c186403060f000d022403a80c0b8110301c802090b001b44034068064000e000c1e20001840d02c3c100620b20010700070401d00c02c50000101040d0440f4080b520000c40c2d50144040c0000103018080c072010600264a18407800300b01313440361103008103240c4002402030f9030002200040100a4100f9210304030050700f41c100300c110003d14820b1300080c03480385c18019110082084c3c0c0c103013860700840c1e911a030552901440c2c60351950044400380030003820101044001e07801540600c1083c00f1752900c00b00000719504007004441400101c1d0480754280c00c2c81031011880c01c006541703400d815600040d00da038a001803118140b03140080070301001005c2c40c40003540041d01100b00001c2e42d0150080d10b03d11400c0700c10000303c03886000d040d00c2041c007014240341e1140c5000c011515007042450014112446c02e20202949540c498041d12 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452771591 1250 452770341 452770343
    0x207062a05060f13080d0903020c03060c090a090204030b16051b0307170304030c030e0301020412050a12112a0402160203061e240d060b130203160f030e0a 68
    0x60046414450505400c00100790400110401c4c43c2a0300300d2076455203102c0c4038400c0400640303500c0748011000c0c94000c3c0140f00800701c010b400c2d1429031030020300b8030100382c0c00050102d02c02c044200000c03503070302114400e03101541e9004000064a4907829181c07100e9038082d00d00c48040102c03c20100e420b80204444103061341004030700460321002146030100e2402104294040c15820601c2000003003944a00502d00700d541500303111030404001030101c0c1c00392050750040c031300c0301180d50022001c05c44005800181c00d401003020310141120b0030b00464120741c4442e56980b4580c003800349840b240107a0020341e00e0b80d0b20396400c00d6000f20802004203059030030803000b405200d04650880c81c15802c051040c41c0c1d2203030000c0449410b19500006410040e44058200c1c44080900103018000210420409502500c002c00c0c1050310403c500d0118060007506201d94000c0c80d034112801d0006055000780e9010304091440d0004545013140c0440c4c021058103140030405407208031080c0400414460a5506 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452772841 1250 452771591 452771593
    0x9110d08090411070f02040e07261c0519051e0d0f050601021e030d0603081c110a0810030b0901020d0e03030403140708190807120506010207062a05 65
    0x4030001010801140c1c400c82c54003814803c2007100d5000200a590341c002d1507603040300c0015189416205003840d02c040c680180c8211004481c20740404d504041018600e01c4100342101d4143e801240510fa0740c0c1d8150b507250700131078003d0105c4046e1f004050054404c0d200585003440c00c04001fa00f0b21030015a14204042103164001020241703030505010f414800c402049082c0080c0c100000000e540311000360514081c0302807c0810055a80c040c4202c8082444991083c0302d200d03140c0c00d1a01c05c07944802082103040103008120b10b40c4034080e010342c0301800440241c0c40c1c10182003070340544020348010018141442c0a030004800030310076a0704180992060400142c55040a284540807122100d00444050f4028820000020303030018068843c0b82c107a80003140c07079006910b0150420302034401d8a5030115101c41f8400d039200d0340440070509c507c155954400c40f0310340c000c0802e01290015101140103130800002481201e009986507403030843c020442515001c00f03605092030483d8050011215 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452774091 1250 452772841 452772847
    0x8040503091c060b010c080f090307030602070b0f09060c07080d0f0f0608070b1303021017010909020906180a1e1118031906050411120c010f020706021009110d08 71
    0x2803107202c0c81074101051382030a195222004688502c05140619100d5178a401c1c000562682952400c4c403202c0002d65004500b0b6451341024502a020200102d40128003409420005002c401001402e58002c06202e42c00c50324152140d11805156070102e0700d4000d0590302d80244803a001a40d12413200d4122120400017651410250440d00b0101e40d0390120116540a00c07111040440200c00c08041300e5044400d0813180c51a100d0079149803100d0400c014909a4010001032698116000310320315030302c2126070044960380d80c030070844d4001c22410400c2c5031441c120002601700401d544501c400700a003d205240030011401108140c890030080160711640224841c08403140804154110100880117804024911403444410b81900080a450710792a074000c5401c4c0300017480c1121760314001400142030405007c0000b42d0718508079410360700182c03490000c854030700c1c80031491405454041d40903121420180f99104058402003c09641712050321080c1105507403542d0705100110b11461610303407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452775341 1250 452774091 452774093
    0xc0b0601140c06040c0501021612030c14030901020d1b031409270603010b03100213030605010902071a010617060424170303100902031b04090209030601080f0d08040503091c 76
    0x145c00c1e6440d8007003415503000c141d568031410081351300078060303541c9540c0c0142d0200c100e040c00c07160b1038800d40000c1c0c20714010100030f601804012008044030602a002c030b07200e83c1e50460085030304895030040d480341c01850003541320001e4421419400000c200d28030081c20407000f800011018241e22650145c0d0b94800303507c40610840f11100075500c9401180204072950250000c030743c032028010041c003892a400100d003081d6428262001001d1604004100074960716001040004e5004c040217843c118803c0010b8203401e0020418581a01d5003592440c5110b41c000c00d0b140300044010b8070107640140c6420880d0000095040f0400750f02c1100d090840c4102d10701160314001c954450180802908100300f00b00c02c8040600402c0c08403469070030b006980350b407600240000040400400800e5440000e0000b0b644105a00604401c4104405480841c0d988a0a05680784600030302c9841c9500200500c1481c98001c4208a6100f03004a059a26080d01d40000407409182d90b20800c54400c08140400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452776591 1250 452775341 452775353
    0x20031005091515010206010e0a06090204030803070225150201090f060516022802030f0d0305011802030103050607180f080319030b1e0a0e0411041107030c0b0601140c0604 75
    0x15001101100b014030f0107416100001d4583d04140102c02041d145100440c407105811303408a0010159040e0071515130b034580c6402034850340280c40d110011b1283c0502d075810721603251030072105810000c9100072007500d0701800301184004114aa01076558a050004c0440d40702e900d01210350303100b0040080c5519200441a500c403a6444c400d00c11940401207018941c1245201c00d14072800e04860f4010450003803000a140000700b0710843c100f070084480412189030950025416101c000401c1c0d414000a044801c00300d0109100c00340443e4800720220310740c01d0003000c0701000b41c1c08280701029015150902800c4e048180d9000d003400d07500008580c0c40c60380b021158180c00000e11328050002034120000a03420100301d606440c1521011080f04008d40d075000e4a0000070800407404400c0f626050510615064040e0912405241045040a0345417038040480f24100e5046d1602f00c86c61116032a03031002100d00230403841c144001421044082c00b404000381c03410400c410002c040610307040c5806 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452777841 1250 452776591 452776633
    0x6030b15011103030c030f041403070302060906060607150b190609050906040207050a02130e16080115030b0117030d1d071505070303050a0617070311010503042003100509 75
    0x900b150b5001402400b04040002c01100e400c404540325440030340e16641401c034086841107904414510000a01070209a0007160a62007114500c084e0380f419542c000c02c0c40407510490f84024560354001c50071400d0944687d01c889000c54015100090316400c09844440d00300d829045940801c180f030004001da072405543c1240d03c00c0b41614194104026a9a00d50360303009904002445900c160410003070902e001d07441f14401516100880c1c00d030809031b24410040c841d050040080c15401c0001c02280519040c81401c1285d9001401d10716a80c41c0c20b4441503a5a404840390700140810420105449001e000302c4680a800113108048082c0c41d07641640307803440c1e0760711602d081858a01c0402d6a10b41140558482c0c541500f0049003540d614400c0b0001400d258124103108c0540107040440ba0100081b80400c0d41d2260042d04500614000191624042210010b04e401d070440c101008000310705400164128000c0d0848488201d2110310505546040b1030184040c1c1c40500075086010701c0c0c21034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452779091 1250 452777841 452777867
    0x504060b0c10090c0e04020d0506151207080309060d02070602030c0406030e010614010309060f090f02091b07030f021c110c010306080a1103070b0a03090b061e040f06030b1501 77
    0x810414040c0e075070f100503c2001d4402c143d00810311361700040c299194010888003d41c0e0200075246189003101203c065030920300100c50180425629007540c40700300291060540707002600071810042e45904219181e403042511184a540900000000540900265008500765001551030f46d060403001002c07126010fa02400a078140301c0d00f0409a810185080700c4110700f07107000707d0070641a0400c4405400b418214074071662503c4030b00c02c20300483e002101d121920888030082c068960038160a020427588610701040d103410403080b00041c0c01144079003c200c00740c0c01583d0000605002100a08401541100100b1b103d01c07075040400d034051003440224082401d0400507141440d4201d035079900b008200816003001c11412000c2540c04008c02e0009002c4c001c0001d99030b00c00c008009004d421f85ca40d08a03200741410010650500e00426420304041740129046511034000041101070304002d100040811350b15080030003c1000154070768032450040c601130311200302c0840010012030842c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452780341 1250 452779091 452779123
    0x3050703030801150318021507051903020f1c2d030902010323060f1c05030c0607030513060515031006150c02150703050405060c0d03050705040b0f130504060b0c 71
    0x4446e108409000307894110090b0144e880c81000d40700d080c10302529200d0481e0280c1140b06005103c0c039640c000c041811040d5200b0350a4492003016a119165503075030728082c2c1090495400750040310203114a030600c10b4251002041103004a00412800d050740301d8030034000c0040c0e1143c00d458159601409a4002e13001108001203032410034460301684010301910192213041e4110001c403ca955203000c09a80c4182d013210210200341c1441c0c681d07502e42c02450f80c142c80b80211000100414000d104c0d80b0f00c60710303410120000a101a5407540f006040040400e14414a00036010710240c40c20001003501140b45071f0000f5000b802e01d090710f080c1c020085914000c001040f550000142c54000402d492901e41920b01d82d120340d000d190a5606002d242c0100e078014001007450858003100144c0c003000d41246403810060b5840b009800c03900b40c440c0340990f242c119401c00c10421300d5400900100b0401c50790340c4030385054030780320400941903420650001c50009404513004982c0d00040c48004031000000d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452781591 1250 452780341 452780351
    0x2032d0606150406180803031009050f010b03130f140a0309080316031d030604030c061d1c1b050304030c06050406020a020d15050f0109060e0402131104030507030308011503 76
    0x20307454002c00c2c0300c0c601408042101e24851982c5100c101403e4101800301c21094a80b00d190901c4a40300303441962282c100709030b00f820003103084bc4034050f84c410f0507502654001451f582d2081074804840344021022541c02015074210004101c880340c1d55450803070442c0c0501443c0c0305a043c0140a1189170300400c0700c5c1d4004002c561000e200c040c480920300c6600d820045a10071540d800d8882100c0c1100316160580505000c00040582c0300641c2d080e52885100100041c42c203c614402644400c0002c400382640038407184544034010308d46450080c0400d01c0d00c4485c1074203a83c0c22180b11041c04904450641c8045000d03c04c02c10482d170380300e026044602e0302501b030600e425002503880c500c4980c064000d12000880303c0600c8176094a1520b40c03031441e07005108a052a5615040041c024411118100d2900c8808a441c4510280040c001d540045c521280ea0342c00000c0c0c0c1c1c001b410078084a0420210810001001a01c00d2144000a50080d2541d09040d8940822201043c0080c288581054606 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452782841 1250 452781591 452781619
    0x60f1106070c1b1410020105070c060f022710080f060603072c0301110f0306062a1c09050108071202221508090a0b0402032d0606 57
    0x10a40e90103015450b00c80e00d802268100424118100c101680b01654050700200e440c641c24000c00140346003e50780040c43d0b01c4050812822600240c500d0b20000f11041d020710302240007500b2002500518160062a00000b0250000088a01e03036228880101c2c010a81107907107844031466101c04120308040d405450b003040f038a009a00c008020900c201d0b0301002280c52603102d07010036541c8a03008902e600300340384020184159183c00103200b511960901c0044d007031403007d2005a42410040c005240c3c10b6844803010411103801410108512204601101640c5000301c0b400e005441244001f6020301000034034110980755040c4659418004102d20800a50364002940c943c03040340c610740500441d00d20441d40c40030b44101c002000000746400d0301a4481001f041680e81210140030340320340c204152940940314040100c94260903508800c540344003044580c202c19a1040c4010280c07203800086a000400380b000412070691044031f8100000c410320010810550000c02c102c1c0c111a0602e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452784091 1250 452782841 452782843
    0x150405011d0c090d0b0910020a09121104051311030d080601050d1b0201020a110a0515090102160c0806060d02060307031104080d02010e19020d060b0111060c0301060f11 74
    0x21094090940d0407040c00000d0101141000b0b94019600003090301c040101c10341010381c07400b50103071007009050065101001590a0510841d00c3c04585034484105003441c05000780e05101200d5019070340840160301c0c400c0d0035682c501c2020f10840071410124403410b8203040c00c02403a030200e80b40b5800303a8090540c000445030451a22540701009284c026940d1b2a0542d540000e40080d2031000510141240b04050341a0190090314895000fa50342c02d1092100020541e662034024402800c0350300020004c40c040d400e505010f55124102030b0000d45003081403c180d03d4203e1001c80f041d112011301c6c460500a081d0140310440e0845011030b40c00020341100d80026956201c0506244241940d408038950050048400e440c000c0030030700d00303442c0502141398020b8080d202c01c05032081c9901910482041c41d1104031030440003d0b80185c00c14078915441e9907804c0c01020140712903030612141c0750512201c0d06042120030700c10f4101501260b1a94900440603040c0d192290303043c2e01340302c40d46484c4100410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452785341 1250 452784091 452784119
    0xf030301062c030c0906030a0f0b160216260703030509131e050a11160c06050307020d05160602070c06030f020702130209040b060703020105060a06080f06090a111215040501 76
    0x68202c82e000c5c5207446d1800020314208596070010004448071018200b0701108401003841158040c646070001d28100c02c00f240c54941510303a200c03003003080c02400d111080c5000c2d002e040e00801514034002d0f00662143e031519027038240d40101c00140e000130300e000c02420a141d02100c0104002014000030101003035064403030100080f104c2d4455521000070340508896005103152074404543d455071851450340300c60325000701c918180d40b4510481c200082840c42134088034400d440b142d02903d02c2c100608030403501a80b251014010034000e406082d0b020900c0e41c8000c0c070104d8072400115800d070340f0384900030301503a0343c2c0348500b80700b0b40c8144035039030150319642e10303c4030708541c1014010b0303503007881500003001000c809500070b4202c58085201e0b02010340540c805400b808044662280c0c6564443c01215808001c580302d118466580000c911a41040c0c0805608030101d00c0d400b083c4080d0f01d40c0301c0302450304030703440c088203075507030b08090007003500710803a6256010700e0688040c4055030511081801d464 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452786591 1250 452785341 452785363
    0xf0608070e030c0d110405010b0702030d08100b030a02030912040b04031113140103050c030d1725020309090930040302032a0307050f01110f030301062c03 68
    0x100107400c203001103640c18410751108160040c5621403105043c200b001400030b180c03030602d0003207103008008036851040f402074529490f8002d0052403e030b070701c20301d045501c050080c05203a9009407064004c181004036002a5200707000c0c1c9100183c5a1800e00700d903c0c0f8040341d0030510142280200800d010383c078074040c111025a900200c0c0620001519404244162501d00946d0000c511304017009240700907044445048a0003201110b000c40c40358010991651500081c01010801d1107814454580402e03558990180b440400003041054041c581c8a8101c0c1000c00e140042e0400548402103140000150b604842c4400040481a103052003034001d0b00780f0310032050049444400500303078420302c02c4101c4000d1540501580c0d50700007051094004890000e15072034941d001c1d200b01c11102c0c1400244d043c100d0304004c003003e034050905401034072010384520000103a40212445a1600442000114001d00c01d981d10f41070032071002d54120301015810f4148504402d8000304014044d9000140c00c0740f90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452787841 1250 452786591 452786597
    0xf010908180a0e0105010f110304090c112a01200102040924030b0603031314011b02031203090309091602061006050a08060d0b07020115050f2808061f0f060807 70
    0x11303610420080e552241108c02551140c0701c005004242d44030f84e5000041c040c01a82c4600401c9009040d0284e01c4100171501e01a11906600c11100c0c0d1032141000c42507025010304000381110f4500349500c2001c810004a80300681d00000d007040564110f00c40c0444041000302c2d0b008680c0301c002c110114240e150300c400341070844e044001c106203039410b00c129001d8150110401101c81c0d90b0715040c0d400b02d059284903901050030030307007148500412080300399003003a40100503000814592010038260b40000d0311540a070322043c0110a01e83d150604a82d006104103a0400da51b40c8911500a00d030220041c800705d4010f01040701040480d03041803c2d1007182040d410003520542e100b0f004a08141100c8a024111016050a0100703841e019402110480004547c4425540d03c0360180310b65100038035041d80c0c00c0902e40c00300c107907282a0100b95902d00d5024007109006035a44004040c604182940c0c030f02e0710b4891050032000d04ca503510b41a48014503800e504c41d03600c00c0c50302d000074101c0d0030000c21080074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452789091 1250 452787841 452787857
    0xc050303040b090f0315100906330909090501050a05011a030a05040f0b011d0a020405010c0f060608030712022404020d020118090e12090a030f050f010908180a0e010501 74
    0x640c3d54240038180311000454100010b514240c9610009465a4400c85028078a486008280c607224440500cad4009161886d0601d881643c050560041843d0341d81002005a2901c3c0444c82c0e208a000d4100c0d01070088001142505000c0800c001712601a4428810b51007081644640c446902003500c0e4041c01801c0700207070584e40c50400002a00019034020170300d5480d03a00100311007002103060408044454030000c0b1a82da050410000c07882140141800b25140740c080d00001418405031080c0c1500c40c607404030f584c03a0354440c01451600041002c1b0343d98103000059188044d4100f10300a000c012880650507402072000007103e08440150010340200c060075070381425640101010b82c0c40f0b90480c140c0520b0680e9030200c9400420020041002500610050004d506400d1003500e40c943d0004160510b8240340d540e030300d0010054400111501e01450102c180144402c0c4a030716040c0b03020340e00c26662182058890043c0b80311010b00a0f115046400042c06845844101181034500c01c0c241840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452790341 1250 452789091 452789119
    0x2090a0204120b040b06010e09180c0a0f05011b02060f0306040b0901090b01020d03020717070201300f09030f1803050a30020c010e01030603060203130c050303040b09 73
    0x406841103400603614150081c0c4001e082146140e40f051081740a20354032801521010011540c501072041c90030b900050000c040f506140c1c0041c519000a20700d1400c0b644412102000301d8203074802c41d03204400c00c005032003007003025580124800d40800805112155498400e600040b010301401003403d150383c20120008910392140e41c85014051030040c11000321790386d101041c0c006010404031450040c0201c241143c0c0440c002d0007607440c225403001c85455551a030ae060b20b0010b400685060307040000c01c3c0c600c0600700d20452084a11707405d00c200300045810340d45408109a840340c00500c85818501641c0102091348103d03c03000090091400d58111100c403013154001205580018000b4040c62003020100300030603c080c0d000c0042000000302100d240350100145100005288000d038000c2d4903804915886012803104001050500140b040e07180d41314402243c20407600f180c44c0c01070391410324060103a00b003055801810700f10002c40c43c01d81410850103060042c0d030900d034052202911121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452791591 1250 452790341 452790361
    0x2030f12040c09020c010b01020f0d0221090603100602190b151212030618131719020f1209010e060c011b0c060b1e12120c150a0603020901030209 64
    0xc2c01452003500642d2180c00c0b500342c0b0b80c0208507040e85107001d44600d902c0308005020210301c5180002403074024098803002810400041c1100203d442c0c11100c082240c01082d035600000f560050030200d400850f034900b01180a80350101a00314260003408048441c030010714584001e5911003444000d1148252244002c250611851101c500840c05001003060a1709000ca01451148504898980c116150469020007440c000d6583d003443c0701d0303803009010128810824035140050380d00365803032030210300071100d401c94401c0082100042c2c1000e00031111850081261a00b50041000810700d04081304001034410041840c2c0f040c0100300c081028204482c0070b502400c99807035143c0d04001d421042c1d80c0028840b0001290403a461841e0070412030740360402c41c04038035015800c00355510074002d113101046440a41c11842c1d036100d22420400046040075100680070b6001c25034020815121181c01403818194028200180d8034500201000940d8030f0f2244241129010342c0d254605480d9002c0c0c5c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452792841 1250 452791591 452791613
    0x213030602181305090a0f1712010608060901080316020f1005041a090906012a110a2907030c0c03110f0d052505130e06010602030f1204 60
    0x3410141c80452606514084019610041e840407144089580038001d40c5a0880d94213840e5505a58460000300c400503490518040e503890140300c808403400c803d800440d42c00e901400700901d21940c0040108940768101c2c20480e004042150080800e60420018a90ba401440300406514450030451070540d1504041d81c1e24141003c1c11240d1402ca01e0070018207254894451540d4100d007020030141d40ca401c01080c1e4008030001071161010340c03101c40044509040c4c0f030128100d9520125001070007100b900003405500c07403045090b083d03950703440c00411003101d00f02d0707205a40f5401e04c1d0b8400d016001385850508506000c6100d11031700c5000c0c90904660002d20500010314031421650080f00748001c3c2a00b0703181c6c0340021501f03405c45c1714900040c050fa03d0510b00d0014034543c022000518bc5844440404c1005c400300c016855041c1c0e03440e80002c0035620200c3c0c100010f140d48045003414600c0c103121050242c00e0764001140740074025042c000d450307c42d5000c5500e030588200c0225041082d14a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452794091 1250 452792841 452792843
    0xd08072c0d0c080c10020d12090c05060705010902030606011b0f0606030506010b09102f10180b0a0506030303010329010312020d090b040902030c04080a03120b011b0303021303 77
    0x10410342d690311a19903c0d40c0f0035007041100d110700300c101c1804842910000b843c040d0003642ea541c81c5040b200500321400a800380f960110b414403c080c5d000f080644429000c0c002c0c0c54003034000428020540e005040c02d00c40e0207000709041000d071400c0d04031158a031a000e00c2c489c0c2e911944580003285541010002042140c000030043e000b11400003855441e41c1002c1d00c00c1c4c0c1400c680000c0c0c0d1000c1c0c85016074268004078841465007c00c1d0540001e22815080d00b4040c0c506844240c413001c00744403142c402118000001c070304036101241c07c0d607018400c18136043c59102c0c400c0001000f0500300140000d130350307000521008080104103c162440070384c0c180d44d41c0c921101c1d04400000c0558403850910085e44600304610010700c600704205070a21705c124001c5003201e40c00d00901c0d140ca070034061400082d40c402464102502000c00000803480d5040000403031403402940c6244d508550308032071005480c1e0020040707041204101c4044001c2c25050003002d8015450300700165034000049101d9215a02580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452795341 1250 452794091 452794103
    0x10501031202070f1a0d1e1401080c0114030703021201030b0103020909011b11031611090705030c030a0902010c05060f01150305011505130b0c0d08072c0d 68
    0x2000200e201c0a030340da4000340c080d10078041e1600f604000001e11803288400c5551030384001c1600035244401021070b01007031030002c511185038490454901600034010f140450f500c50440080e041c1c10500304d40505152800340880d84c2c035a5000030800380701101c40300510394000010450881c041c1d412982d07080c0580d0248000396950b418003880c1c81000f403100740d0040200e4000146007040601c5015200e480111400e80e00c000c0c10b07d41111501c1020b00d5040d4640300410811507180390101c0720203840b5104007070000340680c8040502c54011400b40031241884010320901000c080581c05036940609135141c0012030b80040c1c001291403000384035000e4a42e00400c418011900c6411000c00e060b9030071600c44250000da1001d0840460b18244121000c03000b50641701d1400600c941c0c02003040042481a1160131516000e001009a01245202160f0780c0031b0070400200303d8001061325441036450400710204041011504809101d001c0c601e03a08120b08820300c0300941d141c00340880d6040d0001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452796591 1250 452795341 452795351
    0x618090501060507061406090f0c0c031201050a05030a050606060f0403061e0b030705060d1a120c010305010b030408030412050d150f33030209100807030c05090315060d020301 77
    0x40140c0a9072007084e09980d801d040402c41a100d00031080c40602403413016185000c1030341c44c00402d04481001070300c0b109584404000005007180d041000d82400d6440c1c1481304d0241d4580410010403209950149000383c010f44050004a00049a4183e1241058035100d40c1c1c4c11800d00f40100501c503c1e00000c1032285048120803080c111040b019654024800d0100704a0110b4030070035030b4682091183c160721181c1041641420310302c40c4c212a01c2c000078403049076035116110300001c0d03131915001d002084503480005122290360707050046600400007201c1540c90340c2003030b8440b49100d220040c40541246880d000a5442c03504c20320484010030391f003c60030003402e0800981e43c2b1040c5881d10440350a8141101c000c2585518003a610014056054141c3c920008030044483c4180c19801204107142c1c0c2030066444bda2110144085c080e141c3d9aa4001c00e0324260602504440c00f0140e0101041418040c101d0541c80c00035407441041104004134415550f020001229400d501c031000b0b425500b81 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452797841 1250 452796591 452796599
    0x1503080f091302180f0a15181401090303050a0c1506031505090c190f0626010305030418060314010c0210050708060904020d0210080106030c050c070618090501 70
    0x100040c00411030100c900c400200d0705206054164081c13428000000d004015200625180c0002c130081d0622006d00180c0c4010b554011140f03c0f42c40070b1000300049600301c800b0184515070310107810050b00f5110181c101003050b03000028030315661400001d0034480001005400a03005642c0c000700184c0c00142420031104554032480544600e01c002c40740d44c40200d401403040301c2c0d0b5011f000d00c1102c40400a00006442d40108001500328414048040f404950045200e902c0025014050496034403940c00340c00c000840c000c42c4d1281003810200c00901d80d00180001a00030046a08490703c8440103000200604200e030300420241d8002010200b43c0c41003545070045c10b42020f958203e0940a07250b4200907c80c0000980b502102d4100008040d040041c4140c94900315450700180050b142c82c105403125404602c91941c0100c405011425000040203010350501400109208070314085003441c65001860f0b40d110300c0e50007480d00340040085060a0102400c3c8040014070541105000659507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452799091 1250 452797841 452797867
    0x60507140d020c0f04050f04110a080604060c2a0b15030703061512031e030e0307051b0a0506030a0e0111041212030e0a020904150606030605031519150308 68
    0x1e00c4896020312900d0020314150305d0203101d124458500a150707540349544030380d03824072024210780340d9070f41c0111550f0000c18070b101c1c05c00c4414440c0f44500c000096400c13400402500c10306141010a44422100f004035010494010480e030074079510088040444e111300042804045001014039018801c0f0302000052203226045220a00400401810183c0d2200c4030030f1740075000580c002e404501c080c0c0d5802441c48180211840417039451070002002c1115028aa0440c0d010f0602940c0952108141c00c841d00041d0260f512140d070121410010b4904d050041940c5005c010307c0441c4c1c271540c500e121142c41c0001c0d003000d006a041d9241c4682d5441e100c00142c201080844816950a4104240091400d0107845100c4c18041110700808480e20141c0c00c024132454020f0007210034011400359241051940c1c01410090012500c000c81c0d041d06140a06141c0001c03200d4102c4035071300d60410b02c1000c0310104030441e54000743c00c402090180400780d00300c2c2c1e118810790005254060020745841c1c0541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452800341 1250 452799091 452799103
    0x50405030a03270e010605070302010b06041d060402030702100207020d021c0b0c1314030705060429030c04050d14100f1a060301050d11031c11010e0601060507140d02 73
    0x5035400307200c1c002864202644041c0c10f400d000711110301525034018014580031340013828165100780700202d0a0280c18011a00a40140d4000300e4000c1e20480c8659041001c41c5400d035010303006640844c00d501d4a43c03002541c0b661001480d4414641c00106c0005545411001c19106600030700016000b4800c4104081d0528501d50300366004494100816030103416202101e440209980e448540c081c02c19802940f0440c1000072030364580309071750f0001001d4842c0d5018100410803082c00c3d0765860b20070200d00000c2e00301815071403c0c01c2410800c21a031703003031140103440550764240c8d4001c0c990400c515080c41c0c42c0c0f041c8603103941b69104280071300c40c0e000101d0700720404201c4490010f0211056070103a442c00780401c0c0c6059035010005100600440c02d101c56a07140f03540c001c070b00d40e540c0b4015031002b0a060407031078a02c1c800a4014588041d21050300204041d03400c00550b4000c0009004c1440050f444410601404081180026104080c088910400b0004200003025a50044100200030350b070b0718 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452801591 1250 452800341 452800367
    0x601140a12051f0501030210030203190e010c030b01030207150b030f1006061106090d0809030714010509070605030c070b04060f14190c05160f0507151b11040c050405030a03 76
    0x9283e4041504641c000340c00b8280c1280d5002c0c1160742c6207a0080800d40c065040180000403050100c03400c20001116800b961205001c0c60000203000c0e10100300c000c090300c8010203580d05250041054900040f41d0f9024400046284440000d51805140000c0d080600a044c0720300e25110348090509140103da204804464a58036000542050b00c1e1210341ca41008452481c260b80000d030710400301c0c901910b40c2c542e008051009407840c2ca085580c0d2020071443d00d43c099825690b448040003042001001064040c2c0360703a09049007140750403608481e4a00c00c081006103c036006c0c0000c207041000ca5046806203c0700d48205101c0002c00e03003841071714030b0b4048504500b9110443d100114009032840794030381c0c0a40d0707507681034600f0700f140200c50f4880a008800b102c0c0b44a0707803840400403030020f00111000d40110940200000900f400041001c000c41c881000e101c142035050b0000101c0180c0d100007040301c150b402090721040e091084d038090246910043d01405103a030100d0401d80d005082010072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452802841 1250 452801591 452801623
    0x70206070b151003110711040e1006150309050a060930090501080606040509040503090907021509070f051e040c0207091406101209080d2307020601140a1205 69
    0x3e000100e045c3d803a8400d000d5920841000f500e00411800b40e20100c107102c0250021941001e8925094600103550340748038402907a0720f00500250192003082544a82945000e12124600c1c1e2202c0361291551030009080c6a62015040100450b503061200410342a550043c3c01c1c203901000d103981700411764058000642404000303d00c40d800760040302d00500001e0405803d02c2c2c04c01007401003070800900240c5440c88140034058071a955820081d20800c095809000401c0c0318403240c284c0d0501c083c00f0300c20f45ea040840c051110301908440d0400f200c0302156000e01d24590740300224440c1105a6140780c0090811030300c1c49407150006544401c4540101d03040107100000450f580225406441055221004454039506640300780d445d15400000c040c000155564a070b9076407200740d8010300e40c4141540d1640600d0a18041c3c04481e01c9801d9480c40401d9114a070000000752a02c00500920501c90b400900b41800c5444100c5018080d20140090404200d01070500d155a682d82d4030802d480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452804091 1250 452802841 452802859
    0xd060b220b03120d02130b0309072108032707030b091908072901030b06090718060f020f12030a050c07110409032c010807021501030206070206070b15 66
    0x700d00700011400400d888142941e400c00d030300c81900d68065444000c2c0c000ca102c0c0000e0011580c1901c14000b0341c0115000c0d0b0050800603c1c00089850b1501c2610420421107012100b140200e00e5960450b45d100d54103050300c0264a07681e0780b460394041001c240d8002e80d842190b0010040011804215014041000813243c9400c00c81101d00752180d000140207003c000207202100020324407451025901044400c01580000200100380c8000d1090340180d40200181c0144411410542c8000d60000050310740f801480d40c1c247e445034400109072280304100b000c0b1102c0603919034401d0005100c081010001e56100041400807101d441d001070392461041403510000c02c1403540d030041100c45040c1d105002c0400042d00800b004014042004144c081c8400b021440c10340310f9501c045072070102c4104982e0500b540341074000405440c401041c0c03034150341c01044500d01d86c401c0c3c404204d0440768102c03001c0c2d54030441e03071010a60a00031280300038912400b52082c481c00240708d4881131401a4103641c2d03890 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452805341 1250 452804091 452804111
    0xc0b0601110f012a05090d0804171005070806030a030c1e060e0705100f08060d0803040302011407030c0905130603080a0207030615050105090d050c120c1207050a050d060b22 76
    0x41c040300103405403008540c0c2004158211f0420701032892415002d988914241a901c0003090345920fa001804069908440e40d0042180ca4611420742c00071010320b0828014a80040401c0c1d0703039107001c0409424069004140310810050310005110340c0b40030740264070900000d203049400b07409412a0700035203004440010440d400c2000c1d500d20424840d03966107820458080702070300e840e84094000c1d034001d811a060080410040c100071405207100b0b500000c1e0703413140a07480421508010385203908041c1006a16440341d81c0c084d030038505581d000c031002a01901140400c0d40200380590004000100200d5002c000a401180100440b401504140a251001030b21317424400440d002d03150200307009024045690400703601d0346001c1840b030400c6030821640600001c01d030103111140703074686500c00c005221440c00e0030f180207007019880350010042c160600000400c011207074040c09020303129082c0710005004464210007c1180098044249017a0501c100408400009d04000c1c0d66820040c40e19 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452806591 1250 452805341 452805401
    0x90705190f0b09090f0a0b0d0c0603050601180b0c2802091f1412070906090e120d0203070203040f03110a061106010308090103151d01050904030c0b0601110f01 70
    0x41403100010f140c80c940381d0700c6407849030320800046e0828509540d00e001529050321203509207020309000f680310030529031602d48010252013004141c28108800c03c00440543c01d00b1103081d1040d03450201d032864503038005d0031070369140504044d0300c0c82002400040c0510008941e0b00301d480c60300c0c001c1c0c61031200c40d41c0301c0c403c0d00814070017806100c04090b12410b081044500040d01c243c05044020880c12401000054161409449803c188441075a80c442044580002e102e82803080d070400d409091050110060001140280000542c1180c4c0010009640c544280101e4029080c440100c2d00081c3d2281040b400e0405100314035401000c03580000719002c0c2c041c08060010210b04c900401803a801c40d500c81e129038006180c414185910b80008280d1400700441d80e0029080300000301c0000444c60943c040c01d80010390000d401881c84100b88000f10b640481d0a14200e034005520800a4403140012a410304c0440c1c0000658010544907a008100641020f010a07000700f10744010305901082c1d02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452807841 1250 452806591 452806597
    0x11b1202011d0606010c11030a03080604050612031e0f0c030409110702100f11070803070219060215040c05150d050106090f051504080607211e05090705190f0b 70
    0xc41160312101c000f0b1103d40c402c03880340070000c1c4540300b07c101261a407070110b49003000c2031408501081c1e103031003041803c0c146407117101d40c4107908a41e5140421070301c2045549910400b880c054542010f0010200311750060800c644012001380c03ca150303a03040384807145440b41c200e400b0340721409092060901200c5184030030344100f260018240703120018044070565041282660300c505118214078095025142409010024854800510b40d0340d06244108144d502c4a411122a114403003201404229400a03e1b691003107644a070962154a4508180b800c003c031030b03809158010700d01c0000d031400784500000341104285015041c407450741c132800180c3c0e00581034044c041c1401128031080020389403c401c8004c28990303405425241c203865001c0306043c200e08131011804114842c4203290318034480c2c080515070714030040c42004054107007030003003032041070a90480200d1610380002c94440501402071000400c00102040c0358106030f2540058050013600c58181d584000340300000c1e10114400403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452809091 1250 452807841 452807891
    0x2071407030506100e0a2c250602070e04140d0504061805060d230f0f011a0405040e0102191e021f05070c0f0b0406180201090b09011b120201 62
    0x4103105583e2100ba41009080c1800803c0d400a6100c2d0001d001f0301c0d2401e20340286054690141000c01c40d0802c0d0030746e9041000d10b00084000c0c45403070801c00580e000c2150404c0c2c49000104140035121030900e480320801c101c2030750502c0c7c06144451043c03142c000c8001d00413100241c07140c000c100c0005850240c00a89445120f801801c01c0011021649c1039500c59010b400d008864100901a110381040c05100200d9068800e80321008c28055001c414081881c01050300e50850705050403604104c4400f4001d51285500440d1144e48503234030b50f0029015610045074410710704507109080c0c00d00510110001e91869141b05248210b01c49040c80460800d2001c0c403513080d04041040c0984402c0d00070400103101004102c481400c1d0070002c1d40c5080d00345080e81c040c1010494604150174950112030211010b040c1e10415090940c1c0140d0300b220152040f26605080d5686890007500160340f40c141601c02060300a58000200080046080d0804603100c143d90081000c241145503501012840e101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452810341 1250 452809091 452809109
    0xb160e0f01020d080c04120c0501030b120a0b04080d0515010e0a0e040807050304030209010e060f010f02061303110a14070501050f0706020f0906070308090607020c21010207140703050610 82
    0x83d10b014503014404903a0000c2c0407880083c9070542e9201d0380c0c1303500c01144400700e90703030099401c0070842581c0c14014802c2841c3d040b64a01001c030601384606036904025132004100c0c0d01d030000020140b00011080d82c480b148a00014071291924803910016110920315076804250b001086001a00700103c411081d00c42ea44480340c220740716a120040c664004000485581c402000003000680798142098028946928000028108030302003014000e0b4210682c1e04100403203e0240540d5800a5510b4001d401845029016042030800f00d610001c3d00002000078864a1064020840700c10520761092800e20140e440e000e032620011121449440c801062140c5d00b4002507020910541c000c1c140341402000c41407404900c8808241e60b9004040c00341c0108151104101e41e80009000385980300110784043c101501d08100010a0740e4541c41e5119407103441d0011500d0705880c00d504882d50070f0781044a9603a644407048003913035110074071b000c11205401100c000c2000d501c00d451400381501d0007c0c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452811591 1250 452810341 452810353
    0x7050402090d020a060513080102070b070c050109061e06090e0319031803030f0e0a02090c130b03010314070e0411090a0b0909010c03060b03090a0609020105070b160e0f0102 76
    0x401080081e4118500d0076034032a00c2e00c0070001c016a0713603d4406000306100c0d00d03156215400301070f005114180a501c4802c03a030b401046a0800220004d0703e40b076029840c0e00b03182c500c5038540c0c20510b005203000d000c001d2a8038a006540e20101d07046240000b1850607902090000b2a2503140441c01d0350242d402506442d4802e01601e10030015042038440121083c2c80c00044851448240c00054901c1000903000b1070382c1c3d544080034000e401d0003994210002500104603504031070740030030105003000303000a010480218075448006403440010004000402d41140c4a503180d0424400003804106980814130402500044400c02d00e100e0500c629040025080c00005030303418440703164402407014a041e0f9a44111002941c0c800b012180204540701c0006441810080b01600f2201c140c5c105125100c014001c00802c0302001401003246a405000412580d1042c80169020f0258501c010680707600d0104000749000c00040102a110144c2c3d1000e844059020920101c603d030400780324010f800c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452812841 1250 452811591 452811599
    0x180a050906060c0a1a0604060e070f110304080f0d020f070e0a02131211090c040f03020d06090b2e060512060112020d050103020f040501181e02031305150907 69
    0x1c40003030503d00000c4000d4603482e12040e6030703401200c0d042014800500040e0001d014050400388034910103000c400e200c641e810308001502602c0c0a01c111011801c014841940c02a5160184151030003424410104e40d0500c55800000780c80e00f241d441e69900503c9604903d48403040d000414600f01ca004000d90300c0652150000100030754806200602a0180d000c1c0000da208544110590b8140c01902c00042400b840341c10400c0c1c461000d8000c00e20290144401e1008038012407403030040300e604682e044040d00c40f520f040c001a09050300064040002001040a01d9100f090205003142c40000000d1803040c0701c00b42030081c600d0340d0041c0c1000804c01d0240c4c940c19415424160b81201050503c0000140310032900c6081e030f4003840104001c41e441f00700420131800c22070050002c0d544103c40a018560610300354440a8462821900c2410740f03595000c41c00e54000c0321405007441c0ca4030001d541e20325003020760214600d0a0f5804403094407606404aa00c0d001082015010718604805040d8062030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452814091 1250 452812841 452812849
    0x9130203041203020f210907061d0112090f14010506011e2d0903110619050a09050d060e19120c0309050307091508030f0d091a070302180a050906 64
    0x55030800c50704030401c00c40981d00a542010a00144607086e02101092501c4642ca50034a070141e800001885003d0400d84000211400b840c01201d00a203460142664102030010103009803c1340030b40018032000903c1c0c140240f2000048848005030024130003a01ca5a004641d60f005402d003076803180f034140c1015a8458810415401c0c41a038030072000481a00d0042c000b5201d6000c44130070408200c0088c020000c0102d40c81c0102c402c80320485066042090010075107551000e60314501d800c00c0400540884124007400780d070b00103018040e001103144040c030314000c0b000700b01c890000c04480c440c58252424080c15242c00811240d0f200d0181c89000840701801d55010005040c11028820303128000301c2c403a101045800001d200144d0045150a07040b01c60501320480c54102e00e12542080220100101040040f54540b80c24039600040e403103000c0c1030045102518043d84c1444041d5041409050f59154010f04003030342c09803642610300350a020802c8040c1c4058460a17422800b0407000400901e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452815341 1250 452814091 452814097
    0x8010302031605010507021309060501082a030c040c051201080309010311090a140a0302120606010906080705031b16030207030606050402040509010e1e04032102180d030e06070501020913020304120302 88
    0x8c0f6100480d40d90800c1e42c424041d50002d03009182d0a5000381c07159080c48940241920b00d407075901c03042401c01420741c4082070307c480e9031260890191781c03180008131600f442841160050031440c064040c841d619018a0b50704d981c010600e0341c1c0064280311020000305600c10440c0e01011008190030502460207080c02502030f661003410f0303403010502c0070000140e1183c0d04c0710603403220310170b000d404907203420f0001400066440c0c00c2201049904020000741940000889406c2400c030b0301c26220070005100c0c1400c4900c102c4400d003580c501c04108440c201500042d904051f03078840c0f541800700c03a48410a0004a00032845100c2d0322074000c81c010003d0103d501381c102d410040e111021402c003a906d02d1401150301c03059508800140c0803030071070202240c07040c8042c9028440441c0a61620b004001000030324a00c030001c1d14441c820802d0100105400348003406c06040f8003070714141e160307611810154001c0d00026503407030003400c16030300010780d0710322320b2003120710a1364130504001602c00142c40460082d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452816591 1250 452815341 452815369
    0x3318190b0310060e0105040c260901090f120201060803090a0b0708040f0b0711010c0f030806030c150c1006030201050301180f050408042301080106140d0c0801030203160501050702 79
    0x400b50030441d001c01120b5014807006032100004015040d45844248811030b550340d01d403a0704000b161000c0c40464030340d88a111001d41350640404c003407603c81d454100d004010000c4000c00140008603550b007080035100840c0307002c2105070000c109542da182e0400d91244070701d2101d5036000003408424803510f516000074000450140c1c0200e0304154407842114440091600404111071f0081108404c012101c02401c0c90600d0038a005821040b1a549220044c8284200141881a25000500c441d00c1c104401c0280601c01403644012108003103907038140b5805580d900007140031312407009001030850f00030350701101e50681d80c061643e86004100c00003519003611412120340c072178501501040190044c0c6006602681800307039164541490001e2460004c1c0c520144680102900c100d0760ba080b84020303045503e51f04094002850f0720048840c0c40c4150507003403140601c3c00382045000c603840b4030564141d070301c2a801c0f5800c104401c44110340e016010f10a082c005030080264a0040c10304240b440c40b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452817841 1250 452816591 452816593
    0xb0306221a0a090212030a050f0a031407260c041a0415033e09040e0a1b171f290109090b010503040b3318190b03 50
    0x1020281d816000801d40560740080b00c1030f15011000258604520180c1d05c0710307140701c0203619290701d401c0040c1c0640160303071003a4080c00020078500d050902940000031701c0c06010511260794a40100c000d40719002c0f40f01e0300c2460440003e24442c2a400c03621429010b034244008480c14140343c0403035200301d5000b180340420409414040002c000720103144115400740300f41c0380030401c01c100000b5060075103400b0f452014640e03115030009280c0403000b40400d070350044001039507035119080f00100300908401d04a01ca06480340841d100140a014000c2e9503030610b800c214001d543c0d030741d0214980c68100290300007020750400350080003c00344000c1d81340441c2d03d82d040c01240310250400102813910b41d01d9521200c0315100415007c040d03034810102c2c030140c160340e01c3c1040300c042940b000a11500005000414000904010421010005460b00b41a22034402180941111400c1c2c2141e0075148021141c0125119000d55140781c1000005900c5580114100700b0321003420031895006d001e00c40810307601 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452819091 1250 452817841 452817863
    0xa05060a0e0406140a0504121818090210050c1902030c0619020f01060b04030b0a0905240c16080a090b03010b04060905030a0203060f1e13060b030622 66
    0x1d0021500304051060340150710010b10741541419010b0581c1d0000c14045106240808010001d900600740194202c16407800c0c5006009550a240c07032200e0a03001406882d240d0b804100b282c80503500003503c2107109030707050f407891900d49005981c0382c018581c10440075080300703104035402d1301102c0c800b00c1d1641c001403c9030b90500303440e00403a03080c0e805450400d0038250340340c415103251354041240501d061440f0000f0040785180c421101068003407400001d020303500503030124010030044c1d000b4420013a0014151000c003544026590925130010b00c0780c04804162078005007035050100e007981e4400020100804007407580340e6901c40c00c0d42c000d030b403500b0601c007004202140301c40d861009036020305001031070a0358807410400302804601080d405503100754040c0c40c0040050b20081031103a04480e41c00300600b080c0e12003820311100340d002c0054130400049a64100020304070202d900c10801805000c00b007120040210615446400440d10310300481c0e0441121002d1902641c00c40c0c1c3d94074015040408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 452820341 1250 452819091 452819099
    0x2408060d0503070f060203090d020d0210020a050405060a0f0f1112070317010807050a09061404020a1b0317011203020c100e0301060b0403140f06190204032909070e0a05060a 76
    0x21300110310701c0c3c180c402c41c2d408030801000240c104181040c0100302d0000740020f0b600000d000307688250095410f5040740c2c000c2444440c503801001070314085c3c031000340140d84490b040b000003030135452281d80900006040008020316240105492441c403850100588000c25440d00b5442141e0301800049082110b0701d50b003e2600001d00c0805070181c03001101500c0110b140104102100407503400c034500c614a811401c01051121140d280190308090300c01580b14094a0400d554220194014103085543d40d141442059805a10802001c19503036140d100780c0d880d0442d03031002034418040200568040107940240e0700e01200d101c0c11003201380c9400c05074141c42d11b01103400d41e103143d8050240c0f0000440c06104002c110740b0080424220400200f5007a40c11228040d1380d000c02802d060300031014a40105902869a0100e501851f0811040c07006c1c0140b50794544004006900c3c88068010000d0125589280c04156030040302d02c00c41344011700e0307103405c000c100003058090007042e84400c6181c1c0000d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 452821591 1250 452820341 452820353
    0x60906051602090f04020a06020c0609040c050f030f010501030507090b07020f040608010c0203030a0e0307020109290a08060a1a04031103010612050a120311030403080a060f0f2408060d050307 84
    0x1803280807800590034071400c00d407042c8411f101c1c4036040344c1c007950482601c2800390348404050b00d2241c5012a00484c0340d4901c608140c2d618402e158100c404104000201703c070002c03000c048103040341c2e02030386d04101d95034a4900807540403805014403440d921041200e4400b6103080240314499800042001803c40e903100e8501c0c4c2140c1101c00f0340d0026030404010001c45201c541f00c0c014032140c0da44059880c00f0000d90001b01456028011940c0c49000c8240d0320290b0b4642c42e1542800603210741945a45400141000d8009582250105c2c07181038106004201c009074440210010b1450540b00e40c2003074116542c610030340c3c14100020342c05640e00c0342c0000391003951032510b410f0035020300d000d444020100e0900c6200c155060702e480b020302d804d0104030344038200030380100c0340c0c02505403030441820b0b11085041005001a80c2c40800d020184a2000c203c02c00a07170128000c07a20091410b04001d50700c6041c41d40a90480010034001c124071600098283c00c00407440c0c05000d1003401681c2c60142199210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 452822841 1250 452821591 452821609
    0x10020a11160509010501080919061a0d030807140706060923040f0b070201021210080d08010e16091d0f06040e062a0309010c03060b04060906051602 65
    0x1000860303441100410003014040300c14195800425019418140350110300000018465981004644c2c0006003a800302444600f15600c140ca030129407410184c100340010f031829051210584001c200c0c0c030b5440d450a20040c865003903050711030f440c0380d075110300050300d0b030407400440100c41c144200b24100004141d03210344400307844003010005813028040707000c00000302c0c3e0f031900e010208113240034400402e44c030340c0006039560303030083c1c0d070103810f6403031003800c0340a80a08951540641000d00601400800b00d1501c1400d881ca0a0121794501c90450000c9640c4c02e000c2c4a04c040e40184c0002080e25440607a6004502c040141880b1666983da20686844039903012801c54410300a0000c0c040d01c1d2a64841c1a80c004008680501015880a110584824028000b0f03558a1210740b40940d20345001940420080418614a9281c2c5071075044e0a01070103141c007050700000d260140100c0d05101000a030307401d4a000780c2e60380c0819400c00300d081c0c1c1c482d8042804038001c10003110101d0010b03500c4040c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 452824091 1250 452822841 452822857
    0xa0e0a050901111611060409020d09052503020d020114030709062c0f1309060b03060901060f092403080a03060b0a140304020a03051509060705031003030806031002 72
    0xd052800240c1c040c2103403000c21568250200402080701444070b880101410303039401404640140c5106000614144202e92212a2050011500131039004140e13022600711b40c0200309446191f500c641c07102c01510100c50001d00c5e403000203442400981000a6402c181620604100d4883c1100c0b00841c255a001111800d0014004800502c01c0c00c3d0b212030b00102d08056600b103c0c12480d000c4040c481001d050700c1384580030f00807061321001e05546845041c00381d8000d000040101c3c02490402101510741e0200f060702901ca02000b040c80c92074144140c80403500c0610900110a04244000b000340450300404860f01d1210201720700f40042c84484400291710440c1007a5940d003210700041d054664642c4880c2d5000820f000c580200741d0482e8200185206600d9011f42e40d036103a1001440c5203a60341c102401c14814800341706010789030381c0400b50180d10300004030f4000f41d44008c030444e282d2008803070626054495040800000c1e006400603504680010183c54100c8440b5001c44c0481c0c0010903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 452825341 1250 452824091 452824111
    0x604050a03021c090e1005060412140a080a110307061a18011404020903070801020a09030b0a0903050a08070c050a080307030e010506030a02120703080c0c0f01050a080103110a0e 78
    0x10103a0105501040a2060041440101c1c1803911100c6000f401a041510590000b10325800000b08808040712400b4060300c0004d1019456a4844010030801421030008940c4052600276140790008006085d007412540070066078500800c83d01c040b1090301d40c03043d0f40e0078580f01c14420200020618001d01c00c07203500122081c8200b411070410440300c140d05407640c41c01c0742005001480b0000d0000d0b03050080410543d030250f03650300d1400110f4640006a44410b5140d4804190603000d0395020105400700c1e40101d6000c44103848214025045a01c01580280440c5080040d17011581c0140c0d54194041140c2c1440d040000d061740313402e0305003501c10004603280440082001406078152068140400041008214501c0c00741d0109684124035180680319800108052a1407981045507601131680308100b680c131075140120081c0d542c250700d18114400c0d40132021669141d481513041d9040218580d840404591171502c54000400001000c6900500850404240790043c900c0d03040c0031300c103100c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 452826591 1250 452825341 452825353
    0x1603080f040e091b011e0806130e060103020109051c032303090109021003150e0406060515040f060c0b04060515062a03160318032018010b0d1d060405 66
    0xb881c42403000d6503044104e03042c40800004840c828643c400e14924014050a00c0c0101e615450001200071502c41a10310b6124140041d45102c0d41021940c3d0b4100c2e4030030b0302c90341e10141e02c1d042007041d00c0c423107104004140c03400380200e43c010034450040c00001c0035140341648240c40040d01102c12503442181e100e01c0b04d07915000c9200440c1001d015802e200129854100904081018041c4000701d062080442c011008002f1405114066101704001c0c08024000a48a80c1480038030701c1e1340d0042c0c840e0344d90380f06541c0000524240140c240d003860f60380c4108000400d0f9a181d4031000100307409000044c507003c116602e41c00039121000241380d07203102042240b041ca03050000c0c09a00b0305900d1006030241c0c005200d849000c0d071004e08004500380e89801e1840082c45c060444d0147c004080d48080c4c031400070408041424060301900440c95981034880b4102d00c0c8041c84455a8601d0a11662004401c2000030165611459000340640018400003030004002100140e14000c801c0c0c8081d00c440d0400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 452827841 1250 452826591 452826613
    0xe070611060a1a0a09150b0901091a0c190605011a03131401020307090f080304050303121b13091a0f060918010b0a12090c030b270304060f021603080f040e09 69
    0x7514541c402031000fa045989031081080008ac812035851081140c510110000d208240c10f1040594200f284600120b071349015926848494800100303400750b0301b83e0315003800030443d11180d20760b600810141081140c40d580303503aa071001c04c000030307041c0903652940c4a035003204000c0e10030300003140a0742540d59207228590800813000034000070381c2e1182100e9442040108241e8038044250707003032204010034a1220381d4030300070a120030b0989000c1d0400700f036200240314800d421459040c0c000b0354022600c03c00c0042604840b001070344003155507165002403a00314900481c0341c050f0007450a090b000e020512026841070590913806820f070443d844031b076000715906103450f5001c5110b8610140e111418040221503854104000c000c41c04094082800c07500010b000b80241c2150301c410050705007200035000c46c0c440145440360018091240003072340300500c440404c0c0c40024003400c501c4580342256000c51135950b81030500c1c0d01c514000c0e24041c0d03080c0000a240052620494451405000500011200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 452829091 1250 452827841 452827871
    0x18060703020a1b0203060c090d0f05010c12150504050702390a0e0f040204060b070b01090c020a02131d070914060d151a030d030e070611060a1a0a09 65
    0x1c61060300710420f4090b00880056500007407495040120510010b13aa07040d4500411100c0601400c0a000c11041da51500200001503000c2c58800802e503440c080010b00000c08034096800c00001140611054032040c400d900d46648425008002070048440d0f04203d0307841141c03100c80c40500d803614080c0c081c13900710b00860092020750054908445490342c46041c104c0c02c014002016091302c8025070300fa0005021501c07594021806452156042e544075042071415260164090040c03c05443c28099580421800010103000e050341c020441046682600c0c411030052410b0381102c141441848401c2c50820002d106840181204413801300f0401d03210900600810000341006018022072400c0c40301140c50544043c0e140b889080011420115805049100344040c0c001940d042c0950220500490340561000100e00c5401050f10f1045603281001d94100380c805e0450903007a0800340000d1108001544160f104802c001d151600003c2d0301d0700030440841e01a004145070542d503c507034100601c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 452830341 1250 452829091 452829107
    0x2f0a060203030f100b070f05071d04020f0a150c060b1503010915060c03030b150d0209030f06090a030c08070b040b011412120d1806060e09010204030f03050318060703020a 75
    0xa10b0b40d141c09000c1d02d801d404117070a1260800c098a0707001156007100800c8024400c01c8000c0c10200c5054420243d030610304588002e06a500f240b0602130604141f8131818800c0c402c204880c0c240980500400c6c400c0816149580c84041c1160050ba84050b1801c0e5a6500740d0350307154994484810517200d41c1410304071812116448801c08400c4230b072817001c02025902a00d22034109034140340200f4030108000c04148034071920b103544614a00003090300c2401c0b003415805040b129a0460860301039416400010303840e03a0090740e26100740c0d0400c00001010134001c2104c0010035100c0c0041d01c0c80d290b401d489600350200295000c464036400c5100400c41490318409286d407100e01103078003100000101880550300d034035201707030881d01500101d1071080b412a180d11000307240d441c8c064100c0c00d0309040e18216004207418040c0f10000844403021500c01e050510944d8103499200013074009907007083d18165010b402c02098003110801c01c0f81880c0c1c00c11014400c050040c0c21980700580c8820345d1010103803c2074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 452831591 1250 452830341 452830351
    0x2010e060a0e030a0507142e05190c05070b0a1505100906030b0d0204061815030f0807081b061006180e04111507031404032f0a060203030f 61
    0x6814a540b40360303a410080221081c004850034165035445003450006450840482c500010b03008a1405121400f07101c865501051009078162514240d601d03000d400300c0e030f0140e40802d604081a001801c0328805540007040c40030311801c18500b032107050790f00c5d013100c00012100107a1041d01e03410b201c070101d0800008807015000499461103001c0f070040300280109054414002059165411419161141150841c00e15005441841029224070300b0306020100c400c02c07220014542404046207156100e01c4000796940030121002088941d140d910340c64101da4810344140c0c3c4100107400754070300740c805145458541c24000d8a043d1130220004c1240b0402d80c1c1c01042408158241690242521209082035076150503e804d001d0315076040c20b001d140075045500387c0042882521402c080245405003981c544207640f0002d03281c3e078148044129000e140302c0285540101690480c120f60010b414400401c410140d1b28002001c200010326030207540d60000016810000c107119401101c0b20000e5440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 452832841 1250 452831591 452831611
    0xd140109150f120209060a12050a0510110d090201030f0516030b0603091908040306090b0901050603030403030c0f0f020306100e0f0103020306070c03020304080106061214060a0504111902010e06 85
    0x40c42c200e407030f5000000312030f0700034802c0751312500045484c0ea661181202500100120400003250380c602143c0e55400341c4c0c0281d85620404150722149541402001c040c0006002c04a0400070400d40e0540a00a03840d4100d0605403074240fa4200300f030b034620916100e0154010b0f00720403107801c200c002e070032244000c8407540960403c0040001d100750000d0488005080d1700c640c05d1118080f4100780c402400750b03800c010049411300340220184034a40309114083c82503100208802e482e090200351352440385120040105001165900c0031803904da018415503400381c20013251000460340006d081c40b04c04c58940c41e20382289034050200d5550708a10540c0300c090111402865415500080e41e40ca100a01440030004000040d40c1010b2090060742c1c02403982c44001c1c440103848040241c1010300072880c140c622460f104120021801042c1401e000b00c2e40500025503143c1000c0600018015000c0d044203101d60802608110601d0310074144c0d000b802c9540001138414101d40c10b1030900502800940301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 452834091 1250 452832841 452832869
    0x31c110a0803060d0f050102130303090608070210020c16091a01090b040b0c030d090302150a1e05100b0d050708090607120c09050d050a0506010f060c0204020d14010915 74
    0x81c0c100000ca03034000108076a0311403001c0c01450071407030600900200600c154000300710344c0000f10a0a0f80728003034a10036111410360688a1108079403108041311305400681c0b10640340d40070218141d00820041501030300b99030005004500d0084002c900ea440100615074aa072404041d9030301c8010240551024681032450300d24104d91031101d4003460103203070401840001d40e04a07084e030800441d10341c070082d0042400031450608019488029404070504041002c10010321150101c0c40303091341c6c4031008110700c00440883c0b85404000d00008000032640b0425070004100c3d40040c030041c0014008259000c6020302c1d001384002c01c17000000c0c000703030302e242d1000040c0701845c1e030801020519014840c1c800215a8025003003103c0c0099103900c656002050b0040d80d90610802252588129000d0342c11125140d0b6a4105c0307401d0034080784540740004009c40c112400610f030640042042c001003400100b10b103c2d192007010610307802a402107501654410b01290f0030617180c032008004002d440d0411403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 452835341 1250 452834091 452834093
    0x10f020903031c1e050604182006040512030d0b03010b011e0302090901140108150102070e0c0d060f03030e030a0f0b0910020a020307020103180f02120c031c110a 71
    0x581c2e0b029402d20841c10b060710040d1400b0040c4079a2101ea0790006102c8030b5591042c8540048004010a40e442401750341000904440d15202984441140d03a100540f240c0d1200070312074100e900142140760580c4041c0030000041c056449403296034800c0c603440003450303031000d00c4100352044402400405010b03905180100516030b8015410050101c554240b6043d10007514000302d000744281142c00e075104d6a80b000129400e1500050107004101c2070721940200d0f00c0e0501200c072071800e040090750060f0702190003030003120a00480300d0380003c04000c542e03041074040b030000300556a8a030413400307114010000c200b090503808240e5150302c61040c0d0103490201c50f140c039a203480c0104c041000c1c0c011102800030507801c89041098030107003100c4a40031502c0d071303a02c190025142e0344003d40c04e0f40001d04004c103007254554a014003502165000180c0e4139001c03110f83c20711400813290703c110045401054601d2806450070b007d40d035a081e003c8941340c1d0f81003020394400307040038025411104c031560114003600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 452836591 1250 452835341 452835343
    0x4020a031e1a070f08010e130201020c0a0306140c0315091518060a0f0f150203070b0903070c080102090d03030f0f060306060e06060a08130303110a0809010f020903 72
    0x1640e4212041e030031007008000d005001c6810a407801800d84400c070005003444044004010b016418031342d211407100e08150f83c2200e030301e4400e00540e4210f6041402083c1d21180c1c2e0700c000f0340780501c1030050b501040e6100e000110304d00641d6000761529074031a108641c1f02e03a148412154814040750800f8210b08150743c40c2e80c55811861107070390283c1c1e09030001c00c034444550181d10301c0100c0000d1649038040500c110321008002d00740c60450180f05140c0001c205c11207032001d5030094580d00c613504002c1528107018443c40000440c41601540000c101a0003c5500080000d00c1400c17020001d40d940d51182c0380c000640c184581c000d121a905c14407888640e5540c41500d142c0d03498140ca40032541907451a60200205107203441c08801d145013a00c00010459030b60080e50407100e0000c14211981e81d21414032420b407040d0b80c1e1100000341c0380b1000903102e040d034003060035405020780350019940003030101612107544034103c1080070403c0d1904002e000b0409019801a8143c0130005504108003c8046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 452837841 1250 452836591 452836609
    0x80607020a0b0609190f0e010605030109080909060d02030d080105150304031e051c1b031b0318020d0f1b08070303081905010b0703020d09060503060405040302010b1002010e150402 79
    0x82d80c404c01c0f010003c540c090341118544003101c03044c4c60b8108810398448101c20b00a09510b03c5e00d28055082010000d01480c044c442c44017a0b0380c100e1081858902d40c1d10800400000c01860994869110308542c00942c030204021603040c40140c40e9400154184030030040c2c01a12101030b682c0b00c02041040200003079028400c161075481c01c90b8109250507601100f510113004000c0740151001c0d02c00c0d01c180782d540e07083d0800000d100c0b0300024100300d0000303440120161008001d04441b14000384070781100315840f1742e12444d00c47d14000001040720303142d68002000c0c1460042c0540701d202c14145204140020403c242000750301d00e144c030440702890401c0241d01c902036440301a090186000c0000e1036041040d54214204080396000c00c07056848407003000e1396400003901540123214000d507542101d405480300704251111a15024155540e41007004098403005004400315520745069807400d488102d402c140c02e03031007130300040f40c1090618101e80c0791144150900800d00d50340700a01001d0b0300e40c802a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 452839091 1250 452837841 452837851
    0x5070f030b0a1104120201030b0909011a04110406080a02070204050406090311060402090c090409020a1502100e0304170102160b0a29010c05070f0e04060b220e01060e10080607020a0b 80
    0x38171911683c500068004010100d4200d4101541c1c10801007007003411340c40030b071030481d190f00c0800d107400802092000f00d51041a00d001450030410092100c1c5025155181d80010710b16809490040294085400d0b140181d404460003a15403907000101a0050141d400c0031403070300010012741c94560001001c41a020307105000303089002408001c0307900d440c0c024070302c0290040c00e030340c401c00c3c0d54003080c2d807141c542d042c0c0d070000600403940744201c4c0e480d20380600442165000011070034681024030403e03800c1c4003111725803a559400c11021010001c2181c6001070320b4010051910a031405401c40d509903841e90304001100700703d265501482e101c81c0a40021000c9007031038490315680d0f0704d02c1c000d460600550012611803280c410006a030304a1040207510880c420302c400d0003000460014032992580408908440c10001201d06002e14110380c0030101c1080c03c4800403441c241c1e160aa00c0f81040705650001603403c1d100814840d01508000d955040449403008102e0790a07651200e1010f2040500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 452840341 1250 452839091 452839109
    0x2100507050408010218100c0b040305030601030e0105070e031006051c1b03060b041a09041704150e04060608100b0d091e050609030c0318030102040305070f030b0a1104 74
    0x40454030007841a002c0d5070181c086040210741e100c00705403403072465580c0345440340d2040d440f126081506520a030721205a41d0b44c018410307126500c1d1a0350540781c6401c0100040c1c10156203048040d611002402241d004030a00c0c0c49501407130000b5020726080c002c0c41d55859062038205401002142c41c2d040d0694114801000d50300140c00301450400c10a81005105031400a07d1620120502c40b407a0b0000e8510031085504100e0a404580030391240f400040c84144e024041d040000c002c80c01030205503a00000040100e1314017501c0c0e038103912402525180810024000d0440001241024030851340a0310041c1000f0040745040041210302c01c0e918010f04010b00340109004600002941004011030313885600d4203c4283e2008035800c110030948400e680c01e102d840041200d039080070045403840f82c1910091440c0c1850340d0103161805c030a8451950701903600700b1000000c12004c3c007079900031341020601c2118641c69030038250442d010203000c5000e4030b03181100c0c64030254540d400f29011541c1641c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 452841591 1250 452840341 452840351
    0x1a130b0f1014060d0507051803060105010c060b0120101406100c0501090501110309010b090f0c09210d02100b010534051f0207020a031b030f050714100210 68
    0x780210f16540600103510941604000501c0031150300800540b049080482e010f96458081008040e52404288075603404a59101403c034046185078000c8044d00c43d041c1000d40c0d440718450703c0b0620900c1e2054984400b038000120740030750252603008050810840301d80d040c82c1400c001000503601d884140044003400004e9085808100080d04481c0080d60000001c01c40110380c0403241d45203500481d800b5416500e020356030348080ca0a15801d03030040300d409610764850354442e15041c80310341c040484d281c0e0241070310031150304002020b00500704204500c03020780350b504001480a46460110f0002e02616410320900400c1a6441420307154481071645514402c801c07449080b240c4c0251400030305a0580c514002102400030000c1d43c0480d20b1804001141c5210508030f4420803402180002507101f030407080e041012a44468095503044848807141c4c01c0c50760350380d07201ba0b510010280202c1d1a5040803d041010341154401400d00003020f4800c414003ca40501c029103601e800141401d00640e15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 452842841 1250 452841591 452841629
    0x10e0f06030f0304091b1b020f0a09020c0f06010e040b190f0203070c0c080111120c0f0a020106090b0f1809032a0d14030a02071a130b0f10 61
    0x100102d4803801e941200f581c1e540c0343c031004030401400000403c4414114050380340c1d8a00ca1054491072007182d82c081c2d041c0b20342041c41e4200321815910b0300001b6031005003030350b0120f48070b95544028400420110010801002c40f0840036040c50016170111200c002c102040101103070b41310a5940d405142c800040e03034095010f4031580000e208070b408030b414891005c0200f022407500079506003841405410690940d941d510801400d81e40c0780c50b003c4070301003000d1100b0440e140c507140300340b5040001040039600380707000d641c02e51010740c00c004803880060703443d008200000d0810b4452243e200d0000c1d2924100c0e00801c20104070061700091003421158418000610f810700140250382c010302242d171000c10f64606000c1040c0721100d900b81c20b110079021785900c5400b080c2c041c0e000c98184e421810801800c0d035441540203c0290060304090342e1a4003504502c80314000341c8956039206134440e9808111080507401e044484183c01044420548141414440641181400303001103c084000b204000c0d016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 452844091 1250 452842841 452842843
    0x306020c010f3201051003021b120d060509241908030c010f0b01020d12060e040f0302060f07120903110604050309030d0306030201080703110c0a03020d17010e0f0603 73
    0x10122006007a52500103840e49420b81041181506443e0060307a07801c25904607008045028284220ba51040f081180b0b1800c16009801400000f4449165103160003c2c8010040c20842850001c403900b42c000140e0782d40c4030083d481110090321050b102c9030079030701e402a401d14003c80c0b940010040d15441011401007527466100441e00c2c00031100401402030758440c6159603907003142900100c203500300a0030000e006181d1245220246059000f40344840760760b1410303203070108110300492810707880364408208104e20109641c0036503c9140c5400540303190b070900038203080002d0003604420410301c045c400c6840d40b0106c6a0006507544400007081070080c98180c841c4e0a18100100460040b082080103118010010740a131400c10390a07034204e8004148d080302220307002e020007404070300d81c1404a00801c1c4a079008c1030380c20040d02c0c0854942004444514501940c0c0340c5e007100160300284490b4403c0703a0101407030061145905030070307040b941042011401400014610651081c0c104005050380d0b41c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 452845341 1250 452844091 452844101
    0x1101110a0210081501020c03070b0a0915020d0f0f090515091f0201060e0f0106120608030c060a0606030905100c0c0c03050c0906012a26030f13030206010306020c01 72
    0x2078014803050740361000c404042d0942000312400302e905680301c0c0300119254000705a4031003818004029151040c10045444116008407851900300042c131b4601080b0b16108100c0b9140c0a0300d647c005100c1c602940c800200780202c900158400c10464140e00e0f0001c541080c5518161a0201d030700441142e164801c0d500706000d2141c0071640a0b040c1c075048020b071011443d5141038088564005d0000319104c40700e810300140c1c180e80c94044032082c0c00040090380d118400e258185030001e10301150b080d40d5141e13180d2458020040c0c000e0f103600040144a1204001d01c2401d00911b05030038240b05441c5141c861139100c50102040c170150303603142c544c4040b00d41c3c405d800c40c00c250b940c00b04050308965260308041c0d80e0303202d100000368040c000000105200b0f60140c60441c00f6450300001c1c0d1080c4481c0364150f100c00c2c1c04e41c04012504045003006807050002e0000c40d401582e5003405070340f52070385081c0319550b040241c040c210070350002d440c5440d41c000c6940800c1140c10b41b60082c0000d6502c0c6000084240101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 452846591 1250 452845341 452845343
    0xa0e011104140f0306010506121b0d02031918030309081209031206010512010306151a0d06090603080708030709090203150909010606200f03030a050417071101110a 72
    0x440c00040c08510b200845105801c0a2000da800c180d00503490381c10702d59215000c0c000c090b80450144031048900c8601040c1c00d80c07204004207104030007174007540d9000b1650005002c2d042c22a4000c810403100092070401d03254005402c2d00b06002c0c03d00a540b040130301050441016040680315445801400003620454001001c00e030340303020722440c0c038525283d101e410100020410004000c089510b941c41102520f8120014600c202026413950b51114010488100c5d400c00d038141d400f40005050042c4098607000d00c903d0440240c0d2840c5e5605c000e0704075400d41d001901c1c2d07280740c84000c3c800706118070305440d515544160700782da4a880311030081e40e1445060344241d01c124000000c01c040300c3c2000144070b4441100741d070701c000c494450280e018282e4105020303501c0019a4170f81c01010404151101e1207207070201000396015000808030060450b40121540340a282d101c01c03e01003085046810b603403241c501c1030201c40c1003803042d0b5541503074107400520140c1080441c18101108203000e0210031049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 452847841 1250 452846591 452846621
    0xc050412230706110102130b0a170a05010501261f122418080906090303070606150c080a0f17090604060b0f0f060a090510050403020310020c060a0e01 66
    0x54080c1810042e0b0716200b0707003da04001203c107000401c4030101402640c024101d0805004130b603904281001d0040d40050b010002086101c00c01911a8185007403898014115608013040541c1004005081d088162003c0c08880c2e003400c2001120440600768290400220346000c00301c41c416401118450401d5002802c00004480007171040014050782882110103144030040b50020b860240000c5441d10001c01004129502c1400002003c0707000801180700f0081a403030030f0001483c0420728640040b041101d2069480506010f00004010380c0c00c0c821110b0b1501d00640c05541c0d440c00d210380540d2003020180003421144410240c003d05243d2580c00800284c0c0c030107403401300d00c01c0c0c1e9607002c01d0b90260b400500e80441d021190402045120501c10701410801c010010341084c05961380c004072541e0104a030021011034295140780700803422541680e550394903581140101402d0900d2900c4150f262441007226060803400842c50325408a000b040029103008151050307405402070001844034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 452849091 1250 452847841 452847893
    0xc0f060106020a170a020a0b060136211101090909080a08070f02070b03060d0c08030d110310050f01181707050a030c0506031909080702030c03010c050412 68
    0x2a0540c0003e42e096002c0c0180302c2521450007500c1402c4191242d03201120040e0048008038010414085085801c0441031401c4140300001c1c1c1c0241101e40000b50f1040340300f280c003594058056114481800c0a00701500c2c4e08805a442d003200901da00c1121100140865070030f89614205a008440d00c40c0100900e120911072002130340360038042a4001604131001c181c81c48081980b00d40324441842109005030001c100050410300b004809800041000340c1c00722001d094600010f0658100340d004216240c0107584560b4000b07101c40c2076450810b0180e91001081c8100100031500220300c070304850f01039415410812242d40104ca0004070381c085010a1807900c00c1c0005c01000d0b030b2500004140d10300c0151036000d5140c80c100050342d403a52001410508150206215528152000f50303049a04a090072504100034400e0006890003400243e80180c80881c0f00b10550405018107000441d084000300b00e1030109480103070150007507004240c40c41d114170b00c90004105d00d000700041050071210702054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 452850341 1250 452849091 452849099
    0x40f02030d08040210080736030302032106240d060806180a1110090f0f060905100807141204050307051614060f0f07060b03012d020c0f0601 62
    0x300b0036205a90490042d0421400403500c14450340074240600344903071707030b80e00c039001100d10024885400c8460003c04c0000300985e265000341a030f07280001544690017841d203404200c0c0741e17500e00055150824108520607410040180e0340c5103200d40390140c120700407588180854600d50864019050190409403405d04041104040010130b94440c0645042c441200c4580383c8009484070246100104100038800501c401850041c0a100d0f2010040c40d003007010580d5105203c07034a0180b0b52041100e821100c100340025503010140074080d00003030710244030401025230b00030555500101220200552504141c2180c0418403c40e04042c1c0c414041d8012070415040aa40741e600100048410f889245000020508081c103840b040320340b440850842201c0071410300ca9954051240080d4a400c20010000012003040c0540711290041400007504101241450b00311400544c000c800d05c0e001701480c0d141c01c01034041100d02581d580c2e47c05a15450007190b80c070320700b46403101c102c2d40c20300507603001007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 452851591 1250 452850341 452850347
    0x1911090d050609010b040905030702040513080d0b0118060c020906041104090617010e070e0402030a151b090f1403030f0a0503190506010e01110f0105070f11010204060c0b040f02030d 80
    0x50040359003d00800480c1314120800003210500d01004096800601501025223402e510440d803040c8000c0072808800134a95801e100f5030302844003011519929004d41c00d46583c40500ea50800121855a80c1120f0400030060429101020028030a03035900300010701c291215000b0f15000d591510b41a516180c03580105005410381e07000b44c0c002c0303075203000380c044040f01b05000395005600d00c07a000d0a009410425400c01e203001c002c1040c2c1e01740c13203102c0c0b20301c0000706000d07140442d900d110900010348000744084c211500c0c245480c60b100700f2904100600040c45c20b5040c000440350072070040780001003544040b90070760294020254030300d20041000801c1d01d4200300114420301c05218001c4004217005901800c440d81904d0f564002180c11180d140c00b540a40d0b2111210131020b804c45103d0509441c5c150300b505d508603451400100250440a071203078110b0b00251440e060700000358185030a0100090840c4104003024000c00c101d0700c041018041281d0103103488036005005d540c891981c8038400b13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 452852841 1250 452851591 452851603
    0x1f02070510021303120201091b060f0c1101180e040b0402090903040308090405070e101806020309030c0f060c070f1805060d0803091204030c14091911090d05 69
    0x35500c500038511115504001d500c01c5502921149a90348446421516001e00c0c210300c13851a407065660311622500070a65480f1101015849140c08402c09801c1100040c86002c0c5000e440080c4540c0107a03e800040c5100340c440540340080c41c11512207005441d40b81c400c102c5035444031b41449402001c0c4010310100100e142d200c0e5000396004005604c1c0d203003005680344100d100140c0b1202d4140b015103c0c0d4a400c0c1c001a80003400f5181c85800b41e80002e00154481c1c0d4130003003020200e400d611091680d40000f01001e0700905032030002c0e506003010200466190440040b107203100b844041100d0b81c955030340c0015560a150608221b502c0c2074cc80e1081c81000c4c250a00035980c2210ba00040e00c01ca4200b9409030714070440b4080d16203020b0600d5581c401c40c00ba00302400d60320860280301c4010b5a40c40584014000030350080c1008031200d843c10300e401c1d0b01e80c801440454080c420a0080084045140820046918002d000000c188180391035850290244801c3c1d0355005c0946a00c40e81405400114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 452854091 1250 452852841 452852843
    0x20607060b09010f0305060118090b090726210712020313150c031812150506010306052101020d022a01020a17060d050312010e0106051204080c1f0207 66
    0x21a040b50341c90b01c42510104400380700083c80c0da0320400c010301c4450144d00c4d03124460a440300012681c00c1940e13591030315801040b501c422069010207020009503860764101c2520b5203d50350362500c02c003042001682c0314042d00e0040004008618804000740700718078103d4a0352900010301e440f000c020184029241d50020404c010003903040d0001003600302800c0c612070003103d400d8075216800c24650340e0540d42c500c0b000300da510412680581c00a1076850050030324801600c0350781500070500070a80c050003100c0018107001e040502d460800d02c100e40302d180d0381c550f5002c1d502107101030ba034505903c2113029210b00412020220f00100d448642e01d5044501065000610000c094112125400d418203c0c050030410f0340002e108003202d414002008441990004405018649403181d80d40306e50f881d59004098800940303840000400148580b01082800f52483d0b240041c03420100d080c500324100c402420151905800141d5140d1442041141c503121002203202d2749084c12500c080d090007074004800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 452855341 1250 452854091 452854099
    0x1206010f06080c0904051009110403170a14030907030c06050c0d14030604020c0f06072006010302030c01050d09171801030920011202180a0b09010c0b13020607060b 72
    0x14001c00d0041c0a81c44003442410030440d0345040580788010071010f000080c5c014401d1125040000c20b03011414040c00328140041c00306140c1d00d03032030344c0340c20b42c02c40c0080c0c0045c0c0da80c000c0030721590780c040da0f00032082074032026152142ca40340d4030b0b495001814051950f2000f000b00c002d55000280c80c3d50070601510b407058405040d1f5591000c0310009960940702d0b8484116698001c00014195140030340c00380150341014000c6901490b055048c0c80c2c81c041d8140d45090214031015088040c07011000f0603d00007841040c040c05032545950701182d0f9441c0c846d080941071000104900580246603880300720940d8000030300000707105001100ca030247d400450b510740b03501e85412002c46030354004d01440c0d100340c0e840b05174811071811114841c01e0041d0f000c0d00050401114950580d14106c0d0b41c006020640305900c7c0840100300000c1c200800c1042a603c0800044801e02c490003480c0e03003105030650440d4001110040681d1201c5034820507101100009500000100e0000b0520045501107200030798180c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 452856591 1250 452855341 452855369
    0x150c02060a180203150a061e03020f06120420220b03010c0c20060a09050a050a03031b030210020c01050f0124030e031306030209010905041b0c0809120601 68
    0x80805200c00106180203505513000241c01c04042c015070b17840550008200c80002591030321101145d0050300c0d585129050079141d8081030081d4600241d2100954000700c8100e0301d0001691448101e113840100060110396000c000c00003045e054181000c4400d40c02041c2c50818202c1c0001201c40305a1003400014082c0780411000700c1d414140b16070200d9513030320380b660840c00c5126528640340d0a48800c41c451400c104084210a0303803501000742c000401c031900c032450301c0303820441485400902c55210b5882032035146800c00103ea04024102100c0c4404d4140c94803004050a080e460181104190002d0900c00580b89412040c10741c4468021a089000b0511a990310400c4a05034041402040d04404e01ea0122340740060290740718042120010303050f64104000c00e200190300d162203a000038042900050482580d603800301c0682e01812007140e0400c54680c2d903c0e44c00e4000000000b2640c01d002d4505608814800c4e4401940e401d6200141003070140b10f2242c0c002607c800083c4201160940340d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 452857841 1250 452856591 452856611
    0x50907050105070b060a05100c050114010f150903020339010e100c1a040b060108150d0606180207170901021023090717030c03040909150c02060a 64
    0x1181440403210140d44a508001c80c0f903c0307000c50000050328050b4000c0d50300c0c3e4002419128000001e9080c1c00944810782001d02e00e050040c20b441501201c811100107110040c0300f0686e80f00022070a1342d00c5041941358a088145050720b403480f10760400383d8503101d0207400740100001003090005401028003030190031100d03410002100000b0129680c0800c01291004c07480341130041c00c2d0060f4036058580f0517030f031000c80c0d1203120410800300d104041e5950b0b10760800c8144120240c2403900f0a01c28a000c0c8150316011640240460300200964812191020600240040b6411100140000241c659031041000d41000002d40c401441119070300300d600070144c0200905000e5035084030307042e000381c40c03150f0032840e440006002d014108018544450440714601c0d140307809662080742d040300200002d604060102c034400d807a01c000c4400a034820400c10301c200b08080141d40864106060104030b094203843c01c5500d1240d68154080200d140204d41c2d40c14541c00a607282c081d90f0f04240800c00c2c1c1c502 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 452859091 1250 452857841 452857843
    0xc0f070602010b0a0e0c03060a031208041416050114271207030b0c09041b021005060307080307060b040915020301031115070b04110d061407051c0c0504090507120509 73
    0x83d078403c00303401708140b00020300042c229100465104600401540d04141c495030341c420011035101c00ba0002030090030802040101d007901d0044c0c8603043c2402005003143e03014441da50001b05010340e80c1040200f4485034450350040007610105880c00c0a40c4456151100c0b41044031100080824842c60440c501d5602c112004a001805d41350407400080d00d65840072407a200d20780c02041c40f5500f09584a54035808060202d08142404d801580a002002110040c0310300361180030741030b503100782c0041c0010400440000110750b1200d500c60004504282d140000500030035180c2400b07050001d6617000f410000e15541e00446c1070380d105040840f10644070704248040d0286c984140d80ba06030041052501040000b050039503c284150107008080c0f4064000c10745c8402c0049080301c086850354000720026010440c0160711809600d03090b230900611121726a000c9001d18105800c6964560a0380b028501c26000c8074080c0c88004018406400c007408020048142d07103c404103c00c0c0b13010b0202e20030602c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 452860341 1250 452859091 452859109
    0x70506011401020a060c0c0818150301150309140703030906030608010204050607030e0d320c060a1107050907050301060206070c03050901031a1206060312030103020a030807080c0f070602010b 84
    0x41c107a0083c0351518059480c6401001a40304400034800d0420325900010211070040070102ca00100e2051005828401d02c410510741e6400f00e013184c401400103210502d21840001c0c0500c0441c6000704801040b41040c151b220340320f070000441ea00a5040100505400c200f41104840ca5550708010003070380c50418501300d000c0d07402100d40c4020104600c401282c85542c801d12202c00c01040b030303024200c10741d964100000041c02d18070344501c4a035000100303081c4468242d00318219490003521064030780d07400190f10b61290040386410300505100305820040300300150009000058016260341c10904c6014100d600f00740310307100051069000040c1c3d114468200b40380b50b99070503141c06041450345070040d00541301c0840f81c0d00c04503000c08416249903581281001070054484085e20701410701d88145410000c0300104100c143c1020001000107032504c0a40302d003103d412001c940d803100043e1400800390301c121600110617200c3e462440700d01e2480420b90b0021101d540d0020000c440d11182842b500d82 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 452861591 1250 452860341 452860379
    0xf090306131a040602130923102603070f110f0108011511030403080c0705011d0904060b09070f0905010906170720010902040506090f2707080307050601 67
    0x410070031682c2c20080608403006070050312928015050000b00d008009030f10790389a01c00e076500c54888540010191448845040544480b40401924a000d0314a40054501c2d4411140d02e4030040d4820a00c045d0103a2a0348000302c40301061b02e6031051039040066245600c00d2040e54115920044040d03e403811490040d540001030311262241e070f180000600040100c80c07040414002070345080101000c003800240091403182c08500c0e111000500c026245c55010b030000c5062006140301d07441d50802d04492240ca0140c1110054515681c5103032513805800f001d4a02c0e900181c059040c0700c58550441003103000c3c1c9502e40d484448850b900c1c001154180100d02c104400b04400703140c401e03d9004e551039015444a07840c145a22031080301141e032040f41c0d240a200001995503080c200085107028014107400c140c0449408115040560001980880250400c0100307020703103207240785505001060a125511070380070340d92540d43d580e42403a12584684003c4825004160012500c100c016608981031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 452862841 1250 452861591 452861603
    0x3060c03160c060b060c1e0703021302160204110a0201050a110d050c1201060801090b030a08040b0d11031008010f3c06060905130e03160c09020f09030613 68
    0x403082072080d01c020740340d090309070b45958030341070300d000700e074840b10700509642c42880010501249030f00f501155011040031a441c0d036030882c120420242e0380c0da0428a5010350f1004005a13604c0c810741007440d180d1903424000390850b04205860075a144c0500c09020442d800d90001d10080c0ea494030101c0858003c01c94030250344c0802d1003001083c089a82c00b80da40903a00340007051900710740198140c220780e400d9024500040340200180243c1210740151225804180d000b0038824019940f80e4a083c0600d020340b0102403004585121000780580102c585403020200a660343d00300a00404654262401005495800c2442104800409229000c03585442544c07140c84e5051305c55241580c00d621206030503c0702142c030002c42e1071030075a115540c000c0840f5103034010750914280c1404103440c07426201b14522840c00b40500c00c11017003c82111700001c03909201b21201c8200c0d10340f10703001c843d0b15080b900d0047e00c0401e852924080040040c608040b040b1b0448805503903a147c1c52a614442c2d000003080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 452864091 1250 452862841 452862871
    0x1508090a17070c030803160f020706050307032f0409140112030e01171314240a1401090603020a1e060503100815040318050109050d0507210203060c03 66
    0x284103041e0090107030a48100603c43c0070716601c1e240e207000c5070800d560001d040e1030303d018110b07841c42d041080a42304805900107480700d5841c200010b0801e00000b40340f0000d054840800c03031030302003025511101c1c0d03502c2610200286012424070035a141c01901400034002c4c508107110044e00c82603504141280ca582d545009401402c2c1e500b110b950203204411810f001800d00700c500000055409148101490030380540004128184000c2d220b0311502e005c5072641000751411148904060142141d0b405025564080c0e1240c292803c02020f82040540c2007a26090000c5121202500075000f264002c50b1072040341c40d12030081701000c82c00404c1d1511144050841000030a024030302079035000304204145405160b40e076910310f003041c000c0d5401d858841158000c0004242d0000c0d800c503003d0075a07a0641c0c6c00c450400d00081c1070501c1074040eaa00c984502e01d414400c01104000d00800351921840c00382e07000c07980520410b10030203840012072003030140c900060041c16851341502d20400019000e061 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 452865341 1250 452864091 452864123
    0xd0903110f0604050603090c04051531090308010806070203040506160609060f050a1a0307180e12032505091c050102030108030a031b0c080c0f071508090a 68
    0x6940c070818100700340c011a080c8400103850780c0c1d400296105190440140611408040810080f0390008000032008540c4101c1441203884010152914001321030502c0d04615008105280384495141d101a44504128180003015031201d24a41260503a00845d800768071450000e036180d02480c040c2940000702032000c40d150143d20f41c15070301c089001d02c500203049190358403110169007402008080c0c184d250002d11230303036189a1040d00d19031000c2ea0101680010141e000944503000392245000c25007074821054030801040d803050503860b88000c11070710369440140303094155800440c1d03000005140301d035900079594070318400a8407000c2c09507076107403800707d240703080004030740c22700b020350700c0c100910341309280080c809100444c06403404030019a1501c580102c003d040d581e80c449038111400382c84690b0400c2c0358100c0c0040050582c013000380307511083c1803d102c3d880d00c4032620201c8914440d491340000d5058903001441d4580c0e03242d0b540c184c0640c0e65103081643e43c0788000350003881004008036000f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 452866591 1250 452865341 452865349
    0x80a0e121212150a15020c010903110f03030d0c0c0b0907062102090a060e190e010e1806011511063c01260703050a1209080a0b090d090311 61
    0x9603c00c02078200b442c001c803440c0001c2420340b003643c1c01c03500c02607411035825148244c04000c0b84442d04e0703007403900d0348070281590f6400f00012020149180941c14441141d1000e5034103200b5520683c00c1c54404000e05243c848005040c0c28903241c058800c06110000b00f000c800012a16900f6a43e0726201e640b400b00c850841d5115020303280c0001c02031190f080c000d91846a40e034100380b40040c0313450b07960740360b201c1600d0041280541d08200c00e800d150110340c0e000c0011070f00c2d006e915811601054103c1429035644100b44280070180000d07a5501d00802d400031030042100c058a010084080c3e4810010200d40c818032540e943d002c2d544040c40c2c60f82c14a41580d10300492400340c41000c0c44000d00c41202510104c00c482002003a00160700d000c00c185138402a901e40a00c1038078840906000410886146448440e118142d41501405109144400e100380d02d0154122800409100e411a003401560b810955406041651280070074055041d102c0400ea1080c7e29007002e5a0b00180302018900d0088108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 452867841 1250 452866591 452866627
    0x30906020d1d0d0503030406060f050d0f02040906020f03180624090703021b03031801050103170309011512110a0602030d0e010e0f0a050609060705090409030309080a0e1212 76
    0x31036480f4224040b40c4000030018809980502c0c858000803c8a5080071011503141d2525040f440c00b0348011042034000c44c1d010300704921525015a0001824206070806101900c1007218803481004000140804043d044501a12030452030040d02c070961a01e1100b40019203d030310242c80c955040d900010b00c28608055000d0b00102c8034100103140c8424004a100403981c82c0038a014a41c00c040100447c12030001da0540341f00320b010008011943c115034604440440c4074010401c0c0080100006442c07517000d602c0a01e080d0055131003580e219a030394108158215140f02e0449410004d40a0300c14039003805400401550503940180d4144850150307c0d00c02002c0c0080045120340d250454901000c0c024400c101d05c0343c00400143c4500325550600c54034040000d0180f481651002d4208080240c0c007005480c40b0b0f400071030300403514040300c0c10304034050f0a40d4600a0081500003820900f040e130481d84076003140c18150380442d00f00c6118450300e612401480031420000202f0441d06c04d03020310703080c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 452869091 1250 452867841 452867897
    0x30207090c170a020c151807080a120c0302010608070f0302180f0a0902031c0f02061005030607050a120c05031501051e0a200d09050f0f100c08070c03030906020d 71
    0x44802048540c6c40c0e04d40114401d80e124140e40e03414541a400f195810320000014244900050100b1042e13592072a07000001002880b080110070443c035001c240c801c0d0440d40080c0101011181e0003500e521604403030904910080b8856030761110030500180942c00e125104034076101c030500d2165078000d0344a016212440c000caa040c010301101091403001d0b10041c8001c000c190f59851099251082d000c0e260850280c80164103142c82102005a580d0005190380e01506d5071600d19150503800034141d41d524600c8600d508002c0c2041c2e42d07074612a9000000c0d520039400071343e03034406090704140191054801d425101110010080e480003640c1e840360002c0103028520310742207440d0326116682b244940d4440c7c80020303141c1c10850740543c0940c6c0c0094803101800b812603058180c0e50001000520900681c86101c0c0250103140300789242030702580c81c00d80c000da08424442d50761529803810400e03040c0709000480c0440c00b03005020a00304e02c00a1404c0c08214030743c83c1d12000d11f541c00c008038560214444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 452870341 1250 452869091 452869093
    0x1506090b0906100e0303040f090522080d1b0c03023f13060201050403080a050c070f0804180603021311030c070c03150504110105090a06080919030207090c170a020c 72
    0x841340704142c5040001744010700300d15444a40aa041c134034a241a15000b4000f003281c10008042125103d045a9a0f0400c29601c4000b032555254850902c001410180c1768400c40344054104548810360404a00500c10380300c2d5080d0781d0001340c010f80c11200c4000014205418040c0280201803070080d4012482c2c0c03100d0f0480940782407403030700007101040c000550443c10040c1d440b2001d100403d9080b03034160340c000c40c00e084288060701d400c500107074541c004c1000107000200ea079a80d00c014401003000300c4014001294520700ba00440300120b2002d0701e13043c44101d0240000e980c1401181039140b1944c110500e05000b110b203961105c0d0304080c420782240750160b441042d14000003002841e800c02c4900e104c00020381c041100c0c07409040040001c0050008141448820006121a90f641c0d502e01000c0c3c1e110380c18598102d86512117200e107045141c003400b003080c910f42c4482c04285a0006440300807182d41320000c0c044080002c00440e10743e0030910074200314801000100d0415000c40d0007030155214848 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 452871591 1250 452870341 452870357
    0x3040611031902030d0608010504080702010305041406100501170c030103020607060b2106100e0a0e1504030314010b090f0103091b1e0603110403030c0c121506090b090610 75
    0x10300b5030400070110b81000780c096400041c000390005140d01801006019000003044645016154003c440c440c0b40c030024109039441e80040c08102d00500101000d0101d4000c54072503141c09649840c40c0700380303401201d012420510041f1381c115403040e021840f661000b001c940c21a441c40c0e0a10400783c1040c001114820f4440d5141207480d1035807010700480d29600302d520f2911112aa8005050840c023900307600802c03440040c140800d00c5072a4031140c000c544040d00198066120741ea0030308018181c070444450710180c2d014441410352540085500b80186900c42d94541d03030b9480e40110f81c0c4030b001e00550300259244900e40066020340c0c007040c1c4481c003a038102c4c94000b406800303800442c80d1903001010007a060281c580c4040e12507981c2a800b41c00c1c03034281001340c030540d241942c61900131480002c0401c01d00840502c20001034441c060000c0c0064010100b800d96149084040c038004040628000d81c074020000862a10300d000c2c10340d450401400481c065103e800500003255002c01c40001401190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 452872841 1250 452871591 452871607
    0xf03180108040f1b090f150608060301140c030603062503090614040f151104050f0301021c02030615030717060415060c020a090603150504111008070905040e0304061103 74
    0x2d200300c0401d1013548804e0000907410480164110b03200054010b0311240707082d418041c614030b00c0b44460b00741c52480c00c104a070740e0342d0500081e02404900d540806000010302c03d205001041c0e03005540101d40440a650f42d564420317020034000310741c00e401c0454000b0340303581980c050390080c2c0c0250281d0b4000c44c0c01140b00822a0050b1100c0e41e4144c800310340a101e03281d451018884500c04160700f0080644081c403003401d00e41309011140c02a401010301c2a41031422500307486e40c0940c111000408200c0c0031440410b000517508009400c21651640103584001c50f00c8800014802201c1c441c0805845003503819902040c10f8421101c01040250465561148076140328207404100c2d008040d180c5e1003000f82042071052006950886c1e1021544a0034041e06100180722501d661b55100b0801600003845d07616810815824428410b02c1c0d07070080c601c0b0360050302c040d074800007542c462241360301c601880a680341f007030004890200c1c0001649404c140414000745218260010000103102c08880c00c0440b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 452874091 1250 452872841 452872853
    0xf0603020a08060f070201020c0c010315150504030c08010621113d170c0d020301030807262506021809070207080a06020a110106080607020f03180108040f 68
    0x1103070421000c0d503101e03030f0400104e40e030311003800c1d039002080348029800c001d00c49035140e680300c000c458864140740d10b440030860305150250305a0000c12a00a1815484846901c06062503002d80400c0c0d0b60781892031070214200105000e80021525040e2000e1012a100078a003926018990b20840391200040c0351101c0907a90016005e440020400310348000c1410360141114581800c16605145000b02a00c0c2c0d5070a41c000d2081d51942c1482c0c10b1030728480d6a010f10500e9144150000205200d10200021090154082c0a4030000d449031100480c0c4c1050f40400c00c10404c0206255040c080c8208106200700103240c03000d181ea05d4518103a0400c04600d0b03900d51040c1e0b00f003441040746045544101d040d50385030100716140c0040141c00070744481350400205949441d04021b01800440e00021140c26261090f000000e506020318020080b4544032107009071241ca05a81d0300c001482000d5014440483c007108a80c074103030200108451031000f1030015111840001c000742c81c50721403020942d02040d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 452875341 1250 452874091 452874109
    0x1807020a290a1b02070803030a02220b0702090a02340227220611040302041b020717071a0702030604060e06100e07140c070803040302040b0f0d03030f060302 69
    0xb4200c401145405094030035400700030100c5106030455000503801c0011500100c1102e0b042546403402680e02c000c01107003400903401e0140020600710701043c0002d203101650300030301046842100c4418880d01e441d0303019000d9019070b154aa0761042300e0039a502d900d040401c12240008548038002841801c1e5800103a00d541602d10b00b00c6102501c260075800d0011038414103075004c810b00c4802203e0500c9006400c030118141c10004084640d02d40d511b04002c0c030301c0340c1520b00440d4020428421044103003044003d1000a291520161040e0140803504000c90301c40c8040140d0b0010003000c50078608a00720031101c0e03100c2d0007003c10020030800c07540961420703c009449140540c1020400c4e041c51103c0710303d80302e001041046625003c0a0030320002d19605081500031341c1c5440c1000c03141454034240d58551241024614080c031a00000141c0202e010002d482124006c032020840c801070002806032441003202400c1e44108005200b070000b81c000e51140c01ea806200a0021344151280d0110313140358 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 452876591 1250 452875341 452875351
    0x9030905151c020705150402150304080a02060a061d0604020721080f07080727090b090624071a0f1807032012030f03061807020a29 58
    0xc000070703500600b40303480160141c8a400300004514080494454035103e40a5500c41100d00d22800e0214040d503443e05070f601c49584601c40000d959041c540780c80c1001340e00110b60718025001d203038001540810203205420441c0c202d00c0320700c4404503846008211101c401400c29900680c01d20191012070400c40351080040c0c010015511410701000015001e404020103503000c03031020344100303c611680014800d400800300d0500c144041103005e440418001e0500103401e0b400304040d00000d8880040c2c219012481041d1609109a00c8500900c01e401c011034403c8820a4510b14100b5101641070008010311805184000c13000d1541400502c880320059480c0c0e80280304440c1409040c0c41c00c140a40822000750b402030900600d1540c42c40b4112040d034801d486800c4202c0d400b4519038690b8a6450700c080700f02c00a4031340d2000d50744c0500004d41c10655055004111a010b0501c140c1c001c11109401600180c00400c3c042010b41d650044c0e05500c02900b03a082048100c400b041203a120030030718016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 452877697 1106 452876591 452876629
    0x809071d0a090f1b080a0b0c03180703110a050105130303050f12010905070f05042106021903060e06030a08031501020a020d050a120908060a09030905 66
    0x10700d031611002d8100c0320b20f10405000c2181c048400c031a0800d001400310034094856240c2940e490f00000300801204038480422035020720038000c0d541c4050540c103119004150603030300c24107040481d442101c40340d044da410000c4034a407800f0503402030f04082c6081c0e4142189488690311440035448060b0600c28009031110000340c40d00c084980c0c80d041d01c1090307401035940e0842000100f80c1114540009003820341007100e0580310b002218100c4000403890a01d0700c130750840444064400150444a40d6400c00103084e005d541d2002c2c111294180c0c3e217000925a2a080820000c1c020040089120f600304002c01c1000601031025a0b401c00380c0c06404c44405410440181d141c500d42c1c01010358051642403c42040040000d00601045c4c40703400c41e400a0004c001055800081c0f5005560654002c40001580c490156200300c0301d841c004d25004550b980d58001051808000c0a207400d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 452697841 452877697 := by
  have h0 := BRFrame.cov_init 452697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 452697841 ≤ n) (h2 : n < 452877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
