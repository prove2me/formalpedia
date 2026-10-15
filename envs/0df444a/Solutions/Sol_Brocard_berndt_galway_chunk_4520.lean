-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:09.1811+00:00
-- url     : https://prove2.me/submissions/198c7906-db5c-4fd9-ad5c-16c004746f45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812769784 ≤ n < 812949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812771034 1250 812769784 812769829
    0x9030c0d180803031e0613110702010e06130b030a0b030307080415080c040e0a0906020a1e11060a02030c07050a08030a05010e04030c06091506060908100b090106030b 73
    0xa64000810714031000941d02509251200002291503000c012240603039510440d003901400466001c2c0ba50b1130001d811a41c00c04440ba0404101c96020300c1008000121a00050750301c03801070000500c01c03060860b119104500802012600100e414294411540001149070b02d03551961134100c0100280a10590035000000700c1104100020005100b034640340c0d00040801e240e0000c0031510b404040720f008500100c100010f0201940c0c40d01216400400a0008030f0604060b648172740a0b604440240c1d0089030071401c0380d041a203008141e15102e900f00b441c00001d03c21300d400410f69907d101410000035a075001004c03e1813102c0b040119070724540c1000448070700340f906280190003a4001c4a010f500c00380351000100d00014450506402640c02d239444180311065502c4072802010980421110a4a0751130325244504807401100000d085a45034580428642001a801d140d540100d09648900c0c0c400c1807941503407446107007415250503140c001040c0404c0e001281c80d1580100040d9045000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812772284 1250 812771034 812771053
    0x406020615040e0a060f0e0102040515071e06091203110406140403020a0e0a23060927010614030319050d1104140f01090501090603020f210402030d080402011709030c 73
    0x17901c0e0084c0400b101e00000c2040017480c8803402e10300b00c0c00b0300d00580741d02c0411000e6040340d505081c000f4000c154051307145014440541e50344070402a402d10f101b240c24a4888010000b40b00360303c10004809071031400c003070081003020408117085100e03a014400c02c2c007099a098920940c1c80300c09540141d60f010f0301c0d10450a071100d4500041788403c4070308646c2c09041c2082c00b0850000c00e51051f8840020f40c00860303168a4030030400c02202c000030b100e002c000c0c1c0300b0350303590310078903922030b00024018000f40000400a0400207000c5901e4007051400c2d000f94001c200b20828409440034403140c4000d540b92694440694220780d2001d40100c45103407050031b40101e004a0245c2c2d22400d440d4040d20100e501001a40c070340c4c0c0040d50360800f20711074940410110300003004060300030b070020070803001808100340c0fa00b807050782030340b6564200e128044405402c4404002c210304080110200d907000c90f05007840d00b4601640001d040a81d40741104541e00c9283c4041140301d1401c00c151407000020409a45d412003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812773534 1250 812772284 812772293
    0x2f0f220f060305061b18120d03020d0c090b0f0702030f0109061b020f0d030c090f03200303030f01120311190b010f0b07060207020f06040303050c0c060406020615040e0a 74
    0x351404181e03070901072000071a403c81c00300c0b410305c00c4900c42d08a4a80c280075250540090004202d2000d0390007600044c00300805030002d00c001e08019410703490040e00c68046400301c404444400c00e18400707001685c0c5050041e602c0b140c065490400303000f40c08aa0700c54031440032a003424020841002d06608000c0810200240d503003050401c15490b4800600310300c2e081c0701c226a521485c1c4c001208039000002001d92662098220300400d40080c142044060350b00d2010408140350780d401075800030320301c911040a0715a0041c0e210340d8220304400560540c10080600c0480070300610400d01110801c50100e01014010003030ac420002120050340c0b09049010b143c0303020481c031040308892924402e0000300d11080804480e0098608041036503040c110a561103200941c4540426a481881c2151000190341e8010050002e94826515541c40c4d441032264507241215080442d07110f03c41c18071042c0300f29170340000c580b54040d02d0500c10f10b600c030b489030020070010b0407550000800c9004040041c014070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812774784 1250 812773534 812773541
    0x180606030c3c0b07061b1409040c020c1206060a1202010f0c06090807080c0f0d0207050925050c0d0201020301030b0a0f0b06040b0918060d03050703090504092f0f220f 73
    0x8001c0702240846070300281d20440c1e01c041f1205c03803010f40c01814001100c031801c095000200c60340c2e0500407903402500c140e00088410120025141c03a503480301c0104440c505020f9400c02c01402c0c0102c00715031004c80c40c0e0002c5e10b00c000070140c03802040032043d0f0080511145800803210160001c0700790f5560001030400300c11940c00319400000d01d100f10000313900c210030000b0701704258480365405001d0310b90622040122a80020f81102910045034001c04c0303402c0310b40b00082014a4290f12403079590101c4078607550900c9080c100e0401036900c1400100041041d201ca8aa0b0082180b14002140c0000c400694020984002580d070010340208002c100b0780303c040000e040d4454201c038003a511880d20000341c09828411101240c0140f0500d5402d80024000c4002d4003c40d0312074185020b41940f510301050895104101c1900c07824455000002a071400c002d0003000803030312198080c002da001d980070030390004903140c02501800b444264940c02800e41e12000780d002d1510078051150f40700590001018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812776034 1250 812774784 812774801
    0xf090203070314090d0e061c06030308160815030a0c06020705040f06150e03030d050c031e07480b06120a03030c03180606030c3c0b0706 60
    0x441e01d48120321000c00f6030000103c0c418079120005051400880804540c04840d0381501c0350440000c3c4412806c1c500502942121031602c1100003407428550b06000340804009007064240b07100c49008210459440000164400f400080015014030030303401003446c0c0582040080e0a616100c5008140240e000c203030b050454a01f264240aaa06549603070300407600103104030602107005050051016000320b03480c44120300300800707403030503c103c451125081e41c500701d03400c5c2c1c2c14a000000704408950041c0000c00c21303042406100c030403803411410140c1502000030030050581c0c1c5080498001c2607005410005006500d1850156078820204d520300b103411280040711105100342c00540c580c10800707840c0e001002d01c80d0040008180399102074000b0f101c450784e000c0c105a15841c000c0c043c81015062294414485c1000042c6a803540c01c0421500d04507420580e90340728045804003031020b101d240010080003903018100c0a181118402c0f11036459070740184903012020692405001b101d6101022 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812777284 1250 812776034 812776037
    0x403060e070936020114040b0c010c0f0806090a021b0f1b0603070c060b0402030124020c03070605030c09091e011d0a0b040902092a161b0f09020307 65
    0x1485083d11000e185040c407203400c0444040c50405491031200c070000118246006051001440302000550405980a60420400c81c0f0000801c0c5074844001d02c00c017a041003092505001c4c490820704000c0c0100400760980c1c0c460b81041d40415500440e541c125261080d40c0d0038503580d444a0782400d152a03980401000c0d0550141103a041c9801807100010707104964010002443c5907520a016201314a8005094680030743d150b4508544ac1c80e10710055001c2d2240c101c003404502c841c0040e14060303411079810720f030454001d025108000c0e05d0002d403003010303034245041554980c1d032940704040082c0180c0c946c40341d0050301c440900840744001000703c1141660b100340c0e064142e0b2184031088207610480c0b142d404405510001945240e807a6005410050004001027620b402e02e40000c0d04a2f0300591740040c0304e90002ca0303e00041e074000045190008410b40d9480d0826040400d1921160300440f005440414200003194904045180e020050400400300ca1217203512050204000c1d0000c568110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812778534 1250 812777284 812777291
    0x7020c1c05030a0f030e19060f090b01050d0f0507170607030b01080103020d0203150705030a0b03060108030d180c09050106030f200a0215010308130b0a080a0903050403060e0709 78
    0x3605906400111444a4228004520b400c1d2249821500b40185219400030903030755030207200d0174407400d01080100200907811500041707214180b86086500d55240e003444145449515000101c7c40255241103c4040707a001a2100700c40c102011055180180100140100c8101040507001e500d8000a80020704040300c00a0b580c031802941100c800b8441140031400c01401007005150280e02c80314890b201900f512412500003003800f2114070150b40e1200801c0003c0104040501c1e240318075205030604400a02c1c0c59490850032031340701c3c81018048032070191a0b0b503d4152140804100d980c00950103424600d541c0d0b62000c00300020b001c2030044100103414482e201600c88a5400754216400401c404148000150980d25180350700823112082580103110038807d000400f01c0f520f6008500844215603031350303522a60b008040030340d500081900c280c00d1103611200c03540700d080250b0094000c1c400140c1c400007400d040d68540199800140001d0402d90f281083e820080703806002c65003104400e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812779784 1250 812778534 812778559
    0xa050711070614030a0f050709080c01020321041103030a080402090a0c20010f06080a05010507090b250b040503071208060d03050d02070602070f05160506040314011407020c 76
    0x4039190311441c8101000200c00b00c0c01c0e030700081c91003801103030001c5c1246000200030703d03541e4100040d5a0112044000f00d541e1040800c400c150606c0b400d0380112003407010714648541180e0130104260340706507441d0320700b5054001a040254a00708401d4500d00102120f0700d460616900a080c44022141240900f2010300454401070b05030144058234105500c0f114020032801a0218401c60000204620703903413a9400360020b11050700c00c44010b03101d0703003019251450722070603d1420f49030003030101000c111001b0301c02c10000741e003c1c040c5c482c110000c0c0080d40000005482c0c02d0200a40c1e007002a03d41481e41c0140410008000010090580700300b400402041901000f9074150708211a46034009100140000c0080e10070001400c1c22242410014205015501c4030303401c81e0000300c003c4613150030b0001e5050605c407041104404541070703004614061410f09001c2a541e015030f00c0001c0c00101d42c2607011198200a400000201c004e16161071128948184001d61f15055120f41d98000d0b105910407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812781034 1250 812779784 812779817
    0xd0b040606080705090103062301030608060f04030c060e0601060914030114070c0f05030c01200702030c0d020105090409080a0f0315030b090a080c15090c151e030a0507 74
    0x124421103030307542c507000301caa601c41005070303500d92207800c40504141e43c6074808122010305c1e05144c2c09000b0541030030500f40c01187e00240c00c5800e80d410540141e8000c80c200a6144019a5070700d40c096450b14048600354410f1425002404100c589034925009607800800c81c1a4006030510440c0c06611a0305806048039092508a03680812005610088600003d52a44c080c41c031903030301d031803080140da0a40b580e141c40b802e085821108103200c03c2d035164950082c190f1307009681c1001d1151110201032611b0788590001c2e58604005212601030040000d68006581c002d40039240100301c007510a1003900300500d00700f5400d0384152800b5000c00c0001c0da100741454400c0c4900c00310340401000160301c603030443e04c3c0d0700f0080c00010003204c0ca9100314440c0e040040c8005000e44042c02c3c1600040c5101040944807804010008085400c568000c400402d826a914680036083d200303001e207010740e103007142d4032480015045200300038000c850010a0006621031580014496201c1d81e0707449640c3c40c089001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812782284 1250 812781034 812781041
    0x1e06040303110901120e030d0204150807080118090c05060703091a0702090a09020d0215090a0b092d0a121104050609011a0712030c12200309100603080d0b04 69
    0x40b00f0380069009a42c2e245140711591050f26004400000c0b2410036100425000683e445a001020140c450b0901282c41d01d4100d0072540c0c0003001d0f81414061036041c924488141d07220a44031050031a16006c91f60309010311245413001602d006003e40e03039900d110781406420041c0502c124000d408068010b0415110a441507031441d59006201440786e8a130082d030040a0244a00c050341c2c0003454006038401030ba184101d00c0c619852003200380c0d031504044020800020b01d20f40c40584496020000a440d694800c449002500b0038610042c920200d0000c07a0601e00d00020103058000c048460003240412219917410121441003000341904d151910500094500030f403030b8260002c4009005100400c0136080b0800100c1600b44200d041c80d115403105502c010a4041c000080796640e031000c0d061345c1c9c0c0803900e0f80c0c0c07445441c0c0c424003803030f4070008940300c4111000000981c130340000700124500ca0024170244807800118541407007100d4a81c14910542d900030040c01c0185454180d032480030741441d02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812783534 1250 812782284 812782297
    0x3053009071514070203100c08010e01050105030114010503090c0a06030f051006090509091510060e220e1903030506030f011506081e070306141804030e031e0604030311 74
    0xd030740e0181005201c002c040c0540207164101d82c03600500b100b040d1f941c52030307101d0303210409529500c2000951400940100840d01030308807504006040006100740d139051940c01003038100038a0300c95680d98540e041e82d0b041c40600ca2610303030303c00d000341c170300050741d07603041e005415080c428000400150300c84403584031403142140319600110b45010b01c2000035103806403010390301c400c140003901c0c50022140300d02c10f0381d82c0d0119003840540d4184c41080c0030181d0701284048060380c051b110b11a02500d5110034000d0501240c06500c0401d840d0f00e02450703222820b20811000741403000c0200b650105038070300a00503103400c07150203001c0c1c45654841d058481d41400780290801007017074103003103003400c0001c1201e40310002021000b5024a20818240c9038054021503485101140d4000035114140a0b910000410a042c41842082001c40990201502043d00c40d08981c0c1403c2200c0e2800d807000c082414000365840c14100804001020a2410404503001d031085100344c0c0e00f0030810030382c1c4002e0100b5000d0354 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812784784 1250 812783534 812783537
    0xf0c1b0b0f041b0f150203070f02061303051f1107080403120c1b030605010506070c0e070c140d0f0c050d0c1502041221020a030530090715 61
    0x108007249020704610903458019010300c11080d4068400489065a8034a036071000003515981d560411403030600d00c01c6440c0b01d104500c05586010000d480b2010481034581001e8031031100022402c0b01c07505900022001142e214081e107108032400070740000c1c0610080034402081d8280f0000704401c0302c85000b00d6203044d51280f02c1ca81040c4c1161141c0c034030418280303400010311100c224140d010800300c2800c80e00c10700c5d140c000c92450b42d003145000000d5842c1a44000d000c3c05060100100158001044102741c43c030540150005940c2e40c20704440482c00d00c01e014000d50040d0100c6614088041032109a102c030b151900b809103213881030111030f1045001d4000c0c01c5904943d07100c40b90140b10f8050b1181140c000d07504142d030540c1501546c0100e82c042e901041141e041c405440c2c04211880000d008207042c8001402c0f11000784400180d20340d40341540007000c100000600402d0301030081c003415a08020704101140100d6404c07001d220b006e00030b03600ea00342446481c0c1c0014070119096903952661829 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812786034 1250 812784784 812784803
    0x30f060609041b0302090415060b0a0f03150f1e1a1602030f010f06080606060a1e030f050a240f120501140a0203061212040e06130f0c1b 60
    0x180d48820503545514080c070764880150f0400000940e03141062140218003489144611402c0c1c044103000700c2c0d171b030f5503c222405c00e010310080c0c1c811608409110756800140c01e0118210b0324044c40d45403d84180d0b08900c103020041c41c80800c1c250000c4400c072450341448803074140126150041c908a060300c1e10800a84030004000c0341400040d41c80d03100200c18409422244150014014203094950310042d040781d40e65940d1040090000412110341c00180a80c0c80f54a8101000002040d20300904c002c080590307903c401c10440d05200741d02400309482c0141c0c082000f801c02c40e845101078850351010054040b840b1001c00002c0c4000507140d001c07103c8950200c0711080c0f0308141c0d6000600907c5056510b95a601043c0091074000e0410718802d00580c0c9005a0302e28156041000c0c520801250400542c040c032801e42d08500e200088405852101e9107060703681c0d82c0c10300051101c0b40314480b00c500399801c215440020981d0b581141418460350b81381c00da0307002d0340301440d00c1c142294190050300d2000d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812787284 1250 812786034 812786041
    0xd0c050c0f0102093a111c12050318030a0503010603050705090f01080a0b03010203040b0915070f2003070606050a1a030a090507150203070b1006020604021516030e030f060609 77
    0xe420810400e40300c0c174000150b10301070b81c3d5654182c8014001e4065550a4014515a20900d880000c4e16000c00045a91000b49111500d035031151000344069a8140f0000001040a0800d861225000c0c042c45600300c075a01c0c08032120091142d0000e00c5004040b13070a2501180c1e0031070280003070b0780d5030030005070201c0009040000110b4040700041c2020000f01d40d6544580010340f0203000442c0720300c1c02001c00740a40c0c240800c1c01e51030050285100315041c10282c0c18015035a50007210040c46c242c062a044002030300481c0385000201e491402403000344030000d0101e042040f5030b0001c0c030498800f1a0703581c40f10390b80d5216142d0000001000168072580c01c00c001880c1c5c0d001d40d840200201d01460440d00400e407214441c140c400071110860f4090780c03020402d44204008140352070340c400000c003111240e241c54440c2c045d43d40e610107000240f01d0044031502c1000e00c2007a205079010101c149030104080300d541c2c100640740311014030105010703004a40c1072050520000070054052000506210b03803035035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812788534 1250 812787284 812787319
    0x2030a08042301030e100b0f060c070f05040c02031e0f0408100501061409011805060340140a0b070521040201021f060e070e0310060b0405060a02030d0c050c0f010209 73
    0x10841f64802c1e0300004003040c5905c26214080503001c445c030342d030005007901c03428505e10400d40340e05540130500c680d052001100d03640c0d41c04410b80d202e0103180111900108000100ca000c140120307501000c05d92404240001c0340640001c3d400d060340500c5004000c0d43c0d80311101152107100701d0708001d01c082001c0141a001e0752041c5621520728a00390303150329105448100041c0e450340207446410407440a1078000b01961800c817503040081c012001000c01500741e442ea8400c00200340e80020344152904074020000c0302c000d0080d401802c0e03100b4a150f025107040c150160a64100c0101070102d1000310101c0c040109a250819000310b40580051001c11441038604a10052461084072860b8031281d0000341c80c9001d85805018414580b90480c92241041c14140350083c3c02c20100352060401034104481c8112000b10303030030b4440540311351f941c441a1076416450751041c00900300f2034500d804400f01d1340c0b0398000f0160401d0481d21050b00c401401e10f0400358241d010701c072007136a17001400340d036a19480e9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812789784 1250 812788534 812788541
    0x30f04061b051b0a2c130f240c0815010c0b01140a090204030b2d0f0a0e070803121b0f07030c050a0b0a0507030903050f030402030a08042301030e10 65
    0x3c0c1d00070941210182c5401c060800e090b405440340300c000c0814188004640341d608081980107000365050b2003000e64603102c2c1e0f100707000d0f40c400c0030f4214803180c41c500d201e0010810b81224050346605046c01a180401e0303004105d544d085442003c0d0384030303110041a00790b1145104c0d04045810800011199082003440f1540c12008030625920400b1504e00003451111400504000c6004120300e0036a85441d840082d4400c0d140424141703014550020b480d0960790511035140c06c901e00071408681c90b43c95451f444018050041e4600044c402c14100140d003180c0080200ba1f5100d00d00400e50b465200c074200750324400d42a950001d034180e41400b400005520b03460250106500074074084101d0300c101c1c0ca41904001c640501a034110b0358040801040c401140511a00309515140400401c1d81a45000340180208220010380000c0000031406554023046115419074105400d16a199030720301002d046208807014450f507409480071005102c1d8064440c0c000c084603400050084482c182d403514009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812791034 1250 812789784 812789833
    0x1090b0109030b0109020408061008152d0a0c030e0a03231801021218130e030a080a0501061b0807031206180b0a03021c030908030f04061b05 62
    0x40204007000003010070002d064260007441a01d4006a41d01c0c1408007090030640d0080911190041150040080e8500043e01c400d4001001070b980000e0786038030040301841d01c0c817507a54a030246642096948451b511103055400741070501c20405c0010b607103143c20703000e41da20355440003080d41201c40d4510200c0d00a2414041d81c0b074442c01d414020000703d8000e00303141e40101c1004500500513115207007042d44c040000241e03504404c681b00c0e0412511400001c441440c004495000340c951450110503c43c258018041000c84031050300c0d241c04011100629224049a46400e1207060400001d0000d01030600c80030036500d180c0e0320305070002407619030040d650b2203008110304001d00d840c0d040500f19040d101e00d1010702200d10300000c400446541020607206e0a10f01d8900c110000c003010001651000c5400d407030381c11480c254250b4410241400c0c0c3e050f625991160b1194080021684409070517100200103560316a240c0e444410000141c000c80119648402007039540f00d6110400e0a000c01d00c0d05000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812792284 1250 812791034 812791037
    0x206150f0d0f020a12030f031104090f14012903010503060105011b051516030e03220e010e01030c1d0c0903010b032506020d0507020f1309050c01030e120301090b01 72
    0x542c0b501d42d07000c00c10107451648a01440c4900326543d504159002c00619600d803010714041c00649000a00c40318188210702c210310300b40313640c0d5026103440092074002c503110000d1a004d0f100c040d85e44640c000748060580258101d0030545c0c00300007400a6140342980c0c1615009001040e036030303003003000558182c08001740d401050900a410070001460402c0800c2c0100d032031114a0000e82004034500040c14000c0001009040c14100e0780034200c00000280c55040c003615842e00400f0760710320790029400c400c54100282c00c0c0c01050010425036000340c00141240c0c4203014800000c0d64486d4444d55450200c020105018500c10125000e480600042c1102010060000501c8480c0000203840d0000005904014410790005038104000c441c4403c0000d25141c00980020908841c0c02406449801c4000b842a04c3c4110000a00d48070560311602001a40108200700701c07607402d103642e459140307940190010703080c500703107820031840401d80c0c02003900101c80081c1542d082100300005001006500350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812793534 1250 812792284 812792303
    0x6060a0f09020904060b07050a0b0a090308041b1a0a120501030302150603010209130b0a06030c080a050c0d0c0203090a0510090504090812040f05151e100807150206150f0d 75
    0xb0958410b038001c010041c4928008c0009d80c085140460001a00405d000b802c3c928006045c00071a0301301206035800b550007030001900a0f549000405841d2841c0c2200c90f81f038035804901d021030307055034000f8841001145c03903070411401c047c01a06e0540d0800d01000f030058011b9528440403030603a50507103401101c014005400c0c18120000700785689008018170070403644802c0d03010080c1c1008400000908450314050044401d680c1019040c42400b408074003446075143e00044038942c8034006c1d0f5a0740f40743c40200340420301590000039560340005482d148151500440041c040c42c6c20304440c00061810341f50310f03ca061514082200070400c860064a003424100860045050820790381403241c0c0c412130030b030303e1401000d04080b441c03e505141e048800c0e41d468014002000068114034014a0f0b0112a4011070754554a01c0d509480c0f0b290710400040c42490400701d1800010101106000c1c4541d0864456656400402c2180c000d90b4000300d4104101003488029801d01460350407405001c1c49600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812794784 1250 812793534 812793539
    0x2a04050712020307020d09052e0c1e0308250c05011413050d0302030702100506010e1f020d0507020a0501180b0304080304030f0507121d04140906060a0f0902090406 72
    0x1c0e0141c0c1d01c100d0380400142c0020b140c5031201c6800610f140080c050503a6040c11002c08044480a80300c10304003000d801c103850441c40d03110148078a80203500d02d035020070310725442c50321700c0d004504001e0384c2e0300100c010940160000d2924004413080554000c40316000c9a5030002c6074109480c03035103041c01c060b20700c3c0d500c88181c1080e0480c451181400b40004048003950300300c42c0c0c2845401c00b808072059404050040040c0062994001416a01300f811410006026260310780144d85090000049070380005105040f0800c007841c040c44842000348503002e40314600001001141c1c541304100000754084d4604e0002d101c03551244849021280708516140400c64650401580f40c3e0401c5030226141071000081004065020540c1e801d0945182402c80c104440c9507141444104c03501c0c481010814a0700343d220303402e0740c2c4151507128010301400c2000000004085030701c0c2120126042c50140c0715510102c0c42c9030400c0a400d4088641c07030440007001038101000342001e9030100c20166402a200c0101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812796034 1250 812794784 812794817
    0xc0106030b01142103091e03060702060709050a0305150411060f0a120c270515040305070e07140a18080a060506011805012001051006022a040507 64
    0xc282c042c20314410120701c0c02c101c6008000c01340040c141007001c0c0f8070208030381c00d9420100200741c0701000801c4a40e46000344070300820080e1003100403650741d41343c810351050007945600842d81d1801000300b542c0388074540d0f840380c00380b00c03144049100061030381e8042c5a4440096440140003600300b4441c3d9080500307110b5034000181150451494a101094002042551242c014681c44900c0d014107030180030310300c880701014106c0101602c0006000d240c0102d0041c0424044c54800d015203001400700006c50300595402d20741d034005000490700d5100c2d1030313004210710941021072032040d0741170350700c5c01e500ca50114013150180c2c104540380818000c041c104068100c407071060200c0030306840c3c0010043d00401e82402c03000c1d201e016040e070b81845685180071903990440d1210200f680d200b070030324000380e55400e4140070000010400b411600d518090030302009022402040088900c0ca50846814418000308072030541e800814030300c1c645c81451210342e680c2c2401d40150343d004016040004444028060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812797284 1250 812796034 812796053
    0x806310e06040b1e07050403080702010309021302041e03120f020f0709020d051303090605070c0504150501021c05041a0712020d0f020c061213060c05031518010b0c010603 75
    0x70b003210080400c50403c10101c2c052a4440a0b0a10b50002a429800c0c20000540584200d02000e13101040001c2c6441c20b69000360000368003191301030076141096496501c40e0740250094001d0702c2201707004d14010f00040205117001c4064a40000c3c1ca440c1001c809642903031090200c0f02654154050303001201d0110400348030fa28014102101c2c0076170340303c001a182d0005c4030702c020300705081c00080e1480400032a5001201c0e1084e5115800c00998442c4a13045ca00301c40303000f5512280e0f00604007244c4154a0280c5040300c0300b103840a800301c884d481c0781c03040400b41684084446030f0000d0390510040210b00c4038081c2850400380b16041c0d041ca0302c0d0307554036902c040303450b612120405070340034001040100b0343c442c07603d41150189101800c0e2001700300f800900c50744100c0c3c00c81030074415003c0100780414006040301c95030b25406402040a14550704c409462034108071180342ca9040c250603540d00c242000c0020028202d080d03800c00001340e0030086146500c2c2c001803001c1300d03950758599011001507030204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812798534 1250 812797284 812797291
    0x15061d060a0501030e0f0d05031501030905060403030f0e0f030703020607210902040f090302150105060a1d060903030409050901051e04060911040c0c170a0f0f0e06030c09010806310e06 81
    0x141c03500e540f840c1086d00ac280c0340f40c00c1c2c001d41e81010300c1c0c20b6800d03000c82c0c804140544c0280d8146804215601d01c0070b02c00021b03181c1c1da01e06603001d0007004284080e414000004221651094003aa44580d41b83c0c6d1043e512691303514442601001280b1340d1000220945d070064014503c010070018000e01040491411035544010482c05640610481441000c8030711260f40104001c4402c60700e070024a4000034401c2202503480745941c0810505290a6590601034808001018040345d4603207668284000150505881c002c6041d444c280c0802c0d9550003c500141030141c01e0f2000341050388841d900d010003011004815030f203200868040589941e00c1d0301500044a007950394192066600f414542d0f807100700d86045a0342640c042009644241c2c0002c0c60f6071b040b00c4107042031040400b036000c090300c0400c1e180d141c3c19404040081006000f0800e0303005000b141c00b080e03840d41d00c6a42d41c00103000650350b01c81081c12440044010050710a100301c0b009070401014110041000000414024509101603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812799784 1250 812798534 812798537
    0x150308070303062102041407050f07300f0c030c110409060614031b0d020918011e0b0f03030904150504020301060507170403030f08090a15061d060a0501030e0f0d 71
    0x84c1010302507142078001c0e0200341b084880702d40b04e242009000030b440c6126000403070180500209a40c402e005000c101b60100441c00c00604070050410f010416140c0013000d01d82c404528800c00982c41240320741ea03c00801541511480460f05840d180c0f4103a020007c203520368041d0320350044000080d000c0c02008002e1482c4003500c0f0326030340301504060412005101d9a0204140215000c40a58030110b002d580e007601510b050305036446075000c1c0c0c03102095452100c0d80960900c1004228807030210a00240c00018000400a07421a4400c2085d0360003003001080d4158002d100340740030303460a94081030003c400102064201543c6001180590300f09038051404200d0128515040c04120010407982d42010400c4030b1401d4210380d00909a10b05d6600b4400401c03074038400007040e02d4010003104003940c0d04004200c0c5082428107120001d01903900510b010f90ba691001c4c2c00e402d0a080c140786015807001400010054101001100100700030f00b440e01d2244140b01d020000b86509000075605900103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812801034 1250 812799784 812799839
    0x140a080a15030c054f0e0c01081302010f05090a120c050a0b070506010b07151a10030e030d051b0a051201170c190f08061915030807030306 61
    0x3410104482900140b40c6290000d030001c5c1408070b50400800424284850082c180f40c071441656200c0301c0d00c00c290001d81740440d02c2d1103d14109803c0002c1e0060400500b60303038503038081c0e9680e0075102c0d80c89040b100c004d0200d40c072041c184445500030000380040c5034024003040c02083c1c2e035840100d0013950301c240640c0e29080115040c4003d06202084001401104540c580750a01035035500c0d035918070501c02e4030302c5040d011400c0002c00140580000c1851403480081c44044400890b04602c0c641440e030382c61081310300e4038990106034000d0080c43c40103898103000e181012112041100030388001003038407009400201c2d0b40800401c81a02429099217075039103450b19111070030000d101da024180c100c48480350881c3c203414510f102c001040007001a0646a103940b15084200e000000c0030240c10054085818480c085040c0c080001e44600ca50601210300d0035a6104038101401c44200c1d607000300d00e110b40c1e00000e1011035411401030950034440d280009800f030f55250551940c01c0c1d500311041c90000c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812802284 1250 812801034 812801039
    0x2101110f13060309020d172b0c0318030c0f05060c0c06060d080a0f0e061602130b0a030f031419020d0206090c15040905040b04050706140a080a15030c 66
    0x150715020080d0010781420828101c0c3e80e00000d50300d1482c07000013821400e0f03099080610b814001c0503a4105c05482c1003a41c0b5104203485800300942c0b034100d00c03001107440d10aa03201080d100c1e00510004100300301c4148200d1110fa10b0071100c0d10350702d450035601c4600c2804c11400188081041d90301c182e0310094001d4941d54540c01d80ca00704140608521721403d12459801c0109150300e08894001c481e0f414079a049016645055171580102c0e03442c15800140481c1c45d45500a20150000032940b088179070740511207080c01401c045980c120451a0080f406403802d00018408601000780b590203402c04180449801024040036440300445150b0058001c0c40c03401c1395078040000d081ca444c881d0000d016249000300b001580c1d185e101c400d851150486004480c000c00b2004111409042c000c98103200d5880e103801d04900311501540c08442911550304000740c0c00d44181280d40fa012950303040e0501c0d00e0840c240c212940080030b0402d02e9803540c2d80c00a140c20503c02401040118450b0410020036031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812803534 1250 812802284 812802307
    0x5030901020f0724020109020d08040513020c0706030b0607050f0106051f0f050d0f05040506180303010b12060f0405100906270903030e1506031002092101110f 70
    0x510115500c10150f00c9500c003880900448504e103c031002d04a82000c01c0b080f10f100040340034084092010303412005220101003403013285801401943d2055988140b003105488881003240f0400d800031801d03400c141c40c28080030344a5001a81040b4000f0302c9a41805410f448a90070003101e41d070884140d83d540d40c010045418480c9024540c90314182040203c90413410f03000e000010285200c108002c00041d030718661030400c0c1e1250450381071031101000140352618003242c2e1114255010621442554500c80904c8800000c0380d068403080d444840c04c1040310900d5100405014004961141c03904940b0189900c507031190305d200303241c1c86904015092805210400b00c8405400003c28107684030b006010000503031960090108080d00700050b14045810100c0003800220200740f0075004401c807010b1141d8040e00100c2c010340044041c1c90011074030090314000ca104404801d9000411078220050301410b21980c030b50b40101442c00442c01885181c0e80785510b07480014090b00e500408280ea4030640c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812804784 1250 812803534 812803543
    0xf2704051009151d031210050f1008060411370e120a05010e0a17130303111518010506030a11280b0a08090a0201051b01180503090102 59
    0x491800c20704108140c0749407140c2c902d43c4592032125400507190200b00c98001c24880c0f0b401040415041965290b090604101c07119000030f0f40c0e116920b203801500030506142c0002c811140c09001401e6000c43e01540400352040d1200418041d8019030395410500c3c07070102c0c0710081c104000040c02d60184044c0c0e00c01c10035011114405400048002a036480070560b8002c5442802c001c0119100344251101e481004d00c7c090708030380002d010354240300c2081018007001803004100c6210f24081b103070301c030810f800c002018004c02035584110011400108007113030042c104001484c15a8080c1c070b2102c400300c00d500c00c00b010295030000034424081840c41a1520a108040e00b210040b006046000541d0310b45040180428605170700c1074808080742d026406155032081c18101c1110240c0200503501c4441101d16007101410b94080303a200740010f8195100031a96000e800da05848090401038440031107492408a89071101081d0760b01d044144580d504000789102840c441c5000315174130351941000a050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812806034 1250 812804784 812804803
    0xf0a080d0f0902030606010507050307050a0c030209011d070516050f0303190b06030103022b0c050114090d110d2a1703120604110313050c06090f0f270405 68
    0x3a076181c111400d00580e404103800360800d02c00d1a04235101c01c06030070039604501c9903400080c03c0b48240210030f01009004442e0b03104030b900865088105a076070710240300d0f0b0300200d0103000340009850b40024507080c1c001e8010349584c1030f030141c501900c0c40c0f007a0741d1685000d0003d040c201d495880441002280b24004e404812030000515082c0b03c500e081c4004a81640410302009115071404038400091011510406034581c51a50710f012183d842400e020141a009000b0b80d8006907991200000071400b0134200ca00c2c480c000341085e000301c42c107031329a084221040014582c0c8211400301c000301213002c000c02c3c850f0711240d1901000b034444401d012602c0860130380d84a4000070121030a0f01c200d016002c0241c41d02040e210070840380c40c1c1d842c00002001080c204070130800955021042c4814500c071100030500c001d10403001c0703c0c040c103540c2c0301300402c0d4011801980c0e8042401000d5030011304041c042c0188030a00030b400b0b030240f6011006ca0b240040c0603a201a544829042c08210900c401042501c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812807284 1250 812806034 812806061
    0x190c180801020405151e0403030f08181c1e02011a0a05030a0809030c0d030818160302130e01020f0703020601060306051c15020a02070306060b09031e0f0a080d 70
    0x1400341381c00c002c552444009094220314400120f144288416500c8046039001d908408150b56a40c40c1d25000e098174881c50350005c0000c6140d000580b4044400340c1440a004507403001308140c58100782d40309061154010400d007040510032014000382d601c1441c403050741885400100d244080d10b05410040c4846e200014442c0c25200700c00c020603100881c00c3c6d00c0b0150400982ca41e51403544001c2440c040c902840d040e0820020804001416806582c050103030107070344415000d14042407001a5180444400b078029440003107010801403621a000b98150b08800c400444d0040640400a0880c5c00102c0240b00041d000690b03602010350500404c3c0c00340c43c8c9414100038a5040a0104114192400741035212900c030081c840107008100076120440781007104255903410f00c104009449980510041721101d04040380800d45100400039103140c060064000d0007070242c14002d00b0402d16050b440c944981c05002c110540c000c2041c4281d80c0003900401016039100a51414003080752130a119401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812808534 1250 812807284 812807287
    0x3080a02030717100b040b070b06030a210e09040807142b0201090f0809190509040201050703090f08010203010f150c080319090b09120708040e190c18080102 69
    0x2d2a4000000c00f4101001001d040c0190b500d40358032014200503900050007180010800080c1c1030410070040c030516116a0b45141c0c5a2240c5060550340e403c0084010132400101c0c0c846030b11034124481820011069183c40702480340c5020200340e10b014181c43c1964a54400541036090008900300c6110b0f802403e4010240d8948034407200803500550140d040717900d40c001c0e0360007102074401d405c00c1d00510741200d40d004c035506081c5002803d65104040c510300551070070494500301c011000341c4008132032001c1c0c5164001d40d11359004442540c0400c4007101403080c0b032140072580922188001025003a6000016078035410a440c00c412010941d1243d8041d060840000051603400000c08001541c411185078072501c41c480e0f01c0740c0e0b04112080300c0481c0751500d401602400105006c66000c1c40b180c2050303602002c0700c103410b80c090344502e103c080c0034214104001c01030329000c00c071010b40c809a076040d20340d00d02480945c0c06058a80100b10f0500254076200c042444903550340c5102c1c02403007a01c0085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812809784 1250 812808534 812808541
    0x41704031a0c0d0e070501090b09010206131a0f0f0a1b0c0311030a0302210103022b02040908030603070501023007060c02030703090603050615070f0c08010903080a0203 74
    0xc5007100d400010000340e9111103004a02030081c02070550311001d607000004d0159550451110350307039001511a490001e000e03400c001416181a40456552820603409402140c2d2a0240b120070100ba809003250030440a080e081ca51501218001340110460408001c3c01c0c1040e0b01150026140a424558000d152005000307042008111001468016040c4101144041c0c1019240c013601111251727114000042c4504561303074140d0003040444145d02458602c8503100040e0300c1d4082c2c003400b000b9040303038514241c518140b00501051030201040e40702007440241c0c5034045010381e92014005c844406012051002900e4107205d4070001e04400c1c80109141c2404248000c00800c40c1840500203101d20302445c120071520b00c04076502c15400c81000d00c0410a6407000941c2d80c1e001c41000e400003030803c54042685480707405000c0c0608001025650901300024a0600542c0a03030421229885c969071003030001000203c0707007402040200000181d10340c0c9400d028184900080c5200c030100c1c81003080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812811034 1250 812809784 812809793
    0x6071403100905060f04052e05010203070813080307080c0c010201140606090307081618050c1c090c0311011403040c0e04030908070b031008010c1d010309021804170403 74
    0x50808450400c8408585910740c0001700d41048105010715030860704140412106810a103415040340e2201d600810b04100c843c050741030042c4040c012180140c000f040403c020503a40700c041d110589140544201003662808860704d198041401111000b00c00310740200c20900c00c0c840c9000100007030000b48120000c07019114070144c0c0c010b0115104480120701003809850030021040a0110380085032501d01071030940e0300d41c05215104000000e034014031a00020400c5020b00c5018408840e0341c2420b0082d107d50399480e003141c0c0018400701a036034014200115914440040066018400c03105501122100060815803c00d0409034090b030f0420078000000d60340303c540300072141000c0000c59980c03581c1c03a00300d500c1c0b00d60381c0c4040c600380305500b404124003a440c4020b6010720b54040b41490040d0740d54000e00c0c2680c45d2515450045171030080c4625644440404011030103d0525001402181960020390040c0007034801c8a200e0741d401c8200000c1145050b4504a040c801107229030420b89598be8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812812284 1250 812811034 812811061
    0x60b030f1915090b090106021906020711060703090509100b0d05040201020304080303070305090105070807020a030807181202040f090f1511070501090c062f0304030b01030506071403 80
    0x4a81c0858801401e000d4403441a41c05202c0302ea580120000100f5680c02290000e05010a241c51080c1d02d450b00020301d0a0000510410040c030b0300848020064082c0c4418000750841c850030743c0c029613170911000752070395104010010346200b6200c00811a0401c0c00380009050001c050310440b4008a00a00550380d845095881c00d418a10000c141c0355114030040303095015507401503540e44404018400000d825410552040500b0002002640d03a0b5420490f2001c40175100880503800582900c8007084c45140c1743c0340d202030141400c00b10240b48110503502d00045070301001300300841e900350a0452a09004139040e4100b02c4a00313025080250f155a4500d03480101d000b400591030390540e180c082481e03004160140c51140d011500d035801410114042d01181d00115110808802e0118a450194801c03440003810021041004010a81540c00005903d2071001310307448180000000160414002c9020358401c0780581302c5414a00c0000c0c00c030380010030503404a0b690602c00c001d903900c0201c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812813534 1250 812812284 812812291
    0xf060b070807020402120c0403050d05030f0a090c050a15030e060c12090a06110d0c0c080406110705151324210c050417010902100c020a090c030c03060b030f 69
    0x12510766105000d10014000344900410124031b0b0b00541d0030031a040c0300c0c08020f07000302c80c000c8003600c84400030010100c840f48070494913503010307612072400b01d42071b0340d41c0d6402200f55610828120324455240e4000500504595010302800131a554243d50701503403500944113032120381402000a8101030002007058000c00301c1e405451490100010b06a0004120051601c0e801c800208401c0d6402c0b14003e0566005070706c105515420400940281e91103121341d40545500083c285080a00b000c4003100c1c00c4541c8601301c0094881c622000c40d05075540705402c3c69045503070f854603a0b1403144c600452850003503680704201040b07801c43c14190220b410110003c8041d0149004c10b01c0e800007100c1165242c2005419104151a2409028110341c00c50300034419140e1038841c1d19086000781189030300340c0305282c1d0300a4103c0111140c881c10b0b64040e1980610440c401803100701504d8407412180700301d0780c48201560001e52221030410325180c0500c54400541006c40400e861752406070104009210040d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812814784 1250 812813534 812813543
    0x724060e0f130c0f140f030c0a0e060a030206030a020a090f08031c090f050d08061e0d021c030216050406060f08040201090f060e0a080105160e0d12120f060b07 70
    0x11020281009030562510001d413124040c0312941a858000c02c00c24801202086800b030300b4800910507441c60300103070050704008000d08840e01c0307605101001d612480054846074101030000e40110041c1d9460014501c625003007a00140c4420b51482c00030a85aa00e601c29042d1802d5000e09005000011080768020340c2c0d4051120034190ba9048070310001c02140c0f001400c421000105d5100700702010500d504514130607a0740710010344905041140b102210354814880ca24035404400c880d0401304219400b05000410030f0f140f00e019080c25065402d43e641c0d0490041e0041560b0a0101c0442c805020203040150342c1040518102440940090b502802c00ea05121302d0b40005011a845000780402500b0413800c1c8040803030340d500d000352a980245a03401d1144d039111801080c00d100520500b403103400d14070710f001380e4041c54110694644550401441c0c00808942681000c80c42c2c000000d42100180c0d40c0c3c8100d0001105c107514111202510110943c40c20712404100420300001559412030b0407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812816034 1250 812814784 812814811
    0x809030f03070e31050c0714121603031404021c020d060c050c060610020c09040c0806180609070501021c0201152c0c07080904020724060e0f 62
    0x140d25054030781c8031002043d03a5000b80e01e00c035422010810310307640c109401410b0303a800f605018140c4102d4240d400c11106041200e0043c829000401c038601603003111018907506951000b903099104d80301540c401070954106485050a003000c040e0b051092180c2291a4000e0000b00c2c1496400607862050b103000340c441c05000c981d4000150b580d40305410500d680d01001c10002150300f41005821038110342a80c01d0a4064000001d00d00d0401100e00e100c0d100f46680a0238450903150f04100d000034010703009030340d0346901c1000404e40620420126020b403440c02d03134a10110840b440e14030f2500400520503500c3c0d41000c5410495a60001141c800301804041a001040040c1204034014107000a040c49103102c00c039000980400605840c00802000586a09050f00105010006c00400b51042e5035840c10402001000c90b408401800e14140c004002600d81051a01e078039180d1003c281201ea030b54044c040611504444500c6044001c0c0b12640e0f07490301c680740600d4a812310603001071490309040754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812817284 1250 812816034 812816041
    0x606120203060d2d030e1206040b160903051b1c0c06120b0a03110906010507030509090a0e1510150210020c0c03120a08010b04270b040f0f0c0809030f03 67
    0x11350000c20001c41e0240c201020b03418450030010680c2c120205414060b00800380d10030b1100d2008502d15100d03a41040703401c006621019010411420322703a0b2888204103c0c18000b00014409000c1c00501030b8a0610a010540c2c20204000c04410b0f04840d030030140d124018a0400240c07189101c404680e12802c2200c410a040b142d488080c100842065600510000000c010031810701c0c1011018002507510142c650381d0a0010340d1203120310301001d00807070424444650360f07140119102c0d43c052003440010031412082e40209142c00080340001c9ca404680301e0030000050b110f403c040c402026000440605150203c030060b4541c1003038501c002d0000d80005101c452000c0030424000d03442c2018049508280312134680d400546c102c00e5182000840e4100001801058142550280c54800760b10a6a034000048402c1d181004207081c1c2031a151100c0301910142c3e43c1344a03c240d590301c0c0501c08120f4801c000c3c0f66030210b9a48007080300c10300c05140140910300c4000816500301c01002c600c500c1e90790701c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812818534 1250 812817284 812817323
    0x20709062c06130e031c1806090302150108030904051612090f020a03030f0e040b100f020f03030703020a020709060605030f130203070b071e02062b0606030606120203060d 75
    0x200701d00000641004e840134403001000004100944540303c0440703414400003100400c0c1c8031a6161005032040410948020840320703409000118400e00480e151042128210405030000342d01c00c1d00f0980010076942c80c10700346806441e610030407001d94000411407039100035214020040e001030403940d490182d03a0800203442c14501090340c00030080c540d01603480c0785c0201421009100c0100103800d91254602509060182c1440d24030010100150a10300070022212070000d200c00900314440c0c0a91b00080d140140001c50241615a4006daa220700c41c10b0044d02d130018960060030b90728600301041001ca81c0c03203400d803500300c40f0f0030040b103045895108408000070944e41c80690300d4090400c000840c01c4144004001662007450092101089600000e100004144d80030350480750411440c6000c00b20990041c085086000b007a0078001c012007292400c0f1800d03a00900301080d66214244101a0030010986520214120a601c2d5150103c049040800100702c020009000044007242e42c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812819784 1250 812818534 812818549
    0xb0106030c091d04021305130602030a0216062309031e13091d010219030b03070f030c05012a1b0b0a03060e09030702030c2806020709062c06 62
    0x10480f100d8800f8000f00b00366071200c51140155002c82c4520140545080340300418021b0a2203041c04171404c440407003190f140d0401a40c00204800c1d032041d0700300880d00703003221030015581000d4024080040d400c0d840e00c000e40000702400003a803424414260804c500f0b410008200c81d40c400b4040a641600150043c2440c3c4a00400003403085c1490040800b0401c002c1d242d00101c6202003009445141300e1800301081d08038032600a40031515070110b20440c080038026040071500c414050200c0d0034441d91030840b41c440d600d5030b40044680d4801442c0400a5680c07004403d54080340482401a41592208010f46410f5544c00014201d10b0313000100301200f0070040c1102c0051a40000b16540c520881e2401401070401e03010f21000301840d0f0003c102080000170a80344203a40c060010828000381008104080f080c15021072900640c5070b0281d03283c5444e040c041e9008100c41d8004201d0942402c4420b001d480403504410b000d102c1f201f8082c0452581c1c160b42060a0000315440702c01500d540f808101903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 812821034 1250 812819784 812819789
    0x601170309100504030b0405060a150303080610300c030501061b0204020d240e010b0909090c0a081507030504031715220b0402070b042003060a0504050f06040b0106030c09 75
    0x603520b80c0c0c000c12023131100100308184908c01c1c02c0001c1000101c1c5240281e440c101c90300002c0c000070304440000d442405c004007134802928041c00d080c0005a00e09042c8401c0c2460fa001c4402c001c882c480d40180d0b40980d50040d042c2c005c01034241802103604001d00146840e42802801d070440300d2718007002084d5103541d411218441c00b200380c01d12406410700f400d82221034101d6007100708403040200001d142c1c80d200e100941a19a0038082501c0e1408403000c012592034090030241c070900a00e140c000c00d039551543c060006103e0344002d8004020013040d0b42e40c0300c460040c04c94080c035007440100b0000950141e2603070b00f10181681d0100c07468403600c0710403402d4062803000f02d0300700409e89400c0f0100d18480f0811204600030100c280446c04110303040c80264090040f00821841422000ca0f0001d4203080100c52140f00c0465103904c0302110000280c640b44003035841c402c225a8407020311007070050600c8005940c100b01401410756060a0750307031b254007800501c640340406648280403130140f840b58406200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 812822284 1250 812821034 812821043
    0x804060908070f020f03060708061021060518011208030403050c060103080d0e030906030a0e03131e14010f030f3305030a0f0615030f060b03060117030910050403 71
    0x325504180f6140d0820000071400f68812021242540054a40028428802d144554030000b07291110402d00c07008004000141e014021607482c1c40c03041c2c4200d00e9800b014480180030100c1c42038600b205005203c0007014900c500540900c00605c03101c0817081004101301d5000561a07a070759120300313040310f00380a07080404810f40650b100001c1407240000c050302240192070702c108401c040b00d44060350b507481400714003a0041d405100160707001c90075030b100c241c060808109a92500c140c158001c0408040c0d43c02c0702c2c032040c001c0081e8a80b0f4035044110240500452a5a10f101e22007100019004003401454042050b4503001744c0407100c04030790403201c0500d22001441d040c820b0000050301c0aa401744a1240881c11801c40005042c0380002ea5100042d03001140003054a42a43f281d8000e0400702d01a04207002041d200003002030202c0303501803043d80c090340e0b00007a00000d1204150034040706a010445604404910b03800c0400080121000c90760112901202d00c0500c43c0c1c29615030055a20282 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 812823534 1250 812822284 812822287
    0x3040201052b06061107080601150908160305070501031a040b0a05030708150f0601080c0703050906030412032f0d090206070305040609270b0406080d020f06060a080d0804060908 78
    0x190b41c151160026000e98415840314078032403c031000703c0d5a0b070f010a48608802c1d68801401001144900e10103030401e84424504a500c0c10f403680d00c180d02d0180302156402540034103580400078414240185009820b0920303050014240c05d911000c1c0919140400603c55030345c8564502c20340e669260300070014031019090301c0780b0a41d02d0407065280c86d00608006c1500c82070f900080e004003403526070f2910540d816180c80344203448641c41c2d010b8682020f9400c03418030000701b03c00e0f600d658a40c005544a144118280419001c580c24010151503a07086454034007000c0413161058131003100e4486a50300c0401481036258207600030007501408400718040c3d0031020020340f540501d07a200004005882c45601c0d44001d15a0795180d0381e640d0803800545420110742c540310000c06c00e401e074000d081020001800843e145440b0541a0304014030600e000c0c1c0540d000900e030003900c250a00809500210460746c2510151074a2540c41d1141590302030001041202c000140401c1401c0e800a18869000048107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 812824784 1250 812823534 812823607
    0x1c0902030d021b0607120c050a0209270c010e12070909060209030607080103031d0103150803190503100605030c040e190b121b030c04141501140304020105 68
    0x6034451a03000c8482d50601248901c079038044c20054111904039500c00008100c0700f000c04401c50310f404c06220122803c1c01a14a000c0169480382105401880100074021003907240140f40030903000d15207228505c0760484514030700541c1e085400b400d07032980c00303070380024000342c00c1481e032400d080d4140c0205083c50b180030000024040c00d503011304400c5105604890150320303a20425102d40e0030034440180000e00019001ca81f0081c0016183c03003405041c1808030b400540c840391211240741e80d030014400d41c4c0c004181d2440c00d40350418a42421146418641c0c03079401d04c4011180701c09420300421050207400400b1451114568088074020301c40c000018145040035015031541402600154440c60b080034818a0360f460a401c5004c0004100001018120007400704e984100c50100406a80b5000340d084200c6141c545002d1900015410243c005c43d40c90510800b2010107100c20700c103030401241115092900341c0c15400c5a4101e1340900701603031500103601100b04043c07600c05d1400740351051720700306 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 812826034 1250 812824784 812824787
    0xd06090509010606091415121602060109151502120a05040602072106111b0705120d090603050a0207062307030e031c090c0e01150903081c0902030d 65
    0x641c1c010400c0400920a107503641c0e4080b00c1403649030255002000c40380c002c83d80141b611a081c1e18020040186403400c0034104207101a8a00c0c0440c2d076605504600d4800f005540d43c18807480703014241caa401001203d4141c0703049440c024880c050040c10082c20003000084900030010280448980480150b83d51404200103040e40c2151060001501c0b6072000854040014a071480c043d0710741d0aa102c443c207400b601e8800252981d031500c4074803020104913920750b0b8010852540104200c00004059240c6810184020514410103010068010462031486607030b024085500301c40701440c0204180d200d1181d5070000b8490006c004014502d0000264001e035000040030301d41c0c0c60650b2203565107540b801019000e441c0711303040c4c40169170010440b4404200c0d03400ea2a801400a45a002030785059580d00c210242c0c1072500000103000104004010b183c00407009500c1a0302180ba19100c003a2455944034000c0c050b12851040c021004148186014280d0348102c100540080c1251031980603680e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 812827284 1250 812826034 812826041
    0xc04060806070c03050d1d0322050f060a091e17010501081903030605090a0507021902060f0c0a06020706061701020c0607030c1b0303050108011d030301050118080a11090711120309030d0609 83
    0xc00c8a1003401c00207005009c1c510709500c280071501e01500d0170700b41070080002c205c40c99111075049030900c000082c01055040034440c0700c1740204450442c006409007025408290005041599211a81844010701c0302650100c1c4c2000c12100003000b4108900c050315040d406410290484c507005407914041140300941a042030f8080c440c0c035001d07034421100030302d000421103c0304c040203500400d0810100581c1003002005140e10000d0700c0c00e80d1070080a0b0341d43e510999110300c03020340c2c1e590b4a0301c005005540140055089286140008611b40384140c0d98842d00e504004000c00141543c50902c20042d502450240624255000c404003102c20140f80c050b0041400b070046088640ca00f100d41b8494141802182d00003510700c00c021403c60386000d0044980301008021400c003800007400000d00c0140803c50340b12110701c2281034500400078070091240f80c0d0b4000742400e082106000b62602da03001d0104801c0502700c0e8010312150750355601541640303180708408900074114604100003a10400c190f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 812828534 1250 812827284 812827297
    0x20f040b0a08060a022709010e0a0609050408071704030c0e0a0b180106110d0207151416050c090f060d031e080126280b07020c04060806070c03050d1d03 67
    0x145a4601c1b044a02c5000700f43c0b0780051034030741c2003a00b60b401408540d07840a0300c2c0360300c490918030110b9010780f503116010036148203440c2118030181c003003030080c104056201c030510720316801444e1a051600d1074071411204503183c450041c04240c070402044043d6099006600c1c10034000c0c1840030400d92207a00e081280a003407088000144c030000c4d0051480b90080744a24040d2000d81c01841c80908014082c000b1242c44900c0105202d0709010051840e0828005030499005035200c81c0320902450a205080c1000c0d200d075148602c0c02c0344100f1504c0c401001d011a00007000342d6030028607800c01d280550710000001c0d10901c42c4002c2400c2141c4007544048428180e906042d0b9006086a403a0311123815a9021010070061350042404d20780c01000c00070715a080b5140034580a485043c0303a4132400c03034110080c1d0300c2000503080040d085001e41014001e0f50001d065203001880ca902e0f10000c02031101c003101134005c1c10024002884e51b4900320a4104401c1501c40c8a0854000c00c0b940c01105e03a00c0d030100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 812829784 1250 812828534 812828557
    0x40212060901050102030c0a061505030a0c03200d12020c120109021c1a040c1206020408010518030409090c05040f050103050d17062806051305030a020f040b0a08060a02 74
    0x71000070501c2d510104c11744000c816811300600b00611140e07902c1024002507000004081c407040d50029a03568100507886006000362152120030741941003c0c2c1d0061094018040b00c410044040103181e01e815058000e55601304c0781c01c061046802c80220308088000742d890354860205518003510450661101d01ca00e482191000022946240704c2c030544403c2c41000380070b0800450000c088440c11462199015101e803d960900a0715102030700002400003c2c00d40c1c8490703021406200340c15007403003595001030042d0002a00844d44c00c070717204da0300e12860050503003070b60322061204200315900c401c69001d8200188144501100001c807600240000d2005aa00344134101c00a040035005094000c16003c500100e099181d64405c00d00a0030f200854400c00c203070030320500b04070005603880e21000c09452569540ca43e101401c1d05410b5010340c0d0381d004640f10750000d5500500580e0341c0c207030564082c80d06590102d5030360143c40021341e001103940c0c4090390350300039107040014071200c0b603000780070302c5030388 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 812831034 1250 812829784 812829799
    0x1110021504030f170c090405131401200702150d060f0801051b0c0303070f0c020d03031506090e0105130e070b0d050c09090a05150a080708060a020c07032004021206 72
    0x31004d200345464815921007548803020400d404050074550041c03540100154041000000280d40da049003108107a000200d6942d1a034030840c210b400102021280301d246144c03103062a0b0142c0000350340d8009641500c61020340012040040700d4a41c0041006203016140070010660b0790568502800701121640f2226034540814040700c40c13500d00b03860000003020011030640d40c40380d02c2a00d001c1400280c1c001400070341c004210050366980180f6558a01c81e03a4041225000010881c001005d40d070010400c0c440428000d00005a900c103840341140c00444007240c3c10b152040c03444008003007015264115000701e4a0200365116860010400c21402c6102040165150340d100340d500c3c051244255446405000400c18507181074002e16080180160403c200c0300d10100003d0b0a02c0150384000b205801c98a000c221000e001d024555010250318820341c50151180d101030b8a40c0361500000b06070f1a000d40c01c1c2c2102e4a040d20051030000700c003500856444400101000070380004440f83d5114441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 812832284 1250 812831034 812831057
    0xd0c110a230105040f17010207140307020a050301051e040804080a0b01150c0803060d021201020a2c10052107081909030207050d080c0105151c1110021504030f 70
    0x114030101c500700c44421111a54142c1443d1904c0200c00940c3e41b038101540d001d01220b404030f002d5000ae440e14599010003940d86550307034070502c200403440d944030074400e0345400100403050030020501c048404030100d205034180c2e19882c2402c518001ca41000641d44140002d900810440d505054182e40c42d10220081040003888115180c00320380e100240300510500100340c6a041040510500510040101c81e045007440300d000d08a8003e5074031400000c03141c03c514900285c0704090100f81c0c408030b50b4803000507101580800c030300c0c05480e40070708104180001c000c1941c0c1c454500d81d5a4501114a000c5114280307854002c00c4114181d440300300700c22206104900c0801140f040001196042d005810070f54500001c20031f01d882e24580540342c004040140d2040c1d1182031040c03610035910030080f802241b6101084c48207268008442544406000f1200b00c08605403603840754650a080712031414a0410201c02c80c00c04043d59588640e846150091000b016003202c08517020041603944c401400d60f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 812833534 1250 812832284 812832287
    0x1101090b0a050f0a050d0906060f06080405030406051e0a0f090e2503090510060e011505090904060b0d050c0103052202040908070b04061e050403020d0c110a2301 71
    0x314107036040c40801d500f088803c0000440501800000010703040143c1001d840d954801c3c00c1e03607507a19080b14496629a000c1c882c0040500d0b141c0c0140071a13141484040c80c1c00c1d6509c950341e201d01d00460342409000306043d603e14843c800510400030031051100d89812149001400c0b10305841000c2001c10803280012a804915200d9a44101c1e01d0f114410010415142c1891110b00503402c3d9404154a541c90640030a00c1007040c1d6548907000c0000180e17003860045407a02c5018103800010702035050540c110b221070350080030348820780003c0f030f49060161502d24012004120f141c0351103401c0598040103d050040c0402d005850318400c0c0c03010b100c5691604030011488107020351913203003946c100901c01c000d410320f40d001c0c0f501d451041021750b10300101ca44a031021048108c80854441e502c0300203c0005400160203030255020580080c44581415a80a074580310141c2d5440300b001300999150702401485030404c01101c0c40901040340564488007410300f0b8000c40e154410b480c8034028108100d55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 812834784 1250 812833534 812833537
    0x1e050a0606050c060a091b06080603011109090a0c030b0d0f1a101202030f0f0a12020601030201050328020d0c030b27191802130c0516021203071101090b 67
    0x3c111410241a01c1c0c0d0f2800412001402d01c40c6d419101d01d9000007c1c90007010300b84400c4005043c940d11004101e2034076000b05802c0d101501c012459198091160790000d46a220029130046246030000c40c0fa03480c50007003100208021456994070604d81c0c007080052000e084501085180600081144c14280121829481c9800c1da811f12141c0d44030398080001d951041d0560503590710003416504111907001026103011014030004100fa0400c500000803c5500c58802e00f8043c1c0900103070481d5031568001a1250000801d540c00b0a00300d00c00641415000c400280454039520808640300c0c03120b200d0300c90041a605800c0c4010901d0041c40c050380f85404074588003106089443d490130102a00720210f05014042d200786c070540f010101848050300240a0040c4503009408001540030703040c010040aa4100d4050185007807901c1c0103c1522903004084034900701e040c3e003a01460311602d02c0401e05410b0382b402d0000c554040419503804011010804928200c0242d0304c00045076100e0707284c0c1d440c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 812836034 1250 812834784 812834797
    0x30a03090311040b0a170313090605011101060b0d0209030321060f04050408030601030b0a1535160c0c1e0e1e060a0e090f0f01020403020112050a1e050a060605 70
    0x1200c5c00d00070801160550807580c01c5500c440109403420120070f034500415441550300040300307164503420240300b9542c0c0202d07044e280b88445402844000e02d001c001c0300ca1031042003104c40d03001c2d0300081d2114171a01d080089920003d9000710000080150320031020a03c00140d0300303a0303c02c20020f034090f04036251078040c04d40111b030041d646a18644600c00150010005520040d1b0401c0d800100058064010306c040d4005100c42d0702c60980e14080084031076120021128030ba01e0155085940c000e0200070000742940c80400e1104180325510600026120310000c548002c2641c04000030200c0c54803000081c200d40541d40282d40d0362129140e8007a014042c004031600b48070b1464080c0d01000040d401000150045800350580044644810f40e804450404441401165012054030141c05070308000e91516003500d00c0c021800c0a003940e0000b440a880a2080300030309071142e0205142c0c1c035190740298880d591412045184200c4080307081d01400c0201e4980110514184001803441d001e04100ea00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 812837284 1250 812836034 812836039
    0x6041407090e06150103150821190c05011e15080705010210111e09092401050f16030f1b0f0f050f1e1c020327030a03090311040b 57
    0x3d25034680c07800c2d000300d1814070f00342410143c0714401ca250441c1040c545102610f000300181c89100d1a0140c21590240001014950b0a408005101500c07484000007412014540340082603400f0f40e0411034003500c2d4403452000d0324540240100301c4421250300800d50200d40ca64bc803031003140d507692100e0301c03200d05108280c0540c00000442030044d80a910101028480c400440d05149465003501c0c61925100042550031000003141501d900e03048124030740c00742091481f20800080c400c00d410b0011070911000341404000304070803452088030401c0d0340c0e0014006504141c007460505000f820f51503d039134040007049591032000e4081c041c0111041c1c8164000d603115418214a40d42e40300e80c481090410b688a00404000d444400406e101e80c80381101c2042ea040c04a0059440715801e0082804880b00510082038200c0780c0c054010040d608005100000282c1c029410b1403d4440040215003180c1d03d80200c418040405410003c03070400d0300e00801039200d10b6081d04092008170303100d01102c182d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 812838534 1250 812837284 812837293
    0x240921140c0303060603070306090c03050a0b040e030405060a09081203010e070e03060606070f0c140a0f05031e07030b0106050409060e24030a0b10030b060303161209050306041407090e 81
    0x1132040c14482c0c01190405258640000c003290b844907800100c1d0001c090301c60000b92961b0910444400502800680040840c4c1c00c01403910300402e65543c80c4124410a80200804140e1411080c001c0c00c616004002d090192101c0052005000b002e80c0d100740030311a9450036110100703d0325403260050f0203032020098000c1015072260020468150401c3c0d104443e04c1c0c051080a50019502d01410310091040e1003004900d00e2440c0c0800c00795080c070703070400340034140a0101081680e43c00525803c680c0c0316401c0d13044044001d07004140c10f240083c3c002178220190003000203841940a0001c6c000c8400c91070040000c982c0328454950070b8842560850f0300c88804104c01c200000c0161106858544020100c0344501410f40d00c2c180062411a41c0540131f5001440410500c1501c0841c00c0c2d1005044000d1498046d1201d0440308024050038082e1405c0c0c03000010040b510b00560241d0060310f00101221039600c1c040c580000104401003583c41c81d400340d0400052030050a01071460040300d403001030f1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 812839784 1250 812838534 812838541
    0x121808010236010516050d030f0b03010c08040807020d080c0c09100b120703061e1409071d04110711040c08091509010f0e0d0f0507240921140c0303 65
    0x111203517000508103000c041012003214000910400040318251030540703020910000b80401d5804480c0c480348058046e9041030142c00d410307640041017590181e40030001e0390701c0d140180007141c40d2005652000f0303c1401d00080c0c0382c480c1e5800003401c3c4804041158442020b81c1c0744144ca1a030405d0070f114000c03501c1403d100d480404101e00c020303d5401134151800080c3c441e41c510b0140600c4880d6500205401c120085c00e00072443c101d4000664080292581c1102e401e081c007008180030b1409140c2c03034901c3e80c038036108071103a5241d4100341f940e07000030344a150702d945403030801030340344c2c1011009c003031044c0e01d840d180d13050b00b81c0540070301c0d881850311601825284403247c3d50203100510003003480300f880d5070301e41c0314050400c16031081c110b0782401c120080100d5104500c000d00700301c49070762010701481001d000311000030319850540c2d051800500956800402d081c4020000f0b4103505000902c941c2c0c01d803040c4032107075409400080c200c00041c1d44190f00990001110103441c85090b4400302c0a03042000007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 812841034 1250 812839784 812839787
    0x2001060b0307050d200901090f21050a0b011403210306060a020703020307030c150804080a211a0a1e090506010215040602040509011e0312180801023601 67
    0x1c0e02d2040350b10791010031800c41c504621900310880c5104000c0071103021606c01c80c15644085203901500003034044044240c00d140c41c803c0c0b421411013800d05814100c55031401045070038450359406035480380d00e901c0c031540c6802da80300c420042c0d011524021310403102200c1ca024502040074a008603500c0c078851550700c444090003125404807600d00d080d40f14468000005840402003c00110700400015144a08007003044070700220035a0005d04000c4044180004104c2100c110390710b01c40b65041c0405401c02890f5200c1003100b50846000300d103450700200d0b46068040868181d4400000c803004e40546465901008403640308910710f00741d41ca107400e000d000c0b42410b0341c04640c0007072050040ba480c028001e0000041c0c400101c03000c07206103401290030859810a400818090510610351451000803d4441001d941103840701a0031419003e600302d008034080c00355085c0183c2c0411680c00c00e0764680420501035808641030b240c0d04090610f000101d0809041c1a20402804204404034118000d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 812842284 1250 812841034 812841037
    0xe0304091a0f1306030b011502010516050910030b03030d06140a18020f070816030f0801030b0f07122f0906030c0a12020417060c031009050a02040b0a2001060b030705 73
    0x64210555a04c0d103000c400718000108060085c150802d4031450701180d041d001782501c0020b00845030075105112081c903040d40000555028503420381c3c401001228954003100549251049076825000005040207690150780007141910038540740500381c0e00c2400140f20301071416202c2c0d050f250400803001d40740002503400905c034940c0b03c00a098140070441c2c56500702940301b0b9181c54400c0001c00c401508054025070300c000444030500300030007558507549900f281010003e00c40c0f5603844c17400300000c458a01a400e80c0010804031103007007109200c80031b60305019419684004000800d10044c00800c8080002280c041c218083e004d9800c50b00c43c48500e03c035580141c4140410302076035280c4801c0d9095240302500040040341000c1c101e14104403043c9041c0900a8010340450030200200841d0b4214001c0314401c45180c203000154990300d000c9500004c2c00f550300608042d000c0092016602da501c940868400090344812500300e100c4401c58a00f225841c0c4100002031005100040e04c9174019030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 812843534 1250 812842284 812842309
    0x1401064d030403060606080405060f0106050304020f031c03020d050603010905030909100518010501080a2f1308030c061e0604090201030b0a080601090b040204080a0b1305010e0304091a0f 82
    0xc04480c00d0940341c1d55000241c600c503401030b07000581440300304418860100000341e0007051108840e0029414903000518a10000304080d015450b0381ca002289910f0801c041d41c0049400c0414900c0e0400110000b0041e60010314000f2050381010040381151a040c868000d20380d50004c02145884c55090500202403c000e01c441d03151303113200300000b48948034110340c000c4003040f000309140c0d80c1d070600c0c0000d80031010240c4680e901e9480c10007001c60307280402c8910b40a006858030700c43c01c580e4943d103141d6411b2081040f94001150b03541000940c004001010f4810014202c3c181e900070741d00c0455001105200103c4486c6803100340000c00c034142010f40c8404c40c0381e40185800700f450000d160125064a03100e038016420756018500401056000c0c0c403d0140d008021181517150900e01920259100381440340a81301c02e5034800840c05404070040707441070f556403042c000e008565030a02d0303e54503504648502c56005042082d01e880c000301005801d000c050b4001e0020403840c08800911410010301e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 812844784 1250 812843534 812843687
    0x3200307081008010509010219080f010b1e070f050d050c07030312090210090501080c0c15060316030605060f060408102c0a02150909160201140106 65
    0x6400300303e605082c00703860303c0350340008000760b558801e8616101c2c999809035554001c000c82c02c000c1c401c42e00007d0325100d0440d040c02034000e4035516185074103c4041c02001c0f80700100350340000d01008010047c007241805030300490544182c600c03803d009503410700c2683c00c07919040c1c201c0013040c0b002a0089049061030941a2000107105c0e00c264081410018500e94901c04200301840820980d0f9000315129400215510800e083c82c01003080c65954844401c0a03030041400100000d540f034a0800c0242c080d0000c0d6081808400d90383e090000c020101500c14a000d4a0142900c040e1824800b0450b0101d650581c02800003010030410f45e0010241d0240d8030680c4088150112810303035090850031409103494018241c2d0707080030310410960700b102d80160091240d0500c011641595032100d050703030080269548514504403070608a005010b0801b100f007081d40200000b1070601d0780b002244414403c241c080c21600481030501d8810610007034194030301004000c1034205801c240c80c00742e000071100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 812846034 1250 812844784 812844811
    0x30c0f030905121614030d0e0f06040e04030201060902120f10080f010213150212070311120304050c0d200a091a0a060c030503040821160320030708 65
    0xb194001071074188504000341055004070500e0b0051880d0b403000c0310080c101c8109001086180e0740109455420b100310b408188010440041481e49801201e42a001c0303008008940d0f503611850302da0a0000140c40c180c0041d8605400844e5020207032007280c80800790349540f0640780da58010101c00e000b200405a0b02e00208545001400c1e210400a81415091810002d40c0399110440103148580b030541c840c1d600211000c64612440e034000c14a1003806c1110080da543d140b21505080c2c0780342e8580101201c20348108040c180003944807902441c0074611403410f80f0001209082000084c480c001f0b030140003c0d2070b4000740a091000703001405005440509059440e60b82c88802034112003407800404020305000d8904111132800030120300c043c002504095a00300c0403514010315902004200500070030002449034a150132a42c49000c50084100c0c401642d0301e0b00b02c0040d000c0c7c0000282c0b40000c40d0410408414240c42a000050352520480010b42035a9440e03000f12034115000d4095406140b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 812847284 1250 812846034 812846039
    0xc07081b0603061f0305090c0f060f0906040308040e0103110103092d02040905010905060c0f04051504150c060b060a05070816120503010501020607031103070c03031b090302100c030c0f0309 83
    0x804c0098000fa031666840020b040e18001c0c1c1c8090070810780e40c448a01c1104a041340c242c4035640e06054410b200c2030042e080b600c510064005c24050311a41d080a041c29002180c00034101500c650414180d0344296009498042802c0054003030b520020300041900901c006c2c4010092600081005c40891401803004080d00680124007198100c040564044c0d440307080003801e124080103845c1d005520318000514141100740118168026801034611032150800304e101c81405280c1600c0c050284188603042c0362106c280003030314000304040119001800c00003284040e14246080c0c500c40f04207501c42c240b900307280381d0b5110410342c40b05107844049800c2800c0007010400c40c251300c030404003080d10b40c180c1e0f13075041000185c50644000c205904050501052001000c0003000380c94000c0c1050400308112003080c40c00f500a401c51201450840081c0c0300700c0340c0000e07404180c1d5000c890095800c040c801480200c11111608a90009004240700c0c5109200003002c3c001141c071254045c1c50114042d64 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 812848534 1250 812847284 812847319
    0x902030304050a29070203030703320a1805030d0311120403021f050105010f081003080309100b03010209031e0708100207051b1f030f0608030c07081b060306 69
    0x10341d030010303e03181403021031340165105076103c1140c40d42030042c0e2090601580e517000035524813980340700504004840b40001651848a40540a034007500a0250400c5003040003019494010300d0210000400d148810201c010810703200205a90b409005480210b100301402e80180003091a882101e0f1000c1000040d1050031450f450f025a10a90280083e0344820704400f00110300c46007020300c0249400e004100c0c0f40e80180d0403580399000c50a191110740e0f61184665440c1009a2000d13009000001c100110fa00c00070608000c4005840f004101c01e410107400c0c50300301d016020030290164030034088041028410104501d28424000032944165110041181000400a0102c41594000c0b0f007400404c10284500005480601d4640701c018407038000040741040b06404209031002404038001e6494866000070b4000c6507020350501100340c0c2c84480990300d0b84800300c0020700303016040012511080206424094941c0004030454408520040002c0e030f90015105652080c030140001f060700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 812849784 1250 812848534 812848549
    0x93a020a02060f070218061311070609140708010603050309240c030d0501050904170315031207050f06071e0504270e0a03082403060a020315010e0f04090203030405 72
    0x61442403c1e036203405040c41440f412a10248a003c20340d141002000580d8880103807410725110216008a001d80c400c12901c0d00d14481c400024181c030341003584200178070140300c0f6080181c81626044403e110382c2d40010901f25541b074080100b10341c00800c143c607043d1412540b61708000c0d8414014100070140400d003070959601400520303110b03810124020f070301d0702d034144280703801010140c0c1c80829500d0580d4511401006141440110301008004280d070b0702d0058091164166000d030849034000d140d50040c901070703000500107d4051045503440c02100c5030108455010304919216481004100d29001f40b0f92003c030241d04003000b8007440005036030160707042c2d2100c404c100c04560305d03910094030300c3c441d0a031500c17001040034a52043c01000c0000c0d070700c02c0c000c5901032079503a80030381c20350076000d030704200100c1000300540d0501c561820300c04441c89950066000307003411402e420481c1603010055481d41c3c2240e00a542c030104000c400c10381400d060300030390202403000f400d4a292a0310349000500c40d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 812851034 1250 812849784 812849797
    0x9230604060e010f0e0306060409290108010b030c0109290f03070207080106121415070f170c03130515160306090204240203071208093a020a0206 64
    0x481d519011445560081c0e4004100c070b005162204101250f4804247d0f40c90000e08101d02030340e80c81c000ba030184010752007035180300180c400c4a5501070303c0000d51400444400c0c0145a1154a840350800c41454005003012000c00c0685448141d546804804001c01240e21401340d18000c52181c0450707000e0b141d0000303002901c0c182d41e015403681030182c0000e252040c0f1360003d4031a0380c034008041c42192920000b4201c0d4039170200605042001301540681818012441d031a0104080000d100005810482d10f100d0a00c0554804160700c400c88203001d01c0760810740d041d200c5c00780e0820105090448000140c0710850182c0304039004203505045072440040c046410351441d01400340100c5255600d03002c2e01c4018004004194101030a10621700b6030301144048031442e003074220048013403090003071064444a81d003110544444034510000604410011184640c090040ba441606c0b5030000c42c10000c1e80400a010980d640101100f27050504903903850110190721421403c14016640d50005020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 812852284 1250 812851034 812851037
    0x303082a07111c1505151e03010c0c03140403122006040c08100e0d0e01112407020d0c060213031b03170708070209040f0807111f0923060406 62
    0x400a202e13041503080c0307680355688501c03040c0c186010b01c42644034021402aa241d421184038004882e2125800d1952103914046500f40d400e1268800702d443d04603802c0e00349180680c079511010009040001040d21403400014a0103800034040c3c0d511501c14288100e00300d00c1c0740460303100061000c8220380381040803030b4100c03005c500c0f101041c00919028420138454680010091200200c02c803161074880360703441040000c201000b8480409a07104182c04440d10f03d101d401d40d02d209101d040b02920781d420808106914083d5400810403051000446440e107600d02d9840005068407030380c0c2d000203544209040035608034000b0703001c400318180c103824a06604c1c011b40c400c55102d2640c40c1201039201081200000039000740701940215026034206d400f113980c119110351940d40c6178900000c4075000000c0182001c800400d0090030000c00107a5052410011101c0060061003140300070041d103040301c1d03c1341c0010194241040f000300445445890b090120208443c201035540c042901e60304203501140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 812853534 1250 812852284 812852329
    0x140a170411120708061803190509180705121b2a06010303020a080706180503120603030a090b030a0b10201c050c010902030d05040303082a0711 63
    0x10030516090b00c4250b8480d002d1000751540c83e1811901d83c3d1a07010041000c0503c0a44002c140600d603003c0c01103070000c030480c0601c452240c02000c0d000303009030441c034420750140b092518646000107612a07128840e400c1d03941c030301e858251002a051204000035101c00d10071784421129005182810700944600c410b0000300e44d40503802044100701c82d0503c40c01e80c1a82d0b0300220f0051011a40c00310740300380c0f0540c11001003640c5d00e0003072901d4801815200341000c1c981008030b43c003c1c10468044001e11981e140c0640c0203186071542e00c1095101c0c45448414804903007462000c00001001801840c1c0c044100d00307000401c60310040c04074100440701c072014400100d041400482c02403004001c0c401c5110a00c4c000c10500c900f40220f1008109150410006d02c080030a034040307120425001001103907406002d803400c0b0300346444007400a800a02044001c40c1800780081c0260304103902c20300f01c600d03101d1000c0c0e22031030307000101481355400042e0a07100c5851a407480103044d20380d844014080000b1324010f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 812854784 1250 812853534 812853563
    0xc04020d09110d0302070501050a0203090a0b040501030c2d020c0405130b10050f0925021612260d0e030307030b01021603021905090a0e0706090303140a1704 69
    0x108211600b120426220300481e0083d48040ba600283c0c41d415140c007801c0103507456503440020380c51405441401a4401d034056000b0a00f200c046001d0000c544080c2c03001d0246a0310305106403440008003501c54041c1c820850501403422200d03011414400e06401a1241c00d0107042c041070a40348202c031905020b11034405c1540400081540c2d80354090b0241804480e80340c1010000f82c02110540c900c00e2080744070034081342c15506580c0c16242c3d880350650006c01d5801503100041e444800d04001600a06280394002804071480c2c19420045980020458040020345140d04041d003251101d024503e034041c40345601009042c0306190b54400300000860b2a464001401403d442c1b01c1003141741190002c41c45075100080031010003060741c2e412901141400025030b035943c3c04001c0c9900050b41f042c2d03140d092098a45159011403c40c99021041d02d802a4550409940c0c1003540d20000b00026080120342c00e00c10000d90180c00c0c10309251030922421028011850090042650f09603025420014403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 812856034 1250 812854784 812854793
    0x90803090714090106020a02061b0316020f0111071205010209060309070e0105010c1e020103110723030f030415020417010209030105060901050307090f140709060f0c11010507050c04020d09 83
    0x21201e40300d07022521141c00d5811708200035102d000c02c10000740611070100354108041c040070182d5046810080850380c840443e003428141c44000d114040c2d0003a14375400181c15944141d6601400782c00d508020072442e441c100c2a00e80101c2f080c0000c3e50316560910040c000b656a40c4001c5000d007089100a19241d0700348a000150f00340c042c1d02ca98184042030010b600010350141c20301c0d41026a0307007810022608240010b030013501c01241d10320400103001520004220300d040c0c501d0310140b84800560640c8800c0d40780d10391349114204421114620a0001170b000a6040d407901c030302c1c8501c454026050540d40d01141c15036840500395055a45d40226040799581000d1099035802441100d1039403035035250202194031520301d03010b20f04580d62540b19441c070142c0b0310382266490450340c2004042901e020040103154507828014140002c3c2a60f42540010b4440c0306401355103038003c40d0585501c2002e400655059020810840f658010440445001c1c0e88501c080d101d1b102d0505004a61560140380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 812857284 1250 812856034 812856059
    0xd180b0108010b011409220e160b07080a020f10050a1b2001090c0b030f07020a02061b0f151603020f12060a0b0d0c1d030c0907030908030907 62
    0x601c1d09a85800200421603030700451401040007083c041d259100c803001c02155441c4038a101c11901480039000d400d10408481e40418940c00702d80c5c01780d5411030030140c1d8490000f07119110703114000d50b003401006c002c200381c03030000c10701403c1c5401100c4c2c2c0031220300500c505005c001c15942c604140d56100f005071b445280d003e00c55040c00007450558141c13100d004094841c40641008088a8003404030300c0000f5a4254008450107820858460043e603036019014110b0f07208480c1485010220000310301e1140c0000360040b203003680180000e003811203d4201c40030400103510348000d640b00314841380328404c8080c80041c80842210106a00f50f11b07118010101c01010a00ca4804040c0704122501150381400705468480308000700ca8402c1b6120040001c41c5401d0941001c0145803000a204140c030440f0b03030094205944989030b07101d26000d441c160034804500800c1c2c05805400050514060380703000c03160315900100ca802c1c0000c4400c0c1c3e0391100495030b00308580210740b90f84021030600488043c281d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 812858534 1250 812857284 812857289
    0x303130e0403201e19260403150f0219020715020c0306040b0a24081501231203070c08070f030507090c20030a1101060503030414060d180b01 62
    0x10b0b41e814030018140509070399160b03135600745049901c40c0000301e042d1200030700c54602c024000c1a00000400e407203090002c160114903100c2a20659401ca404012000102c1a582243e40109003000c05182c40030704000030b44a0909018207040d820481001e405402e03d4a10b100c042d51a40140015070420a00e02c54500540b00b203a81954072901e110912a0307400254546c1c401d5105072a901c42c0d4640c0d84510000d8100202901003044d5001a10801150607015560440b0200e008441085d070000410340030f07240c0280070740318024001c0228404002d21480b4110b12818000e84014114049904950300b580c0040f8411610301d0303443c00041105080030850f0310042e198804030050210719607a81c2540d0780059200d50001c0584600c0c503000d1031801009400340301900e5015510000000c4144107031039510a003102004034801490b9450844030510071441a00d0300900114907040c2010b100310582140700d081294007900411200590050600820103010410710420301442d10a14105480d0b50058 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 812859784 1250 812858534 812858567
    0xf091a01030b220e060f092a01031a0a090b09090d0503011509030206040b1207020705030c1c05030a02070627050111031b030409060617010303030b0303130e0403 71
    0x207103036003503440401214540c80f00005611580c800702da60080580660301d022503203400748804020703050030710403c40d52050010701c01b51111004001d40543e0608040555007110700440d81c8a03001c0e95001c1d60000501c0018034140b5000310042800240c80300040740c000300045074850300381d20580c0c106894540d800400c1c5602600c60305014020003040342c0814271901003988d03510141d42c14000c5c0100c80700c90203544c018210b65911030311a05003811582c44003d0303420f00c0103140400242428030108404040c0c0318020054984000b03000108100807503051041079122020310790010006070308100811503401b0507000340c10351610700f00340a4250302d1035402080c49403c40d0082803024100c034208100c2030320001d0802034484590f4840c940c4c0346010380c8143c4000c10409030a000d100e5040003025104641c0900014826145c07140c800b02c50311002c00c46400700710f0400b0300c0107100083c06500510341061700903080303070700300941e0202d0900300d84007950000d07040501000510043c035601001d401c0c0d00c007011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 812861034 1250 812859784 812859791
    0x24150a030305340807020d1505041707020a06121d0c0307050a03080d02030a020f0304050105090709110306240f0405011b031b031101060311041b21060f091a0103 71
    0x5541107000c0140303d0f8070018882c1200003408011035480c14074800380c0c01e4101d418a005100324010748002071409a80603101200c460b000060001881d8044070101c50f806840c6211040c40c2800035680103004024a2511a440303012482501c00700540c800f084907a07290081c003482c0900401e00d81007420541044c1d00034111200d062000c10686411208800c0c210307140180e5035555010740308000c0c0210480d041010b2000800e00c400d00c801508810300903404042600c500c43e60340c2405400301e50906211151161007800020054600f1480f6034000000d04400500c0240ea924480c0500e9031000c0c42041c281d4601041c103002c256440520141156000d4242100410f07003514044d085441d03024010761400340140c4a441010720444420480182c2c41000703110550726890580403108005000f20f002e9843c104552031100c1d0301c400e500081c6070781a00c68140080a103a445070b6484070841a02800b0f54907003100165616000b41d400c4000c081a2000242c4610002d900c50303e031074038900c4000d042504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 812862284 1250 812861034 812861107
    0x70602071b0b0708130e010e07120b0d1b03080a050d0b0409020f280b09010314010608010b030c2506140c0d0e160b091224150a030305 59
    0x42c05001c44035400c0c0c001080940350101c4100c20313131032112a60408040744865000001354684036054840c001d13000e580759580035002e058501d00485a00c00e0340d60358006181101e102c0461064901201d00583c800c07140d1501c6503c94540d03c0071030340001c81900010b000010700f03241041ca5881a001c2408080f036080c041d07009130b42c001031038288903101d1300e5118a900c007a000310004210f0001001120440307000c014519035a55416455400c10880140402d00380a600c0c03e120101c0c94459050300c3c0143c480d401203900742504543c290300001d000500d10a8208003002e08860b1281c24440b034865104814080f00001d0302d000c0c415240056441180c40d242482482400d1284005942c43c100005030000340c4c40052130103841c80c00310641d0420316402e1002c10042458076140340101444d03001610f442d040e06424890b81d9030b44150f001881540440448003110315600ca40c80da071038222001f01c1200d0041a42c1c0e1002a2100d000d560084001c00d0740004c441c4448090764004560a005c840c0c143d02120b01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 812863534 1250 812862284 812862299
    0xd02060f0c0a0c12030501050a0603060b040b0309031204050a020a06030e0d03181b06110303160e0a030618050f0718090609050303040b091b06120714070602071b 71
    0x400507201200080000c60501c218038400c1d0b40048080307800640345080102240f0b0050000c0c24280030303260141424030000f00d44140a070080c4801c540c0c4e007248103450140b8010b1103151603000030f0328480241c082000740c0c01e60071200c114260702450041c4080d1240e003005104000d034010b40380d4005000d043c2003400c600c02031040862106c5501c407650901046040c80102c00e215149a4044d0040101c403192424a454440c0d204038101550181d03104c00204284d001c0c0500c0d620f000454041e00710f04820592801d40380d00c00c00342c580c0442409400c00c0280d030703140c0d5201c1054566440310655100c0d5040304400c2844000c10603c9402920b1202a21216080158408060340074a489885664540c0840070402ca2990301460550390444162030b201d05043c64a40600902a0b55460b186e101d51040d040d02c844100e08a00e0720820021b140342d24180b0300317405800600710b00816600501c00c00d1141090f810b204917000342a100c3c82948010381e80d9038146000e9060500026400c11240c0c000c403028010748 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 812864784 1250 812863534 812863561
    0x905060f250308160e03070803120703020720040b060a020a0201080a15031b0e07180f050d020d061d0c091b1c0209060f040503010f1505131112090d0206 67
    0x1150241c02c40320b5078031480e8029a030354245c1c81440341d05880740c030000203014880400588000003010341000d00340d48801c1000c030113a00580d00d000c0c003100740128a9441600c40b50072181c000410192001c501c9030000310008130103400c510054030250700040401006c56a1040c84107500c0100581300300321078903418403900315086480c0002071219070a075024a01d2103005a01e00d0307004001f4221001d4140c600214020010704840e04600c814419451011a9802e0a0f689940035a0300207006c00944240640801c030b456449482c0c01d0f50042c1d95200e00b200d00b560480c101382c0a02107010014980e03200d2041c1030004d401c1c8020302c44403945000d8041c25480205500440b00707000210340c41c000807885805001c0e0024805e4107a8294000c200041100707034445401c002c0e104896080b0000c0041048002e41c540603a900700c01d1081412100c200244050714001c003000c03030340c5801c034003002420040a01901082d85e0043c05010961081e110401003411030421100300c000c40325202810460400f01004d4015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 812866034 1250 812864784 812864791
    0x302041d0601210204090302010b0a08011e0c03150f17120708090102030c0a030903060e160612020d0f02030105030106080d0c0b180a060e011802010e0d02010905060f250308 76
    0x103d500300c481034001007010221141c4001d40040007000010300629001e402030015400e60740c0a000c0c000c034000b0f40c0003011b2003000210b01c00540301e80c0200d10707840d42500081404200001c2459950700c1c2d480f10403c050403440740500000744600300624103025201c05c1c003150080d5a1503255110052104000306550180c030700580e4021009600c074418030b00141c0c01c502511007141c0c030501c00c0300310010130305a0003400941140d0040208200124801a245458981801c000c220601441604101035480340080c050780c1c04505e6001410900381400341c2069950103c1103c019940201c01444646428410807004000210080001000900f00a40742c51056200603010710745400000d0b501d903035003507208103100c0b14280542c0c070303a543e07149001c100910400003003c031590302c0e26401c030340040b540500410719070790143c60f0305d42c450b04a0410003402d1311810404078100070b01c440c000142611840c01825042c41ea145c032107601d4414a820464086003060340750280705036030b0034032003011030f4000c00004d80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 812867284 1250 812866034 812866049
    0x30501091505091302030d2309011d151c15031218030c03120806221d07080a1403091e280609050a0503150702070801090305040302041d0601 62
    0x400395103c28078030241c4c1d42d00703200103501070140322502100346500030f10301d090240d090b030303200301c0495080e2100078024002c95036050b0200c2da005815141c09542c2d003520795034040d401071000d1186c03420400704000542205c0d903c2001c502201165156060103401002c05603802d0104d0b0280c139500d15100c003100103480700740100038040c40110800141259400c0c45014680003160031104554901d0140c1c5039008040d100c2000034a08404101a4039100e1039038501c139000041207107800118649404000c004084c8903000d11030002141580206080c80f0040080c50380e00080d01e043e2140341003280c02903150306075020036130304204074180c41a070360681075190100c000a094000b2010304008900c2e1040084441042d01200c0950740700440c104032010420354040c1d940b41418107945a0620401203902d002e1280e164000ca980c0c00002140041215130081c1c0f10f104540c0c0c115621b401c00c0e400c5551a2901340c0001c1d070000f034148190b003054001c2400a00c1400c43c2c0750601217280044a464040c18010f449 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 812868534 1250 812867284 812867299
    0x7030905011805040212040311010c0e0411070b0717070306080318131401090b040209030c190e0406050411010c0c0302091e09062203021b0d0b04060c030501091505 72
    0xa82d9442180c4000183c50040c1c4110368404c20103405001c1200211401c84c0002e0000060541054060190300345000e101e4982280e540c641d4000c0001902d45480e138000341080601c198400b040c4412440c5009144544500e4a621700002c0c0524421800801510a0509220017082a004000100c0e01200358143c18503c000041c038000814182c60034403102e9000781007080d08241ca141034001c40d4101d51680904100381e48081c0c00344001e0b030055600e1194580c201c06941f401030304106100c0190391052005161240d0389a41c520400010103072029a000c503920b404210070064000981e980709902401d0070410242240d83c0c0500c4110b032404000e008482c00e0001c152200c41e030041d5914010223044e010300d21071400b6215280c1ea000101c52042c0030019028010106100030369080301e00d5501136026240700e410300340c0d40d80c0c101079060f034506400c1103200e503605000c2001d21803d81c2c0213500c9600086003c00d60a10028103458060b04268116481d1420102c1140040c05e00c4c4406c80382e064171200f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 812869784 1250 812868534 812868557
    0x2070e0a060306050f01210c120f050601030f0203060609090d0f1b050114060105030609010b0f073f0c0312060f120c0f0e0a05061f0e150703090501 65
    0x1010301419807008007014180411712101401020520f07050340c0300c12119211410303481c40c01400c10411840050134003082240203111484207803500c0c2040034001c1c060201d403200c1a170740d05c6103030070400d034801c0c0c40c189071039120102141b40c140460354224008179031901c040d04095040c1511391a45941c4072003407181c00078001440d81d00070001802c05000b0741d185017102070860708ac45030180c04204000348112110900180720b42d802001602e000b00005000030721140e003403c0310705400e54407000d51007400d044103012490014000c051910b44241020300d031407803500c14010894496640c2c5800458110390081002c1d00c020740c3c4106800035403501860081035840e05030728020700130151a00811101d4114040100b0200c989000180c1028400c0b000e558502d9558110b09808103001d0003030200c810350762000719003181c0702ca07084240c1108004001035800f841031440781c200580d03002d94002c0411011100c010b03281c82d094004a9207034426005c201d182c01c400d0b542c0140070020a01580c1d0601c504803500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 812871034 1250 812869784 812869801
    0xb150a091517100e01020a02030304140a05010507031a01080c180409230d0503070207050108040614040c210f0b040311030301030812061206010902090d0614090111040602070e 77
    0x20100180700070050003070151040002d40762942c02e182070005001e820446201c9043c4014401c03281100c1a43d80950f0441c0c80301e0780c4081c0c007142101240c0d61240700320040a004a2400c1c820307070740907001139100002c0820700302e45489a010640320401e0705001d190406c000f1030701e0b641c0c0c2c215581d40450460140b410441080000e004040d05480035204916200d94000d24041061345842000d07620021102c10b0142200708a419100440360200180c100d22002c200c0c44d40110440c07a0403e00c205004500a04401c000801039001290191980a84040d0402c00e038903950402c6543e8054122052440300ca440d15201c50b0001c01d84402004000c5c000e002509140c40761920810994801d400d5980e0395130341e800c14250369000075509a20f080c203002c0108205180c0840040400c1400001801044e80b901c5400802074000c10402a0440c41c01c0e4160b80008802d07100341e660740c81c509a5a540350b030400c0344202e070860781a20024040604104020b100d05500010000101c1e04c04101c10b41d40341c0d560441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 812872284 1250 812871034 812871071
    0x309050d050c0f0d0b040503070303050f0106050d1d0102160308010506040f050904081b010507022e05090c150d0c140708092716030c050a0810030c0b070b150a09 71
    0x14040c0c070b05175041050004000000c0014a01c2e24080d68040c002e6446c0c4c8800381d00b02070001e12503c4003040d020071503120000940c0e044501d0740704038601c00707407000c0144030285402daa12141c00281011a445c00351802c15402018041c0504000d80300b9a0805041c9504454140381501450b8850850340000904105c800011129841407846d0818548010180c84601801b41525450b016001c0c600014504440c0c4446004065070306004550410070f82c9030003400240405003841e0600c1c05078401220341d03030b1942c1070100300c080801a41180d640d10030810300c00c206d40320040e05c00c04100b1704114960703941d1084d46c15222403540100d5426510280c07140001e401650154402c851a234130090080407000c801d46680d4030818000740070603405200c00311704030700321440c51b084000481c0c018401d242a4501c03d00b182940300ea4041c8040750f8131501c07900c07005c3d40310405070b02c80d40409200041190811425a0030305801907160400680812140b40c00250a0103050003000401c0e42d480c009001c00001410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 812873534 1250 812872284 812872309
    0x60f05090303091504080705090c1603170c0c010e0118080d0b04050a09050d0e0306070f020c060309062e090b010513180e0304050d260a09030309050d050c0f 69
    0xc1105a4140c0400d64110301078105d48580d40d89405050320000340c41c107007070710b9140c412011045001d151108403940802c80100400084c1d0070413411101490300d00742680c41e103502603528000419110000601032a00351100e103010009141d06005421342c184180400044080c4d510000207522003041001d240020b01850600c0780e4414140700901c10301043c9a441103c980b8020415120030351004c1d40117403000e403031038015140c140d031101000900551040f180d14400c1c0050340305441c54051500001401d540040e654840e443e0031820501000210b1210340c11550701082a01c0c003203171000c14907900c200301002e209540030aa11007500c500315038440e40843d102c84411140000011341c0700e95404440d561000c104841c05460305409411540b40001078800301c2e00d00900c400303280481e41e40c2e1034450043c4118150310b40d190b00c9112131001ca44410141c0200c00c0c0035903400300f021b4610300300240a48403a51049016090407103100c00401c50100303807006a071400352a100d817100c0e0090701061110030280c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 812874784 1250 812873534 812873539
    0x3210204030c030605150f401d07150306150305090706110a0213020705060411151c051f03110405060f1c020604031707020907030204060f0509030309 66
    0x402100308031620550b44292401210308008603541d05003903090171040000c0c1d00ba44101d00d840d22000d240307000700c1060f0304412510f0314002d454142040918401c00c10003809558034080c150909201d10340e038440c4c0c82c1c2441009100c2001e0042d403c4c0b005032100142e0040300b00581d0040d40340d200e02402904048028445460b5682c2408840c640040007850103464400b03180c050f542c400a400c03485680c06484030340c02c68002e0016210103a08110f6a40c0648032002c10140c0c081c00080c001c604103000240c4594040c0840520b0301d014174041044002e060380401c05204014411030294540040c02d81c03403400000c01d400141501c2e1403080300d00985581d01e6642046102e1080030081103115420b8801c9075405440a01c00341e19041d040240501c00b001003a84c0014011512213411603c061044d45018006000540303081d071240c50320700f10110840010010020b0003e030300402c50414081055011031145011803d1504006001b0150a6400c8440e020400003044014403030754240100c0c0c8485400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 812876034 1250 812874784 812874787
    0x15060a080a14070f092705090a0f0b15040216020118031b05010306300c1d06090f040b0c0c011407020c030d020c0109061103120405010506130605030604032102 70
    0x3c00c004009490401c220800210300c284006050441e001865400c108111010410700c604001241c004040c0102600717424450400c500000c545182090b0211900a40e280c05c001d14144c9841030703200010421050060307104002003d100d00c50f10070502030031135091030003001034000e07a49095801c050070380018203011003505070310180120203400401100c40c03c1c1c80911285598290303410804803144108816580320802518810404444001502e0f2181c10131018a907218940303801c10040e0350282da142c200c6110180442890502c0005901070a65440344140d46015540d50b14020005031645440420105600c4d903024000e410210140c683d04903200c0390b906c0c20080080d80c450f03080c41c2c4a0f00a02441180b244418404540400c0707900041e100d044a06140c11806c0751250300203c0304500500080c0454200e2000c0703c0707000c41c051400340d000030909007003482c00c000071202141c03045000741b481d1105c104960b0301c0108031f4582c0a501030808000000e080c10540d00d1030883d131042203050610 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 812877284 1250 812876034 812876041
    0xb1c0f0f0e010b100203030c0a050a140c03031902130501030b0d050609010b010905150a05030c07050a060c030f06060c08030a0b0a0608070f211a04150e15060a080a14 73
    0x1d0550001c002c035030080312281d81d10803035113005a0300c900c02510341081545080240d80c0d6414000c8000b054040460304d04100c1400204441c20500d803c114000304640d0070000c1841400c419090b000703100f00c030b403a41d021031805802c4c0c0a444440e201622a00e0305051701d95110f0b010f036035200e801041c0159040020380c0e00364130b80301e4001c40c000c00882030a01c0c04901c0c0c0080101c1c060030540241070300c12682c20510b5281030140320055441c0e13007004201c00501e510070032840700058018841c411400344914000300f0f45006c41c18020341511100384181c244036240c01d9041040da94800700e10b114035030b00941c0443c2d0b02d40320321204030007030002c0b41045500030800303540004130654009a01071040f50503070740b540b44603d8a00c5c001c4a4400310b882c04160302d8a41c01811114044a650205030424210f0130f0b0708410b16044008101995500900450141168042042090100c242ca82d074000e89420f42c0320907400301c2d84005103c60180103151001c00c5031203000510302000d41da100c4082c150748e845c6100c0f039030315 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 812878534 1250 812877284 812877311
    0x201020c190b040308130b0a0545030f01111803070b0a051305011125090c05030f3d03060608012301030f170c0303190b01030b010207060c110607050f06010b1c0f0f 72
    0x144418056019105101d03048cc600d007810301c140035102491280040c1342000440c81144030716175507549980c3c14002c856001403c0422003005007140001d03521807603104c3c90a05003801100c841540410306018400da031000b1000d1000c2120042160a9500460400d240603402801034100741c1007641c005241c40408054980c2120286201e2010840d862280750b807003014138400b000300b90f4003540070722403514a42d5195146650700741144107a400890070328030742d581d01c5100c16200554400703d0315175550301c4000b85500700060303801e40390302030044c845605500d1942c1b4041c1a84102c000680040391200081381c4c04c0c401c2ca4203ca11680e0b9610480f502d0b070905502544042c0391686010740042d01e4454461310650082c011407400200503005480034038503040c402e80d41550003541c119210b9000705a00340882c1c1d100d030041e2592a014030010f101208809181614084060300150380c00241071004581210202e0780e44001c0d08210a00132421520002c42c900c09001c4200c120740710316040c00000c50300d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 812879784 1250 812878534 812878657
    0xa080301051c020a1a0c010609051f081011071208010f0806070915110717060906090c01050a0c061a0f06070201020c190b040308130b0a05 61
    0xd07101102c1d25003208007160009121544011002504840440b60401030500002041302105640580451814020002007421103421750482070f103241c0c0c1c40040c007450a0442c0c0101281c01c65591030303164042e040c110901da9910080b00780840482d211046040021006029101c0d2641d11840024200d001c03c40701030540d8a0900584140902d2500005184a40020010700400e16074844d5800242029000c20514107486010024011003007a50190941d04003d21f40040c502d4000710b28030f00c0c1a0400007828100041c0210300154090300130301010341c1e070205204210740c00c02d091095480306231020070389100d80e0414000c0c103118640285070031410b105007504003205108890000c0315007625010400c050156031000380c01039007d101017034214144840002c0049480782d0b0303031280c80c40d95840032214030351154104403000b25000c01c00c1a0380b1203000c260200540344150000c0d0620b442010010081e01900041144056100d017840d100001001030030300c1400c0c8942c2200e0351070b40c000e2002548a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 812881034 1250 812879784 812879789
    0x1b040503071d0c040b0703030b0f1c020405060307060206010b2803050a0b06131403030d090f0c0819020402180405100303020c0307050a170f0a0b011d0610110f0a080301 74
    0x1070b0b0003800c005007078105600c0880381a00e011000003030500c0c0050318120014503000d50f1043c3c01000c00b4440081d103907101080000c056804210200b401c161134410322098400c05400c05000b036000c80340c10b2003595008910103041d900e1148560340c4482600d00003a69051450303a11000302043c11014001d003a6240d00041d118100001060010360f4103401071003440c0c4200001904010300d031100c244070b081e50070040195030100c000e0841e4102000355400030300b190407801085440c00300f001380241c10006070210007002043e03603001800740d007a80ca21205101c9065828000d02c12640001e91003c4070710305914140f00200003a000704114603180160410001c16404284c0c00b510070402224014903002410302d0580704040c000314220341c504803001c4041e0b401e070b81c0e12040e5801100da07031307a290500c10004c4004030350045001038840d5141500d51000a0318200360306100e04980d80402c42c190b103c0003900240620306103420344900c10581a841d080010417283c000460003860000f03030500606c413024506 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 812882284 1250 812881034 812881079
    0x303050106081f09020904020708041401080a0603020d061121100902131509030b071e2309030c060c03070b01270c1209050601170f03031b04050307 65
    0x525483d0802c040025030301e44865409407000c150014005100c4a0300500f602071409000903040c690541e855a810303802540100540380e014015840c919070b44002019004840c0c00c50401060707003181c011076160800740c0c202034072040e210950000000c0c111000c039071124600030140b42c03141100c42c0000720001c2c019558aa040c2c2c0442c8004039040031542300b00d541202d05000251555840c2400078025044400003540500408200c00404111000c0e021072003000d10355551041c0440150040251100f40c1c000a410880034403004400311440c0c1a611300314500351400d9688a04041300041d140900b00180542c10500100301002d0444000001d02102e511482200b1401ea880d00000341292444940e0340032140c07103011b1200d142a81d29841a02c4a08452500b807004040400080c0e0a032040031500310703015030126004101c0c880114020748100c40380900600032101c03480c0400f695a000c0902401418280f1014440320380902c40225030003401c016080e41c3c040713a961070380c0500c00f4088000482 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 812883534 1250 812882284 812882297
    0x305030a0c05011d1903020129100822080f0c01020702040509061306020a140406020c090901020f07060e010b120a030e1f05090a050a080c011701080c0121090303050106 74
    0x16420144c0d01090700c5120000707001071403100c40d070703406000e00b241043d2021350555589140e01d440d034400c0c442e05c6500380ca1852204204100080080c464183c02150240c4100300c60340040c04080d004070080741c10181201203001c510302500b414941e081d071117a00c51102c0b41030f50020366105444410740141200c1e5008490400c07083d66280c05540e00e40404590310f03881518100103540010f07105901400c5000700070714000c818903150105501550b44103410450140e031280102803464500f1b014100c2d80329003090001d50500d07003201c4410782180142a002440c4a84400d070201041e4800d50042411000041c141564604840c0b0301c039850b2a0b0040083c3c0025000b4021000759042c2035220918003000541c0c440d25120107002c049031f090300409a082d0344480b9031000002d6940c2c65010320703400340c040e42c1c0140500408000000d4100c14070040041344291010300100140c11000c250a0b110032000e0a00c0060700108000b500d00340b2580074016000c15281072401010b140d815032016050b01c00300e44918 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 812884784 1250 812883534 812883551
    0x6010f0603150e0c0f0d050c120703060605031302120106030f021002010c0f030b04090210050a0e0427031b06090212190212070b0408030c01110c0d0f05040305030a0c0501 75
    0x3496101c03d024403000a400e00001c1403104003800000c00981480103d228142204101c4202c1a0742040d200e14a00c0100424244d02c000000c0345025000465810100042d0b49000780144c00c03804002c0c000c601440100d014001991106118600b035803904200070030000d0b40300e1030070005810032188160701911405486281303040c014450b0107403e11b15500d401c0b078000b10800c01180505401c1004580180d1a0300314000103880d034424030340c040022034907615103621441d00010601d01800c0a410b2080341024200e401c15001c454072000500206d074107101030400c903030800740d072500f103c1c0221113200028040c0d11007d0020313a62040402d24400c4070a51180c0c40320714001d66991100644010070200c0303190b03101c4014541950700c45400c82d0810309885496a660880011503000f076803105015410001d01d450180d40300380319002044044008140c00e2003200c40815541f0407880c1e400385e00740481202d041000d030b4080c4041d034004540c0441242d81d6130032074400c001d0414269036412159982000c442 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 812886034 1250 812884784 812884811
    0x10b0d0e06090a0803130f0b180c010e04020c030c060a02040302090f010e1305070510050711100503010308130f080f1e120d0e0a0f120804110f1206010f0603 69
    0x7880c0503107069001482a90100e440300f2901e58805088041028260044030b40014000700400f400e4901400c0d994209140501005910081d190503412450b0403040f0989156038200c001000e0540302a60016195544564001d185104a041c0c00703c45204d20001c016890849400620a5a200303503800b050580b40d003c0c100640300b10a010701c1c010441010001010364a0b02d4071154001070003035046810f82c80c0e950001c5050303040a25040320002d400003441c00240941c001c5400402e80050b41c000600c1c2c0c0030b40000401d0381c00103020060045200140c40c2c0d009900210700800038000780080580903070741c0c44141d5555a82005c5110380207000f0000c0d0b202154a1400c100808030240d00f014003a40400c10705800300981c0264245840c4540d24905c1e10125201000240091740c0714144907104c4000354188081034022024050081015031300401c00003400791180e521100000740d81c12500320004400041c1600f090355690f400342c0c070032800000b03a6a12407480c95001c565a5880800c02c0c42500f103c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 812887284 1250 812886034 812886043
    0x180708030f030103080a02010b1c061a01052a031605010b010c020604050103020703092607140109091d10020319180318120c0302130e070b0c070806010b0d0e 69
    0x9001034107000404c0490311203401042111140d100000b108890000051518040708064a84c038032001d15525080007014418900141e5165204a1110b0703941800201284102e01c0d0014070200d40d07071640d41c0340100017030031801c268020394141c90700d50850310903501030542440c5c0300381e0f40c96082482c1d8034025405020070035409500034200526150074403005601030362000004404011818500146c03001005c141080b481c00e590450801ea5002c40104614010203500145990318015a0109041e1780049418048074402100411a01085030b120150030000841d200401d00483c15010f4419020368011407040a450300348041c60720034004020100d075042c0015540074411141c0001c0405c0c01200c0d48040380c41c000d1458070403030b5200c54a848241010000845481c0c2c4000c0040c8118904401d0340920001c103100b0402c4031450082240340d807010188908003081c240050110038821041c440d22019080000445d8500e503592001a01a42e0142c20050503103440c107154645e1070174011a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 812888534 1250 812887284 812887297
    0x30305101202090408030709051201021e0a050d1a1f080c0412060b030f0a0c0603110f1b011d0a15060b12090a1205030a0515061b011418070803 63
    0x8000f58003c0ea0f40b0782d900e61166001512410500c0f110443c0011140d0b00c0400c0c07151604401c41c00035898034141d201d0071460610704028900d100030706000702e54031103500c503003522017034a00f540e808580d03111802414801000f08003101600031450322010200e40903207101c10b0041518030b030b41d650820359078100e41049501844c09040c94011440340d8480100319503070014062201c00070280c0e4021401106041e1404111803001c40b01c081f41250100182c0307406100d148501c060b0b4007072840c604144d003110282d0728440c903083d2440b0040142c0c0b40d403020181c00d40c001d900c01944d084c2400460038083c1051a500c005000701162500c22014030740c000c6045d14000d00c411142c011540a0400480f03802d9a4400507000304004050300c12001040049044182a89035010168030395136540d05108510205035800142020300e4082c1d4180028540d0711402e0880340035042452205180819040c5080d001d03099080c5040d183c2d0140c00c003449811104248002e070440f003003400719500380e69a40d02503505c1e4011070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 812889784 1250 812888534 812888539
    0x216080c06070525050c0a03030f0305090102030c0f1815040f0b0c061b0f0304060b1f020c0402091207061125171f020a1214010605070f060603030305101202 69
    0x2407540d2511000a280c180d207240e0711400569012003450030201f0045150743c1d100364001040807034440c114580500c0707280c0d000392317610f0f001394511714280101da85544101403602034508400034480c4c401c442c6000c4c1c141c106c20300041c440d036002d159030407864406030098000d03440c0742c10410800050400e101800c41c1d036400c5009011f02060340c3c80031001881011a601010780c8402c081007461902c0300380c040114032443c814500025000d9250040c85808441d8065440030710442402d81d80d0150380009651014607000c88000d40e0b04d01d000000314407001c2200d40c0c040b10070b2144140101d0200d03000100b80445015000480b8054070880c400351422071244801c500c100002d03d40e0900182508a5035034981c0c0483c001111030700c50701c21101d05002d850300e221000860b81e02007410700046a000140864050b00340106218410100c00204a00340c03043c41850b040c002d00103690402c10050084000e0100c4c1c0060301082450342e2404c01070f000c2d003c12610440000070041010030300c206c00c00c4c00d2800b1075402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 812891034 1250 812889784 812889817
    0x1008100203011202090705040b0c010c030e0607090306050603071814131101050711061b25053109020906181501200a060e070b07060f0216080c060705 66
    0x60303409021042c0409441b0004001e8204004100f404d600c10007441e240c0410340c0005000301c2c2101e0f008080701c1c0740700308849060704000d040c005001d134803082e01810399810220000f003d031520400a4a4903040d940212008601c038285449202c45e541c1c001018600d942805040c0c0c2d54450314030184110001000610008120109402039441074010780303409032040301c99026108481e0300290550304070b1000d21400000388500c0700000d8009103c0d0b0f820341c640d00b445401c40d03013030004001c60445401c5e0007150f020303a08603903032380360380c3c0803081284c003502c26030a000c0e144108016401e0342e029001c4050243d000d40303411000704005040400303200501c507040b101c103810305484e0110a1050a0483c00d48241001484d51300013450928505a2504401482c40181320030205413030204c0a0300e1030944d079218983c000203002c12110800d40c013141c000f60f5103c5800202ca503802c9008100a0154001020801c11000640000c04c90100000c025001c080c40c100c900750f99808800700e40380d20580e600c0c0000640c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 812892284 1250 812891034 812891069
    0xf07050a0f08060a050d051b041503110f060309060114031606050711030f0a020405090106051c05030f19120e030d09050304090c0c0308011e0303140c0105100810020301 74
    0xc545866508544004c001c803040a940314002019a00c054100fa0344c0e5402140010500034900703d544011807100385d406002100d80c20b5060040d8010030301c400361403000781282c04091592403200309010b0034401001c10b500d90030085002e50f511102402444400a82294241035030710300021050303114640702c40c04082d19400d081088841d41c2001c1800c454103241c404840c03170a0b03602070000080348035840c0014180e252040c0104400c1e200042c11818559140080501c15622681c02d0035140051105508410b807440b45801440e41c4126a5400c0300400086201d09c0b007100d000fa021340410100e0b17500e000194441c141ca150132030794064428015688100018141d0708100c3d0800c0740c21038021000d83c1c2c1040c5d45c0780c1c00003082d11903c4a20308009070806481c51b08241e00010014050080801012103154403a000f411800d11240409000d01242e4001c0841d034942e21011500c3c100c988074024405402d03c00c060070a03207009809030082034004e01c40f0200d0b00074502c0c806d40c1d0482d00124000c00b031040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 812893534 1250 812892284 812892287
    0x803160303110d06170106170a021002030c06240117070e0a0306020301030b0402090c120c0f21010f08150118020408060103080304060605040209060d0c0e100203030f07050a0f 77
    0x21190034010064070300388101207000d482c82c0705083c014248070b0300303001c174407500b04214608407400b2390400d0102035502c409070400560b00040c20300c18a94103442c50041554000c0c4160300d5401107195041140c815503042006200800e00f1101080b00d12419800d2022100c05c015507440d190850503026003448000020201e500c280c10b181c6100401900c2c4210b01034503503e484c0140ea1003600305881c4a0000300a101c114200484100d5111801c0c00741682451a9009071400b900c1025040b40071101002c500603110890041c101c42c00580c021105264500700b15250a01ca10024466178803400340102000800b4000270a0700c2c2021100400000042c0e03003080802185140c0554003002c45e02e500740404a60213004105c1c95010354012103402c2c0c0c60b0700c1e06281a000b07031402900041e00030b80c01404030a02584505c0281c504c1c0009003000803941081140c5c08484104034140580d5221041c01d02e240c45083d008802503000f500c542c0c0098406989000084d9540d00c0741c420140006040440d200c2c2c0880e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 812894784 1250 812893534 812893541
    0xe0108041110020609060c070b040807031403010909150b0a0303080432210a080603210705010b030708151801060312020105070e09060d1113090b010803160303 70
    0x281c494500000480400ea010695039154106a003015030b03c0030040c400c020000300710080d0700141b2840c0d501d251010f00e542d00126001e01030030003000d00401240007000c05000b81c044410902d41e80c40704031b80b650707910584c60300501503805040c0c0c0c0c600e206249440000c0e0b824020403117902005000c0859a40ca1a40c0482d00c0810007482900d5030682010050301a1101c41d400d044202c6c015540c0802d2050800e81ea02e040800c422405405161000d40a50044440c00d0690ba1800310a0401544503038410006c00e09100104400140054584405c1464140100c0180861a00500080019800140c1030603529a400e001d10260f6501c0408103444a000d1044d82c0303035100384480300c190313510f400c020030040c29150349800480c0d40d69205e44d0f01e0324445038244a500ea00c82d13460b2400290002ca140045400000045c0540340620348bc083c002003030000980ac0d5040849024021a20041070541c2100080442034400c8136001c450000004050704c0020036660300c3e0040e613400c40e50703d0615540a82c001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 812896034 1250 812894784 812894791
    0xa0f030b0c0702190e130b0114150301031209080102040608010e13140607091415090d1a0601111c110a08040e04061d03090f01030e0f010f110f0403062c0706080c09010e0108 76
    0x11003c802b10020a900940554021442070700306210700056110003420341051030b0071814490388184070422000d503020594904460403601401000d44600401c8003c50400e00740c0680030300075901c4000107000e00001c03014030400540e5601c0d414103450b1882150004c085024040d03000064a4400000408a400804c022a8001d0105640e07d141d6600d401c904c841e070007054241c0401d44410001c144d6006036030203411a443c4406070200703043c1c882210300442c0801d05d10104200049152081800f410000c0903c00e50704490341c40c1d2210355465220080b01c40c00c80d011102642040032016820f1042031590040c03031200005142002000703024440b0003040d00700384038105500e03400e841125440521048603580311410000c50740140030001c1e102620609207400c0f0324004100546061000103100703481c103a981c01980031510a0440140e02402003405e0b0400d050300005802c202042540010081c003110400d441c1c643c03035a40c4458080c0454051803407d1408207010f49101c641d00e42c42040e0542c5e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 812897284 1250 812896034 812896039
    0x1602060912060103050307020f040219120e190c06080103081818090a060b01020f120708120106051909030b0109050a0905010203240a0f030b0c0702190e130b0114 71
    0x807003885512510301c2d005007a8400d0318540c00004003502981041003050244840588056151000710845298013035007070201d43c01000040402040c080c020740e0000808480707190201c412160381061030003041008039004881100d502c0c00e0014145002d0780d900da0403250410309240c207080e01c0d00300d40d0442000b01c5041ca41c1c02051818841d00f502c83c83c0c002a8001c0c0c84000007031543c0603030b0746400c00417125130402084c155032089644601d8440d000a0450f8500c1041180c2c64907002146403810903801074100a0505010820010509540c0302c0090301400c020810943c19685003500d09a54440440c007000d40301507040801441920016008243c0182003194001140016903d401e82283c00903a403c10103840d8a00c80404950a1103200c10381e031640071a039040c1c540c0c0c0b0b4161080362a030b07400d20000304608080303c0054000701d10502687c1407290003914124001e1400c000d102d02c03210341800f401024882c843c000c101d0f280c100c0fa084141d80355105640d940350780d003810342c140e0050240703582055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 812898534 1250 812897284 812897299
    0xf060c0f060f0c20030d091e0807050d080105030a021c0b0709050f0402030609042307030c090e061902030a061e0302010e060705030403030f09080102070507051516020609 75
    0x100010107038401c01d804406070310000245896141002030032400783c4101c0a5824401003028000c40c0004001c0b10300c500090f0f000011840c100c3e28000348008031244542080d0309220001b801405410b00042154074422400d8580850788001c00703070343c044030038000d158140e0704c01086000103060904c0841040302c86220203c0c00d034181581d031401038484c00c0b904240080e03815523041045043c90100340c82000c004840a5046140c41d0380400d403d5000100090202d20407200c20f0b444c001d030f040c405510041da6080c103a41d20151241802c1d00c0d1014a0310412000914100c880900c200c40820407078061300408268900c0405681100c0000e500094103c003c0682d80b408001804982c5500030b9005105140f02040703d40e183d0b00026041141c48060b890189408201c642c0c00540e0100072942500d42c50b003050710581c0140b440484039805c46801c8107001e0342c80016a08140200004d14004540c41200c20481658685888118a02840c450580c5440409007141c0040c0342c07800140c40302e0035000e81400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812899784 1250 812898534 812898563
    0x70801031b152705030a0602030a020408070603020a1701140d030e0a0603090204050a14190902100201020310050f150c1015081006050f06071a1e09070f060c 69
    0x405009402c0d610b11004180c0342c02c006600c40e55001501d4602c1c420b00c80000102903d4040425140d00349044002d0840b40e00200285502e42198142c03000703080160120b44000d6281c030f10280080d070000303810101042c004824035019545003c4410b040e56041a42c116040c03000b8010310807924a09001141842419900342c9190307207800c0d0b02c1c103004011603540841d4405c900d0050004540c0b001e040307016014108440302e124000c00d4000650804c2042c011020741060100c0d040004284d0000e009601c203007114a41e00030316605402941c0124030510b511607105a80f48100032022058145c002d40118000700d00c0485406008003400c0c0c903900c44000e65004040d1034a01608844154a4805c05122811418040703034008028850041114810420074a400c1400189800004d00e066034417444001604d48100005c040c20340141c0d2540380c82e00c00c07160801182401c5446d08001c1400c050480d503500207001002c000503c039007160800c2d805642c0c034030704101c2c04641c59656081c05642c1d424150702d99 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812901034 1250 812899784 812899799
    0x14160608061201110a1d01020d0c050307061401240e060702010c020307080d320a0203120a0204050102150c0306010e06041e060e0301021c0b041107061a09070801031b 73
    0x111504040c0c03501c613080d035801c4280300140030103030000103c3d000e4400e0105495102d98001032648480813890401c6000110381d0701c1c0052640c860320350001d240ca401c04000052070100c041100341a90b501c0b801401035507080c441603c0aa008510300318000540e18200710300a42030a42c0103106081c011315140d03d201000d0b80109103045031950140c4202d5018240b0041565844003801d0541c501844e01340079054200d4044a1100c104154000031514000070189465402081181d251460043c00480c281c5040b510081c0250054400c06016005160500c8a48045444568442e00402c0301c42410742c1c0300d56004541900e2895100c50300400300300808100207810a000e158a07501103030503803d81c0c1c1d00344a0020b280312000306d4400d000c0d82c01031041c000c26080250504203000c09100c000a011881440014041e00100104040c0107000181030350903c110b0380c001040540441c401d241004100307205100c00d0b000200c55540004003140b0040c40010414000500b2000c10040742070519901e8280703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812902284 1250 812901034 812901041
    0x2b0c170603011d2811040c090801050709060912030815030a0215041a191d041e2a03020a021609050414120a0e191214160608061201 58
    0x890503001e80c0b20001c50840c80203e660301d0540324124000d10140380d1610f130386036030040700c03005540b61080e40c4a81487c7d401d148900d241c2030081403203500a205505084902401403105402030f640018203440021a0981e01070b28050403003a4035945068081d0340c1c01801d22001e2481c0129a0340c5400ba000c2c2c8640584e0795500300c460290a04860199503a2a0199074400550f05202c200d40c8442c0601082c0c1603488141c1c4002d4a0065509080c2140341e9004204000c1d40d5100c1000380d8003a2a280441252500d84199610094000f0070200841801465090021105616207488081840301d4807190248245c0103041001d034140112807500302c0d072022031603542103117400c0190015511800c210600181078400170b481e68004000c0e0019140004d5192501e118003184c0c001440004840d0750300a445404d80e5a07546428660361901c02901c07a50648000d40004905549070281c041c082403a036100403407a484600302c00290b01c240e40c1d16080341500c1c9000d00600c8181e11100602250b00078107400e01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812903534 1250 812902284 812902331
    0x60406051c23010501020118080309011b05041a04030503040303050a0c0206120a0c030515120c090a201c1a03010905100c050310050120032b0c17060301 67
    0x40ca4181035075070342903942e100320505911070350441e810028000c86401c0015030420b1666003000032699280c0c0ca00810b42d0150100350b03481c5294171051a4003250040d03110000e4019201000d1140d54040d1203014660114080d03804040e285400c00c100c10400280100d0043c5440c403c9410010b5081d049a00007030300c80c3d0811196402104c80c4601003203602e04240c440e40381c00c60094241081241072142c2031110307030103d00300454046c01c0a1316034400c142c3c1042009141e0700304003c1c401e078594580030b0790501c007901c51100b00a104080c5180301c410030300c04540c15030796a010345840032061181c15203804405440d0b03000d890901c0f98141348a0300c215450a00070351403268000c0006000224040100c141220407814800080210500500000c200c012802d442100e00034a402004d5a00c0c88a500e9204035000d480c102c0e541c8130004488005100c440b1080402106500c8d900d1302030540c0b01040020b54040005440c00501e0841410054035401c1c04001e40149002e400003619081c0c084a188091103882c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812904784 1250 812903534 812903561
    0xf090f01091a0127022d07020f09070c06020906090d03030b0310140a0b041b2105041a15040c03061e1d040f0f08070c080309060406051c 60
    0x404140e12039140e0b80d22442c0180509960304076582d0740351269590400b51200c070b100e00e2640016901b5501600000220984c990200380802c01550700302c0d582501c0c0e84034410403401402c039502410320925000c0011449010b01d5142d83c04030544603a40c01e802980003000c025030095082c403803480c50b80c4460360814200381c0700e51800a103140d0040c08061410016052064100d820080d0410082103440031480c5c00c000c481c00080f480144400c0041d02910740b40110520a0806d01c20b80500c030769100034503105c00e22020110f1486e00b0140d640c14400d441089030064180d0f5650303658080171001000c504ca0b48600c1d050403003440303020104009130a495206528100081c2c0b51001401010118200385841003040390500150b5498254400c2000000304070444455400034001030030301140502c411280c541c0b20406a041c00b14500d0a840c42e500400400c0d6000e0300380880118aa060010444100f0f00c4014161814586429402c0b55944d0041c201183e03503030019046414542140e000da406d424020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812906034 1250 812904784 812904803
    0x90f0b040c08060c071b0308070c1502010912110a121d060405010215070507060207030f20061602100501080d1d06070b061c110a0905040203060f090f0109 68
    0x40c14103031038081c460307044000300741c000e10140044d181c0d46800300c41c40e441c0d0100c031707a038035111428001200780e241603480a0706c1c84400044060030440500c1d510b00c180c440170130710f40d64000c072140070890885802c1c1c3c000603d81400c4001070b05145001d0a60100c1104500e4111f4000c000340d6030301c15018000d1151010041481d000e01455110818610300110000079600d80d81000d1030300303000035a604228412080d2482009000c80e01d510300c20011280b109401c40420340d50b0300e49074a170060120121b4038169001804a16407070301240001012504411000c5008000f19140c0a01c0e0320b5800d41800442030544c4540d8940f5584030300b00b03004890007415030038023a11100701072110152520107401d00b1442010115841c40000c0d40c1c950080d1030350b043e0410081503056440300c0110342e04660313144c08545c043d6107181c4203408021140441401d01d43c0d00b60764030801d00303a40c0c140d403405440095074000d60507001040095040807a00d50300c1940300410134111203000340c945007841c2c00c4580c6002c080d2444d000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812907284 1250 812906034 812906041
    0x9021f051801050c06151504060c0c0e040c030201050a020a0614061c1203020703030f090506100b090a2c3301020c1320030105100507080a08070201090f0b 68
    0x410009112941d0780a0812600c0c0200d140985070311104010015103815081109252860701c6694003221107400041405540b540c454001070480030300902d0444d100e07150b8240110b088100c2042650256512031075070010242141d005566030303082a5005021881011700b03180104410340610405010855421a950305004040c0050926220581d00440844507070309400626418068848008546801620351001d0b24048024140c686803484645081c030408506001c00071450034090a01c8030040718600e6621034034401c01b0701400d01c1d003da00524295041014124503038a207500347c00c14000b2500c015081d610f0020b031024094400042142e0b1070015400025103541040011200805d04010003004050000307644241c018102400b81901c407100180f40c0c81c4580040030b0070144100e00304560b811019035440075030024840c0c41d105446451088925031300405c00ca42c20590021001868051118400d560f41c0a001d803140701150342e10000c3d00b010a04a02001d6983d52003112042c2d200e08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812908534 1250 812907284 812907307
    0x1905033105030105040c090e03040f0308030702250605130b03010f080d090302090103030c030c0501021603140403020604050d1403041203020c120c01031a031e0d02010c08040609021f05 81
    0x11400c0c0c01407070090785013005100c04200a901035030304407543c00201017205041c1c0e1184c02c0c06c40c01558015851010701e00c0b070100c20443e102c00a148105c06030750841d0400c0c3ca22075008116048540096236a12600410500c00070344140d00401c050300343e420b204039600782e603564030440541c4241d2101d40e0041d030080c010310881505101e07454400c001d40c03821108150071500000c441607010310004090002d104140000c250050040c201680d400c18001c546800d07503410b002a20300401413086001031807103480b050203140701d5410f07181501d4020f402d40741046c0c00d01083c091001c11440050380c1c40801010881c415071001c0004001803d040031740c1d48807a030303104d14003e03141105031040c0601c82c40c0702130700d842d080c0d43c070002d80140d40d10030034a00865a500c00d941c800c10852400c002850300b40c02828220109030106a11890a10210100300e480058089100300c1c00c0381c011480400001d0558000700300070500b1a04200c0d622400100f2106000c050744001c00d2284000d8151000803590220b0380c5e50062 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812909784 1250 812908534 812908627
    0x1e040303020105011a280e0409110a0509010819140105091006050906010c150e071d0c1801030b0402120a060906140d02040e19050709050604020408190503 68
    0xd800800c20701e082074048103281c9010000960b101c0c021b006141d41115100348504402410694083c008110003000d5040001e0322120201001c0d0003125201c0c40020582401181c0e10304903400703d0080c0018104056840c1002554088140d806202d100d4405294078030038402c981c000c2594200401c0203429034007082081d138207a03070300c05441880c3c845d08110699070407a0410400f640d000e4206840303101903448080c02001084101c070814414540040f0301b0821a034084414941d000311810000d80e140751100c1000d04c105c01402c5e450034190000000f095000b90410070a06400920150900300c113521000443d0030210380c01008107440303d03810001c00141d84244009007402e840c6040380f80341c88502007110b440a08038000c1c011692000d624200c0d2109119120800d2003403428101c4050490402d5551423415000b4030350401d2608012810a01d010f01c00c540c21117080700003410018030818112690b00e030052400b900c55000c20071296481450702e10041e0342003501040c03841000303000c811000c03020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812911034 1250 812909784 812909819
    0x501090c0306081f111605010e0f1b06040306020a0c0318050607031101020c030301030308040c0e070e01030911030607021f0513080d200909060108040201141e04030302010501 77
    0x28145810402e01c8030980110b180614240c0d03a611041a135004100d011000300300b860030203881e05001245100810800204118049000e04000e000350b4038041c90f065103c410604803828180c0c824440c04400304011011107582800051540741001d659440b018181e03031080b64044005805803000404058000c40c44580d810b5040070074041190a00011a0300c91084401c00303070a004103c0040c41414509404803441b600c000026280c4950303480c42d028117a01015a4103d8080d03042200204004402c41a603500c26400b0f40d941c2411404900c006400400c441003040c1d1303880b081c05440c01d0142e103040000b940189416401042e810101d528440780c1c81144403403240916040006000200c00e0301d0203850b401540124440d95200c0c0d000c0d44801c01000e0340310107030800e0300140303006000c140d2003003010b09400d243c2035480c1d00455450600440c0c1c40754048400901040b030050074141c6600c3c0c40c0c80036040e030b002c014810549100b581402c1d07905940165100301c006030344450040c4004400200e2002c075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812912284 1250 812911034 812911037
    0x1410082e1d0c040902130302060c070f0803030603061803090907050405041d0c040e070f030c030c05030303060d030e0d0b09011a030715121e0e0606100e0f010504050907030501090c 79
    0xc031414290507100b0359200341d1140c0c0030300c19004500301400a9904002400542d0300a00d82c41e40c9124180380c0e5900c41c0120301c01ca0307030705009494000920312808400c42e0b10074040140a080b050b900d00b0400032510340c6070440482c0310322061103000c0f0705881b0b010640d400303508551550390b280c4d4038100c108019542900704101084e00310381488148240c0014407510721082c106d80c045000c3c800d1414140c940322896004d03003d10001003000000388209120722006030385c0100300d410821515001031568078802502c40c030340c1210000c103011003c00d10a6008403802c16008000054550007034840101c401c3c400c0d10090301c103075074401c034192001018504900360300d84242e015000300d62504001c00c40c4000400340e89802e0040c501c5e500f85241c1001d9011440000303002101041025010103e08014926040c1e94403d0744100c1011030030610300b0380e000c05404021a680c504002428600340070080c28444c0140d41441002d10000c11b103660f61652261055589a400281940c074084a401c19110100c0341d120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812913534 1250 812912284 812912339
    0x80a0c0b130f0b060d0c090b011403060303090d08090d050c18040302060a020a03020405040e010b01030f0501180b0a03051203101a1902070312181410082e 68
    0x7520580352465140e4022000f981c142c0c0e50f001c00310783c0110150f007008181280280020545444990046c54400070a03a1113454002100da00034a05200039110598140d20a05c041803403407800030a50101c26200300144c5040c50420350101d901c1e00b00103002201c054002003152446070806040c02030314410300210b0810541490307100130b92154005002c01a005400181d9480d486000b50119801440041c2c400c0100d10364040d2070b0b82c02004400e01e80790029040c0261141011850f004042c16a001c03403007080055100308403004002d106240e07400e504913842002c000085081441050b20341c140c40d9801503a03d280c0010021110b06d15500a0007002d08081418000803000d0020350304002c5205005a00300840101c0a07444c02d446a8001400603546003c40c0000940c40070002c1d80501d942407110000b1078032000126034040d002c500c096005020139500c1403400e88280b441c150072000306905800592004440c201b0071420400380740c404d56440301c004101d0140c2d07200e00c49070380840420300d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812914784 1250 812913534 812913571
    0xe01090804050d0323190f0807051303020a0306060807090624030e0d03021804051608040c090608072606040b07020f0114011a0a080c0d09080a0c0b 65
    0x1032032401a0302499002e4030780042d00b5020140102c001c02d880a0507242c03190030500403065101e032154094030651804003440d5502520343c03030041002502052243d265104e9598900c501200d01d600501114464400a07903c0080942c0b07401032550003440c01340c40080b410038203000c01189800021b81c0008452460507008004108030014213040b80010100c6c042084080e000e0120050f00401f10000201c0c0140e410b2030550a401d80d00a203078044184000c0e00ba403c0041003040202c0c0c004482c81c2c1c50782c0901001c541c9185203c1d944050380248038060386e580369925109060308841c1990002407083d840100c1c103200f00c07201052300200119031403d00000c10008110400d40796500a8002490400010003007141d142c024070603030b0503803c0c90340001c1112040c0c0803542d100d18507013880b500b083e51101c0060111844d0321a0200da2100d074a039182c1c00e80a4a80c03610b01e0b1415409454641803503980c4010100004035184010800b500e031b165a600c00222031343c14101d00511015103440440020101e08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812916034 1250 812914784 812914793
    0x180d090305030301060c080c030a031a10090312110a03030c0201180f0648090614090303090604030812010501051806030901241404020304110f0a150905040e0109 71
    0x4413410b50740a0703c0c0c0320003401501e00e0308a40b1405030700c0c6500101d010100c0c1c202d4a01c4d40c5940004020013643c800e82030f00c08000c40c203000c24500460071850006d138440d0010b00220703480e464041417601b00d61070302008a000401d085810150b042100300e00190300ca0f41c850040940c2405001090b10050040310748800e410f40c0e40c5450780504410040280b915030242821940710720a00301035001031082e2051750007501d00c1142030074601c2d072068100e0001c0c02c0c0100503070a5108804070342c2601d009498054103c6406214250640c101c440710b180c2c144400c01005990340c442c0405080250301c030700102625071064001d00801a4416000503041080074400302c5a002c90a448140041101349ca030503941742c95112340f0a0150000c1010004942c03142d4800005850703021012204070361400e0040b0b0032005005080100781d00c000d80d00904802c0c40c0d882141c40c00d29041c6500403015400a01c41c0c050a580c4a0521a803803800340e04000100341031039003c00503410300d0b000c4c84c05031004041c0200f111917500d68030b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812917284 1250 812916034 812916037
    0x1002090a05121e0616110c1327110603130c090603060c0806031020041202210309090702030702030111030a0e0a020901120f0503030f150405070207060e1503180d09030503 75
    0x103175a0801a480c1c0550050000a2120000400e80508001a061131b0322174018083c244808860120343c86411442002c440d40e03650007c44c144c0c3c030696a032413541400c0200913035034001070b00c1c0c03407078042030003803540b00090040803260000d1154101c0411b486241d400c0500c01c40b4a6102217070180010481001303200d60340840c980c0c90000200c8000a6541d811800303070b00c0209040418030000800016010842401c40c0f1122401d59100f1150000140e54850204028103c10000382050368000e10522080d4a424580d01e40d112034240304903418502203030000790039207080c0c1800741c200031400405d00c0900c1310705001320840384080300c1c0140000d4110707601042103448140304058060803c490080100910300745440150fa8000c1b0482c0d45034145241004010001680c82ca070010f07215803000b98190819020382481800e603500500141440d21105070780010300c144e0421b078443d1401d8044114502e031200074501480601c145801f181040a00c0340d40b40c2107101612800784a5500300c2000000c00010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812918534 1250 812917284 812917321
    0x9033f13060c140c0a060b0105040e0114131503030212070515060a0f1518080a122007050f220b0a1802031f081002090a05121e06 57
    0x8000140902c0e0300380e01102c1400ca00d2030042500f420004055071841400a116803616016020410004504800666444c0700d00d00c600000c02800200420006500861200c4014030140102c1315859008c42c14108a0719106ea21207520b0150010a2003850790400040d51b404089880162404a0359200c1e25613a41200d146c1c003807201054000184642c4800345600001c00c0c00310841201c01ba2524100c80d011701301000c186000410320721450385203841c1c0c80b90708011030301c10034068141d9a010b516070351150310220840c102841040719a044c44940e5030302c010040c3c03200810242c01d000381080700f00605100c01103070a5104020510303010840c42c07048000c1d102e80ca190080002580c0c0411008503041049642c0041e42c0b042c0061880f480460031038008502c1001c4c101e0440c14200c0d40c0200034a41042940500d11890340228041c43c0582402d600408042d10000c056004041d43c4d08009100b100b030201026800341c000e2020b080080300d040c00c2016900250801034126882d003403400400e00308419 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812919784 1250 812918534 812918543
    0x605070f0c02120705100206090d090308040306050a09200a09050c030f1b1c0c020a210309020409030c020907030c0e06031e0702011d0c030604080309033f13 69
    0x341d181c440f010204020981c010b20028140b04242804081c02a44621003140c0d002054000c2040205940d0700c158805000c0c0c03a440f9180506060443e1a0f800050900806040156641c0c490441c04617401082d4808002031016280d810081c604080c02903991079988080c41c11410142408180c0e040c0c40144d96004202072001d1009da910b40040f9900030703c0398000140c880c1400036411143c50840201c02500c4202d00f482803000048400080340d0303a04507110042c3c01400801c07804004204220103009078031041f8500803503151501c1d00050b044a281202c224089603501600c80d04501b044620168000d4072420208400020341d00c02600000013100c078603115500000000703a032100710f0b484044090b1071243d0113120381d2500702c83c003030300800311a0082c42c10180e04200ca00c145000020b00e0754140440580030300101d03152665441c8103500050500e00303882c0800e000c046103195441e61440d98120004518070704c0c000044c52440b034051070001c40804240c0900c0e040200c01f400050300c0c151540e500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812921034 1250 812919784 812919799
    0x2061e0706020c060a0e030a081906030c0905040201260f1e0405011d280303060e0c030f06100e120709060321050423040b04050f040605070f0c02 64
    0xa0110019244614500200360510114480018030000a480c51140d00010801c0104d56035403100a036990050130207000c0015071620000c1c000b8284000201007000c041c0070040b132081d890313030f9a401d14001d05812111078507981e0001c010075981d2080545410714002038201401f03210608401c84914001807071700d40103004020100320030036030851071810681100c80349080d01d8202403a00750701038804240489c2074040054842001c0311300103e03041201c3d10f216161300050800303007400c5101460074600141d0900d681d840d00050186052080f082c4240701c100d40340e81e604d01d41060001c50f540d80141c0700d136009100c2c4c804c4000030303a6000349000900483c1101c20740076049080c01101c0c600310380c41d0420a01142441400010000e4034002c8541c1d00046d44068881042c004500712018003403032083e48020790341d50450703020f001c1100003c000003000107040400c0607200500404c00341e610689d1481c101130520410401400700e244a500c2c1c001c4501d14003e00444c0c1c03919001070524440c141e01170301c80c504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812922284 1250 812921034 812921077
    0x60905030d112b170601050a030e03160302030417031201050d0f020a08031b0a1205070609060203012403090b0106030e07120501051e0f0106050c10090602040f0509040206 75
    0x800c1000d004843d21198001540400d00494644151840040c200124206112043c0785254104640d4403500060303458504241c1d20801c21009008001400b070801d00041100e40d0035619007036480070006020350021a929482c0c502e001d038801d40d0450044e45290030a1100c12050395140102d907046483c21203840304d17150694140003400c00030b0310200030b500c0490403000140c001000700251020110901d0340e800000f412013056a20b4441032000280200c1c034030b610b40c007501030161018000a9009400c0090380782542d540c1c480c200d034400e0f0020704025000300030180400450001c4440311403000d240910020800307a40350022000107018207014181c5841e035815541000b0072890380201202c1c803118a00010604007240202415107d80d001400b00013900403400184c40041d078010701c030020b034444a0340e2034110115010b80041000d0b8203540104200440701c030f4410f00800d510300340038060069680c2c0c07504500500c817200030750065016005800400c009680c50106940c940308881019212091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812923534 1250 812922284 812922317
    0xc060103080d020d06150306050a05060904090512070c050901052d0402070b0c0436020901030e0f0c030615220603020d0803010e010e0103050318010e031f06060905030d 74
    0x4013984100710f9450000c0c00110343d01001e52460b0032002c0c1d40c5040240d103440c0d41c1800070001d51030040759003013401006002e4490800f640b1030042e41d40510152000d82d5040121700e40141d04c410b4040d212440c500c9002d0041d0b10b0704c4e0454500524040712403503644802c142034140056441c003094010071002409504a81d119601101d581e154000c1540c2200d02e4280300f03000b02c6400600508140d00c0d6045120b200845440d110b40c2d640c00c402c0ca059560201c083d090340c9000c0d501540c01c1d03a0406494491481403400e007005907141c02d5044102501002c04000b007454070f0400c0c01050075800c102d80c020390700410f4640441d440b0402e20300201c9680c242401b8154032010703010303d41c00290020f070268074550612921b0005035069518103029040c4907603880d0b51301d412880ac01c1c00050710a07002044680550b041064129a000b00103042c125030f00c54540c40000d082440070380d5100d0485102c0320b10050300d10304034840e26024220a08160261a0400021030350300c8000100120512882c803000b4003511 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812924784 1250 812923534 812923537
    0x30203040b120a180c0902030a1407212918011e140924060d0905010f0608150702120f0a03050a050c22030b1302150c060103080d02 58
    0xc20040601d0740e5240b00244009019440807100309110516146031814410000300d0201041a00020344501050501c4d413214002d60014008002031a40c40c2d80080b030050f08038403507503c512919140c0e0304140003107109800d10032003510100d04002c0c2c80c00046001024050b507900e54584501c11005034280b0000c404520f0040303000c0014000301e0601c17030000410055810031201d0b9401000900545c590303803020a64170315207801c002d031030388010030030001201407020b24451008a00380a0849880641c00c0380425244e0780040c96130780d209070b1204145800d11009000e0300d103207140088d508025042c0f4107103a1603152203442441003070600d5080042810315100704420b60141a0309003200c0e0fa01c00184007a5030069010841403000300e410240020460040c07803041a1190400084603071038460403047c5000740d09001440301500890280010021481580400e44540840c03205010781d94268010060300c3c80080c6041400524100180d05c4003040200d080f50440364800b58850300c0340b12030843d01003c2d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812926034 1250 812924784 812924789
    0x91615050c160e06120307050c06090f180615040f030b061201060e01051003020325110109080403061d1b1f08041115091003090807050705011e02150403020304 70
    0xc0c5000b00101251116144041c10f006076000c559840d4540402010103849005000d809080c40c2c2200f03c3c0784085081101c000c040740301000f041c070204104100000342c550140110f942105892900400070103090400000082084048031325060034a0066490804089804000c16407007a18002c29019262151518140d42d000402400541d031100310151003131b082441540d105403404585541c0160103072013100d005614030b890510805143d03207104260f500469018608001c80603404040b0810207100c2c25900a21507480c441e9038914604218099410b0302c0e101d40c04119103402558012840052010f0b100318005891041c4e071030840d00011301d40e03100740782840340464030f003080401807607888400a072003144030b0b40341241c403421048103010b4222380844003000d101004000107041071405409003940010f2914000c83c58500e641d40b180d040360845401203070160711000c000d012940c0c0041420840d40325000c004002890100c50007580c0c0c40c501a88400856003e40120303042c10305c240101c401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812927284 1250 812926034 812926063
    0x61905060408010f0f06060815011e08010801060902090a0608090312070305090d0306140105071b031b32010e060a09050a15050703082508091615050c 66
    0xc50710303507a0506034043e004900c41c04c128035141444541c00350f201442560103a0746540c0d41e92456550f9003480307038a01540002482d05100d4143d8880400c01030a42d01c2d25007c0009550b0400380e9454031a1442c251107894201c00c0c0814018820161151122003012046440914150b00f903900c98128942c1980700b041d848408003a06001048032545d0180c001c980030310101c83c03c81b2101d6403420f00460072034503240114418840f1003a1915440d611a030b010303050090040460001445c20b00400b640900c1c01a071007294145105c0f48240880000d10035104001d180511194417102c529403c0c2c1d03201141c040040001024411608040a904c20b01c142d18039000d014240c5951800040c1d80640000340354828540b14000c06000487c2296511240c2121189130f07485250a00b01d0b1964255281c00d8018803c100e422545e4840043c40c40344c2c40c180c1c0400001e1915003100740c0c01c00d5287c550400803d0710884111503000c3c80c04000314110303422000b1200903180390c17554550160a031410700b80000c07900001e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812928534 1250 812927284 812927287
    0x90715200d0c15060e060409060b040501030308010315050106051c020c1b0a09090506070e190e0403140a0e061806030f1e100501080c090301020c100507020c0906190506 74
    0x40800c0d400035050009a03025a488050502003140f42030f00741c41a50048000703001c0b06a02180c072505154000c81c413078910910b80450504d610b00041412a0700985c0300f6400a52a00010002d00540e83d0394410321030405d410600032036041040c0503025204490401100d000714071145209070748254140e42103586100d041d01c121004199a4070004000d1000031480b50310010000203207200b0f2481900b5569901c0006060180e4a5072000c1d104440802c9244d50044010b07400c51a560400002c600c0141c210001000c2d00340c106400c0c002e100703119a0700d900d407288508101c02d07a2900d030040e82e020b4020500302d640c03941d24404032200f041d030581300c5400650000c00c0402030040400c1500703003da00c52210700b12480c0f00394200d0185141030000c281d908901e0000d0659090140e9440713011150343c8440f070b114131145485084400b2a00b20307444054004116000342c0003e4284d11440d00465400050620081c1901101540051010003001d0049441141080140c1b00400b954400d003000501000300300a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812929784 1250 812928534 812928553
    0xb01030b0a092f0102030a140304060b0d0b091e101d100608060a020708040b0a141b010c0f02030d05060a0510020d0311030c0702060d0b120703030809071520 69
    0x3c4801480b60083c98201d0151403080d0352000003980c840101aa03103440c41d00c07032001803112903540003420540704141c5480c094052a260020062416807088150460300e180c40700c01e032410028908078500c41d8115100f1003440c003640002d80403404140641c8002044541400c160341210307c11452110a400749102c4140301c3c01c17a0380d000c18102c0e070a0340155005551201701c40c004912440780020310b1210240014411902003001808ac9070b0254140090598100d03894100b4a4001000241b02c9914041c84141d10f04428001d00f040362240d030400d058000e42c000c41c0a5224003a00f5950ba1420b40d03200d0008126546900d0541c004020140000840d4183e40b60000c0d03c40018500e6030300400e0411451440856905040b01e00c103082c0108428103080c0300340d00704000e40d4442c2c80341944568592403100d40b9076860340c08203002041080c00078443c0a15600d400741402100508403c0076420001c020440980d0b04020070588200600c1c3c00307540c01200304000b400804200c0300003001131240c40c402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812931034 1250 812929784 812929823
    0x8220906120b09030f0712031e06050f0909060a02090a17010905070b07080909070215180c150301060c0213020a050a0e0f0a0612090f110108130b01030b0a09 69
    0x2102071400303610225403c1c2d40d00b10940e40d50344154a56917140c1d41c0e08000d4a40810300c0f02042c170004501c1071402055402142c070100304180280da07000745100f6907030348c030402c80c624010540203815242650800000d20301280c03015282d1100134103255610f500080c8510456954607400c0d03001c0c208e030381880d111101d80c92103c98024640d0180032911841003e1011600c16805001c0d25945940107811a10b8445543c0601410300d0780a01004203500c81c0c0f560f0b508440b005100c200c0d1162410340184030300468000722891800d00c082070024045c0e19400035848001c4010700c12a415641181002e1802d070440d480401d00c1c40c00c80c10010b2803130f14408185040700a6010b002040c4c101e0540e95201c1c1c1d8010306c14100709446140b9044a03078008901c40302040310901600c03206042c1d014016000541140c1621030302c5d55091780c52170403540b070706d0819201d403031070340c0c00c2001c00b50032800c081c081e005109416514102c24050601018004440c90310004d210100541c2041c4030565201c1c1c00c071423071031041d20f45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812932284 1250 812931034 812931059
    0x90406030212011a0d150f060b030a0c020c19030b070c2f0a080d0f030b1203040f12020d0305030402030a020a1202030607082a120106020601090b030a08220906 70
    0x300c0b0313260200344000e1140a8a40980e180f9a0381da0417940040803421103d1140c80240300200c2c0e0814200d45403040002d903aa0789002075445424140c002241c0d803402c00100900780500f650125104111241d803d40000d441070001c0c3d0141d95000d801500380d82c0f64154152488d41090074014940465503a00190200403034081e40540c20449240075991410401009018001c40c05850f03a17942c00740b030100c1c0076070388681c0003541c81d002e150600140302c1a180d400716014140c00201c4404503400010200254011a1849c0d4014400190b40f081480306650006010a841541c007404000000c0f000c40c0965134140005442c017640206000b80700c90b920b10103403c0d80145102e00341d109000342d03400200014000d0000034400c917002da4103120800c203818000c8104468034000004000710500c4588000041840410b0103802d8540003007003c0d600d06860b07a000d88020b4001c860003600b19514901c0010305080542d81481940b18449841110408080b80c4c04081c9a21203081c8034100040000c5000901030b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812933534 1250 812932284 812932301
    0x60c02060c190b06040207080706150b0a031d03040302011b060f050109050f06012a0807050a032c0d0305030a020d1a030d020304030c0b0708040f1410080601080402010509040603021201 81
    0x20120902039441a0410040303004145c0040d0030328504001c0d41c9c0000d50300342c0c071000c0c90100b02c40400554903214181d54050ba0410300c0c0450100b561090020103a404410f4256035012800004624103070441e4002060286600500a14151542c0a420400030035400421a01c0141031080161350303035076100c6801a002c00c1d6030503100c0300c020401240080d441510b00e5528001d40c50400d14110015418192000d800c1410590b68560f0501606001035424803070b420303001e80203986940c810030541000f003080900e003100c0302c008400080360040d82c6d40c86600d0401c4095426040594595554656001c06846145d00340d00e02145007248075818551244000c0070742180a0301160b01001c154130090780c2d00d22a601010b0f00b411014582000510380b00c03401000750ba4410080c04d41429600e03000c544201d1100c1d0009640582e4000002946081551140412140c00d2800c1d030b0b42814407038000b0f040b5200161019040040001e5040d0b41d545494002ca070040d0790217030110400c04005000340d4020080032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812934784 1250 812933534 812933543
    0x190503070e072c10030504110907020111030f010e090607020a06150b0c07060e04060810091403121b07030509010c03200c120708070b13030231050709060c02060c19 72
    0xe0500c0f030004d03210384105c078421076001c0c1d12551021000300401180d4007004103948215920348040000d4941c5907030203180a940c1c2c41d0700002c840e50402d440c0644101c0021b00c0200b0683c031040800118560001e001c6036002d82114001440c101c422400c403480c0c0340141c0090315020400501000d02d00e0340066400700326040e95854241c109141803c0006581c800e1003940c0c000e80c040f40c60040114440d5101100c403920504100104244018409040d40c200079090710910001104008400007180c20010081071080a070700c2c070780400d07943d01411901802409604105078000010b003010300414120003079034440030120381003502500d0301a03512007582091a020704003400d0941d8000200196440c00c0d15218800b6200301e40c106030100c0704030342000c0b005d0100008410000005600c2c0e405210703a0705c12010024003010b03400e102c82002101100018030078010324140c100084503034030850306030540d030741c61506102d01d030306034000158135004140802d6002e019000448040c0c0b44001c0e040740006114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812936034 1250 812934784 812934799
    0xc0606040c020a17070b040f060b0f090a180b0108070807050409020904021e0a0609030219081f020d02030106030608160f05091305010f0506190503070e072c 69
    0x185414402611540400200907030b002e00e21010008008543d840710040e9440b040509101040c2c4400199502c00c0e40c1c1601c00c40c1465848000f80308244c081c210607100d06503107481200d0351682c045440380d50003c243e0b14126a4034044251007040040301c1d1440e10303070041c21000c080d503100c40c00d060b100c2c2c00324070580d200751103950300000c4c507810300380103d112050300140301140580d00c03a000d000314102c9003484015400360b6488000415036401c050720020701405c0e903036094100e040d0b206100a14007140012180040c00304010041400001040c0003040c2c0c441070f400441d010803060010107801030155012205001100110340550725510040441d00f030300c0c0403201400b42000406c0380781e00d120f008000540400342800d215604000034910f4005002c64030740030b13030078105896a500b140c1c104030001c00c246854909100b5149440040c19900707440445281400600c1e01000031342d00c1c1e400307110350000002d080001405003406151900c98091401d4515070700b49030300f4010b11058204d80c0c00100d104586 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812937284 1250 812936034 812936041
    0xc020304090b030c03030d0b1c0506040b0a0203060d03140d1d06070f09050d110315060a0b0a09120515161e1d03031303060e060a14180c0a0305030c06 66
    0x40000e514501303038201601461812030844855000b074640343c1600c41d088400c81d10192164905000488000781c040d40140c096414031746003400c40b6142c00b601c142c1c03101c0d0040c02800000d0340d8403503010314003942c54203002d54407070128101000d440c0a0002c82403000b0345085142c0409034050f005400b10494030740183d40a80d59840f8099034829000e507034040c00256080020310450401044640046000700c030a05061084200064540a00340c0c000c2c501c611002000e100b00380c1031240e0001c1c00703006c00000030360030321151510040146505226441e40c8103140b40b21441840410701c00c04000142503c3d102002e850b0400c4140030480c8210004400148182403095915218502c0c2d14501152aa03039002041900000c52203048101404076a0500041104014960180103041d0003584541ca01007544400b0a4020f030038800700406e410300b0740341072440301c0350314169061800b98013440c2511000ea11401003c2424038000c43e6607000344d04003902174404000d00000001519403030400380120391075581c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812938534 1250 812937284 812937289
    0x17030a0b1f17010803161b1d010608070903060c0e131b02071d040c03021f0e010e0d0f2a030c08030c031b01020c24091c0f02010b1c050601080a080403240c020304090b 73
    0x40c03301c1d2100f0000383c0108091002a4180d00310445034099440d2150780000c540f400604041080c01d0103030700881d81e076210044030071125242c1c0403c00c41c0500151110780e01c0c00b03d40320381001c0d180d488003070110600c00024041001c0030316907501a68018250740da040d10300001c3e00b4030b215040304112022a41c10344000500c0c0d0300c0707120540001400601043d03003c501541e104405c2e0061000103c0f101c00718410030341403a0b40b02c0e10903c00aa110a044580c0782461800d00e5040c40c0d06030b400100141d08100000250044000100e49100310300e61080040708412080c2c0300e009000d50001060039000380e520001145003140480941020040e201c540c1584589245d1a51901c0c801c6201c41a0542400000681c5009a8241b507000545000100314528640001014201d0071001c0c0c0c403100c12060700300020b0040c10000d06000d00b400e40c006003602c1031162030b013540b035005600c0000e00041c11b841d60b01d0f0240c107044840007145880048140160000039501941700c0e0440e0003030401a600e4031902d2000f91 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812939784 1250 812938534 812938547
    0x608011a03090c0607050c090403020d11060114010503190609060303030b0f1509010203070f0803100609061d060c0307110f0a0317030a0b1f17010803161b1d0106 71
    0x2960b1810080c401c249030340d410300c41d0360b0b0480e060940d450300503103071104ca0750745550541512680c441d07409400319131180b43c0f01034154010076090441c941d01c8a00180100042841c0380e00c0303d82000d0030440c3c1c41e070f6910310030340620a008814106103982814400682203031650481000c1d24400e460030700c011090342081c0a015502c2034501684101c07880b00406140281c04000c040310401881580d145c409151070b000c2400065290454400d00000208100c01d908040000c019203030500d091603100b441c0c800d004100303040388202559040c40c04000c0d84001c1c4d40b10b03400c842c01c05c1c0e41c1e541a651950602d041180d00510280d00701402070350105c11080c400c0c5411030b6400152607200583d411801e01c42d0302348040c190402014038102941e20030002615075548600861211b801030303a074550320907911100400f02c2e1100c1e80240103c0039100c0042c4070181001c02034400007001a142100c00150600b06849004101d00b08004855480d50300413615500ba0805040819508851085241d0740c441044520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812941034 1250 812939784 812939791
    0x50a020f09040b150c0a21091e0e09010c0e032e0e011b020c011d100215010605090a08060f0c070503070b0a0c030509071503180c0608011a03 62
    0xc08040240305075601d440c1d40720a02203040030381a480e07032001c558600d000301e0388848808042d983c880c46107081003200381d031502010784c0c0d1000340c0c2c00081401c051000c4c15003180390183c12841e00c01c088201b0a0000000c0ca243c004210007100c0c52a5800c002203650300810088a159000503803c9271101101d04000035040107a00740b0084140100b040c0651103500100e98440100701240c0700c50011b0a0403509010300c00c400c000d5850410540308500c48060b02e000c003602c1040d410300000201c083e54901416421859200c81640c201c409504050000c80c18218440100d280e0000351200203d642e90f880405409055425903103a0521501c40841030707a1071004540c2c604003143c0d180002918121410301800031280b04004684c00c0c00419a59817003c1c600441d0500e00316565904a21100c42d4940145038200e82c40d100505206401e1010545920044244d04018151200d1300544503400c0303c42c2000b05140c00031501042c46032101d034020b00c403503c00e01c200007602801c0d01b40f40c0020706d9031100b100d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812942284 1250 812941034 812941057
    0x40b0f19091502010e07050d0f05010908090112060b12070c0b0106020313061103090409050307050102370f03050601020f161502030a020709111c0906050a0e03041a0910030f050a02 79
    0xc2d9446c7c0000c100c4002140ea9044403e82200101e4400040090054502c2184182d0110342c4803640380000401008814486000c1641001c03002c003c0e160b01d403011110390541d0041c228031681da8500c0290395101b8204002404440e00e600001a1581d01001404050083c042c0c1d141040d1342d500000c40e00c08031f00100303203403058008210072402464103500c10700003544100c1c05d89040400c0768580600b2a00500d080315990380a6143c41501c5070b00315095500c1b032090720000e2212008180d940103200340348804081091503a14404944140c1c0200404080c020150701182c52034401c0c102c00d1500c94031079100300c201c1c941006401980d904c0c0040150341e030045244d4000d048440c80d18002001400c895000311103640c40c10044005242c0b0503003c0418156100301000c508e2500519215048400003410440414034104100802010110482e0112010003070040141d0700c1815506043d423003140e1155600010b421002041c046d00740d000001100c1c2c0200d13041040c0d84d00d0002c500c0980c400c1c2d441114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812943534 1250 812942284 812942293
    0x3030a09030329120106080f010204140103091505040c0f0b0d180812040614040602090307080c060405040509010f090f050d0c020112020318070906030605011208040b0f19091502010e 80
    0x71060600d20131000380050510004203000382d8072010305040c0b9450341000d8059940020342401044402c049190f41c1003001e103420401001e483d01da40c290741d02406100d051054450001c00c00303000d51245040c0c00750919954a00c0c025a840207a070003254441e01d5400c48640c10300c4c50128400040c488526003460f00000c1d498644070304001014241c0d500200101d440d980e991541c2c5001c588a111181d2007079115081c01a1750f05000c1040600e441c10981c07010000783c1c0314185400f000e842e1030082e5400c40d03405581c049056140c0d601d240b409001254160b107040b0346001050814400021002500c1e980548140c42e2a420001703011600700d003240c0c0c00070340401d00f80201c071504030300103600031075010514207114691703442c1003e03003241460304035444000707281d0721414107009200b0248201401803141003404075280a081d9104840c40c0a648142c5000c0c100100d8449030780e10842c5d080301c0c4420364540381c50300155206130004d491010036005140c00000e0a07100481014014415040402c01040090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812944784 1250 812943534 812943611
    0xf01030803182802040e0c030d0f0210180c0b03070f2607030e07080c03120906070606120b01080316111206010b0910230a030b0303030a090303 63
    0x4080c40070044008100c24864922000303d0b218860348203c60100915240c000300340d41c640100003d50300c0051500c1e0054000c484041d060b9a00041d11000c4d1260608000720368840c40e00c1300fa0305103a05031003152212400d0100b280482c1c40200b5202c0c0c42a44540c9200905503211541800381d8001100c4920104501c8902c005019014483d90304a0030040c0484880841441e02c0030486e2010542e03804000c6901c81d080c8119003001803080c034010700070280c02041c1210001d000241c0d0348003000a4152a07043c006050302d526200c80c0109c0b020345401540074008595074807903155886a44103001da804004e00310021943c00004800c550b00da4001100c0b501203911151030301d031351030382d03140001035402200302c40b1500d0310b04c10030301ca041c0c02480c42c4d00440d82ca8601000510454006049041c030420424443d0200d45c000c203060f81d108c156052041660301e886550806500401403420002c1c0e041c84007204008910000e600520b0074244640e400307110300d842240314007481c46160012107030141401940c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812946034 1250 812944784 812944801
    0x92401060c0204060305030a08060103051f050910260d08072102090319020a06050903060a021602150304020a09062111091e1b0d091401060b04030b0f01030803 70
    0x10400102e00090002402c00d0392070740c91501d998440241d08022844100801402c0d60b094032a4960201c0f1540301071003001003401c942900315544d809418400c1c1000c90126042042507030300d0300003400044010f40c12124250160803c91940070041c803540344141101344060b0b52181171414021083c50310341100d80800c1840e50171181e0301008980c0300c0d01d03600b0301403030b0444d40c0d040080402c040440848100c09041230300500c40f543c00160040014494208403601ca80d03100006c005034404e40351500180c42d40e1488d081408a1001007502a43c044802001d1a0a141c45440210b0046208440381010244c2e00d880c441e0075076680b44101e00f002d080a510039941580240c2500029500c6030002c04000c1ca0040d002032903965082d0f804403070141582d16894200d0340102c8a407500030b01c1003c85850040c0071a4900200d51140d01214002c442c0c44101c08810003e50000d004042016440207002160322001081d43c0c54202d8070056a800704054046291003401041480c180d039084003070985156501141c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812947284 1250 812946034 812946047
    0x807081b0f040b030c060a0e040e01020a0c03050a0c05030d0f1401140103020c16030f0314071e08070209010602160501090b040603020901140406050301170d0905010e01020708060a0509240106 84
    0xc00f5402d4000c0e43c00701d40159403007900801c403510751505c0b1620442a5038060008998050707109000c00c2e0702c1045205c0c07055400615100d0020340c0343c500f095aa0401d108102e900414001e402002c03480041280c0d481d00d076080d00031183e520403034203040000403030380126071400c0603081c4600e4911035185841c1c00d840e9403085e001000c4015003c01210a46100c40310120190794450b40b0540742c41003000d845404150b44060120300107400c058030035040c04915114160410482c04001041000d4506603c04020856059500c440c0d00144411050742c0d5424020391550518010090b01c010b00d00c00100352903014031030f07400644c3e80070042e890420f810443c00364000d51111039024140302c5551101c000c441002c0c0c2c018005810320399502a02e95151001070320b403400e00341c0f0586205801c640400120342c0c1c2c0c0300001d04101c9500b440c1041885448200503801d2038a80e8000800701e002d0700003048072405a0350401da0207401c4c036004459490100503482c1074442030070120081c1c01c500c02c000402002d8411403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812948534 1250 812947284 812947301
    0x9020901150302130914010509010308090405040f0218043e0402040b0f0901091703070b0402120a111503090304090213050d0b040c0807080c06071b0807081b0f04 71
    0x600601c0d240d04070090403c4c96005a1144007501d845000c003d03401c0a2015645006120941d0035501c954156541c5030254000c10301940c2c001c0e680ca40c005010301c03c4540300c0e00f00079500a84900c00707a44c06a0056861000100c8095440260304079000008400400c005603440404850001c00100300c144c40c5d03c048040c801249900c04c0d001c1c040031941c3d003902c900501042400d104000d50340c2c07803408009002080a40c5c019211209180d00b4030540d0a000f01c11203940b540d0008010000b0754072840018480045c8100594561081c05462410000345e00101144001c084458034004894500204803d2008a0f0960350300d81080c4000c019201c8c0b642c01038802c0516218050844d03030b44950215600c0c4540a5060b5401e201c100240400d00c03a8800f0783c00c01410304c0c1070103404110709043d0815038555110305000d0040d080064500c0034444920b590030b64403c00d4400c040446569002c5d8995980001d000350500d034000c007000c604c2150b0030030541c40c1c50218040c11018588207210100001401141d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812949640 1106 812948534 812948537
    0x2150417060c071a1e01140102010e010c0219152c010e06010b0703050d3206100c03120507050301150c02090a090206070c030f1103010902090115 64
    0x203450200c4141c070707a005100e00c9901e86481701182401292003190401c2580d600100f040d500f6819481b0086400343e0007030145a0000f010f06080301d00b00300c00000943e11852162088a50403074030078176640e0262140b4204480c15031580c1c0251250759000c07000ca40c00002c1565183c9109407120030b00c221a0350000c0000419030408140d80f01010300a0003080e03c0040f07007400426205400700d980360404110709019400d001717111003829040c000700800302d003485184aa01c209042c40312140c0305000c0213004600d2030f0318560701030320141c030049025020040e0145150b84074906074008d40d800b035104c81e6030381545c9624191454403020b8000305140c04004002103040096501d107542c06070401e00c00900042c421495100094940c0b01d0b460005103103001081002041c0036658a03002c4a03a4004c4d08441000039101c03003014220b44c03545070001c0d400310010005001401c90400a0120b01019 = true := by decide +kernel

theorem cover : BRFrame.Cov 812769784 812949640 := by
  have h0 := BRFrame.cov_init 812769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812769784 ≤ n) (h2 : n < 812949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
