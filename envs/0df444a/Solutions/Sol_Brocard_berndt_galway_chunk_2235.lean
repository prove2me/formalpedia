-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:48.142153+00:00
-- url     : https://prove2.me/submissions/58846502-270c-406e-b45d-ca6c44dca112

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401798561 ≤ n < 401978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401799811 1250 401798561 401798581
    0xc0215090708060f22030813140d030c14132c07030228081b1e041e0b1603030f0501090c0f091511070e1003030e09040515 54
    0x1c940c4001c8041c0944001c00040716030700c0358003600c5920b000b40403480700d50041d00d5602c641c00c05107100401207403200c00030070f10700302c103944000080b03a10882c00c0070100030352031038803528107200d40080f071300041d440346400365242794007017051040b20b1580b400e02400c08801003001c20a08001c3d0060204100f0781d80c40300300300360143e003010010140100e81c151040c1c3c1000303030000340a540402105e00140e0400001c48a211030640005606009a660360540f59111903d4254681d200001d411024400502007204068004c1443e0310100004608141e5142e10b40400f050901d00035640d5400507046000040050218150490345d0310710103a0185000c510a91506600600142030420002d614000010400702000e601c901c2c1d04102980f0342c00c26800464004071808a038a004060300e228002c0c1404100d03601034410000c505420704292429a41c85441c0030381000802c60b051034a9900d020020000e05400100d42c040d2141c0903505001c491600c2d8170380f255142c0c03408912540e100c2c3c80c04001007040c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401801061 1250 401799811 401799823
    0x6090606120c3d0518030d0e1905150a0908031c0924052703041406040308120a1104051f051308060f0604050105090103120201020d02030c030a0f0c021509 68
    0x5203c8102c00700e10f54410001895a009441c1c18400121000712115003480d0010b548118400c250307481d075200d10140c105000011030f4000172450712160f03450000c00c10b03a8401d04402000c0c161b4900f495110040140e004010000b164401d81a80c0c1007000004c082c207a07420546000c5603240c02002c80c0030030745c603c5c10910a00342c40c0e07614030064003d0b0681a00100c800c0d00554090440e0381602c02038420005400c40c10380611110018103580100010410302881c1d0000302c0341b4002c024040c6040a50ba0384440806d07038009000f119040e080c91003001400041481402740540c61140e8041c1001c0c10100400c0e4030741d031603601c1f0f11880d201302c0c6100c41c80503101d4001c44400070b41e0485450300080d0317030b0b071020350791900296090b20100c00804005070940c1418400d50307040303420080100d11164a1178a980313040d01c0004815404554080243c0488488140015405161005040da0b500d1501c03140e000d040340d80c1c248020f400e050400f40c0070900d10354002480040c0e140d0041c1042d907242c031510b411501e444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401802311 1250 401801061 401801149
    0x7060c020c0406060c0b010e0618040602090303070308040501060b130902130302060f04030636170a2001090b160c06050408030f2208030a0e06090606120c 68
    0x15043c00d00105455134065076090089210f865100c10300e90325170f902c0031164003048600b5a0803a001400e41c1c281460051140364100c1d000f041d0061603d510b0b14042810343c2d02164007503021602400611007048401d01c240710081400c413440b00d040c039001307203040000005180300d05044582c0104080444404c6e180e514001594020102680d91110500c4078419400a00c410b460b11761800c1c0303203440144035a2051441103206000444444400c03031490a080c890b0310b4a040c2c902101d004103040e400c0c00680010030345e8030301a0310340d000540e00b05400080015000c905024459042800d004001513510000d640c000491182c0b061003100482402c660302c0c2080407000d001c07107003031100340400d000ca1040158010700030602d100800e69103d001c0c00f01488882a00480c440d072018a10711b01041d13160001c1c60f005a04d000020890100544005141c8801921070141c20b400c0079044c4007652824000c445842d03032541000e0f010b00c4190400148110040c1c1142d4a0442d040780d0030300c040c40552000601000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401803561 1250 401802311 401802319
    0x41e090b0904061a030f0f120304020609190306092102032106010c020409110a08030a09090b0a0504050f0702010c0201060311090405010e120703090504020304050303060f0a08100b04050a09020607060c020c 90
    0x401c0001c5981d440000c00e00b0049079010301c1c203410302d40c808c1800450b4440c680142500785846e030403504ac0449241c4040c9144030281c690031002c000142540070f03030120340b80502000c1c58907605900540010641c0080102d0544d0300801c4500440d0359282420404124030b6600e49505a83d6980107079000b00303031120001d40c0030345807003980c3c8100018002d280f107030f090341600c1c188429925103a000d5520311031030910303a0106424083c108401c0e2020340000c0340707007107000c0d103c240c80344e595001040c195082170300d4218845400c00b04002070b003a42403050050300a06440240842031541d11130016910350740300024002d165240001c1c041c82800d40142050513842000c13500d50f01584080401642c004034411000100030324400201441c05000343c0c0c0c09590004c2c081c52646e00d642c030030404c4040f003007420607802c86054900001e585505001807034002404540100707941d21380074108000c81d00010708401125140c40c802001588480c016106102e1f480704000448010703d00040e4545041c3c60401940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401804811 1250 401803561 401803573
    0xd021806031e21030112141c020309011206050a0605030405012406020c03030304080412050c030f1f0204030b0118060915030302061e15010c0503041e090b0904061a03 73
    0x740c004006a240400c2e0000314044510b100484803d41c0301c0d01c030130b1040403c8185640d03440000315084425200680125608a4004000300283d5900b4080c801e420382c00543c10100d52960715582200000060180300d003000c020040c1070000052036503280307020b1401003010101c00141004000d6001541022107224403040e00300345032032110070342c41c0395020300d00c01409000f00d66022803e0010030740f4090f6a200a8080c113250a1000600c03500c1850401070710203210303050320505c80d43c50a00c40b030f98400360a4070240032500040d004144c44900c2070150710303075928030401040002c101c9030a00c45064401d01080c1d0601448c651000c40e0141829800c808022440d1190350b01080c1d50401090301200d129400ba2169a640d9000322043e01c5185050403403002c07540c0001441403150300c0d1550140d45014100300c06207200d1038641a00d142c1298100036103d940040204064640c0040c044000307000010003807148604040200d880300601801c0101210f031203042c2440c2842046110440c00c050250803111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401806061 1250 401804811 401804863
    0x30d180b0c090109080102070c05040c050d0e0313050a0b0a08040201051207030b040c02062a0408030c0f070b130e13080a360e040302010b0d060e07050d02180603 71
    0x400c582c4040c0781d49000c6010340400081703160040c0203481c034039600411080c04076803a1038184006404529500810002d042001080f1070701c3e28868100c0001d0910010358850548990005516038903400851060317032518001c2040503034182c100d881d904614500300c40e558946d440107032460b01a05e4400101410b0540420182591543c03080d00b41890403101030000e240060307003d98440300c040c0c0c0c50480190035548103200d2000713045003201108101d000c019107000c1e590401d090541c0c024200201c0786401040c0e020b03100300820406040a484007103469403900101c041c2055004000c0e00c21012501d10140020301006100e1004821264005030090750303074120340000800745d24600c0710300d05800f100d280752040110031071040d9090f200b10500710124240e040c07851035a403061b40144210f08564890081e112540c840744035051115100d9440401c440e050a07910909001031604098002d0082001650250b078402c1c9214200c0c1103220700f01140d1b0340f12140428205003854419002c441c00ca600610 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401807311 1250 401806061 401806081
    0x20a110a0b07080f04080d11160b0f180d0305060a03061a041512080304060e0a0b1b131206091205090307082e0902090c04090506040c02030d180b 64
    0x1500c42c00d000da440c01080d41d1030901c0503002c044281e44c0500700030000e20402d003002c5010340c841042e00c20101c0c0c0302ca00740040e11805810603070b81c80108555410100d820f04c0032003818404c550350025801c0c2d1750b04545211003610035540706078004011041544880110740300351981c43c66203003d9a0000f0382401921080710b80244119001048039009524001e40ba03098040c42550410990729041d100c00500001d640350010250005030007076483c01e80e290488040302e5010041581590b1180b180012a1300d4001c1c0c2248580c89440304c17102040c002000003602506805d680c0000b5119442904c0030504003509120000f8200442e008007034010031950111029000300c041c24601b0b408400b142c845907182d07011540c85260494005283c0c084144941002c14407158500c602000303080c50000c0d204d103842d0001551260301361404001c0700d900080600c82c50700140a0345502c1007003520244410200c545c4020744e284202c1065003402642ca1120000305800382e1016030a0301c5e0007041003001030920407114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401808561 1250 401807311 401807333
    0x423010218010f090609090b042c061807180e1002130504090f060e0a15020901200a0b0c0912010204140307060903060207020a050d030807030606020a0213020a110a 72
    0x2190201e810709000c50800c07441604c004d82550f201d5543e41805034a00b802820140921414160744280c980c201031428804820300400074007403101e80100380c40100b0000c14140710024001000404510340c13180203a00c000902c407800c80725000350540035680760a010900628100d904003090380501c034541002101241c0103050402c1070540d1283d5403907500c2d41000200c400a90000f80b040301480002800b00d2015407105000044100a950211281d0782c1e4409142c5006503902175035075804980031201d035078402c0c5a64041403c00747d07031100c00b904142e841569504501d100030110041c0c000010414152282950b540781070140c0040198181290428040c1d002400380d04850005081030183e14600019074200300c0b142a1201d00807182162030b00006584600e03426604021403840008264461980048165001c0e0340d441410307041042e070003004d5440f2940300c80d086500102000e000b45c4c1e10811a100001e8040d200140d0f5500260000e50300c1d65220556085640541d1800b241849014516 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401809811 1250 401808561 401808607
    0x60c210815040606081614042912040f14010c020a050d02071220091302090f1506090a03020603090f0105100b0d0b0102011d070f090b01050304230102 66
    0x85012222003040034801242d0084c86001c00140008012a15900a02005d110301d0009480e242403843c0846550709031030b074810b40c040c0141c00c010882c981c40c1c5078101000b40440c02e8040b8029440c0c074000c0c10700349010150282c0060881d1405200c008200b200c503050a10308065010700910061284800107503c4d035074074a005075400c2c05000d44440c070240c4042201019201390007048004c0b0519a29114604045104502010021020201529a41c40303106030722071a84c032030f40c0c60000c64003803040c0002550b000e030400c07003c20306843c00c1c86006001315407480e2105106480316622a2400070000750108442e5001035001200041032000c03061021601107115805c040090001e91560307104441c13241340313522a00d10000014009209054580c0d044240400300500c00030036080400d8440008800c100e1340c100d455079003d020300700201d1041301c41003401007401740820800000301c2c0e000a0b045100091005258540ca880d5206480001120002d070004a05c4021034958120f1441c0003502450507030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401811061 1250 401809811 401809831
    0xc08210907240215181b0f01030606091415040303050903060711061b0904110c0f120723030703030902150c0a06020a0905030a11101701060c2108 64
    0xd00c40381c52590b0303a01091003607149035008040e0f4084405501c0c06800e80900000039144142090304284c1c0000c010b0b41082c503d0030842008610342d00c4e410002e9400881310300754149410700303100b045129004048002283d0404c01014064002c0c140016861184411400a1140e002c50041300349a07100303010b0103035510281d00300c480035160b0420941f02c02c1d01048029046901c02c00008410004520031801d109402c103048a09100304400018165900520480b1065001090042d0700803001c20044290745001400760481c0e0903160018660f17481070701c6001d0501c1c5003200700c400c031245280c00f01038611741c410405da80c0c070b910302031500401810311f050b01030340300d181d800036610340c1003d40c0c03c1110400c107285c0d401041811842d5981e903020b9003040b104039080c0a03404000255584060100d006190710411849017036044282c20024151810040e1204105514661b0340450249030384603030641f5050f042110700340c1220315040500d202205440201e1030b02c5c17440c0d112212900200c03081c2c0520200300d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401812311 1250 401811061 401811089
    0xf040308010e09061902191806090513110405030304060c0b010f260f0a0b010306050a05010f090e030d0e0303060906040c0207060318020a06020d02010507020109030c08210907 77
    0x3051020b8a200560b28010950000c02c04034a603c2d1081a035450325400f03030b00d000b500f0140043c1611561030b800030303c0140440e00c8480f4025440350f0099100b0081e107010b003441c1c0d900781d04040200b071649201e480428442e99540509040100643c0203580060400a003225500c0d9250800108625000e1404581701c541c05000800e8001046480d0800c0c0c4504000b24160a20000a4149200300c403108400550040c0080c3d41403048090003400c003000e0103032480200c1940f452800404a82d001810000c50398505001801051801c00280c0c04460350741601040700c1480d00f0301507065110341401602968605001d8003d140e1010019520071074003102c1c0e2100f076a640c00103000c08e50b0701c140e0382680142c110140901c5154000c0c0d008592030030100302052131100e06a808108061a550031a001590142c58008082c90f0f090188652113a0903100910070601d43d030340c0192400d0b940820060440601040c840700880241446400c00c0500c21001076150a1a80b4070784e4448445002e0603803085005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401813561 1250 401812311 401812319
    0x1006080102120705030a06030203070611070f0b120c0d0504060c030b0f01051603020f12270102060f0702010b0310050601021605030303070503060d0b16090617070f050f030f04030801 80
    0x40c030a03542d036104801c22180c05541c50000840f9540c2c03009002d0982d0b990780b13080c04005070b20204411009409107855454419190000135031410303003940d0000400142c1600c003400304403000e0b0181c50300c102406c20403500302d03219840100d20900070030f80c0c10700500f481c0000f00001c1c0025038015850218503030300c080003008081403d0001d81d6481c54020b6001c2a4100701d0080003074032040010660318000e105480f08024060101da0074042000ea408411020105060401040042d0350040900c0d4600e08000d0049034040040d443d058000c1c5008801ca008a00040b8164000c0d005910f40e00401400e480d03111414108900003030405980c07141c014442c0301c030900030402510144a044d00c1c4014000d42c1982e41ea0b5a0481c2d042e4001441940c015201040303e1000030540c0e1611401100181c81c0921080115040203062a0240c3d1007802040700c038104060140c03101020080c0c01120034605254904404202500c41d4456401d102400d02e800108000c01501141d035941e020750f101c2d54800c0702c40d903a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401814811 1250 401813561 401813563
    0xd09030507060e06152407060b150703020a02040221251b0605040203031c05061017160509060f0d061707060f030f06090e060f0114090402061b100608 66
    0x4c03500d0600380b0005109a00c610b00d03114040c50b032980d01500504550840c501e03106e03846608030b02c1c02124059210340e0840b441385465a000e00b20445000d50b03060400c40f082d10025078902202e880640555070000c2c0f070465460040d0345060312041521944030050401030f1304c0f00c5c4410405c0315680d001102c204c840f0a6198030030385a031035200d0100421010400341d140c44030350040c400175108a074188010000880c24014084640c094140300140c0024a460300b5000c1c4035668140c407ea400c20882d10010810507003001d42103103030b080005c1c0c100c012200105808141c69030311a2040c01c41c1d0024001c280008003010000c000c124030003401d203007881441c0c0d031160703600ca61284190312825540c000e035905002071480340e18604030040e018074012549060000d080c108403489030300807525040c0c88412109000404114103508403083d1000b2183d6503140034101c006030820041d91503c07400c00d0102003010356807520b00755400010008405e06140d030403608940d03a84c14800d0791510035a410031000140d0500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401816061 1250 401814811 401814823
    0x9020d0f230c09010e0108070306050c160c030b0106020a02010c06051305120d060f0501300f020403020120101a06031302011404140f01110a111914010305060102030d09030507060e 79
    0x1156401004401d085984400240bc0010300304a00050180003620303209112080301c20030709008508041000703055051222001e48160007400540d40000300580050b40d00c01400009260002800240c0342c44171841d19011120381340000d0200d01c5480d00a854922801c0000e0003e090034080c01c000066444400d0140e080c0a441114040348580302c00e00010007021403551a10003c0d01d0380204155403402c84102282d900c10245040654080740500455800c131203095601c0a41011007640e400310a41c3c00e46d50740307a0320701846001544440c4940c0c0030800385d540d03e6090081c01000980c5038a42512401100c83c03203500140d0014481031450300d80500c4040458054940481c865900c1e641220709002504070400e04c5241080441070321120421010701c16a0314451181401e109100c25130341c20403580381e01f40483e044011f41c0d0002c042090032107908100c050f42c03000782000314550b59060010303401c60240c1441c20400300d040403807800030158050003c02c4050320502080218289088015075200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401817311 1250 401816061 401816069
    0xa0b0d0f090503124f11060a05040e011508010b1206150c0604150c030b0906100c05120301090f090b13260408010f09020d0f230c09010e01 61
    0x81c204201040c1c0011440111542c00b945400000728040d1780b140c40c2c100307030464080740344484400d140c090b010401d040002080d910310070020f01015085407501d41c3c40d598006541010300c2050001124003c0601030b05c03d41e0700410400960f03218541e035032503122070b0311103d0710418000901c03140c0021030139010040560b946508d8031484d440d42c5546070030503c8055100c1e00f1025645800a0045c1d180350714081060a110b82c0c03007600c03c280c203200b44032002e03001e803407a601c120420702d0f042440d00c0d02c80d44c0f00d04503100c2e1310500840305001c1140c2e09001c152001030100d04e01502c24010035030507105440140c1e0003103040719541c50313041003004c42d542825002c440c02c44a00500c80e500071000714030520201801c203e1014050b001240441100f0201503120806440007805425008541080100428480c1d45501c02080c0030070f04c00d0540030f500145c01d0305080200184008100140001409030000d8003009081090000100c0c08201d181801d81d035800e400c940c0c0344184031410000c9800008041d81c03504072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401818561 1250 401817311 401817313
    0x507080109080f0f09090a020702030f061e0a020d020a050307140f0706021e03070f182402070801020315130c050f0708070b0f011a0a0503011202040b0a0b0d0f0905 72
    0x10421040820070f85500019580c03209090600c0303800042e549501c0305a00805c0101c6c001a070f18035480c13050505112110803192800e0300040d080081010a40700a038000e91103984000000e40e4030700500e13100a004e40c00081c4040c80c80854107070f10954110300210300407095034681c1c0707452008400d003803811480b40055a113000382c0c0a02006001a040e900a005800e01141c90924107801c00c084164080d0412100c94000960f00b100c442140d503040b03c04e4480050f0a1050031090500340990b200d407100001015140282198901202c0d0358030078010700000c0d00090300259501e090140034012410711112a90780300d0103558541d680500c819200b510924105511024146040291291030036007040600b81c515100812205000403283c07e0b0700e40c4210780140e0280d1443d4104a403036016441d07400d2240ba0407120800c0089546608081507a04507800d0701d1440d014070782107100bc0390140034600c03111500300311180342c08540801c10700f002d0210009011020811010403d0201c01a641c9150001d482 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401819811 1250 401818561 401818567
    0x70803130e10080c040c02010e0307140f03031605210a0204090e010203060325080a05011406060901020616090513050106140c0718020d1803021c140304020d0203070e0603060f0c0a080a18060207050708010908 91
    0x40c1e4ae0140012d0f00902042000031082404600b20400100008035801d1046070340c002401e01604516225010085544030004c50035440c0c241c0200c1e07980c201e1440d5405944000030303017407550282100b01d0381002d04441c5050303c142ca0500d01c5c4c658040c04080b07401b144c0d00101000001d42c50700380300f026100d0a500507401031055483e89501350081b1a044000c46007000300075180030540303441c2e041c820448240b44c2200020558908100100074000701d501260408004100200100d140000e401046d1105040301110050115240784024032607810040980b5040900305c5450340010240025203a00035002d4515522041c200080100071010300c81c404a4142040a00b0040c0c1c01400340d84c0c000e00c0906094604860f640010f0b00d41101c540c00030811072201c1f000c100080c2814010f05400200b0b18254402c9070601072908619400350104400800c507400b00007401c0441c1c2074004c00000b540c207800c040c88089507400c001d00a584844429101441144800039009205220328128107401c0070300e82d81 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 401821061 1250 401819811 401819851
    0x105130b071d06070f0c050f030312060402090a03051b040e0706200307050703031b020609040b0a09150e0108030a050306060a02070803130e10080c040c02010e0307140f0303 76
    0x60450350201c60210404440c82100490f83c88010050040501458904120803c01d00d001103030580d080c0c00045c003507050343d000b1003620f41340003040d80c0303490b40300001c1400241d56010214000703001d4861940e51108070024004180200410030038611908030300705603074101848050005035190b5528070321995010450030800c80e0310a8208007103100c010a6281c601100c0601c2551a60304001020340301604195801c2081541000002c480594a20740c0c80000b0025038000450070b000700002a070140391141210061039864514040c0030340381220302000580c2e0700c402503a000426a010349004001e45070004103191500209a82d5481c03074643d0382c1c1c0e185039522018080c15401580060741035102d02200410300c814140060312018800310580701c00f1610309183d0051100002d840ea1626102e03108091004c00000301d0403004100040c1d90104001c1510f400c00c030f005004d1602d01042500003c55150100202046200a0104000c0403900c01c0041c11413110703260b100035500b0515a00306405040c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 401822311 1250 401821061 401821067
    0x409030e04090323040e0709030308061005090d0c061103120c1e0f071101031e0203060315090d110f0604150605040e1f090201051e09060c0c030105130b07 68
    0x842d024840d00d480c00000340315009140c00306400840c4503c00880c003080c02d0042c10100305001d6805100b500d85849040d140d034801800031031003e840305015a81440c44c07001401d01030802c907200e068018203034230403a40c2c5034140a42c50701514003d020011300d10110307905101600100340c0e03c4940300302840406503210003202c501d0f030ba03120070344202c880141041d031407842c0700702e0a005d0014206000c0d1940da945040b0300d080b020100a058160b1305161a06030b400c8202c40c000786a55481782202c41c4010394035147e100c00a071030300300020700c4011012200c4041002e0b18402003103100800340713907846a91000d002911100c2d00c0c1ea007015011046e80d800200000c010900752000743c1a022842000012580d4a660129059403025066040c040d801010010fa910500d2004c0740c0324009007030010407000482d640000e00d20300c0f0344800321a200c2002e0b03803010412074200c02203942c1c0c0e00000300707826541c081c0032010a40350203854138498400c2d4a400001514031a603d441040016402400c43c0000d545a150039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 401823561 1250 401822311 401822321
    0xb0301141206040b0103171804110903010e01060504060e07080406090305040e250320070c0801180b060301020414010f030608070807080715091206090f0f02010e0409030e04 76
    0x85070740010100441074015a05000e05401640250740c09942c0e0b40c1181040740c0040c0d0714039154900a881080100540c46544d0126200318000722070104188850300035088160054540182d81540707402c8141c00340c10710552042e01120070540c4c060282a0f540d17506030084000869411000c210100c000900040c0c182e480500032a101e81000b40c1410744400104d5505241254100303c071049100390380c0d0300511900410310004035103180601050240c0110902400320040c4112801d8101160820410500a01c40c030080d03c8500b0007080100300a4404000300c281c0d803170068520300c40e444007141d810300307041c0201c405861003001d81c1d440b1100c02a0046400c09030b150058800c159441e10b0124103a2002e1019074002c0884000402a160a080065044c0b00040d4459100324000107060822143c1008205003291030403541c5200e06441b0781001d4010b498a498000c000c080400321000c10090458080c9800d18000c2e07139003002c2040318406010803102440720250200d0483e109501076840c140d044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 401824811 1250 401823561 401823599
    0x403030204030606060f0314060f10020a12020a0210030507050327060106020d0201180c260a030207060e0906090c0a0203120c07030311041206020f0c0d030c0206010b040b0301 77
    0x6140554030349890f000c44960307801000c002054040c00a4509030f040c020480290a54404422541800400500c601c90008a4140500c0c940e04584540714000c0c403c1c1800d46e904106103020081164a000351144201c402c100c1c861500e00c0d0107943c1e2a0b200748500e1b480344105880341e03440e40d03c0d40c6115004a500c507590088a1280750384e00a2607040e400d205c228000c0010b60000c4c04e42d44008030300a82503a403411980040d140c059480f0b0004507403181c10740390454000e4042030401076918032030313004c00d402001500b076024494050342c041096400224402159420340e14891240c2407a801c0001504080d1891a80400b040f0007007420306071868000c065160050040b07a140c0042c1503210030204100b2030304942820f502041c0c5105160301401101c1076004c4400d0043e16003414050181601180740030094409940414103081c0d012254007100c0960800d04202c076060a26280014041c00300b1090850050085100000f4135103009c80035a0195204d010442c3d00f542c1c24010400e00c01024045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 401826061 1250 401824811 401824817
    0x9060309080c0a111e06090f061b03070605010603060630090605090c030102040e0c0705070b040e1f080a140709090c17060402010e010e0307030203010c111c170403 72
    0x20100724800030019001e2440c1310301218221842000100000c1080240140c0b01d280710003110306400d542c8110031610302101c1200c003d5040d41c01b41c000b10750180200504114004110008240c0c0084000082d00203a8403c850600c26a81c03541021810b4405620649012506524032000501d1140100041c2e4040d00326114088010803c0f0301c00c00c1d5802d051094074117560380c5040c802c00400c18010710300f400d00c080d0001d41c505840d00344207400c2c08200400260400d4400705903001000820302c03c07e0010314a5003003140d101c580322020904000703000c2c0e60460313490b444519a44800301017503644100711100400544030b022410749900340403814191030020036019a100200f0f6003045803180d40d44440c050603c401c090b6003480901d24a4640605000f89660300c0b41e800c1000607a8071076100d0721214028608140603045400c00320b4901125600025131550070b11500e070300d035540e006420110750b0107482c0c11204041050204130801d4269510100f0000c1d424021040b1100b1007444880d4006129203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 401827311 1250 401826061 401826067
    0x130c0b0702041e0e150f04020d06020d020d0b0f1806040e16030524060901090b010c0203060f150612180f030d02070c23100e0a08010c110d0906030908 66
    0x400da00c4040500400100c290f01d9070b074020120141010422034402000d51561040141440c4007280c200160040000f4419450043c6000800c500c640644d590b070710113140d00395200c402e03848048001e81000407906001d242003000003060761801d1210419105032002a1034625140c0c0000d0001900f000c0d8855000745c4507040c01150603002a955031002903010310083c15180e485002c0101012520441524000072580c00f409590303030304c14004504403620f140c00090a44110001030b141c182c60124003075418001c2008000440c5040f2407054841c40618140c5140f81154408010b070342c1c050003040360742100140d40028413122081044c1c06149aa80d8121205d031780a02070140c0c1f0f10341c80385000019013034000c119601008084069031000e0055a9a03200c1d80b000c1580040b01403001d080c254510480b030b0540328480301ca01030108020403000c060000614a03403111030081c0600108c00c9000d00003207001d644072607040d6000c100c000c00c4e4009640c0304031101c2c0c50000d00300c0c064030032a542034030303650010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 401828561 1250 401827311 401827331
    0x20f01030b09040c030606060504080c060702150a0e10050a0e0f040908042904270605040921110d1409060415020f0f030901030f02040b160b130c0b070204 68
    0x60b000d0314030940c80f401d01196080d0440c41d1030020796021354816028070030103001c1070241c510041904c41c00c0100641e601500c55a582c0000f03070f81d4148008680e40302031000954280f402e5031084d420f085c4000c05803903800c1306c0c08403080102d4003441581c800304006170707840d0142c0e4000d2801c031200b52000e110080c0046102c400d1a1600d83d2030754800d41c081940300d80c2c2c00060340c90303203c0340981e008214625204e18030f05080c54604410ba5030001441800d0170389940c48a24a840d01490317004001404029004002e032005a141c030460312513290200184100740d00c2500303000e062194680034244081100034017400c1886000680e030030380100309001c107400001e1060f558151140e002400080050307448401528a079814040c1c10100800d00300100d5400070b5207803464a000000464031540800c1c41e001455440c0c56021000034011900040142c000c0041e841180e00f800c2414003d0040c05019100002d0b10349019a45007084001001403c2d1040c001c2d0401c100c41816000e08011400680081414080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 401829811 1250 401828561 401828569
    0x803070b06030328020c01020c1c0614010609030203010f0504080f070302190309090c0801230109030f0c0608070305090606040e1c0305011e030c15170103030504031a0f04020f01030b 80
    0x5031030401d00d2040c00000d04410b84da6810010014090828005400502582000304442404100c201141100000090410010160700c00603504040790a12803595840304d1000700030080c90310042c2d200e0340c2040c01c620030b10503140c4160760040e644004050702c1c10b51010600800c5401880c41078003503000302126038a64481c1454000120341c40380d40d403098040d0800600740125045140c0800800c5907180041c00a0300440203082680765591041c0303094117030300c0360040350000d00f0b6400c02041c003031084003450308202403004124145d81d107944802410f079850810480440b14119040780c07550340100080b40072402d2990100686109200544443c0003400d4608002406c5001c003160000b9910401041611594003a00448180146810003414519103d06510000c18050307000c001366011f4510803901d0154100004140d2030000c3c51440350380d85c0c01c0181c40740d0014441901c0140700f503032101154640c00c0b1032983c8100500c4240d1405c68646809020b01080f0055200b414160f9031078808941d903503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 401831061 1250 401829811 401829847
    0x70905100510050a0f050d0603020a0e090d02060c160f0f14060c0f0301050f03070e0403030f0b010f02060f06040e100626060c0a050403120305060109050105040803070b060303 77
    0x210400e02240d0649008240000880110004010401d05101e001d903490b0303121391100d490301d0441c600356407550484450b1100401c0b5650000b54003130405140018031606070138805210300240700666808100c80b00041c0d0720382d8812948825801010042841c142c01809020410035000b000c004c40202519a624004114805001e0300c0440c2c0b0700d4030b8020140c1d0200010769005070300e01281c608103840300b0040c02031408103004151040d04100c450250740d0324100400402400c5103102c000340c80c2841d04001d8018801840074a044034180b80707030b142c0c1950044140341c01c81e070b80c0c1e45e004100a03982c28124401168010701444d42c0a5251400701c01e070359808000c425030001d1074401c001703002d601d0800c07482d01030b4501c01c0b454041039010b11419101c0e8080800c0142e84950302c41c890710b940d40d0b0313200411104c61050b0b8100401403c0c080310101e0303c240d40350b03001900c5280c0c00e880301c08100751680300541e4240240e1280b01410ba008020744000201c44d1030030641c01c14030203401c880c240701c1c40f0340b40d2408100d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 401832311 1250 401831061 401831071
    0xb0109111e0d060605070b0105190311040b2d01050715020306030a02130b0102160b0a0503070e0405150102210d0b13050a200c06011a0c06070203040504140105090a0e070905 76
    0x8078041117840621407407c0d082401001c04171103802c1d0030040b141c2c40741c0140c01c107440040c00d194071501d11074401d07440d030341c110900070807000f003441e400400b501c03550348184110090707410902c035090b46181e10954040d0003150841c1d500500440c210b402013000310b034040e510090075a5013601404074000010b840f82900c1804c2c880920700086020400c03440024504640031801c007024a05031002041000c41880071186ea400c0103242a960366a11600295541d00313101c01e071950814900360410060180c444108091280260b00340c0d0b03074451120310044204210343c0700c0d550882c1d5040001045820282d408440160001703803182c0809411003c40c80c04883e0103c89c45540180c40e580700030b04a607007004042c40048058003200e82029000c0507025614081405106100c80156040054540d801c609403071860030603208444540c40e008a009440303400c24441c05002c2c40c140481001040350403580b080c10b81d90080c00c12107050303551340500c1d00a0301e40220110500e001d801c801140381d0215001e00e13485a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 401833561 1250 401832311 401832317
    0x3180b03010611120a080403020312010806010312050a1706010e04090515100e0109020d0609021c0c020a1713030c080c0f0a121103070b0d090b0109111e0d0606 70
    0x96241040c05000400f500f0712001003034100c1502c002c1542480701c26180303001003614015441d40d40f00e10b001c1e8034500c02c0c2d200c102c0801b94645c0001a1144001a8240c1038912800628440804000d01036400e80242e0403a500803452500300101207a61900c81264044014075081103d00c201d080400d0071079240344015034598000c142c0b0414041c000503a41900403001c80c0c4004001840e056584140000601812041c40d070005085600e0b228241c010b0340140400321030865803211314551048120882400030f40840c0c2c2002c214144e99800860039100d216045400820109032241e03014802d5881150b907000401204180030010a030310900c4030026005c80c0000b4800c0400d044200481c4200108100e803044903150010300000d02010004500d080e40704018070069140100040e0a09000740c101c1c488905000c11030a070800345503001a03111900032400c0000c566240d1100e01d00b44e84402c40d41d00b001202c00c11000c0d0400c00c5010480c01d400723941c0d150079802c01c403607000948241c1740194000800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 401834811 1250 401833561 401833567
    0x80d0903090504140a0b060a0c030f03111603090906080a060209030109080a0f021203010312110a02030f010c1106010b07031407170408010e06010e0c16021315090e1903180b 76
    0x80d110301c3d00c614246e206007110f0241c10181c08541c020f0140d10021402070407c00303156a251801c6002c1d4020b4420b508444180e0358982c000c144022440d075510f03100036000200800000102080340c0d1107184280d800319000707404a41003a4460401070760042c00141c0d059075076a002c11000c1149000545151b44080c0e4860211198180d402498441500c0380150000d0f01000100002075204d01c0780e1400e8075503410040c0a281c01002c20781c0c1003407200b0902a42500a0500d140b401c0d28040d44000100030480d15190340025114a0300e41c0e855109029041c00814100180c0c00886c1c0114000d000d5116168040d500d010959520b42841d03400500300e204142c2808182405420020b00518600308501d4004202d00d61400c4120503d4001c0074140f010014400600c04407000c80e4440e0b0100c1c065000380c15002c0c9070020015401c02469101d0188000e200c580e81c0109040c2031a0040210b04003040d802002c40d1803025804541c000760346030f022420301c80140744006000d1104441c40000701014100691 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 401836061 1250 401834811 401834821
    0x40e0c0d2111210d0609060f08070b0403081b0f03030a05180a121205090601080706020615060322031808010605090c0f0f030406020d0f09080d090309050414 69
    0x1c41c02450100000c10300c400c400851a1041c0c00040045812030203007101e0b109102a140e500240d4424420b110303504d0750401300d000c0b036602002e0300040111400303605080c0300e1a5840020b030303440e05014080d40d80417a00030801080820b01c0c00c1d025041d1018a441d50700e80280700040f01d60314200e0440802c070382d00e40010007040101c10680c42429030000d0002c0d02c1201440005035000d46440b40e66000030300740000141e4028404d0f10901c6403148400d180c801c100407030b061500f8500e03554000bd128142c0c40f40310708640448d070305d4404140c00c0d02607603801264803045136045040180640005090852840b910303052403c0b81d00b0b840d8040306184d07010341c07070700032000782d4039003100d601405c05070032401f143c1c0c0c10301c0400c00c056116014204c0c0c4c0b0840e049041c50701c601d04041075030b082c0e10a0003103240e50300c40b01000380014080f03a9401044080c1c0000b00c20408174015580b040306a448807040940000414032048a80202680100080034842d20f0071341c170172070b455500241c11280300c50420300c5860b140f802000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 401837311 1250 401836061 401836103
    0x30b181618052502010b062b1b08060402090a0909140613030302250803100906050105030705070201020c060a0e0312160206131511060f04050c040e0c0d 67
    0x10740030965181d0074400d92400440038031821180d204040b52050f522012a039880d8400e600c41184520002c24003980d481c416414940280d800380030340c90b942d00c40400d1070070460180e8426502280b100005c1040400c603203041c00d0790001802400590025008c004100c6150744518000000c2e001c0114001411411030400c88102e0f200000049015440780302400303841040740c1007180903164180307400f598400c114000c080da81306805c0c40b4005184170380811041003020b860044d51240880c1d200030390300c00c6e1340c8003d58401e0320f1051180a0120f0810004121068070400041c074085006004480e00c900485000c07400903400080c420001811042c04a43c40303260503c0843e071103080c035007140c50500c0c101900d01e0109020a4400a101351301c00103440105040c5044124000d000710341e80c07040003507100d210107403910340c0280701c00415014090011b003510903200d501a018a4105c7c000b0300380304003800c06201c003c00414240e980580b1400071680c0c1d483c0c1c0ca000d00320b210303142704d0804088900a142601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 401838561 1250 401837311 401837339
    0x5070b040308012133020c0a03020d020a0b130201050714011b0503010b090103020c1f02030f010e101e09050c07050c030601030803041b03020415080c0102030a09030b1816 75
    0x100003a402025882000ca0200800085c003e144039070007450006880c1c4010049146000b810b4000600200c2c0c142404880801c50112640c000d03025282e101202200483c1c41c0d08241c0c070001c0c0301d81980c40100b60880130003140821603c0c410305101e46400d00076202d1105d04407005419034800d0307454000c07144074481452145607501006040103410755051030703030058007802440d52040c1010f9020459525407001044a207140c4d0144842c03000070440c85440703071f9010358800c48142c50990207090000846d20560302c0390602c165125070b00c05004038101410b6078840448601e030603107265034001012545498520485d4000c0d043e81004c1543c070140362611a00340380c181c54071103129400400c01000842e03840c030201c0b0340c01907001c0c820480c1003c0100024183d0f1540341c101a4026103030000120310211880100000d5070348403022a4003e0001200482e600d10442c00c10b00c0004a00844c104001130204804070b07000480180c40c1c03400c4141201100386804030b0340c031122549841403002088800499406 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 401839811 1250 401838561 401838599
    0xc020c010f05160c0e0702150606040b091005130b07050607020c06041202061614100209010f051b0a21180e0901060302040515040e0312041205070b04030801 69
    0x202100740a88050003c0c0201841500d03040145100c480030403d0078001e801c007a168031030a000e001c0c100030b40700a50b01e444442d9087c000c0d96207000031071170384e181100a5404643c04000a10b20b0964101b061100b0041c480c0c1041061080510914541c0e02c0003030140c00250030300c60701c0d60703407602c2242c00c4c00c5103072080c0504100c00b0354100d014504055100c0c481100c0582e0448881c0720046400e62020a0b164410314403603485012554a082003003044201c03941102c40d116004968294100540440032131203078000d02c03404a5287c0e9440b041d040c2c00f42000d0030b480e50201d20302c500c4046a5000c4c0c0703801e118036080c0c110345500e40302c41e0504a00c0d64a00c1c0c10400c40b452441c000071201451448c0b03511042d102c3c01500f04d0151202e0024440c1002500302c100650340c064030600c890f091213a0800f40d4100900041c43c42907040c120003040514001040d80c40c080302d000341d000f4a603181c5841d1195807146c3c80041008010342000103070f020420545600b8003861007641c80e00002d41c540115100d1140da0020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 401841061 1250 401839811 401839817
    0x7030b010201051e070c03110706110d02060f0720030406210506010c0332190509180c0c060c040f081f0b040b0d06020408010507170f061c060c020c01 66
    0x984c40c4124035404085548600710b414105440e55060030103683c0403201004c0e180103842158004038a4540c40345105401421503811650354400c122011b076243c88048565020300404e180004503810320601e111a06185504248414450402c0b405402c551194108002003426100c03403031b10810719201c035034660072410242081309081c40320009081c0500240c01404024000007440d4046030140141c4054138885198150a02c0c1a114440c5040d000460303c8013016002c034008180c031354012002c40d40e011800411202c0b05c0b07902040250030040c0090010030120100b03002854902d50304000d86070094150b00c0d4025200c0b450501660b6103607805401c17981720354000203468607695403a900c0d610000d02d066000418040030300000700b80100100b810b540d07404160003546000b440000d0707008000b5120400001d01160385c0c7d40205640010035840d000300e81e032070040001140e404130740741e0b09904240010906100c062403511290ba0444801e003052740c000355141c4280740b00540400c405a982d030020b003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 401842311 1250 401841061 401841091
    0x603480703090302090411040c210605060904091a01060e0a060e060a11330901090305251505100e070207050f030a0203030a050301090f0605100e0a09020307030b01020105 75
    0x1680052007072019203c000e014141c100003150030011002030500019001030020800d21906034402481000b00501140e0140300d1682d840391004217501442d000c1d100c024041904d881d4245060100501c114902619509030115041d4007048021880c6070081185960f195065810441003107038010080e4000e4041c011255880181074072220191450380c00241095421818121311041c208202000214241a030804084051501d40344017040b070200e4030100c900083d40c0700c494040c2201e0307050001801050050042003203c120882c40f0000d651541c00001044011966502482110405465100688400c204101400030045260040030a0740c04640359050005000c0d44031450b40c0125030044500340504281610200404611683d01a0032203075104040600141f65420a00407030b210541006d005100b04000c50281009036032005029085000c10080d050750b9a005c6006816006081003100148059051002c1c42c407400c00c5480c0851030b590000002421101c00500130520400e02ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 401843561 1250 401842311 401842313
    0x1120b0109292a0d0c06020c07080d0309050f06040302070302130b0409060b130b010e120102070f060b3316120210180b04020f01020307050334050c06034807 69
    0x14070540401c5d5045000169200c0300030001c94281031842d00410414802c440910785030781d505620203190039010b08151141c0f0401c8407503280d00d8480039540a401640848002c0c800361501c0c603001204500740b500700041d40081d40011800791410b041041d2281a03560f0303003000b035509110544070410208500d003040030b040b8200004c0c2c00200c0403541c00d4025649010036545490f030035030446004075007104101703401100134075010b030241c590400305a006040f0119007645180700b800c0d046006241901c01802100510401884035800c40410044400a410041d0010078407449207224910030740c1c0c3c0a4801c134030405c1039800a4074000404615003074140701c0a40c01040141c400140c00c280c0c1104c40702520960400100d203140190b01c0041e1031800001408240f01d42c15080e038084520004418105040c68522108406000050098441e8100800c10503503850084001c540c080c0d854404503500d000c070843d0031180c50751982140e07510520310040b020041c0190f00b80000d50300e00c0104080b4604101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 401844811 1250 401843561 401843567
    0xa0b09070e010806060a0b0c0c1c1b0602030f032e030c060e06090d02150412020f06032406040f17071e090b01030b180601120b0109292a0d 61
    0x2030300c00e0551447d00450705411055040c8050102240020034449400b843d4124440280009000817188031210062002d9030f4442c0a0420045401a801450515010310081e4903a9071008018400d88503c9541d0292140c0b1009562081032015594000c4564110318103840300003146c0d0450020300104020089803541c40c1c8080364208881929940d001d03450030300c0828100c1d40d070100d44a62090000c6400f003001d21080412244142c000c460a0594600040612030b1034802070710f28a401400300900302c0700ca0f09040521580020018100a1601d03640351803414044502d0b4000c076080402c01c2c001c2d000c82003010040320021f8103844940f03510100000f82d041d91407000500c11030003919150f01400001380e0007a44401e803c000040d0005076107246850302070400500481d66203010840d411080c000d254418460561910b0040e10760203045800c0090300d03501110306510000c0e5120150b81b03040000030466000d422049a007086024000080c600c000e6a40c488510102d025a4012104816090740c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 401846061 1250 401844811 401844829
    0x201142401050c010b060318010b09010e01120c081002070317071e0302070c0b0a030c08041223131703030c040b0a02010e16180b0915030a0b09070e01080606 69
    0x10242400c41e42c80044158680c09000345c0016290300c900044100011810381058810905458400820003400340404001d146403081c0034140010280c1801400340d1a0b0351000051454011420124030903500c2500c1e9107002009041c0f0307003056402248030001c2503041118403504040c407800002080c034090400601d2240c5035039808950290000d010040745001794103e6010342e404c0800c42c0ca0b03186c0c441c000c042d560f41c028000c1c000000c1c43c1424038450302d03106841e41401035074058141150100c0110b4122000c400c25003000788600e800c910b0392001840304000601200300022085040e003031070f00313400e41124580c000543e441b5820410801518400744000c0b1000d036a504801c1980700c0c0b2081808a0041000002c8150240704140e000064103610102d070100725102110096030b200d00b920a400c0030303203546810040c2c010020307501042c6221090f1030000c5844201a080320302d0284140c03202400200181c8603280240c1009105000300035a0030211401740c0078075801441b950030800c010a031030368 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 401847311 1250 401846061 401846131
    0x2505120c0f0d1e0501050118020a0f1d090103050c010806010c080a0c0f0209040302060906010b09012f060112110109030201080f0604020408010e0f0705040e101a090106020114 77
    0xc18014004010000c5050f01c00008500350340c21454021540d20300140200000e000b000e110300c078401d910403841038041c000c0b20f9083c0000e40c0d4007209034480b1041a100390030444000c10364615510300100194446410703250003140508000c00380310403007070300140000c90083c0207541004540300400c004554907800710383c0503504502c3c0182e0f0300291414403060103048203030000d6120090300c06002c141f50f40001c003039009580300003e4440c07990341c0350030040051152044071400314601d5410741c600f14409400c4420002c203401d000385004520180d4883c10101c0903004500c040603035170440d00034801903403d01e200d004400e00f8222045421600043c0c02442c000b884403002e46004000244580c603640c06a030020510720009000b0b9606500206413143c4410540a034107214801c0000b8403403916000740c95101d08040f026000c11400c0c1410400940181d188a40300c101c9801041ca8050300c588030707014020282540001104040c18040c4161100d01a001001051084d201e0344060404211024044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 401848561 1250 401847311 401847319
    0xe030d0216080d1b0213020a030903080f01081011190c11040605060301030b06040908130501081f1205010905100501030318050303220906030c05011107060e060c2505120c0f 76
    0x302d0a03480080c0c2c1b8840c5010700c141540f40046860007807590160450700c8007a200381c681c098145d95000708810094001d100d2404a42e004e86414859180203601031194150003143e002c0ca0081004c41d40c9680b080c200c501c075000500f8100254003840042d09038040d1210003241c0a0142c5403501c0002402c0b4001808041e04008954001c08c090f9600c3d40c0c00110300f15441643c450303c90b500348a0342d00782007011707205050100301c0302d400044916964642c0e20348070744101c5400316100e5007403aaa45001200941045555640c1c035600000466000c002d446201d00442e14003085544c11464020035110001c2410852008010b4040c02241e602006a603031602e003180061841d0301d84422201d10b0801c41d07911908180c1e28058000c814884070004410540d40207032038150042240a20695664506105000000e0440000c401d800c1c9802e100a100081d0300070200d68415030005c40045100700b01c0d200c21280040590010403960030200182544110f8040260200120310408980d6030036604040c1445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 401849811 1250 401848561 401848607
    0x80403080d021e0310060311030f04020a090905100b060a080412031116061b3c020c0102010c0306080c04020d02211f060219030e030d0216080d 63
    0x5028070342d4103407007560840041c40000d03a00c0b01c940c04241c0c0d90080e14524000d4620000120300075000e40a4000c0e006021000245903590303c080360903e4250144c07040b6400f1380c0d01130380042d920141d40540e0901e140502c0c0902180c505101c0c001045600328403c1c075004103002e2184100340780d000f241c02c55000b5080000c102ca000d00c14481200140905080210180700204901520340b41c081c0700c203200103100d80f2080010580f104009060010456000c00000f95102004034034400d0030103035508a454210103160038441c0040c0040401e031006409078006a000c0ca10042c2150b0f0709010300165000e03103040400c07049060911640d03d954294a8150090390001602140c50407607904031002426255818607040265980040780d408065840e1888001442182c4030008101c440001c11629190001c1400c10f0b41c001450281e0400950f056007444022800c0100a4505014221403171f1003d0340a0442e10041410102402403103800800440c0d00022810000c40e81108056402a510300f50703c00c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 401851061 1250 401849811 401849827
    0xc050d030b12011a03061b0a0c06090c060c0b06100e010c0c031703240906040e100e030a0206180705150c10020306100201050601020309060703090f0308030118060308040308 76
    0x365402240e0041440ba6290040c2c2d40f070040b80d28030758003199030f40c2201922100c1e00c03404690a00c0048483c507042c0c070308004002131041c0768011603400c2e40f914850700000c81c110020352101d590081035940803102041e0280810020030545d80021544114115208190b800780030600918841c4040415030603c0108080201031018903200f090007982d0210403010b20a00200b0540e0309138000750b0301c0e03102034410844a910010a0643d400405d25006072400003103a58140401c13000c0e0800343c0c500c003514040c40031030b407a240d803060045508540715000110347c0d9103032641c00240340460007061011608022207001e14666008900d0740d0440c0d0b0216140d00090743c40b082400745d940f1602c441411180304a402590f4400f8058024500c00c80040300c00758540c60300d428080c0e00340c41013282d80d01d006030030800c0302d51818038141e000742c00c0700382c02032a0249409444102440200303d0380e400c10780e015000840100401440f110346140c980700c85550501800d8910f40d100340d03103030180780170040c0600404510300f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 401852311 1250 401851061 401851069
    0x30203040923250905090a090f061103180102030103050c1504080303010603091109060d0b0c07050601080604021215040602213421060b0a05040f060c050d030b 70
    0x9103240d0030390502c0d00d02d01e00341283c072994100581904180b81607950454105254000e01c8a002101d00c06007141c070a5955844007440200b003d2801143c2441041c1d0340031700419014450340c2d202d01c80c5260043d5480c02d191009031200702d000600c60304039a004000600010782c001c02c00d480309403c1960404038020701504690014000c9401451151201100020702c1913450b8001400f801e01441140220180740000c0c040c01540403241c1d103811407803017906500040d50146a456002151900441c00c108640e500e05013440c2e0281c0c802c07181e07a88407106100540c9001d44000d000702d00f03071100600340003090b80b0300214032450080028000640c00320b0480007801c1003402c00c00800d40c8105280030189003180401d11800300004401101c1100252800c08020800d0403210b070802d00340c0c0b104a61a0f01400c000c0c1d032580409001c0f00521503c030080002c0107000341c8043d092000c0c048d117466440343d051030040c1d000180b181e07100c1e0f0204a1501418404034034040740c04a0f00032003904e804070320070700980d0101e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 401853561 1250 401852311 401852351
    0x608100e0a0b09010504020a06111b04230f090109021503060f040501060c0b1b0702060d0204050303030403050c0f0a0b06040e0f062d01082808070606060e09040302030409 75
    0x40d0920b6514801c000016030113500c100d100d42d02c01c569071103c4903101c1c4411102c2c02074a880c7c5040070f40c40200c030180170b240100525201400014004100e080b8910003501400c1103c2c0303d001e4440340c240d414000c81c0d248001388540c0c010034007402084000250b800003114401d040c1c4250512071f8000000c03800070380b251004419001005002440030b035954690091221340302100039110740c0b59007804a40c00400d087c200001c202d510307950950904449808121907980b140c50f1a00c010340d800c10000803240c606002451040380681c03a41510303030381089503aa040c604d84281120b803542003105100c0005442c48032031500450142c80002d10080840c1d02c040c0f81caa1090f8142d241d5208000c01c20510480c8810174180c3d20110b41401d951441d914041c07a00108020b010b0854540c002c4402104001c54000c0640800044821217501c6161261038100c00d5500808007a40c3c51520384c0010301c10343ea002154131100c0070301500e180f182c1d4505614000c1d102d0090b4004c01d404a6124004d002c1c0307840c0c1900c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 401854811 1250 401853561 401853563
    0x50117072607030308060f1801060f02011401060f0909050f010e04020303072406050301091e0519030e040e030306090c03151e040b0a08070603021e0a030b090a0608100e0a 75
    0x85800d8a6104d05000d01168001c0799107e101d44401c01003a007103800d010b002c008030310101003403900700303030b401c118050322528040c142203011596110000580307142c502b41c03158001c258a81b2900b00c03201401000401000e45032700007081d25410a418007600030b80d405030443c110349504034400c5490300c5910019055102d20400945222412241c0c112303020000181540c0403400e0000410402d5600c0c014182662045078019203040d0820b4503e03441c401900c14203038140f500c503000b40ca003d441d00d080314004030800c10030180d000a103d540b0300086410144103451070070980780e000f903013585003441c001403400400810b07048003841c0c00b2000c26030100301898800e041807001086960380315400801c9154000c0b08030000c40c4500d0626003814802c1c04c00040e000103507040c12026000c1941801005d82c0654007071a164801e500090046800c2c61418401400200700300f65000309040c41e0800420200ca50f002e00099003040c505101000742140c0001c54207010802d010011440c3c045000c802e40c10701030001c40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 401856061 1250 401854811 401854813
    0x60105070f0b010f05040b01120b03010b1005040617090d0309080d020d0b040b09041203020901180602011401050103180b100f17060a0b0a03020913081305040501170726 74
    0x4030001004400d02c0c6482c103071504e404504180c0703980c60b4100320a4550322410035021070300001885018400d0703904804554840640017054448250011960b0f01c075911a080700054800700e014044c80f42d03c441b10410008100032540320714204000261f0311001241403a00a155031a0740080400682c4c8042d602309400490045444481010451026261040c9603920641c81c094400d82c15180103114076010f15000300110121201d0700800350025840300740d5090500208001842039080f2401a0f90064082a800451902d48030008c581c482001030708002c0c1454100688003070741c0c82c00c40c0700740400c240c0c1100d10800d85445102c607403000160160821a460400981c01050241c1104c1480103041e0040084a0b09a50741c00410001c03030313420000c0e05a01c62480c90041000d49000e018803a04511640521440e8000c665200180395100b44c1e000d800400840b102080075103403e1003180d0042403004404403c5a040103050340c0c44141314040d9a5051044049007841303211800030803550304000350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 401857311 1250 401856061 401856083
    0x50d0603150e0c030f12030a06030c090e0c09010e070c06060e25020307081b150711010b01050f04030b1b0a030f0b0103020724020d06032105041d06010507 68
    0xc5481c0050045807803215801c0c03158984046080c24005030309000244010301030309440d00f614011a19a600141000c40ba05440e4000030000c2042c1c1d9440a000b0725884a0015165190034001800d0640c3d84400520540e5500010010b102490f2040c45c4e1100741803900f410880d290f4070b882d030001e0407a90020700a40d50340204018140c07101030003880c4803019070343c0d8150841099030000c076624864074a0007054414240280314510240240e858941c03009032054031035400445000080c400c404131203076400034a404c1d0090076131100a100c0e0900d8602e0a280c018640490003115403958441c500c8014441205240014032040d006010203100c02c161381d1016544460205000340a000b076507044600d51440d04000214030740c0a17201b11203000b41c1c44240480c8000036801156624058910b02c409840d40802420110035024810b640245208003c5131041d000042449004440349907015411b04c901008244060b03480343c0528541401c0200e014a130503900c9200481b2140200c1070010324102c004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 401858561 1250 401857311 401857343
    0x1801050306040917031f0b09061803191e0b15040908071217061c0c0513020304050c04050c030a0507020a06050925060c06020d060b1b060a0c0f050d0603 67
    0x208001e5001b4009140c10751803c500842c4084100605486200e01458041052240c1d03800e14101500140b50001c50400805030740700702003420600b84c802a40f1318811400805020003110815100c00201100c001041201856940001a0b2800313412402070201e03040009000307541e103070405020107520028080e124402c81c682100040803e034007000206410341e94081100c0c141185452003544010030101420240d0075071024000a030010548404511503408640c1d92600d906910b9603412042c001652840c10b03007000e034180041015102e01c124117050900220f500c0300000d99802110701c1d2000112503c4020003a0f140501c3d00c100182030714140010402c9100c40420114201c465500440600c904102502c1001c0d18140c055000440c0844500304082140d40e030140900c580703e4840000c09c55260082080990413080c041d0300d1030707111484403031071480c014012290401d4501c0410302c458100b0f210050700c400c0d4411003070410820040b50081e0080354980001c0011904144032001c11807030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 401859811 1250 401858561 401858603
    0x219060902030d0c060606020a0b04030507051513030e0a0b0417070801110a03180201050a18050402070507060909020f0f090f040f0b0102161a030606040e070f03060b18010503060409 80
    0x1070326100b45d4121b0324007070000032001e0010588000e11030b885030030000303507564940d02560140c00000c0144e80e9842458054411403882c010031a0007000011440d186902603403030010851543c107603030349003e1250600b08000d095102ea058500fa038603c02e0310880501b03c0418075a18010155200d5001c035030904180b0203d01c0c2c0e0100051004680541d02031022483c524040c6030903000800009000030000c002840c03070207101c1c05c008009403060700c002030900c1e5030b60000a01a40c121650650711a008090100503254210a40c48000d001f0100b06604007442005c80801500072000c13015040135002416800070b070b442d464402c0403480000e1082050401040580d130013000c50000890142c0309145040c3c10443c0f1030302c1d0340003c840c000c00b1804a00340c0301e0040381c0302582015048940000c0280404291901640c122500c580502d40da140e110340c0c40c00c400182540c80d05c1d80101d6041c0c80c20032805541c0c20a04522450511082c200940d994440c2c3c0c011030b0060243e80d0300a80740300d50035010400d549003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 401861061 1250 401859811 401859827
    0x111041412030d0f060512010903120b01030e0709050708010501020a08040b0703050d02070f05010b01030b0a09090f050d030b1309020f0d02010908010c0815040b01020a1506092d05070219060902030d 87
    0x1400761400407c4006810440d1708032000035030301402160781c40001d81c07003020300c81d0050b000306503040c0740102d03044089010380c518160180d00882581500c3d0740800c10440d038403030b18050061000b48010448401e550b00c40300214071403401946824500010104289801002118640b50452034115640c2141d8207020030754016034202107400754200b40031302185600c40d0090072524070000740242c00141c6454405001058400e104803510b0807462500c82c040303802070004550003001030314081010744620f001c01400b5090305407560229031800200700b015860b440a0041c030110162034146070080700d40016510900c3c242e001c5070003503080c240314199695100c40c0321030207100c000b280d60039000c0d84072007004107541c1c0d6025128010b0707120300d0095010071383c40c0511001d2000359050000702a502c4e184c610302500c2200c0b103020044405240201880d002d501094950580244010840d078104408001c0d20b8040f0070180c90740040c100c2c4040c2050103560f6011469443d8000d0495480484908005d00354078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 401862311 1250 401861061 401861069
    0x30c04051f0e060a05090904060b04050c031e1006081b04080f07230112022104050f010c0e010c0503130801090b0a02030702070302100210051005030111041412030d0f06 74
    0xd00300a140c84000c0c10030b00140d8131080083c2d02c0d40381c1000c120406125034100000c00030344000e46c41303000c90051900c07a07109440c0620303880304e516542c034504610300c00c44405070312a5001c1014100c508000d02604030041c0784040d1000e078540b54625403035070416480300d40881c0c203c11503000c400180014032017200203541c098403031505003603801c095990715912200100c1c001c0101c0f98980f4094a00769198842c401d600e050800c0e17000014242a12102170b0803040381151000c505180b01001403009001c1700704080404000b03100004c0c40115460240104801031050b04141802500038010040107000d1050700c8a83e0a107103003aa051961721002036020b00750b105405d941c0d0075041400f040042c7c03210300807644240001c3e0000c240083c555820301a08285c0c420001c001c42c010b50501c908165514002c150140384c80440c2d84000d141080201403c4613000c1c4a4014049d500b00010400990b40954814103000100c0c1c0c030140101d480c96005085100e00b65600100d6840c0511400c160501036004409903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 401863561 1250 401862311 401862317
    0x201302041802130603020c2e05060d021f09030b150907020307030203070f03141b061303080112020303070b07050c07121e02130c020f0c010e06030c030c04051f 70
    0x7080e1070040c210482c4502c016a070a0100302802c248001d9000c0c3d0014400b001c0c0c0714080783e00c0c416003039104014450194500c901204c1034807140c0325910241d80070355030f0003020440709022591500c4c0e00140c0d80710040c3e452400d203510b40794200c00215000c0c0d08208002c1d80c0140c9000400d02d090302a144c41178030303a00070084c841e1104101040c0001d00c00070a94900d945d06400461514880c3e845442425210000813000c100441d18110011800c0101804000b0b40503c00072550b045580720540c01c2c02e90050540f00480102145070700869485015035045464000046c0050030a07400401e066200f03810025040055000501c10040d03031010041c001146804295031205842d048800340040d070284014221800d008054102c100c0c038070111050107031008104103c0300c602d280c04101902c500700900005604231190a0501c0102440b68640c0e0034424601501403100460003d17201d4000a17224880f00480800080d050703008a41c103e80c0900b000500080780d81420100001035088520200000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 401864811 1250 401863561 401863589
    0x5071508042102060a18060207140c041a01030216080a08070215070f050a02150c040911160b0403033b2a040b13020705070e01030201020a20130204 65
    0x26a0000c074040c1c4142e00303a40e003c2e000d661905002c400c0a05101b10312002c00d4003110300c14000148040c8011308031a40320315000d94100340c040701428101100000303002d0003142003841d440c10b40341c0b04444910070a4800d080050321103481c3e848090a840e0464030081025038001026071072103401c205203038400c00321030b030880301c8020400310465458a0f041d5203a0011581401545035881d01130307005055100000d1049821492280154007101801500c098030907090014080c008078110f8040c07401c1d6107544100359450a85e80d0752000014806d150b901501c4506c510f4041410140300382c0043d0080000301c80d02c2c0b071000d00356051220103107190705c50302e0304800c106000e07004180b90041029400a070042c0d0683d801e038000101a042d500f04030501455219644100c50546c9a0712614600c4110018000050f1200076900d406c914000c0540c10908070002c28500400050381e0018024580540c043c4000910888580342d10f241541b1100c4107541c8054030810042090029501400071118100c1b88961 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 401866061 1250 401864811 401864843
    0xf230c120114090c120c100f0c0b0a0b0a0602010b060a0503040305040e0703060e060102061b0c01060b04140f0307030b01052709010b091501140f0f04060309020306060a120f0507150804 81
    0x103920410503130170603003150704070035040381450145400744031b400f0040c2489d032540b41c42a5642ca0200300100c5518440c1d0360340301d002024034103149a96034041c3c0024002008020b60140c0007030418020780042c40300b0040004009000c141c4540c06880c01403810308640700c10741c24501400b50142c9030358081d00601500d01c00018440703603c00034845014000c82003015803003a40035045014140d22504e000d41840d03403104030000c1d91900c0305000b0700c01000f2070220040040b03007200070000398603000740ca214401c2c0c0c09a0000d0021644920351a411188112580840544500d10040e040401254000103031001c0f0310400100820641003c1500c000c1144c03c1821a41d880030282c411850015519000508580b01d9040d1000c2000c02450148142c10109090141c1341d0400c0f0010761181d00070100281d10340d040081141001c200ca030740c000108507042d0b549503007002000f581c03070541103802610000e001d501d25800d00205115a0000c0c007041c40d041c0d01c2803c01a60064032441c0141c604413501d001c0e0406081c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 401867311 1250 401866061 401866063
    0x201020a080a020f0d0507050c07080c150408030a03090f0c15080606041505030c0d09080a030501080303060108060105070311031314100e121203040f230c120114090c12 74
    0x103001c0300c90201c4c010704001041101c040207100007480001804410051040c1200b030400c01e0038010100a80100035103881078062040114072840e9110118100344003d000c400b40100c29110242110b29002a0503d03203402e0920b0030030203500d00500010751003500850a00f0802c1240c4840c0356050308c4184560319040107000052003680b04045140d180e00a0007414240302d00d000310b810009030392041d81808440c0c0c80150444002c101c084078044400900d07004215010700070980100b11500180d82075150000c0064003606008020138100100015400101401220302450001036078040b02d4035035954a8460b40b2242d1203005805030300c01c110341e202040740780940380007080c00701507130f50300c28019905414094031120822a1020034000d054500c20a06c840c007000c1c5100d5030003000910702011550410070005960201502411501658520706494000641031724050055906100c00f4a1091089004002400c03010102021160078860081000501350041b060110307441180c8201c541051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 401868561 1250 401867311 401867317
    0x30210020a201f080a02091201050f091209100806040906050705040f0503010204030503220329010602010504050706051e0d0b04060b2110030b0a06080f07420201020a080a02 76
    0x40f10001e4207100014013500f006130007070074503001d01610a280801448440500351031703040355481c90b030114580421565410400c8003204a9801d880000d290407141c4002c0b0704039041101c88607041c40420400302c1c0b425111640040003040c2c002d00100100d061040000b80703240c0c4030307114203a6240d500420124280c07074103100f00c4044034fe021004615054104421580900204540c5440801d61b2407001001c200520302c64513195003001d80540ca41c0c00c9444441d501c1003010781281007160b26103400c110001d100020380c04151440e5041aa8903100002c41c0c4e07106445c1d018002c100c02c282c010441c006440456045000802000c03942400006d482d440032055038001e04c0140d641e48071034030111880440041468a0f00410200010840c66890743c44000822800342d441080385580d500c410001d0010500c4000030050114010340700d09490090300001d10f0110701071080e810752243c00b042440d40c458100e2580b03003092901c0c07080d20380010001c0c0a8001d4001031000000328070598001101201c0780e20031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 401869811 1250 401868561 401868619
    0xf022808011406040b01030209192907060f180f060c030e07060c050c060324010806060f130f030c03050c100c08070f021201151e030210020a20 63
    0x86441c2c0c0d61100200030141c4a004032050605074208001003190b00c541c407003507600046011a46241c1481c283d003003ea04d10310070381c1c284030503501c0d101124410301302d007012943c0aa030840c40105080b0300b5404001c00038080541c0d4904c0442c515000602001041c000114038a80100410426045a42015401d640d11854004030b250440c0c3c0c0c043c010207016019120415000c0c204030340d52400c14a0200f04182e0040d00d03c0119440c0015003281180ca4403008605454001e207402c808604148012070b545000788404c0c0109200c1c04926a240c11022420725070060558103101d03600c0e00e5480c10108142c1c42d03140026205070090603c1440f49003454a66400b50b980310340e407050341e0f90b0b0701520f6410050300b00341c0341218100340b80c00910b000360340c40c1c940000c604030015000051a1604c420180aa202140e1041408d600344041c0809200001c440c0752045075015180404488140d0601324201001010000c14401c010b0741c20b03901c500c00000d0303101c1c9076490540d03610040c6201002c408040024102c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 401871061 1250 401869811 401869841
    0xe0607121a1008090f011802030c0a030c1202190b070302070603060e0609070201021603020304150206060f12071703040e0906190e01021c02030f070c08160f02280801 73
    0x141200354548030342842e540c08a604d0054404101e86010030368250365501e0001c000740d00c5001d4080c02945400d10034031070303560f804580300303140a4610764030100e011801c6c2c81511303180041d40034410b0540d120728400714039541c90903a50354545138070f45120414036049810160011302c80e0907404200750f4000d20800f01515481c5070184c0c420f0b9111704c00c00c03000031001400881155000d020601400712001102d40105219802541e2030714144a061000a012010725804550110040c048941c6a80c0b00054036000151007604443c001c00342018070740752070707584240c500b5901d442600005120110142040c0c40340c01c5140100394883c000fa90b50354440c15200e0307010102c101c2284d40c2013120f09921a0104c6265400050706000403042c14000071a41c0d4102d070211f503a00042041014126440811750025031070508400a120395250003e140c040d408482c56070132040503c1e072041c450300010806200380e0041c9200308100c52140b116154011906004a046010410100368a1010b0280c2601c84ca2980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 401872311 1250 401871061 401871079
    0x60b0907080a0c110a15050c160f08040807090605040515090703091b030308010e0106020706020307030e06070819121a0f0a0b0f0c0d0f05040603020d0e0607121a 71
    0x180740c004004010590090000c604c0861070109020700c0b407400040d005400c2c19008000c40d00d840001d0f00c2d0020801000c000c010802d03c01d03450403090350340c51040e4000c88400e200c0503845c5401c08440c412600411602d200d035030800210703001c3c10340051b8145e54041c1c0f414803540e11051890010b0981140f025544040b441d40044d420301e01c40d40c0a82c00050090074800c5090500043d5034407954500d0f0803c2c0c002550b9200180240d900b08013007240186100e10091091b945801c5009440b8017404400a080200004800511342c0d91181502c4c489a0486007144d03403050100c040c1c02184000c0c040302808200009192100c10800d40300303015800c3c142511031464065a030301003124002050745002c2d40110101008210045c2c030401419500b0304108155640d07814400e5401d141c462a0301000f001c00c81880007810301141d10000381d0b0b040318178900300540c68000b0f0070b10740c4d1b02808103140002c502e440b40c001006119503002444221808402c07404000210740000c0d407440070401c8056641c1c106041c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 401873561 1250 401872311 401872321
    0x10b060703120b21190816240b091f150201020714211c0b0303090d061a1c020d080f070605011403150c0d09060906020304060b090708 59
    0x1d00300c2000c42c0c0c00c1050700081c11082000004021003099070f003d18154100703034000411150100084030700600748680e14801581c00d6134540e8880d100c3c0307040d841c1c0c941c051403200c2410005207508041c0c102d280211401205213402072080000d110074030800d4403e5640101003100005011159201c14030080610100b00b81059107200b80b014041c0d000008543d07017003007084c0106e1105103880358403c140402411024024490000c0030711030682510003071030360421502070400945600b1030b826401050020451803107907000241140201c00f0041d400410035600300301000000c4d07200d00c81d03c1c060829400862078168040c0f00c080301071b140c14460b01e90100c0c003401c0054602110b100c0300c614401c0f9810341c602100d680715003242d9000340c002281e0389510703440144110021040c2d0303040036010030b900030240c40040b41d030070340d0711050060b2a00104c0300000071440070410f01c1d9003100e1009500450300b800f9040c0b00c1d14007600258001c43d01070350410304d020480703825458100e07541350050856a951260544803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 401874811 1250 401873561 401873567
    0x20a170d030b06130b0c010c050f0a080403090e042604140d08090d11150901080f070203090d0503030612010e10050c04050d060912050c0a03050f0c03160507050102010b060703 77
    0x454952a98403800030300c07000f140a548010007034058014195400e80f1000c46d081030030f003501c00070381b00074040c0641401740c18040f84844041d10008061883e00d907016855606081d00c1100007900410b036901c0e03511781000700f44a04251148400940300b500804080c8140300180aa8025401021136440036030300ca00a06150150070307094941d0144010328078019140f80040c2600015420072500c10b2012811503104d41b0b0300502d01c2d9a08222400c40710714041740900000d0a06400034846250b51042c6004150507510070400d54403001c101034500720001090341007007940c9801c226800d5116a00351625406a020f060052116841105000b8003441c0901c0b0b803c000540f000038070080040740240305c0050f1036510f07030b4002280580140000988a101c0c0c1c18048814150b2501001c1480400c2107a01c21103840003a80b0001d06030145072036501c40220f440082d54900c103c00300e07134940c6c0c800822400f407000002a25005c071648039804803801255160010ba0903645080c64140e880b0f0b4050000d2800700740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 401876061 1250 401874811 401874821
    0x6020c0a121704031506080106031e0c1505070c1a0316020a0f0b07020105060904050607030b0301110408010605011b0809010509040207050a0b060a090501080309010c0f0c0e04020a170d03 82
    0x2c881c51060302d09060791216100960441d42c0240e071103c0c850340148200030203502c14540a000c47c10000c3c0302e07103421521081c160004050b8562001015080940140200003910380c01030300d890052044030100c0d40d14018a19001890240d44c009440d20b00000d04604400000e002c200d00c0906480c1103a0381d0f000c0e45c124042120401c0b1040d40036040c51384002a500369070071802140304800e04c0145060111000342101c000030846401060610184404510009202c83c0e10260910b008a0550101004203015100c1007420420101000c500460591010342203801038460aa0380c04002d1520003c2400a8240c85030014020b01030810140f200e65102e800200145440540003514041d030940d01c4078601032580b182a255a00d0040074000e8502d41601164024010300d04140000c0d418400302d03680702e02c0340e41c1d00700d81031113000c14000c4200402c4090381c0c5081074009400d000c087c2d50b0349078006d2048004071402c9110f4040004c01044044452032480d000b100318200070008403c803e041540204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 401877311 1250 401876061 401876063
    0x81302010e0a0b030c0d06080c01120b0103090b09060615210403140c0d030509210310170a0201020d050a0c03080405010609020f04090b090403210f02070b0702060106020c0a12 77
    0x1d1203050b00880c0004100b001503004070070503541da0390344072125005001155041d070020305041d00200004249680c0c07090120005101100c00080c000c2c1c101c40c01640201070441c00202034500d00d41c100810448041845442507402f96200603001c0c8507005004c00d0362081031202c02201030a208010540b210020306654007e1282c2400400320703501250081305900030401d00c140c13036808020b4000103030f80c1c14090b468101010744003c01d0070108045100380000b80002d210000d09a01000140c0d850403a0141400209400c14815092501803a2410748481c44401d0584c05489140d50b1040e80707034840c0c002c460301d958056a40c40333000c1440f0307501110f1580000c1c0c03050ba4950340315800070500030720701c0c401000f003a413844414550f00c600d040d0314281550380d580c601034452548141000007007500701c1003149501e4107400440500380c2020b124400240b02694216413840e101007039480400c09909502401266280c01703d600584e640d0504a036115280c3c0740c0280c010005160420408070b500d81c40038505 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 401878561 1250 401877311 401877319
    0x30206190203160f1209050a090506040b15041a030606160311010204060c020a0e040506010e0c040e2d04020a12080403020907020a21080705070203030d050103150b01081302010e 78
    0x21034001002d408054000f90070348590700c03941c00e140704002d61115608110348103420300141c414540800101d034002d41d4861712940648520001c0d0450b91203521141300484021300c6143c0c004801003640005270080d00664911110310360310501d4184906050b2840f56900a041c3e6181101c0210346190b101d103520812014032040000703038030241d01d0a0020300082d1606135a4030841031868010070582c00295880421404a48800d010203e6400300b806410b4885200c444411521807075000c0010b0712175035000d1800d80c40980103000c40c803007110315440317503c08050040e114100074034844035241030020b907002903102e000ca12041040c8100c40c6503102c0014001c8440d00c0c24035507280c010454003282240c801006811140200d420041d41c409203c0c2030710440c2c81d61030098003880001800341308026101c24103010021440307104540d002c10032520500304004040c0100c1d40d4900e00010f240c4046103504013109d081240c84441544180399651099600b16038039003c2c8082034006544802000c0d2205804c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 401879811 1250 401878561 401878567
    0xf0f030b0319060f061403011404051c02030f0d0506151602011d0604090605010f2a020607140a02030d0c080403060203090a0c0e0f0109090201080f0910180b060406030206190203 78
    0x10900517109880c001d102554250300128031180825007180c0d22032480d43d0301c1c0341a5000344000302c0c10006079452300c07554000071403283d201d1007081a407545c050342e0180401000c0000c0d81d041182d0f05030700b18a00440d419100820a080c00074103c0103580aa49000540204c0c505146809580301e124240b400700b04000a02505030116404540544d01c0398020006554035004208460350780b15414083c0e8407070915142c02c400500e0000b8402d045600c0b07400f00540c10480d5110003c0d5940c11044403417950b0f100c103810200e1460f034200c0c1600c03142d40481c1139100b40640c680034401e5a005103000c0300f4056210925604e824207541c1c4020094101404a074200d100d04460f00000cd039910101c0c1d80503143d5103202c28035070300d094125242280c1050700710031500c0b41890b8400d40140d03009502d180d00008981030002941c0ea0b00d10042c0c1c80c03c05840100d401031414100040c410703d52000136641c0e25406001c0810050b5248001e2005461291100a4007c0c1d010440c1d00c1915100c090070a410404074810740c1e01d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 401881061 1250 401879811 401879831
    0x8150a0b03011401051c052a060a110705060a1218060509030409112701030905010c0e040f050c0a05252904150207060902030a030f0f030b031906 64
    0x2c02c64440c41c0c40d09002610142c014082403a110000088103407175905a550701012590324161188070b03e201032040300301004c0d0403c1569002c148030f500c1021000d8141c0da164840154001c4c9441c42501681c0f4550244040100e260b04254042324902011500ca014141c4240503130031008080924828400c1002c0e200d023700054240d0155a01a0320914011601d0350700780403c10382101d8a07640ba040b80003034100200c60003030000c01103a5a001141014449401803818010790181c50002c400401ca0351901d1a4242c065030407050040f03051034181c40400086003415015011a0410b43c1e14140e001f90511101c41043d21420041100e540d0700d000040004400c03800501010320740d020101e030180c1c03940121440d40c2c1c006050381c0954030740702d9910700c41034281602c0340101c0c901140d80740c2045640010b1030409000c05904920344240d8050119039030301c130840c00d004211944400c3c080d400a1a4150442945403090040c4003111f40300034090b00c07510701c4d014008103100443c2d07041228419181d8180f00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 401882311 1250 401881061 401881063
    0x102040305070608100f05090604021e1c0203040c0312140d06212a0302120109021828140406060918080f030703020403120210050601080108150a0b03 66
    0x88019481074005002880c00c10364082c0ca000070043c00724483c0414040200018070602500d50107d9800391140c5107281c403040c010801030300c40c40c0384403001000001c020182e0204904010034800c0b0b03d0010b900300410a4403900c00580c8001d541c003904010b602d40003031010452000e90b0441221190410841c42c103541c0401400302c1d080406840911031f40c4843c204410300c05002c03c68000f001d103103512030840301c4035605c000d02d0001e289400040007003000e8542d14625401400c00c005180c000301450361000003001c940703000e444020001c90142c291686504100109140014040e40d4041d444002240703010b0140c40c1152100141410341d56124102c6c4c00076142e100f00654000e81c0034800c049005400d25121800342c1c0c0303d44000d0303c803450090300d4050104080c40156032810b001e9581c120361b20b45980c041100a03009030f40000e4600403070340d01d0300780c0b04036000178240504210807003051295070f503440010354002c203003446410215084904a030300e0300c1d248200401d6001d1980940080c1c40d040302e4001c0303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 401883561 1250 401882311 401882317
    0x1d060315060c060a06030510050702030a0e040609020d151205070608070512041a010f0b04030201050d060812070b060a060e0402160b09030714070b070b040809090a0203060906031218060c0102 84
    0x1a40382d91780d88001c0c0140001807102110614103802c0600c403a050810b8025a00e22406c8108801c00c000080d10026607500d0350003030401488c01c0b610640d2107202045e401c00c028401403049602079046c0903000210151058000c524103504440500b000501c0d140c002d80d0a004000c1c644000c210301044030740b45000740880551f025074040c4080107101d4500000c10f41c51050b06810844656402050030040400c0140486050704d80c203103081a1210160001c02000e0401c1d500030310040d000345181110102b03902805021040d016590030742d01500c500c014000d078202039015040028404c0124052503040030b030024044e0340002c014429900c8a80d0702e035403015040958003001d5a400c00203a40d424481c001c1d81c00b6a00311604405841d046281070480c405900c10100c0c010001e48030707100001c091022003070a40d507080101034507180031807400300303d1413000354003c4030018130422100e0041601400c0000710700c101c008504d507200340340000550100c0c2ca8040070300591640010100a0909190028005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 401884811 1250 401883561 401883571
    0xc030304060f12090c090e06011406070201030608010e0616030c050904020c1005070201290d0f052a10020604021810080a06020a08070219030e0d0f030e011d060315060c06 75
    0x883c04040d410501c041b0300b55072a5a071486401d50002d001448102c0040d0350410f0b91400c00c9950660310b640314801a80905010760182e0398551812100e5444e0200c0810403a1007159468058030b24040460b400354120b03140e0b4003019000030814003110100c1d0400b5401400c41e401480200c4045040c45990501a50703011254140181d44417060740246407058500307050140c11074100c44c01c0c003805c414080b42c0030300c0f0312110181911000342101c03810b01c1020302c5403d148503003040c2405202c035041c0d4401d0302050040e040da640240344903521408003900c0400c40c24019580203144d07590520400003082d1018502031f14144800324006000a043c03041003080b114031910030380016880380b03a140c80c003801a00c40180303e074040d5044100707008607000740b1883e038541080d030500309000c020704030300d0114007049008000188000c2d001c40c840002d26400c02c800190b12030702680c40c036450400030044082c02ca440140100c0c2c221070240040341100800c0d034080842e84070050420b904080c8010075083c40c115054074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 401886061 1250 401884811 401884823
    0x10060509131409011d010204080a02090a09050f0601030516050916030b040204060c061d0a1e08030c1308031305010509031002040308070b01060e0d060b0f04020307030c110c030304060f1209 83
    0x1307005c0d4031003072210220b0a00c80072454021403c00b45403080503a1954154030300248078015150000320200100e42c00b02c03144680000885000d1404502c40981e00d840078041903502e84180c0031070500450b0341865074000e46c2c0c0d0242914209803290a80f8040b80c14a40f600d140034984c42c1c20b02e0140c0340c3c0f154030180000f01803603603901b032a0442500b0072408480c1d00c101507241c001c6000c03000380c614a100041140742c150f0700983d40f0912030070000c049a0748007155200181981d40000038483c3c01c800311001b601c0400440b89000d03a4003565032402641da486201d0801c100d04102380740800107580520081e0001d0351003c4c094501022100d843d9100b02e0307200d0b80084a6150340440c1340810b000d88921450702410550a1034607040140e20001500d101030000700030030b0700d6201c8050525580341c154043d04203a00242040d5224104104042e014245140c40000010b49688041480c0b80b00000c5003410440040d0281d440d01e810210215075a015140c203001c00d01004002d06d252000c81762013024801c600403c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 401887311 1250 401886061 401886071
    0x31106090703060e0d17100b040b1b010b0a09020f0904050a060f0f050f040509010e0a0b2a03072a08040e2503020c0a23061006050913140901 62
    0x21030f0a0040300c1100030807034a9035210070a003d2410350481c10081c481400c91301a00a580d4030004507504595540d0414081c47c0400f04000440450100207801c13501c00c030341240b412100c6410505400c0f03594561969a02c002258400c0002800795030007400181c038141e0401d8600300104d0040703001d9a405445104400340d544804001008180d81c850020f00045200140e010f45082c00041028100455152049690310041703070102409501c02d00d609140c071001d480340c1c0d44160800142115040302c5140310305410940894201c814483c11080178541041c03002d0850700d4401d000c4410070003140d4410820b41d4489000006c10111a82e00201c103445090f10703564403070901706410503c1201601800c1922003d4a266000c151008032421020f902480c0c0180c07160000c107109460013a9034035000d810f450b0989403005283d04c00000c003001900c46902210801e4030ba01104403084607451080350002101403040360214a070002e041c803601800c01c03c0201b95031080041e00143c0c03402c2540c0352100c0d03030f41d16 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 401888561 1250 401887311 401887313
    0x90a0e070906171f0e1018091e020301091407260a0f0c0b0c0105160806130b06040323010c090803070623010602030406030e0622031106090703 63
    0x610310034090902da10b8082c8119810180006031488090903a00b0100c103500e11410104110004c040b0081041c4a17441d00203003000d001c0d900d0941c555000c1d00c0c40f0307d4052000020b2080040c010300005e41e5119100c0c20f5410040e10303081c1403a913040340040fa40365486031140c0011440d400089203440010102611003140303030078241c032011a00300001c04480b54050071000342845000c00d4504444da040102010030b40b0b4a450458280203a941082045480c049801440b400c81584124421440d2044007421440113010a65410800315840795002c080280d0740c4a60000c41e411100d00c14101070301c0d46043c95200c0d901c41394221003a07100c440c0e1503104000d1801c031000c0240503500101c0b1240c00c0109845080441c0b55480f80300382400034001710f0300c0d40110341d04000c4018549210100504038000740d540c50b02c4000752a94070620032040020f090401d10a54960b0208a1030301603250319000f0791445a00c81c42c81104031186940580c01c0c030100940e07905001c48144190340c0f01745c64150240070440c0c11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 401889811 1250 401888561 401888567
    0x10303050c0c03060408030a0f06051f02100902210106090515090f07020706050a091a071515050103050702101b1205040b06060309070f03051501050d02090609070302090a0e07 77
    0x92600e03041c3c4203a1020f4240004034407064126504020b4000300801e8403107080b1003074400740807a90710081c2c001c1050007096000c100c0031380d00c004d010381043d800e4890760b040030038044050381e050380c0c00654021003800500d17100700c8a89070803000c4000c40600229813541e584505604854044487e54071140b00000c4608452901c203054580c008145090300400c0e0416001c020740c0c9206600407003041c000009414098a40039210ba8801860f01c90181c150050402560315181d4102c004102e4641103c1c1030080382e142e501e17004035818404040b44078035003503280c100110040c2401a00c6481075000b90801a0090300d014000c49414206036540361740c2440c5004d6004003140c040112501c00245424280b1000401c65500103410030300450303c958070307510b920110600301052503018404d048001000001002004103500115683c0c40400b564103070b81e92410b211a07140c03e40d0b0020f41c080204000a1034500e0080314003074019001d403800500381048a00800e0300f0414a40050220400780020016407641c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 401891061 1250 401889811 401889823
    0x804030f062f0903150a0f050c1e09181510140d090305090d050f0c0d030f081b0406020307141504030f031112160305010f03020409080909010303050c 66
    0x14140b05100c260070750118040d03005102d030041d8824040c00050602c0c01540d04000343d0041d0209818081007504141003010003c140c8290034942e10341c140070014248900400c140c032400900c1d11514030311680b0450045d0f03403582c40310a00d540d0049400021b1000303803083c1d82e5410302c50389414442c1e1403090840c0f0100711030340c0c05e80e4020500f00095118500082150981510302d82c035001c2ea80070500d449140b60941e054002c2c0d02e840da07044421082040700b480800a421703505041d240058030030101c400f006000001c000340d840580442c40310852524001d00c00c000715a0f100c0b00d40011010a020007503c900c2695025511800c010303480400d40100b0300c004010b1301117001c1c422070002c00802c0c0078100c0c082c1c02400300900141c280000410300144050017600500d11841119000a969604400d186070001d5003d9491341080c2303217003980340981a4041e2103017038141c0d000300003009405450340e401c21025003007000d0304465489062103d6642c13a00e920310780ba406180320340ca6070394407034400818061810b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 401892311 1250 401891061 401891081
    0xc0b0d0b1e0d02041e050c030a1a060f031305030c1b120c010f030b0603010e0f1b0d11040b0d062309010512210a030609020c19020d0804030f06 63
    0xa0309001c07000c0c0142e0703940072101403441c0d030590380032902d500003c4200c0008000788501503020360038102006004002d604c001c0d0304c10f0061071020006c0410103c11260004a008056900070108200044039240c21402643e440048110344a860fa204c43d070300c841c21504564520080759008075403040022140041c130350a0000c090b1200741e4039039400b940166032004400881c506100003045900f0b035451082e084088190300c050b1440c1c1c5d407540c2d552031601b4032078411246050f511741e68001142612120407111700c070413008608410b050030310004103d001428000e200340002d182c20000005e80c1110480a0480800c1c02000001d8081c58041c22013082402d95203210100030404c582118140c0c0ca00708190b042d50380980304100e09080c0d400b401498103c148d00c0418000004a2910751203000c8000100150032031381d0f03401d001069a40300c501040c2d00401d10140f520b6080300082c0d250140003050700f503507a81d000402885600e00103403208451035121350000c1c1e81e164009076000c41448120301500c0200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 401893561 1250 401892311 401892349
    0x90916090c300203040807060905030414040903020604110612150a0506070507090b010309050f0705031e0601030f0201031401080303090c120d0804151d15010609060c0c0b0d0b 77
    0x10949085128294000d000c4040d010303e41c044003040600c4181005d4505466108d44204aa0703100d6013030107903507508180b250990700ca000d00e01207903441c2010f0041030040da03170bd600106140d8075190f443c120340c040b1150031540c006005002c4000040c01092085002e402c212b03000b5520407004400303004d42401142c02c6280118000c014510008400041100807520140d600150f100710190049018000c00d0b130015140e03204000b541502d941c404143c000803644102c0403220900d003212175150305412a41004000c40d0000801040030134454000b0034203a070702c14074001402000071400c1c0c01440703000307800000352030b0b102104100c88208100080d2600e49411103a210364010301419140d0f0b00d580c0009001d0800041c2c2000c10100450300340e031501c801c510000c0601c001c41460f01e2070201c1c1002c059405440f4480c4810b116025002c20301483c3c1031b1134150b505d1003050780c1458000d0f500c0780346660b001c50f602c3c044094000b8108132408080d1250300088000850920a41c030304010f144003e1507174507041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 401894811 1250 401893561 401893607
    0x705060c0312071e020309041439130e07081b13050a1508010b09030705010f0e04062d05010f2a0b04200d02090916090c 53
    0xe03040008141c610031849104a419a0f5036030380c0049850300301d600c244003d250078210b44080015004005020640400c2d40c0c10422501e22160101d81044251036445080d02040007909245050101904081b0886084032400703400c13091001c1001d80c01010041d11000140c1c5080c04200082c0d003205400c00d88528106d119420f100003006c0708160600f100f03003100c880c0012a10040d1045519a5009181c018078022403a0b554003500000d900c0643e515000148090700081107075a01171007981c0407084090010300505c0c3c01c01d40152514188942001c0a100a45c0c000c4a41030b60f440c00f0f00c102a03ca802a44000d1850300c90a400c0010078428400c00c54a12400701840181d9112105000322505407401c0d00c994100401c0d1a0844d01c1c404164440c80245da07500801401212000e00c1c0c0610b22400241b501030703555140e034401545c1c420644503401020f554902000d1f1420514040d04203220303005860740b03c2c1801c103680e00c9400c80ea47c01034907190303100c50f900040c003a003110810761255504482c80b06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 401896061 1250 401894811 401894827
    0x1050408030105120f0f0d031d1c0c060207030f0e04020c060c0f040f120c0b2b0f0203040b1005010c03020a0f110603130b10060c02040509030c0a08040305070506 71
    0x8101e00050280314060010b400410300000000c00c884413400d108001581c10801c030f0024500c0d1601d000801100102c1d0602500101c1908a41c404200b44016580504003098a0b201d1001110140300c5016040280c00103054011458610042c80381d00e201e6140d502403600314120180940b08040c804c14851841030003034020161010401507406600340c04070a0741d030494413010490324000c0781c20031281880c03800300c0842e6950480000003c0e0a0041001d100c02d1640c0b000054124852506014007910b02c88460a201200011207503c0c0500440350120300851030f644030508a803c201c0d006c4d04e90b512107400344160b440b01c004654002c1c0500b0720f401c450900494401a650f0900c0000051020322030204000910041640824541100500280c3c1d2420310110205140701203600c1075621101e47c01c0450f1422000b0454141110040e44a03189056525003c00c401040d00a00b0300415010401016000407014861052524031a506494640341103003841c0d890007070340d6044180a0704040000e04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 401897311 1250 401896061 401896073
    0xc101103160201180b010509060607081818040b04021e0a0b030a18030503010f080d08070e0415090e1b06090d14060705220b091507080c0c0909010504 66
    0xa5071100075440d00c010040d18030103089004106100703d258000c0040031001c002c10140d10b00381070480b0b0b41124039407455200c22040100500c14948010040d003010043c400e54050f41c5028900201d20091507510212099006a40d0001088a0444500640604210440c2b515901c2c03d03d043c040c0c2610310002404100100b030450307556004004ac81075002c0001941000150002c2000c5c010403a0801501c0007139250281181c1c10070b00a43c41109034012010403954400074680c012041d55503502041501c4406041d608110f00240003500310340c5480945000002400000000b805080f00003c2c0c0d03520b03070b60456800d05010f07450700c51095031564144410341c0d071010142ca98010044903041c40408862034814190030054641c00c0e8180100401c2040468029001c0c005c000d01c202901c451a82d20b0b0029106107403580d0140c1c54401d102444514040e040490107210440c504541040c5400d0b0251604000e641220000607900e51140c105405c141c1400c0c0b110b140c02c40e02c1000280080c2c00c061342c0d01c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 401898561 1250 401897311 401897317
    0x8071101090804060e0409140f060726060d1b080106050102010b060703110a0f030e09090a0506010b0a170c0d0e03040f090903030b060307020f010e0a0b0a05090109080c030c1011 78
    0x2002c10019884d1201c85c550703845502c02d22480ea401030004100c1040b01144c0c944540e0915200c1c031040c000d110000700554060306c584103d0545111072424540402440440141c2c00070309115003060a182c1c0175000070300c802c08151014a01003800002c81481e01407040c1c01d4451a800c41811a41495400e200c162504019509030135450300700a950b55150b000038a01e490759444010b814031018280050905801107040300c3c400b80700342c40c41d004942c0e5142d490359850201c000d008186a21980040112050303120107809001c1551400ca00c1001f6800809000420140c4840440070800941d1a071281c903030f8030603c07055003980d4002c3c40c00c040c500110300c0d40a07030061084007001c82c1c030380a25104051080e8040c00b10818003d25807602d0b0304198070000c0d99900d00032035083c042e40c645568869580c20010701528a2a8071404004035690f500b041d00300034000251544003990340f603d1820f4001040c6401a0034103200c82801141c4803c1d1a1200e145003951b0704030b140d1009071414201041c2ca000c0d100c00c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401899811 1250 401898561 401898569
    0x30507050d030e0907030501210b04030e0f0d03120e060c040b090a090617010605030615130b06030405031213020607060e07030c0801060302010e04020a0906140405030d08071101090804 81
    0x9000034054080c1002d80f20212076500040d488103040c0108443c00741c060307001d80d0585e1000015000320004a40042032010f1248201409800c028000a0002803183c02c00c071710340000141402c1c1348803040380c3c0814401d6516240c00c50104103200002c0f141865184103244180d00110010b04150030103541880d0144514001c680c01c0c6080081c0281c06038440000340f80040040c081c007004110741e620141401039500742c25100c2d030740d420100002501e01c0c000501e00d000f400c2d211290140c0c1e580c002c007002122140700004c68646600e0340c240c9626070b5509406140f0a9020303002841d5182c1c0e0440007060f14200c01441e22a00090034881301001d40c07034140642c2c01c615800ba000090780d11a06010501d410203942c001001c4105084001c075022106401a900304c0b40300b0b0f290600c11610550400c4240d001d0703240d0150010710380802c2084514071a6010120019000400030f20341500c6a010070304080d008102000802c00c11820f018400c1c3d4024403074070224040000804c001400303582d0312109413045100d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401901061 1250 401899811 401899819
    0x20a090914270f030d0b040b030703020f0f0d020303040626010308030103030309080d06081b03031e090d06020c07050a120b0f06210a0b07110601030803281505010903050705 76
    0x3200142c2128200318050086002904403a100c40100c0000d00c064075203650301500071402c107030b00b0320030906000030440b0640341c1c0200001300c1c0a4944d820b00c01d4800e00b5004180d84042550907070750158400b400108094211695100900399a003050011400004800081c5c40e407100801080480c80303000540c0c2c15a40e1510b80440d9500080c00c00122a008003081280b00910707040780040c02c4a000107424580c1e0400d5072401c802191594109a20f034000d070900b215075040c295a90741e042c9145840205141d41001b0186040d6540c20744a02c422a0440d41c80265a584200400d1200c0d16081c200310b0f00500441820f842025100c1c1d031000c801003006840c1e0311102961502240b400c2d55282181d403440c015103100309011084c1c0b0b0806070b42c3c6140c81c8005072207070701220004c1a4410302c24a01e8402900320000140385a9103190b684c4d0015600040185200c4080c0e00701d500c440c042d011042c000c9000200318041150318008801e58001003680d401103042c004200003c20000d4004070301c0d801100c204403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401902311 1250 401901061 401901121
    0x20d05040b1b040b0f0405030f0a1203060b0304060e0f1207062012090705060d020d0c1b080c0c0a170f06060d02010e1309080408071a071113020a090914 67
    0x81c5e01c01c038140c0502d4118980c9402091841002c504000420b1680c0a005240c9111300c80c002000903811282c0324010108008400c1001030041112900100300090f07204040300c0400341c90380145401c08540f04501030f05010300082400920489009100d0003030540a242c003001c0030300d45007800f86403040c0c002c074200074242c0380001807c0840522446000b010b000d41800e566a01d001030303050082d882603100e031a8551500841b81502489001c0341240c50700015404c0340392800944850400b900b244120b05903921a0178040c1c0c4607916a49410001443c1c81803142e01c0b14142d4150302c60404400702d07402541c030342c0008100311040e62842404182141c0a080c10000d0128140c08248100d01d0744050b2462a800c0c03070307100c0d82080040d4004008507008030055405681d202d03400d1a0210400903060740e0314280600405012030758091142200d9500108420300d48440070000b03005981114000030040740311040d08014003001030295518054641d04030084511b40030f444206112404481503082441070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401903561 1250 401902311 401902327
    0x17070e011206150b0a020102220303050313060e0a060b1002010b1f0908010504030509030615030615040e070905010603200a1b0606030f120507200f04020d05040b1b040b 74
    0x2440c203c4060014029083e549000c1414003038040d500150042005c41407a400140045006016403820340b94107645552641e101c414120304042c0700300030305036401d42e03450004000b60401041aa19a40d204000100e21a5407100c01c00c404980400780080135a410101007c2540d03484000300503071b242c00100c05250600d84460210340c1c801403900b00a030b481d0300c1c0c00d05010915030440050446201c1c00c03811103606640c2d074841202c0d64060854403941551200c0301103604060079601c42403018501810009441d0440d465072490448954400c180d400c1c2e84078018810160725015001c089444c8245401b85642920440756040c440c13041460f040000000c0075008508045c10072100007504803009200780c40e103c0c1001901392115810848000a83d01040100503005009544405421102e240ca11101c08802c203500100f19030615648035030115081c202c184d54500c094a0040c0081d03200098520f444d1a020100c500302030051485c0c1c0560300c035a81501c8030701000320f900383ca18414900351034402c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401904811 1250 401903561 401903591
    0x105070e04240f0905063a02101116060c12230a02010b01030e0606090601020717060603100621060204031203140c041d0c040b0417070e011206 63
    0x1c04800480744410320034001464042c41c0200d03d00792503516070204216100d0f8800c020210211030001c00c428402240e070805040d030a07452054007240700000c0c0c03d554142c281d001034001c4020b1403440d404a9801c41061610040c10404030100404440d00c44032071071704010000d40584940903008180b0852001c941107050300c2401d100c03140d0100401c7c2c1000950181103d2031090308280e40600056203000500d403101c1d84a80203450360800e0175005403800d92280401e000207800028141415446040c0c0001203e04500403400c0e02c03102c20101401481c01d185040504144c030241c2d4a40406007400000d020098a6040800d003c94580020303010202e154038100010340521340c03010f0001041c0d04d10229070306030950400b8550a00044148515a907580f9071f0305003038000c0b40036200607407280d81e02c0d9090302d210b03e1000035040060100b696080a5403a10b040c0d845a100382c00200307803449420309040c0031203801c0044c10050102c03a240044e15606040828208012400000d451580c841d0008007030010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401906061 1250 401904811 401904851
    0x70510020a151508151005090103150b03160608010b03040503030f070c1a0a0c08090d0f180f060207080303090d05030c0c070306060f05040e0309123a020105070e04 72
    0x14900d07003c0c01aa0f40c039180f03500d981004c0201e42d101c0702c42d0701c0090801c0301c00302c50303510541c1c0e8014908001179003107485001250321105620140981d94044416440d40c040044030706150f2640d501c41e10703241c00c00c00d0083c00da03401a0b101d004880d00c24424000040c00210a8940c0007262940000b4a9594000212a0002054000340c4140304000000c0d0107254a1501c2e00e101c2c0c494402e09000100400604031444c400494102d001a000540000c001c4c40c460b01110309c1d110310a01e40440350080604089205541551205580d4940c0e00350412215805200001c02804548080c5042d86040f070b001540350145003040804200c40000010900d0010b14155005d01004c0300803104426160710b0b00e080200500e008450302d05c5410700c40012145450300580405004013070207181410810014000215140301201c0001c2c007031808400c0c002201c58a10031a00c2c0810f06e00c281c104140d806140042d00c0640748544116410135080181e450740242d04040034450603500003400c428280e020000301e031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401907311 1250 401906061 401906081
    0x83a0b0a0f0e01031e120318080f070b011710090f2a0b0a0207050f0d0b0a090209070302120f04081b03090a0b130b030a0b06041205070510020a15 64
    0xc0c6200030114074400c10381c420b54162440352007241c03811540f4801070f14208031074110041c00741c440d0000002c031152207a0446041c001c04550b00c110b803500705a42e0402c1c0c0390403c810a0300b20b41c20201e6030030180400c1004690040141c801e00d0f01c65400c0e0201c01c070b074941d500e40542d04000380d01c40303a00c0c00c00c200e0b2032594192043c0c2c100c046d1020000031b403403e040c1c2000a917010680e112101d120003103159040001200e0121a40d50010300b881880d100074090704c1c0070304100040d40b002c48002a103001c40d8104103001d219442080700002c40c200a031042002061340613100e141010310501c401910502804401c83c0c02040030552040706941d240b50030031103072045144400014028690424811340c000002d40300082d411181010507036110781c0c150800703001c2d1109a480c0c50385000c030108840a892002107810848410010540190305004200298865440715045c00e0a141091050000030f1240c0e2019003c01c030341d41003021b001820300035076800d02e10102920203580800000940c144562006001c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401908561 1250 401907311 401907329
    0x705070803040809060a050702030c0307080703032d020d0305150904080309010e0d0c0c12030503011712040609050f090f0114060409110406020607021504080f120103083a0b0a 77
    0xd1284140087c007035080024104c0c0280f0507020000f00900d00230500c5c0c0f040c0d0301c90030000d000c518030f580c404480740e28100820b00107800d82e5496050885240601e962220300c444d40050510840d1408028105e0f031005151030b2040d1261500c100d01c40c1c0d030305062150403580000310607899031107120301180101807401d5042403508c80c2d542140200358024030320b1034005010361501400d00b962804030f620002c4525000800190342000148407003600c02900c2c500e003000c9401103c03040112007000003060351068220b01c1c041030403039034100054908009440c1030300d00c0c00d0f00c0c02c0080e802c109030144243d10041c010301e9510b01100044c0071158450f02d040d00d004087e00002030068000380c074030062040c0c3c8140030340c1005005840005140c42e00005038125012071018401d0115601d81d10f8000f40303604103151545200308200b14084903581e4070030160b400785006060241c0d507811700304400002c6220168400c00900f040c10342e24480c0c98102d0709840d107134204001c0c0100704804108006481c201ca69000b1400c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401909811 1250 401908561 401908567
    0x91a07051b060118050402030a03031d060118050601020d08061c0611041e080a0b04150507030b030d0201060807030b06030715020c1003110a030f0209031023070507080304080906 78
    0x161400c00140d10341281c0b0a21280001c1303240c000b4500c000d03540120b07806134240c0d0000b10180c0002c2c0c86a44041407040902001600c41c15501903941e04242086e0700c000c00c07a005ca0003605075218074a00c940c3d500300c10240010501c0348403094014003055001070800d0f1080301c0840c0c00c2071035910344001c0080ca2561100d01001042a40035641510340c005000c1c0030002d52040f400d41185001c01054107064480710b07002410701d034101c0c0d41c40208049006100300ca03110f0744003101038580e10040c002d0a01034a05d50320040f032100458410326140c003c104d8041021a810640108042740e000709082094940065803013840e50b40b50008a4a0016168422400384000c0300e0082c0c083c035400319105c8103443c001c0b2038517010002032070012415036404000d00ca40c007000410014042d64043ea120031070010001e00003600b0b25030a040080d041c41c500d02d405035011078581d02540c1c00c500d104043d9442c1210090002885070401100040c1207014004005003070413400004141030001280558030520402020259 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401911061 1250 401909811 401909857
    0x304050a1704050a1d010614071113050103050109030e030106060504090506041d060a050f04020108060120060702030924040b0d0906090f020405090a0206180d150618091a0705 77
    0xc14034000c0c00c3c50050307010b002e0002187d00e0f4814082020b00c120300d20203450030004161540030800c0710340e00761203910410709440700c2c400e032a40d4003131180214051000083c925840741000f40505071401c0140d4443c0c0d14011041c814a41c010701940e080d121150000561559410301003001803070704540000184000c0e20804241050003c1c0784c620424070b000c4144240c0e2181e21085070a180c05940082c00b29000c14000388c0594403620f4409248000c00710f0101c2d0001c6004842400d0400948901c0c00503007000880d81ca84c3c0c10410481100c10404103411800b44d1100503400c225401280148000ba40000a8554158005400802d9019003201080010001d0352400312174140e00444201d0180741130a001940b14400420166807143e00500b800c2e10b450303030740100c5048104807204407540c0000f41d2205003000c42c60141540e03480c80422040000c0031801c3c0145240c0e07505182c034003403440d6810a83c00c60001114400340181c030b1406031302c0135507464860002c00c0d16a40158921030045200c4005482 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401912311 1250 401911061 401911079
    0x111c1d19080d030e06040b04062009191a0702120d020607111c050d0216060905010b0d0309060302070311011506080c040b090d031e030c0f050304050a1704050a 70
    0x2080314201400c4403581c244404050b01a1107900c5045506500050b00040c0800c5006004c00e511a00c1007400080314010011250b503200c5807080c01c00d00c50f64ac0851961121308040100440c50350304c5100000316586405c004007000c120615050030a4400407441508544408207900b20400200003070320700b80e04031010000d5551300d04941160008000d00c01d4082d00c0d00d40401d1040306914007809040c0604554407003510a0340c040d8860181030341e0708003c1c0d040384052010540390390350711415011400c01ca081c2006401c0d0381c059150188a182940c010400181d08030b8152800c448041c10096182c40da070382401c0d51041c08203407820449500b01000e40c1c4041c10101d41c0e01c01550521f40341c3e520a40ca9030b0304c55100740d0103140240318417000100b0110041d4a8030090a08a051003481c110045640049086803501d00707120323002e00400e840e1980081d2007500901c8158031010a45003541c103524054031003913945d841340d480c044c0071a0400d00405101d800c60204850203031074060300300344096640740781c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401913561 1250 401912311 401912359
    0x908030f09070e190c12020a020303011409010e040b060f120307022418030c0303121e060105030406090507150207031406040206040b0a050915070201111c1d 69
    0x10420b8081d0350008107020030b00f2400d1900429a01550070800b060000300d19000b444054107500500c020301d084410714a031140005c4c02207010540c0603580b254941120f6100010002c0581403240c1410760060003010840d41c103190340140c024400c0c1300c45032a0349001c194280a00c43c40a50001544800440c03584400401804028400d850280308120750107201131110300320345030f040300100c0308020440c0e600106003007407108564020300b0ba84c5100e01c18000030345103500080c50201030281d41c03020050710840010b11100c1660440c00240d510745040700008045101c010703c020030140e40e69812500b4001f080010340060a040d26502e5180e024041020796140d400d48011580c400c40ca41e40a8600708007c610b80d0701070b540c054480d070700701424941c021101d9000703440700608014050018424507900c00b4503102d110b40d6118000c990f6001c0d903000040c060303805946034404551240c000105006030007400080008000d1408480c1406c003440c05001c0855403004480c1d00c290b081c20103003090415a840c1b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401914811 1250 401913561 401913571
    0x1003030e040e0c01110312010905041b060c060e0f2a01030b060306120f06011206110310051c050f03190f0503012102030a0302060f06040207020d060902040908030f 72
    0x384080340045004100c169400351030300014540212000782c94a500600c400300b26545003a096a00b01981c100080b10b444409034852031849450700f05000c10b02584200c11000f62900c440d20340c4455040a502520107200454010121070307a5141000b504042072007504200c49802c0c06403110040b142580e2401e4481d000b071141011514240e00540660003442440b000000c0500264190b580300360802c90002403208401e404c902461050b910303803040601c140780c083c102c42120907503450981c0c1803103811202c103411020744070780c010028803a01c40c07440030090084070021210f540503510800c1140c1860921850020003900c03038944070310320045004c00a041c5100b4140f40c23104c024400240c04030b038400c0e0b0360540c21000c1081000184181c000b4620355005900500030340002c101a51360100340b5000b1f0300d0400b5001030b002141402040714003498419040042201c00754106042c607000034548078075a0b00d009041c0c035911003095045459a0300a0502580c011209907100e28050f10381781e008a0003110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401916061 1250 401914811 401914817
    0xc0f0c0d0909021201091a03070807081e0c10140403080309101b0521091006140a062102160302010b09040b0a1d01061511010e030909100509100303 65
    0x103008500020360f4420b440100b49880c5004946034601400c1e000240a60710032101c81d0030100040d4031060310b00304561001003040f0001403881c1460018000c0c01c001d000c0502d03807400c45c010085510000d500140f588142642100c0d20403107203445283c02d6440d11f0444c1000c200e22031000c24000144050800039500c0380481206841200142c504000e00705c1d10804041102c00c1d5085042000451003a005010682081464000c030501d01e01e10804510108840402d0140c0c0001501e0555007c540181002400c0179010044442c482c03000040c4034880501901e41007041e051280c044d00c0c2442490007441030f213200030441d5034001400c92f0009550300b23507030700382c0156007062542c01203800c01090880c0300b40d802804418490312003241c1c0b94080c1074110304a0b00b0801c070030b407100d8400c24402c1c0b08500082c80110300c82d221007078a80f030026140344004400041c07070741d16021050080c0302c004421104000d030102d030f200303016070b0303954440400640380394220302d0300060120200300001440f04850000c1e80d020351 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401917311 1250 401916061 401916077
    0x70c1202030a0e1c170d05010e06030c040618150e090a0506100b0708030402220510060503010e180715020706200a06051801090b04030e090c120c0f0c0d 67
    0x10107000d580d29404540020010561a019010a40c807583c4c480917508007506640c98440e8002c040d40588030203030000003000b9032100902c030b524581041251100d00b401d490901020385410f0f40450302c031a00c0c0c55065142a150300c5104540380c1d2481c0200050202d92018440500b00752081982d58000c0c213404440c244100304c00700701d9940a0300c0d100d034125000340005518101c1c456032400c80603040600201c2c1c0100040320582100440c54441190a64128800041e02e150260100700058010b501c40000c1c89810801448005007440f5815400504c03032946542403035803419154030700b0000c0c0c0e00216044107641c0009070b42660200302c0d101100c41c1c0c3d958000146403540040c4401490b6911907540d1644154080c50000d80190440d66201d110304680c64840400000441d007582c68038501210300c80300c1e0008200c101904684520034118003a900940c991a2480110289201b9941d507201a0516a800a0400000307201140c41c5100959046900d8031032031074078650703103030000c130150b80100d9000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401918561 1250 401917311 401917337
    0xf0c0102010608120a0311041203080f06010e03060609100f09060305010c03020a0c33050610020f100e1e1b040e070501080a0f0606050d0e0c18070c1202030a 69
    0x2074040c540b0704104400d5142c070f40c4601c010f40062034940849050b07e94103100c00607880070804041c015080c021f40f02c03402c062034a4951522080d0001340080c1c103108c0795649645440c4c40005559502810546044903039446a0401e1500070440f40d100c4c849501d090200465820a40d03004201140c0c03241009122a1110710b100750103034000c584a00340043c504079003040200d165040180c00686a00c141c08407103000507081754008144403000f04211071744901c00e2106508100c10501d80c004807a1015243d40d0203907400d880d454084522585c00c0c45a1038810a540d00c040500414085284030604c502d00b26400420f11a01d44c41c0c4c01076030301c03038251a039503051605003401d004029400c44407501429003542000e0054074051409403c0f034000a07515464660b41003402e11139840034002035190140c070345030440386038020740302c8201a0080e5900500041207c5440d6100039009500d104030048915a548a1048481e807001800c09001c04246420101e01503070040000d00e103030a6540c0c0c40e401c0311012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401919811 1250 401918561 401918563
    0x30f031207080412051806031302010909060b030c0f040e0708040b0f070915030209060a0314150f0603040201110d090815010807051512010f0f150806061b0f0c0102010608 75
    0x8102c80213030441807400443e0b030080e44182d0003001030f41400481e54101e031001a01150303c6400850b000343c8030081c0c030904d100c2950380041c03030740c3c00070001c00c04207015403030030080740140500010b00801c03200900414805c01802020041c1d8000d0b10742c54080401e02d1030071400082c6408004d54042da060000000490711002110450310720502140d00c0d1955000d00d4290642a01d50204441100b05503091142100a6031030400410705c0c0892039501190300018055010b65501000d80325040e60560700184241e6900c3e121214a0500c800f210350316200d030344500050704d81a0f840c1d50394420318060119242c1506030005500020760784404200d0742c07200d0b000c01100c81915000e000d50a00703503108140030090307450090024006031769210002c2d42001c903040a814804a030a821410b000885c810051020008000c120b0000f00320b0103d0111811a41d501c0140100b84080c0c01c0d02d0240000246017031800c07003200d5004040000001c101c411000480c2c00440e141ca0004040ca4015428a04001a8080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401921061 1250 401919811 401919827
    0x90911100201231e01150201050c07050c06090103060b03040506010f060e0906040533040c03020405010f0e040b03030f0414010503041211100212090c060c0712020d02030f031207 78
    0x71181894904039040c002100d400041c02c80c1c01c500381101e007110384d0143c400c44041c0203003a00185040400120480a401e540000b0503040c003d60080c0706200124400240b4401e1140c0306580159952501200403400391616070407009034508000280000c000c40000d58904070303000b80034005e120301d490f00c904884120f01d141045501c0003894001c10a589006d030f00c040c0d00403144070240f0209440350742c41e1150016000c40c29461a948001002e0301a0606000c4c09026080c40d150442c40e0034107040c0003801080441031a441000170349000510291100da01c41141c160303004007101c0e100c000b032900c841426400f074080c0c54000880c1c2d401c0074074030794007600c1903d016950102c00e0580491060104030b9141010761483e40d4a80b150808140c1404071910080645c0890440240303424501485150b02e8040e13209001c5010f250108400b0041c1d100c00300e10401036407500901520300d100341d0700000352080b692030340103945070082d41c41191801c82d001000309070508a031520010070741c0c0d810805441d007007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401922311 1250 401921061 401921081
    0xe1005130c140d08160f0f03020d08040c091a1309020414010e06060d0915092f150c070f0f09062108130e060301060b040b180604090911100201 63
    0xa9180c140b0000090301c101c018003109105805485d4401446031103076050202c40041c1540c5100da0404020309040e1f0600ca820700310302050821508a013050b075a600030074507036885100c52081c1c1e6042c4d000c0520601000d5500010070082005a6480d600c003031a00040140d680100c1c410762070000301c501d500003615000ca048450f1202a450256034000c24440130b035114500344500e1642d20114500082e80d1007008216400d4003240c0003e400080c1c5c50b001d0420b5903c1c00c411247c64001103a40707000465a0100c0a031150740580c0c10070510002500039100c14010700c81c02c7c10f4a40607080001c80c00b0b54031049200c003103402034440d04064a950b150340d40200d40720760161000a21604601c0c2c220b002c0d4442c40300080700d105582c01407030451910107a801c44840c07034000781000c41070102400441e1800b4003a0b00064800d00080ba46042e203002800758040c402c880c00d0204a007241d8006100c1555008141e90060540240500c8140120315002400d070050f080000d200d5a040c56071009064070500c544140d00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401923561 1250 401922311 401922319
    0x60402060a0806030a140c010305180a03032c03092403040605060111101d0c0306010e13151e020a0f140c010e16080c0a06030e1005130c14 61
    0x720a4401c1181c60241c001c0203d5014031400e0365180000303641d19a070501c00d0481c0ca000d0004804070400040c241c4002500600f0b4403000d100c5041c0c007d901c04503200c002d8652608000a6001d903000280c0355164001084c1550700e4100d40c0001c03042d110100041000c1c00084a032034a0100d02c180e140a0603454062012034064000d00000f00087c1969000607004601414410700d10245000d00301d190008162034500b0558030f0301c801441c0c10b10011401198560702c230000e0203c66002c0300101340d46903030500c80c13029490021004200302d034141c0c4080c030400a0b004409070700c03500310050b44040501100c1c1d410001000715901c4004422030f1a00c2aa442000a559600044c0d15410811140c40d1090a191100710070200882502ca2809100e038000460040014000360b6204403030a54a001c056408140340380c00c00c0c8114815560340380210030039101d5904002690103020350700c1500e030146820100c410070b480e080622500d590142c01404509100e0345910426503101e10a8030580c1680109007600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401924811 1250 401923561 401923567
    0x6140603100308090f0d06141005180a0e030301080f0705040507051804060801020a0201060f0f050603071206030b0f240105030c160204060308090907080103030c030e03010b0901060305090f06040206 87
    0x20b200340f0018452503078000e0100601399142d030002400a2125482154196910038400ca96000d00020b8176601c20781d001c050111241c6880041a20700c00361400780c0c50400c03050300000b440880d25910220b200d4403504116501ea6071104581c59641207010180b050612404000061038a030501610340b00f94940da807181d0601062903a811025500d0001265110f030b00d8010100e0906401d2024040824a0341d0001c01c1803031030610025a413200350b822800148441c0700c0c0a0000e07450713140440350003a145142c061401049901060020280d0780c100410048030041444500c5484420f614021003d805002d84c0e4111150351400300c49000014043c0814010302c0080d400c0c1d007003100900700301461000422020b0010303030b0004080ba0282d070802c54542001049001d000d0414000a030381c03140090904002c41d504503180076101c200d1014004080082c0140c00d0307034040d1000e40181c0c500103409840803045584442014001c1d0a00719160034051103001081c100d040b038001048d50089801400c050b103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401926061 1250 401924811 401924813
    0x41d01140f1311060c01090b0a0e0304120803040f1a07030c0314040201080903071a01090b0d050a06050c04030f14060a091106031e04061509090201050d0f110d061406031003 76
    0x410703449208410f42c0d0140060044e004d2103c003e000300500b0798030032031170a1030502c0c10303020810456180b08986a5207500c140000c0c000d0342008440c01c0c1b004c6810091741e0382c8980e02c3e0b00e4000c0c40b00c4403121000344100548851880c0301740811480c24011105601d040c40709141e0350b00110121030665a4258941e01c1d1400410b0255003d501443d400845c030800f50b034640039640c0c403046822400e13041c012803440d2196004012112561003444448581200c0c4c034081d02585840e002d035070742400c04000e0142691440031030048407260b01101c00640d402240141c0d5045075003040845440c860030003183c24094000024591400340c45166009a0710800c0701c0010701c000401d1180342e40005081c00301d0b034103840714410142c03603407898080d00c035a01c924000300d40395480e27003510844540160301952005040c0020100180c0c0c22000b55100d0b68a9031b030000900808034606000609000010316403202c0000891703020300c06454201409031031041055040c0804840c00340310592204890284a04407803c0c4140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401927311 1250 401926061 401926073
    0xf060d03030f0e0703110306070906030b04020d0f0906050a181e020a12051605060a030c2c15160206160209070801081603030e040209041d01140f13 65
    0x80140240780c000340102c03410b6440c004440d19030b510324010794000391041080001c3c0c5c2180d01d60803001034010345614100b0074409080c90081d8043c160602d520742080b8174080e1146e5050b1000380c10001c7c0244402d01b0b15004100080882000c1511100e05040000b0842c400a0203142c81020008903540d0907c025a183c0c5200424980100c40940300d05941c40c0f80503a403148410405001c0c7c4042c1d0b0760f00c402c95460f017145031144c84001070007541000380082020707a6609040c0e900f4102c2e00c0c100807130042d00c15041140d5036144060340b0010420314a0302c0c030500999080900f11094415100000b0f06c2101404c3c40ca02030003040030441082c000243d8036030041c20100007800f0b034144180e5024441010a03800100c09420803140300c00010b10880c0108410b03841008488207448000c54070f02292400e64400501540000c60100c1c06070741c0000e01c803080e40c0c5407039100720071100980245020390380051208038003070300c011030184480e070711031002150030301c20201e170614025100708031070307080e02c444658601c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401928561 1250 401927311 401927329
    0xd0809060d0908040e01051e01021c02010f0e01060f0b0405030a081b0f0a03030506040915050c090301020708090a062d12020a090806010803090d0615030203070f0302090f0f06 77
    0x20024071900c6a4a01000898542c00791010301000c54500c11103604283c14892000519080c0c298599030611450b08035980104040000c4e468280000b00c64041c020016405030811000c40d082851401c0d00218107608190f100e002900d5500d1143d102c3c15a4480714041540194010b41c2d0307041d002030510b40d000030140b8008204080d489031292a1140700002031038100f42d0701c080300c14040e400c112184000c2540c0b40c814103501030f0003110704000d5400e15845610b11000c41c1103640b0b044a68404c013050064600c038040c0d860382000100255551540c0f460700c4240d50704a0b5107214080c1e01014000b00310b850184000c507040c1103001000d10031841c1402200b5610020300c9940c40244880b5860703030f588610580c0000c081064242d224021030314500f42c103051070038a050740201140d030001d2010000b6569141c9180c41419080f40c00410310456a00700d8000c181d0303240e803000f035041c4101c020019007100d50b5482081200e000300c0d0100002c0c0d854400f0741c03102e0310f012a884181245110300080152901c07511b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401929811 1250 401928561 401928577
    0x5010e0603160e0a06050303040605040905010e01031e05030c0d123905070c06081b1603050306120609061b040f0314071e09050604090c03030f050d020a08090c0d080906 74
    0x101040c00c51b6550042815075001d0f40054002683c0001c0900044c00d2038041d060041c280305030030104130b615688444250b207000032086503002400703404400910004000344e0b4801c1644000b92004901d000e00c01814894020391b140c5505802d241582003824201d00f1054004a00b88000d403000c0d4281c10070307507449099506240400d002d400d020342e030041504540180c010b068240c031400401d0620840d0b05000381e000990180c01030004022900c46041d0103002e18024550506081d0349039101c0700c001480031100310004d07810303e204010802c010784500244250180010200c501d03080001519200302c0c510460203625291a42140204001140c2090321900003064205071806184c440206003950070a080c10800801e091240601c46602c07a803060580091003180c08100076201a034030383c2034148940c8005424890f181c041058810301840403119000d1204400b1583c0343d198841c050308130304003510401c0d81403190700c203860100e08040e190500307240d411008550408075800100281d0354071030340d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401931061 1250 401929811 401929831
    0x50606011407170a180b090f0609060309160f0302060909070210110c0106061b060e0322060f0806030a060522060e060c131809051005010e0603160e 65
    0x315210110340c4208490030348103e80a60340b5515512480000d144201c0038030300c040e08222569040002e400034004980c480c0f50309a0700c004040b40e05800144031400340d5900180c02c0440041000000d00020075400312500c040b0595040e025122615507e1500460100940000d010401c3c0d0280c1e03d000c04449502240c50300c1154031a5200e4410306090390500420f20340c0f800300216098080304000c0c0a500042c03c1d00d0f15000e006110300c1c1c0c115030058003803540084c02680c1e440c2d400c0d16003000c080c4102c85068880c440c160500210108804c400c0c007c203407080c600010f2401c103000301000d10401d0b0031801b50f0380c0180140070700c00c01616000000d18001d401c040000300b40e112410741d5016540c06085030940038980004004042d01071032424094020328011400710100041c101c442d4001418409907401c5000a140c0d1f50980c20280c00101850400540f183c40b03a40c00e0b40326480600d8210a059a0001094031502e07250601499500c80d0381d01c40d041c0d4031040204061109581e000d400d1a8000d100351 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401932311 1250 401931061 401931067
    0xf05210312180a0c060f0e03100f090c0b0408010506010807080402100e030a0b1b0703020d08040f020402030a0e010b0102010c02030d0b0f061b07080718091b2601090506060114 77
    0xc188a4075121008100302e811404c503040811403160055000d440c410071030304022003182452000291100004104c02860079902c11004203030b0200c0750320905002e41c2c021141988241c803503604002036003051099034a250300740000520326521a0078407074000d40c3c81c0d44a041c40c41d12543d08001100e80c1a0303044004121115070981280d6600304000c1d080386000c1c02d07218a150078086003101d60b150303440e690311201ca07000304148000641d001402424440843c0b60211503034842e0301c0d01030000030041202030340c0140040140000944142c2c00320240c0d04a6600030070501c92550016820707540408a0030740560424419200c1d01d0b5519013150501e14001001100d41c0c45110001031400d400a004c0d01c4510340000426080038141001404054003061006140840c60500c02a022200082d6a038543d65100c2004030100000404d0810108101c5008d003182240c40c0c0b0703002c40e81d224054100c4404060990075245580c0c3c07040c4220203040703800030b01902180da142d0005462a080108030004012410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401933561 1250 401932311 401932351
    0x30c0605340b0c0909010f0501020a0213060b040f050f03062701090609030201020714030418020a0e04060305010c0e01090b030406180506040302011b05030720010f060f05210312 78
    0x90915229600c6400f04540b02c3c80c0d02d070140404c10f0310580002400c101e64000038090384ea000200d10308055070488680c40c820b90701c3c6a0305030107054144e0080c403003070340702103400308500725541513210580700207540740270203c856102016035804d03080c0c40f82035401c054205154450a000e810350072400fa00c081c0080340c0310b400c556400d030032a1040c241c00d0700141d5000c11240c007041031500c605400c401801c4000c506241c10102240d8a190840100d41000c0754002102c07010702d4011031400c40c507404005c2080080c0c650f00d0034400d010f8071b40c1e540300b01d00040b003040185885e507000d68803220603561102e04c000c3c00c5586035a200402800d414042400c084455040711001a0040006d144642d100b80c0c00415074800b50078241100420b595020018800c0600400c0300a40e03108180e41d083e00d100108030480004041c004600610f06001c1003556036041000c007252419400d00c46800302ca42c1681e00c04c1012a40c014003031812041550401c40c00d400c05c010030051603074400c5401d90011141e4a80341810f000b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401934811 1250 401933561 401933573
    0x513141f030215040326090103020d0b280503121b0c06161208090c09040c09110414030106050a06031e020406031a030d1b050708030a020601030c060534 67
    0x40c00c09082244800139050040100c1008018001c0e00d40d81a0419280300c0d44003400c1d0f003070007180d929034101940443c4007460202c0350740000420700c5020b800d80c802c01c00d8038506405011703d94000c820151031160b80010307407414000b4852070040950582c060814800441041e60b04034151010340107403040b1203076104c0310f98951000300441040c8819031540414107107082c4118012a508160a00464408000c074042001c281c007500c0190881301102d503940c440c60b0504003104203400030300c0b10360700e001d081c041c407440204001d106030ec1d4098542d4401010980c1054240c581d80d014064002c42b002004001907406074000c007404040300f0000f940007420b200881812038016520030000243c4401c580440910f204014001000081c0c0140c9541c0010080280040142801d03d200310180103406400b4000c040c4075181c0075110310f0096968991117910000d60b41c401c2800305640340380d900e42001442d14040c2040310450070040d4416032890088110010b540044540006481c0e28404058000104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401936061 1250 401934811 401934829
    0x150b161518050715090504021b010f0605032b08070302071b05040b0a0e01170f060703140a051510120c08071d030703060902130e0303010513141f0302 66
    0x50030040341d010403030a600b0910316000860780440420f0f15280340205416901c2844001501c1040d5405070342c1c0d41c2d0f20500c0b054000300c000940b0100354a081030781000f56465410510880700124100c408605900c2c10400030f0b404402006121540030020540c81c040c0115030240d80500942001400c020050700c403e0217004903296108520400400188002c0c9001d10541c1c0750041c0654403a411103090091810881006020b080c001c48525240c004100f00c0400c004207811003150103650042c00c1c1900c01070050000035201c200110059000910070315080c3c4540c0303101d196650310280d004a601303c1442019506e4440c841e0800c15540d02c02d000d01c87c9c03076001d08045100745030ba5240151902c0d94000340714094481a1078200c22100e400d800030f40d179000424109594000b0030020301c101a610000f006200000074a2a18038200741e2403485050003c001b440c100c40d0300799400c4184d8100ea0a682e42186c07404840d01002421b120086501d624207200c5610410400146081d0b910b610b070303000613032080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401937311 1250 401936061 401936081
    0x23030106030c03110c0a1e02040f0b030c0607030504050906060405221107030e0609040b10030c031107120f02101409010e01060f030f022e03150b1615 66
    0x2e403991005008a5810f10800040c0700840a032681010301400301161036260001000c2c0502c2060728844120700200402070a400307900800c10400c071040407101031b01a0001c4c0c42e0342d174400c3c06070280d0b0020a0400204542030182d0550781c051905080004001d44010003510180c0c21003418040401c55442e008078002000104903649085007000e0082d80c0191010500322880b5148148101d0700081d800c496002d0070000100c0c0d526441d90400400b00d8000d00036901c280c3e6000d55500c14690800c1d426a02247c0e007a251590107111610500d140a4220300c18004010b242c04c80505400200c2803260004030f0f82000a80f041d1808000d22088100a803a100c90305031225044000a00c14088400d1041072507040c4400d0007030185a18011320420340c010684806011203640001c1c680455071240d40004e640c1ea58a02281110441090307060203152a05443d100441e02e41445081b154070300c498008203d1b12180355071440c03c8030b514107058004020f00300c02c41d4200e1110082e91901d5801e8000c4203424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401938561 1250 401937311 401937317
    0xd090c090e010902030f070605040b1602060a090e010501030513022101061527170a02090112060b0a260307140d0210060f05040b06130b0c151623030106 67
    0x9940c1030041604049030800386c00703000c0d40020410041250000d007550201c4581c00707a01ca858001c0003035800c2c0c0c4103901940081d40300c240010f0144100e034201c0d00c44000c0d80c011180440b526038859005404a90050314819102034481c1000f9006203020403015215003c0910040d4094070700f092181d00f920307034540201d540fa945041c2c2d02d41d00154480c6804a1302c1100e00a15407032000b14045071041c05441d400303a00c00e900700e009250032414008014070084158082e00a410542e501c0f601190100401c8804898260810a20303400720701e005415002595041c02e034600c2880d002c0c544880c2501c00c0c01c0758125450009104480c0410840070001d03070741001c0d101c00f4000b83d0805c1140241410f40d802c0d0042d10aa2a19405000d051070852014003510015500000c9a2030b8420014101c0d0003081400d1070325406190001c103040b13070210040d09184176200221548030514100e90785800c4012250710300710802000040c5906441904000040001700f00608075510b1034a4068189a1090b0096004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401939811 1250 401938561 401938571
    0xf09040c0c02360609060d020a381e03060d0f0501090506101202130e0d0e030d030221060a1a091813021002010b0d061a0301110d090c090e01 62
    0x700007500c400310341000070300f0f500301e0701d040b00c001903007288040c000ca4029404600384900b191101084100178081d81600b0b80e8030b8100c41003110411036840c03030010744a5040c002c2c076000109804400c2e54001c0001420903540070b10314809880690300024191907000314032503940000f2914008010a84a020384008a1413651b5410040d18108026260200782c041e0640200480c004105140020660440704a10b2445c1600d914401800c420b06540005000e00c4548030700940d040628001506c5090b42a546003840c818825012030080016004010701c5410b00800361a01050300550b001d03100030601c0210725202c1c0703915009d03091018842445107000182072420f520306034018000e9000d0341e1090001e145000c85d401104824900300c021b002c0c494201a25141e64000c1d08103000b40e0501070b05d0340700070302d1040c2491000303407628624100c0c180c0c50003079030b010050070306003d03285450142c2000c1c0e51408152021180050005040c29100850803000105082ca210700501c1c0345c0300301020010034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401941061 1250 401939811 401939869
    0xb04020f0408070611030403030305090c060c06090d1404060e1801030f0308090d05070b1e19110c0a03050a030b0402030c030108100c140a0201090515090706050f09040c0c02 76
    0xc5400e801390000010702007880240c09401c50000704540551740d05107400b007035035150608190b1401543d5520075601103004118030601c54800140070b84a0f201c00c00882d03005141ca00d4064030b0042e54079160b145210000c00c01408034501402c0c0c00f0000c140c0240503c0c400c1d10b11a21040543c110a8008a40c00d40c0740307800d807406059200c044640c20824540241481070a5010041c0c03252241110081c2103520010020300204072600c89001d600d05c80035944030113031409450307540e10b042a0405510b02585042503c0c000700313901c02c1c140c1d0810064580180076000c01614156004d030000441d0f4400c1540300c00c07030600140c880d400614000c070498040b0b50384039410303d10790505202c450300125143d149441c561080f001e40c40f021825042c8000c0d00c0e03050f0f50700c0001004170f0140003041000b41c8144280c2d02500c0314040641c00c1c0e6403161400c5025940803684541c03045565108030707400801020000d120506141c40c06510000c450032503410000301c048c0440d8003169030285000c0700c00b201002070110f050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401942311 1250 401941061 401941063
    0x320105031f1206050610050a120f020d06091b03020315150705030f07020f030c030d03050a0b060708090a0518062e021018030c06092405010f0b070503030403080a0b04020f0408 77
    0xc02c076402d040c412308060300c5010051948400048550380070361a0361a186040c10150b040f580251040c80c0300f805200e80b5121010058642403207000148400c40d4100c4040c00d01c03034401d40380600905101c00300480c007890100201e10071901e00f1804400410000b500000b40104014000a0348420420344c40310841d0042005181c030040750309009411030340d21040d040e030b008249034500541c942000038194817800031007c0100455241c0310307000840003c04200788002e66014010489080310075889544c2c444043c0000708120b00c50900300d544072400854851302c9c2041d8050710500c0d4450211264408806440206d80080e41e500c80140c4c2008080e0145414540200d1038982c202c1281e0320f84010703043e5030046c2110001800500480d54440320a42002403407420034040d62240e8101080c4d03016580e12000090000b0b2003648409030903444005608c02c2c0d800d0549200e2608140074505540e1240c809031081c410041000c04825590f4511214554440c8003500090900310040303500c0b0b234104a691 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401943561 1250 401942311 401942329
    0x13090902010e1503180f01060306020702040b19060309020f0a14280303180b0327070e0708090705150705010b06040f05060a0513320105031f12060506 66
    0x5000f0314440c40d8103401484010b0499400401d16601c0b4030718005500c98080c103140b0003801d90700265082c06800001d01803203401421000c0e000711010403035580b2100810481c80072501d00c0c040b40e444144010080309001f9400003000381e0002d445660780c07601e40d0740000c3c0d82d02202c0c0c00031545c84555807040042800c09003605110442014900499407003000000000715400c3d100003000c014070035020b640031400101044004050030000c007a10307420001d115070344d0702036180c54100748490b040b041c05000900004000301142c092174491071268607450400c40780000d004100343d000340705119000a042e110040038100c00b03140c06200540f107a01c40e107062800d4844240b8107900c02c0e50700780700610a00001d0030244048843c01c5407401c3ea111000a001e480501600060503480e1580c0702c07000070090321201603454034182290040615a0002402203c125103903c182e50001d142400003803910304625021200b113000c2648459081a510072003000034112000b4116001c940b01c60034400710782040000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401944811 1250 401943561 401943587
    0xa0f0320030604062c07050d06020d020c0d14041d0a020903151005220903140304030302040906090c1d010207081204080c010807140d020c0d080106080a020702090117031309090201 79
    0x170040c1c040c4098206659801c014040d01d4401d10580707032488100a2030b07904580709500303892415034072254001c1c1d80c41d4440075411741140c0031a1140382e0354841480d4400031a401d03624054100c01113500400e00c20540014018214400a40d00708150700070366504002c1da081c4c0c0703488150f00c0c030101d29005c040d5012004095200e940100d0107426000c080347c1030221000504c030a071500000f45501e09003021100d040074043d001050440000c00d1006041c0d050300107100b51001c400c1d0a00001d035441080728100c03450400c10304001001c50294042010080408400107981441143c0c0f46130381383c2c40c0c444c2c10031a005a03820200c100004003003082041c1800b0303000080d4001d0034400d0b0385140c50500504812241c140b480300704100050100c074003982640c11f4a20354074000003140c1c04140501e802804100d820f02600c400f03e40b20340c000424401c80380c003c48002507800381200c10706920381507407441c2c800203203d809021b5000501c0b040c800c0040303511829004040d100404640c0002d0b900026100e1191004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401946061 1250 401944811 401944871
    0x4080604110a08010b01020304141c051606081533130902030903031911030c0d290603060a1706010312140412260d0b0a0f032003060406 60
    0xb05d1450680c0c01000359012034003481c8042540800400015400c1511f0341111160041c50301e04450030b105e4002640c0941115014103503500544504040e10800421241c003596284c010304c1d800160b05200180b0b41030f4482003101c20304003c0d1203082600080a2407020b1089040d4040b9280200e40f410882c0711008040d268421840c609000509039240d11006125406808481d0328980b0404102c1c0e002c00140c480c0c40e0400c070b0b07d9050121540030b2a034403460b2b4424461b401c12101b802c8610b5002ca801d42001d03001c113002480d4910b910700f0320940d80c0005001e00e1384422160000070740303e000805861440c840c200050032240d8198078024007001c0804141d10100314000800e88520f00301d00d8216001c1d01d0720000482e08404651a00d2244180e0b20301110a034401c4650f9039104100312440030f06010711001031300b40117803002c040a129034104184101c440388070400f4400c0011610040906c08480394000203282607503020b40c0407a103040c609581c21518195181c540494a1501103450040352110103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401947311 1250 401946061 401946071
    0x3060105030106050f0d061404050601031e09031710051002060402010507061e1b020106050d0b010b09060415020c0907080f0106030f18050a05070506030106020d03050a0204080604110a0801 83
    0x100000c010340014007a4005100b400281000e00b000b035801558111101500180f0140c0e4803103158110b4421245041405a81800003199480d80640145100c01c0f025852200d101c1040303e00540c00790050341d909406204a00d410802c1003d2039844032407007140d12403280c900444c80c0500784003940a10b46005805c6401440034080142c1c1e1110842d2080d98010348042136403246c000c024104023003000200030440389130404107006000706081d441035090080d0003c001d2503580fa428061280703100c100040c1441c12800042c802d000507000074024846c00a000c0900700303911640396085c0304407200000c0b00540c1c0b101000802600c1d042c064141d12000030300c2c0001c07150800d9400c4951b5400c0c180210300c21701d40c0b508021900741c0c0316030f8851900300e808440d50b0700181c0c149050854881d9080201503d41d40140000440d4070700307041040300d04a461315070080c041c810b81ca8004600901000c2d02e41d502031a000c01000a020008014260243d800742c2e562404d03281c48402000b101c8012079214103610b0b4100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401948561 1250 401947311 401947321
    0x30a050301090c090909030306050a0b211e0c0c0607111c0233090606011b0201020316030f0807030b0f01180e0c030708070c0c060c020d0618051203 65
    0x804256030441e481401c0c0030a10750594402035035480e040e50841840580303080040811f00d9890b0300036004982c3d003680c0307416502d603d0701c410f11085c0c071500c401c040048030301c10b2403400c904e41c10068150b40456100a80080d83c500d00c01040704098040d214485e4800c0046920b00a40f1018400250003401500380780100e1143c0b0320310355440d0418a600050780194510746200784600030310410030044041d681121210001d034500407000c040040320094001c20003400540c0d441000a4202d0081805031100220442c610062910000400008030304500081c00032156090010880c5036240e0302c25103c28100a0318400c0c01003191000400b160105401c0049410450725005403003d11040b0a10f400e010013948040d039514205507503401a00788564001c20032030003252280266001c0c10980d550b403039181e2200c1034100c0b020380c0310031130240921240c84000c12035540200b40001c3c91910181c0003500452164451004440d41903441010080085944c1d80402070300340104251032081d00700482c29402d00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401949811 1250 401948561 401948567
    0x5010e0103060e01060b0c030a03060902040302090c1804050a1a0a0501080a0b010e0a0b04050307060c0b0112050a020307030506010510030e0d0f02031c0920030c060d090c0e0403020f030a 82
    0x410700c40a0041ca60b2154543e500b0310003904001d0290040074462580e4421610620396039a12028040c40040d10304076001c15058064001c8604030f9400411102c07068a454007001c0107544610f50060307008140c402c028840b9191409614071419950600040ca69450801800b21440402940b840f0302915801030249a030400042134000e0b524090026200002400503100004900d501540c0300d440c0b224006203059070b8100402c2070314025400c5e030700405c0d035a40b4190b0f0030900315207005114000000062001e40c12039854441b801d0700610864506c8419500401d0900e441ca03082130b03480da0003c0d0018012400c4ca03840640c1c038410f0601e8100b00a0301a006002d845010402d0800c003040480170081380d900d131080040c0c0c0d000c1c520448003a41440149000c00c002044031200858540c00b03922046046813401080303840f245c1c0380140280005011039010400c999000c1501e0000c5d1a80e200c1e02c1c0d00100e107207000b60101800a0200300e03c450308050801a140681c280c103004d05980c8100291007c03e64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401951061 1250 401949811 401949839
    0xb0103140606011409010e0909070906120f030e0d1e02010906020f0601090c0903020907020309010210020906031504020d0e07140319080f19050a1e020309010c05010e07081506040501 80
    0x891150f134680320741000300101d44880303d055419601901c1601400441c1501142e2942200c0401c1c00800150fa6500302d0301c1081c0500c0304001e04900103019032000030a004070320222240500034400091504a956040e0419101d1482910700c40c80d04450b280440d44c201c180000a000180001c150310030303410601c0d507500c0a05004000b149a1900ea82405440c091122103002d141d00408500d001d00e002c01c002580c3e078000f11341660042c4a6900d559800c0030551080790041e51001d8007043c41c41d6580c51440f501002202541904103500300b02441c0c00158610600306640300c0c400c040c11480703103030070340c662020312111103028880e420103d020312403808406000d0b1702c150350201e003150321360b4508020a136071405078a9604c25000210000210881e601c60002d1000316125141c0700d44103200300103003200c1d0540b02204140075070300400104c01030b58015006071031280d00c02c0e000801c1450252200ba17040c611301d948100416803050750b400340700b02801a0001e40c014801e50f01000550700d0b000060f01c07401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401952311 1250 401951061 401951087
    0x10f050a15050616110a05030d020609060c040302010c060c1112070605060f090105102f0d090602070b1608071a0901020c0d053001061d03100c02030c0106030b010314060601 76
    0x71760301548410503500c1d0f059405004110003415110801e1a142010b03445a1003114454958043d441c001504000c81c00c05460682e070b0107035940030004c009613403440c000b095251000703414000100c9440b4103d000800c46900c00311100071103240c90b0540303407604100342d4101410161040207005807c40f16078641c0c000560448008990304c00c085000005c040e101d101c00e0850748001444141b071580c50005c0403501c2e1400c484000b500b29803000040c2d03001150091454050b0304010303000002c2c10004070290070064070940440906403007109241d0340d2518420f40c4905411603d0b00c01c415652020301c440f000995074444007984c0203514002130784120907181c0810302d1b2404107002c80420705541d00c0182100d8030602c0c542c810100006201058110350400800b482148000703410324003603800040c44011800c01403075001d8024070011080603e280054002c1d0240401144020b220806094900740900c134011402111a4a03065055051110400541c1d62546039258001000d219059a001d41c4c01c410113 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401953561 1250 401952311 401952323
    0xf010605060a03091b0b1809250504050603150306100f260a030806040b0402040f031203091b06020c0d02010509120118080c0c0d170c010f050a15050616 67
    0x1140c0f20319004001000003030000700e05c000e035108003003074009959004004500c965142c80c48140800820410502011112040c2d0182c9804038000040900c3c0318140324030000d410300c1e5003010f868001241e000e82080355030060014943e11400c20320b06060002c0c81d049602c01c5e1400c04240c2c1070102031341001e48a4800c9450b101c0035400d107001d200a01511101400035440c00391007171203441d410010084842030710f24500c21458550002030a1a0030f00c2228122035118410490701d6145848038040102c40b040356100b415203403051200010004440070f440e50f5030341c4030444480350800e04020300d440e104410a42c021103102900d00003503078010041d100d5484013210281440080e900320230703015100c0a504503503071158802d803450400c03003080c01030807c0f44104021180d00d00c00c100704104940038040d9000d4038500504c2d22820700c00c00c0880c000c0400200c50000490742110044200084400454004032120340d140c10088094415034010070091601303d038400d0030b180100c00120200a00c0310030050039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401954811 1250 401953561 401953571
    0x405150d03080a15030f0c05060c0c01030b120106032306151908190b0c04060f0c0c15090305010e06010b090f030a080a050403020a0611150717070306080f010605060a03 74
    0xc0b4103107030881c055800a00d544030b071440d81e0b24548442e1606d540b100480b0440048030300420719041440c165000440c1800040ca1185107190064005000c0369900d03940004600144000740c0ba401d00aa100444c41071025880c0d0054003002d82d24a18050140103445811a00501207654000a4644542c1e00e00f00d07a01004500c524001405076401544260200e008030140142c2401c0c502c0343c642c0c142801030030303854030954540034007c1d024401e60103500042101c1300d4481050134404d08802503400c1c03080d00b00410341030310f407405040041582030394040080d241000070300412402703015040706012540e0081c0354039410710308040024010f94043e01e01503040c035102c1400d0340d901009003c41041d0403181c003035030700e036001180104541d00c9400164007039800c0c0200024424402c2c50180c0001c032011001d03020750620721600d24141d4001410140400c070a41406201160020b00040e0150340f40d41c0b07000902030724000400381007054024035000f59900d440003c208603102e000889001000f0f518000803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401956061 1250 401954811 401954821
    0x20708070204110c070b180f0a03120c060212070f0203121810140402010f090f060e0f031c020708070501050d020d0204080303010f0320130b0105040504090b060405150d0308 76
    0x4904c4c06116010703100c0b80b044540000340d401c00040244400d04903204080c034803c0d0010144018426015000b58200c404003038208040751500b1504900340070140381c240443d00e281d440b03c50582c3c010340c4c850030024910b1814001d1039a00440702590080d0b0030b00281d410002c12aa00d16103988006108170503000c600721262402001c01c0c022a5026940d542003084490090b015060441504444c101d0200340c000f403000c0c2246002d190000111141c0c0c110f060102401c05a08850900d0b0b00807845801034065064101d103a502444905031203103441c02c0c1d1107010000c00e10006c0c03400039164003220050300016000d010590b0300404413515070510250148c1d943c50960800c00c02807281d03600c40901400040004a03030310b18000e4102044a01a2039038000140080724189480b92411900b1039101881e0b2544145400e107035044400314070814102035007030941d01c3c400303e01a205035241c1218035141010421400b486c2501c07a454011900c000362003610190500420024001038002600348001000083c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401957311 1250 401956061 401956091
    0x6150f1002190302010b1c1707020604030f06091a06010e0f030c0306070f030e0303061c02010c080f0c06160c1e02031009052a0d03021212040b0703020708070204 71
    0x6400942e40844021045420001c1c000d12404c2032052050f281d08a140c40021181c411070400c15800103000e501414540050181a80c082c0c40126001001170000001240b003d035900b03022030b030107107901203403090031490400509402c0c000c0009004c11620184070303041c0d9000c2c500d4104040c094991060904120001034a4880b021415a84c14419403042150080e80a50101090171094401f4088244803a2169449000171100240c00c240d9281c039148e202c003070041d2024407841c01814580d01c03640003925074440c00da108040d05081204002070202100c1800c00c00680d0002464641452046905000405203412210040c001d015602022280b5612110700c02040c0ca078001d0440300070b200c01c0e003000d1020f0024850306440f607009200d911200044403480200d40030710803210020711450000c0030800b102102510550441c800c3c814020b40ca03642c0385000b01142c0713010200000da549042d103000070340c442d001031150042600501450001444030419118401d604031400310306403009450b00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401958561 1250 401957311 401957323
    0x18030d11090301050a02070210030c0e0f19240908060703053301030b0913060522110f030307030e21061302030d0212040b03060402041a030906150f1002 67
    0x1440d0701d941381100b030004d501001e50081c07800781d1080c0c9030381a00f1036031850190212100501c005000c02c140310b800e90310500c2d00040014105000038003100024004031032800720100b0a8016516400e4401d010703050004030000104420f441501d0002003080c00c0ca00c1464680074058203610a250301c410118000840a021003040b08111080320848002032072101806040c40c44030407808a49820780c5030f03000d41007080103076204024011002c95a04101e5481000501c00100340c0c0e00c2d28031040444040c80e07006502910740950140e52655840001c030001c104c1c415211007000c034441d600c00c02000c00004d4021445100c030180480d042990035003402c80c89440c155119070070004a01801041008080d5640304110307043d03009500301d414070003000e00107036540c425101103030702020014407041044012404c000e540c030201c041e20150906613503041c2d9021190342d014040252850210400680080400400c0d81c080c0c1108082c59460b0a07080c0400caa4180f81d400050180c621000560700c203600030409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401959811 1250 401958561 401958577
    0xc090510050c15010609050913020d0318030c03330b15032802030705070f02120610030335040609201e0105250b1e18030d11 55
    0x10754000c10b40c210b041c00c030100f800340601d0010807440403001c030f40d5061104010f4401c03040103c80600f4480182c003048854403c1030f00480403c014500c0c1c20303083e0f11450680c00001c0d4401c041c54180142146803842861180881c4152003201003581c2d10040c3c2e4100c0c43c142003244c1c0440e800500c0d4400700e4003007407c1d9804035052041c0410700100780312842c601e1140c0d0103d440c0390800c0e2401c5440881458009900c400c4d910580050001d03c10030b00841c40035000100710314030081442078842c450380c4986040260480b0043e2140c02c015400700141030700300121494102043d035514203480c0c5001c80f00ba100c84140600c02c2450010480060100403541d4401d4104940140400216500701002c0c40604040010954001d0355003000c1c100b18120b818003410780c00a0140c40e4142064100c25024500d0311000d281020010280d2011002243c050f1880c80e0060710424003844000302231032660100394401a088202c1c0ca1b092a517484036400010041e1071650b401c0510100c2e100e00400d5590701c0c1402038405c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401961061 1250 401959811 401959813
    0x31211041205010b010c021311042102010f090807180e0a050715080411150409020a0210061d0414010b0301020d020a0f0c050c06090607060507021b040c090510050c 72
    0x500424800d410341d80305085203104078024801c024821004440e003100410300290808401d0302003007803010441d008581b10b802402500c90405a031104000c03100924003a485260009014130b100540d640510542060f803820304044200790b1070560102d644901e06e01c201007600c001101090107121958014034110f03010390b82200c1c02d9440a06000e0f4a0700500d200e4101300400c0704204d40101c50091464034402c940040740492400208418004040d51409816425000402010800e10034501c098440c5901c50360080420500400c2c038041103404a8102d001710f070200c4903004c5103140300310000551207503008806a6822040205150252100304951a8154004501c005000d91a0b07405402c8031361042d52104918035554609540512655034050182d402c50115244141031250041c15190406803030f0614205d0180c661a0896200340c400e54010b802214028030050f90300a241060207000305c401b008a0308021b02e0140c0611440d00c43c0c54013642c0b0410010030301c01e000c7c1c0260b40d26501810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401962311 1250 401961061 401961067
    0x20414040b090601090b090c0f1309020c010609050103080a030b0316181107050a061a060d020304020f150a0c050703060c05040f1208070b101e030b0a020c0703031211 73
    0x494a0301d000d071030854841026100740741c000517502c111801112200d65001d000c81c4c400d0784034540302d02c0195100c0c2041c4600c6c51403c01440390248010401d1030018115100300580b40c1112070082400c1d9001030b03015140d142e0401005001081c00401120001742d000e090002c1c4051140c0c001c81e007002100d40d00c068031885120070000d049000040300c090f01d0b00c01d0117000c020a0050701d10511007805005d101805544c00947d1000001e0500e500400503000184107244101003200c1c0020b44039400142010711860300842480114101030f0a0620101421900c071580079040121042c042e01413048000200981203000f0f0040c40b00521180ac0596000141800789101030817001c2d00d030343c1c400d1281c10910140042c00040105000d45070340070680e03001c608146410a1500d035156a000080d0900c0d0000104c00d1000445280c07094681400e0080760540545051a40c1403000c100c247c020044040a801044140e924132408601c40f404d41c2d6050070031141c901400d000c40c0004224202007050150707400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401963561 1250 401962311 401962313
    0x60603020918091504030519050a02060906010b09310504120c120509130e060106030f0b0307120f06050a09020f0301090b0115020109060501090f060f06080a050402041404 75
    0x6030018070070705a054400c2e00700e0104007001c1c1c00c0450b800700c40401e8a9009903220490107400b195041d50007038007030b183c502d080285601c8006080700300c0047c0640403400009190000c240c0502900740d003c094003019204561400c3c1c21145a88104000c4c28841d10a00300402c0c60310424001c00f055091031844816071031520302008000420065905444400d603060050f40468800d080e0040510fa11441d0108181c90708442079860b5000074401c81c0d44400e04046d0030301244290300c9103c80058180e1700510365545000381c0a0200ca880c640310206860411090b10001c1e103000036105c084651920740d00755a5003103420054054005041d000346814204070520800c9200c075000200c00900841d01040046404820035080f9818003500811003800c0d40010800300f41d0580f0442d404030001e0001040b50481c0350703035040031a8400d822140041e965048000e607910310601c0ba5001521103005141072150078460040e00c29030313004102ca41e485e0b481da00020115105c1c0c1d04001048000300c2ca00074464145 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401964811 1250 401963561 401963567
    0x30a0b0f01080f0604053c0114150102030708031023031e101508010e060a0f09080d02070314040308031609060e09131703160327150606 60
    0x4280300b51421803055001c3c4520a03100400d0b0342e07010340c5d408402414081039808541c44450045001400030029a0091062a18804400ca031552440400000e5680e03200812008007240152080d8140d11141c4e60000301a6000012119100d800c6840e103912030342c844244000b580c21942003812035102070b0307100d81015507494486803e048411401c0c3c1e85005910703091081210341010001d00e2544c0f28102c6020396221942c01000c821482e00010341010762681d141c60f0a6481c4800300c488190303c04410020740080c984601c0014002010091007440c915841e00942802920300003401d503580090400205401103940c9010a104010010745a86d600c9c10700c42e4880d01b0868035110000c4400220030401c03849a0452029950203840d0030b0070304c580607000d1001e103c60090440b002c0b042403415050104444500005a1413182355010350349141451941c05000c00322000c12050508010801e12110642c0720f00d4500842004998410b6510a05155941c1c00801503021407062902c4404076080b070f4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401966061 1250 401964811 401964841
    0x7051210061701050c03060901180b100c0c050f101202070203071404150312050706021b0705010f0f02150c070f080a03060f12020603070504030507060804060e0105150f030a0b 77
    0xb080000c0007580e840500c1d200c2c4c54841111b00c1644005003500602014082c075210714480c0c086164005024aa10001318107802c800500410124994a1032340082001454401014102c02d482101000240c00d0103d94090f200d40c0d82c950a20881c01c0314416100425815620465001011506525940d2a13102400040b00c0b04280c0140d00f801c41a00c0307061050480c8904803584003681e043d8000174014111100d40068004558030754003080307025142ea0b0202c2c0e8050b0204407260281c0469403800d000504214080c0c2c00f46801d1010702010b461105801154484038590820000d071059612400c014102e440780d82c00081000011014001c10b1202000180000c141c254a0410000751034031710f0415052101c3c480c1c0c041c074030380c0609800e005041c110082d503009100744c14030a0409460750744407802c1415540015001070341c071078100f0003882428010b000b00019401e00801850804105040300e40d180313440d825008520180504003a91810802c01241035045421040c0c90f0401c040e0301e0076190 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401967311 1250 401966061 401966099
    0x604060213141e18040605011d09030405011407020303130501090f031e03030e070321050a0e010c0c080706021e030a0807030509070302040212040c06110705121006 72
    0x25665a004141c2c81c0000084805205004011075034581402e0058900400e0051030a60040c51038144081d1036850b90151500480c400c42c00403a82c0d43c1040b0703c1744a981614916203840c02951018030040980201c2120256042843c0003042c141d00300d00d03c203e03203218141c40290140720002d50b0551544040b49013500341c070001d80c0c840c40d902e83e0ba141c0d007180c040d0450001625240e001402da8403480300c500c42450f0454407904011403107081c1060098204201584140c40c10349001071b007030070314070001c07002861400340354101710782803022443d00100040526440039050103103100c18001803008582209005101c2c0c1412207180d1512400000e440d100741090fa500c1070802000510082103010054400c040340c141d48211080d95120021800f03403501800c214007500405402001507260f90004048144218031104030fa030030203190241210303086a0085082001e040c0400c0c4a901c03000c80c0c0e0394100c90003181c490901f1801780e40e5244c103203000560303401a01d5140c2074000a410070150f9020000d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401968561 1250 401967311 401967337
    0xb060303281e080f07081e180106030b010303030c080c0901050903120a0306030c0b1e0f04030f08030f06090103030e04090809040e0c031006060903150e0d030608070b07080304120c0506040602 84
    0x2c3d00e510307100341c0d1110800d5507c041d0a07816030044030701030108802456032040310032035080d510701e20801d4032a08540503a001a0740c0e0344103c81c0184145a0140244207040c40607144c21489442c0c145402001130090500c1c3e1030400c07200081e441045e543c10040c4007101400d6842860750349240d2200540102400e2100301d0b01c035122040700150700c8060030142c44601035504041240780c080160303800d034203610803041c0e038071102400e001c007102140801c400d21001c544650310395540d0f401c1c41c020804402c1d00080600b4494200724006100107607006500f550f0408094030081004c6030945000352041c0030b010801030f009450075071403a05111300055000030740d50094003699000545120440305a6808ac06103001107030031400d00700001040001400018401d10f00000307004072110050600382082c001800000a407201c03814800401c06100c200010500c2c628403601d000c1c00c47d501d140050000820103404c2529514181c1041030241002c440b07070382d600c402540c0302c6282a10f44a4029004601c0480c41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401969811 1250 401968561 401968591
    0x210230c0409110f0301030209090f07030602040501030e030c0709020f04030510090b062e030207080d09110a0f0b0304020f0306071106060a031a0c1b0106030b060303281e08 76
    0x891420302c4111000c4c1d0500014440c5160b0840e000c1c44260f210140514940e032092100d1141050018010b800103980329003005030303450345418001400e694807104840c41c0c6030010040c40c50740040010718001102d000d00409a16490f0340140c40840f4000d60340040c4c60380c001c801520701417040a90019811912880346080d0f1601c030f080c00e1200404c05460b8800e85011180215080f4942c1c401c0c500c44200d25903d005440c03c11542d0308c145240c0c0105903075240282c0c0710f800320020017400200508007880c05494040c02e0314589684403550b02e20700e01c5100b84440e00080820190344449050b083c101d0b501130201c1e02c0d0b038185400000d207024150221640a03000e075101040d69803a1100d4150102c0b03802c4491003050205455002c8421a0082c05c0c104101004224400b03204d00c4803034880351242c251000010f41c0e58958200011840c0000b01298402d800c10400703e070708510fa510303000e0303030400b058400c44a9100410f04203481b5424145c2c100588189031010b08134000c0d901040d414030880601d9282c0c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401971061 1250 401969811 401969831
    0xa030605100809070e04060b060a020f0f010e1027080d0e010603112106151e21030705010f02041502070b0318070f0605040e07050403030210230c0409 66
    0x300c002c000d81c1c0c0710381d03107400002082104c1d035240c1001036086030181c94001405c00071000050212b500000c4410007680102e04c1c8044482c1c006c0c0008202c1840c0c410003400b00001c0b8410094840010740c80c0300501039900c809607440c1444540215a42100802c0c0344a10320301d03181483c440581200201075919810056400c0145406000e03210841c0c2d07110341481000b4012504100001c508120250f1b500503c6220300a4100401c200c001c1c065010034840d4004500e0740b40a2000c40d5138911058100d049402012041341e490742d1211011403100c0407044402c903840030300424254803031381e0005001582030020100c15510b0395030060049402400c00103068003201c00042e61500a0b5102d08241c07c0700a100280ca00c030f0030b0410034041e810181080e218040c0d11840906e410001d50b80226000800100e01401402840341c2140c1d00312146040070307402c00d440c541c0d009607500c0346086004546a12551040807480321584490300c411011015901c05d4548104ea076021608244a036501030f505141c1a18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401972311 1250 401971061 401971067
    0xd080c0102030c0c070f0b04051e0d12030b0a08280606080c0f01020c01022116060b0405010f030c15030f091b0501030612080310050303120a0b0f032508030a03060510 73
    0x901187d400b50101c50030a4680b100300111482044103085020100310800c00c203540d640b10313080024920600007040815826140141210038001c00d041c0200b502202c280115407000034808070307a0310602a0106014040c0d44000010050402c00034461070030b016022410000c00728041c503c0c15010b0700c4414841208000480c0d42c2d40c0300d0a815805600082c0001c4011240000003245401d45d080c00c480c90695091080e049030310103044240c3d9540c0d550030f4044403514003800b8081c0103000c2c50040c7c00703441d800d50700c60442c180315a104117214020211402c140650194004044100d20752004010000450528945c4502c000d09103c018004a071008140d56000b0b21561050301c0902e58600c07194100c030383e1102901d90000d0111070f111503030f90000003400d9a040004066020143c1c07030340b02040c10110102d10030f413050f05aa040c42111820b211070004d40700014550300301401c40100e000f450f0340100c00c4000d2403c25411a80c440c1c0400244c0051268054004908030b80040c0c03514545020002c1c822 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401973561 1250 401972311 401972339
    0x15060c030212041d1803210a0b18040203161202040608280c21050d08070e040b010c020613170c030a0f031205190b0102060906060d080c0102030c0c07 66
    0x1095840c94130b40c042d81c1d110305a8551640c0042e1a41e02c0c04105c0c14000740c07103851508208a500602655030206200e504a10300301c66420141e0f940c014030000784040009455952400308013041440074200083c00d559041103800c0c054400711400721412078689120a90703844140e4816806075050400008546200003123520305c0c0070825401c0303c941790414200c400f240344040c1c1c0c1690f8410500e0350101c0d07111000707081003500003000b101c034451044940c1303040c80c2081410444401405400c608002c94940c002d0030352100048225400642c025944005864000c003401c40a07400c20400320390325880c54140340b9602c06640c04070400d14042c2420928550307881b031a03064803e8141d0001e00801001a0400002e900030920a046c50f03410104003030303110f00c00c442c003c03110450808101c0c502451700319901d12138110f20800c203102402051030b004a425a596601911f040d004d020b00d0741c4243c05200900d025940303900030400095540707040a03162040c150b04001440040d50281c1c1d200000d00b00d41100e59 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401974811 1250 401973561 401973569
    0x19050d0207080d2f0c1002041509060e030c121c0509010905040504020f0907140c0d1209020906130f020f07020f010503160e061b060a0f0902030304031515060c03021204 74
    0x294092514031506282150b0400008032041c0e2041c603101b1418400940003620103000c502c03034102d0041c1c484000050051540d0ba1251051003038461005100342c5002c0703111410103500740c5200301d1000701b880700b0610302202d40300c3e101c00880a02d00c3c0b044290b1352000c018043c11909995451040391500b080008480050394000d40c440c640000c0301344c55052640980c0c0e80020281880001c4105109481c0665405119280320b50f42011501a240303940040440d2040d610203081000240f003943c1c00f25800e481c015003058401d44544510284150440e0442b945001c9200415510388600342494040307031f044044102d1241d03206030744004240d4851020342e072041088440c0410b50000c044c0d000c0d10304402050340507802a808214822400446540700303007418103008001c0005103401c004000c120341c078400c01d00c2d0307045091010740405a81c0000544064030b410030402040d1040b02c9030724038018800b2000d05820380c00d00d1480050700a4101041408042c02038081d207040c2815100c103d00b01e403042c1c0c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401976061 1250 401974811 401974871
    0x3270a060219020d0c060c0201120b010c11031911040b012d09050a0b0d050f100605030606040e01030b0a06050301090320072d080a030519050d0207080d 67
    0x40b07074500400c07000c00c0c0390301c128005065480c08000545070b0484024403a0031901c0854441c2e0541421564444020442c80320500340130030a0344103110008200d0f4030b0036100500781441c40424050035030b8050061034031040c9641c12044500c210391505000440300325281c80d20852500c020711059500034040501408558040d80c440ce42c96030300700c15040180c20b402201001541e0f00c01103a01e403200e01ca12001350000c511301e681c4844280605800ba40e0004282d406140314103407e003c941a000d041d085d060f542c9a042c02a00d9030b031814041390180c000ca600c40d82c860b40c80e500002007485118170510b400343e840751500f070222648400a0500ba9407062301d0080005001c199408046020180b00400e105407440c26241510340d141500003094000815482e251f03050300c50700f0540300160036000001401c84c40302030640144292006000d90142d4001915520358200518010511a0040f1040740f480f080045403560200e041c9184503403c5142c2c13040c03860780f0f800848010145002901d02c03104609907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401977311 1250 401976061 401976073
    0x150f0a05030309130b0405190506011107060c08090613030203100501052d090a1b11030301090b0a03080d0906111326071e0506130605180303270a0602 66
    0x2600b413000c900724207429081c4841c0d4840c3d80d100503580c0c5005040c0108401c066041c440c5404102401c01c403640507000303d040c0003d05070780400070000405c846007107508508083d201012217007824240e0740304c1c004030b0950141c000035500e0b4504015861302d400b524000c3d03044032003681301d40c00c011040303920038083c903a4810f254100f050310031b51103002d180325003801390742041c002002d080c00070031000c90003030300e035643c845480303056060b0700c0c5a040700300e051410840d00d080e10100d004158144d40702d20060140355202d80c2c5070301c00031404d92104d002080045a01c110208d80d51030443c41c42000030840e419045411509165050300200c2e00da00c150303200242c407900b0020019280030303803041d801c0c01222010901c4a0702105162071100041c0b0143c0c00510700c90394609800c140b40e9202c203140f003400b5041140705201c280528030440c00700e1a01041a81c0003409c250356180340c4081070b80780400e0210303800c9506100000e14030045c042010030080c121118000b2a280e24807242d002c115072141e0600500005900c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401978417 1106 401977311 401977327
    0x507030204030206030411010314010306140117031b01060512010b041b09150c060c02011e0605060a1407050703081e0412080c01060905150f0a050303 66
    0x645400c5180a05540c0091500e0002920140c0700450f01c204141c601d074060307031004411402d9019444085e683d60320300b040c040c000c00c4a291054012810000a6002c2105050398a021510000c2c6041c400c0541c40b0000d040412100c04802e503485070341c0010a0b4580b01000c030200c0f4054000400c621200805000584071484030703144001e020131440d02c003c40d0703110441e03000b80e0300d884160340d0304000c105d10700300c448642c0c0a03800781410746001d03a10340b401901584030010340c60030012248894440140d0b440e040300c0341c078414030f070708040100180d0780e400c0d1080c10885d018151001500f0b00703199480e00d1300ea2501d24941c1045400c0070f40020011264100f006201e81da644210034242d2825041c07640650b80005410001442c03402c01041140c0d03140303001e40004e80600000ca10410071850190f50100c0030301c1d0f02010345801503204c80c02c1944035003003020340c0100b03031180500154540f10030 = true := by decide +kernel

theorem cover : BRFrame.Cov 401798561 401978417 := by
  have h0 := BRFrame.cov_init 401798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401798561 ≤ n) (h2 : n < 401978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
