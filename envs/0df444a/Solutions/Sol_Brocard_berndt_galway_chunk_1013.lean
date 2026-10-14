-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:50:01.23681+00:00
-- url     : https://prove2.me/submissions/8445a710-19e8-433d-a5b9-179e278744cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182014388 ≤ n < 182194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182015638 1250 182014388 182014397
    0x90c0705030c160503070605190e03030f0405090604050408090f060c0d0c0b1501021509070306140907050616060905010e01051e070504061d0f0a08070609050301021912020d0c 77
    0x900a0001a071401c3d5203400c45442500581010090360b68000d065804440341175400600781030311050305440304038485c00055003501002c60304100e5404502c000d002202c40c161b4061059a8030300040004542003110010014013003806420f01e942008441d10040c8580981285e2030311400c405480e190200f098080000038101072a4507003006440040b040e007106481072040f801841c1100040d40790301c01905c0f94508410075200046102c001000b05800440d0005410403541d013074969900320102c0c0490b41c903041c600c80c118001403142001000c450304482c0c80124408540c0044d0b843d00302401011f1000c0d02e0035900c41082ca8144802841200c1c001d03e0512101070000c1101030300c400c0c0c0880c0080841d014481c041c0401c10200c0e0f0419109513000d411465200e541c201648001101041280710007504500d1101000c00c0040001804e4000d88000340c5a8007910b540d01c008140c282d104411031a192401d07265055440b9900036851844c060303a0394179000d410100d4046a10040303a618840120014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182016888 1250 182015638 182015653
    0x50114010f1e0b07030f02070f0e15030601230402040506031e011a04050d0213050406021e070206072310090218060a030210050c07080a11010906020606090c0705030c 73
    0x20610110200d10104104500c582280c5030010800090080713042c06801e200740700341d2070100244280061030113840322540708a0001d40352003500c3d50b03610f4103c8245041e0700c0b100300c1c0d80030302d8940000d02174101c50850010070202d1031861030700141c0409402c08150826000d01c000729a40e0b9440000e1741c80b8440c1100c0d9014449c48180e41c4e90b1040134182d0002d04084000c0a84594a081071b80c225000d0310000e480340c55407003c1c80d20100d0346203420520048402171034081444100100c1d500202210301c3c0c0c0c02001a542c0b0281c0c070f40300c0b80a20440d00c00a40c041c00411110000600e826079178203001c90054405a4641d904c540d5250801c107403000c001d0100765a41c4d0585045150140310200d200b0380c21904640b951a1a07000711344100b14502010348200440c0c0c001c0100b0500c100300321150011000140c40e00150341303024951740e030b0840c1142150ac5c0701e41c204030b160302175209000b5802220041d0780141525150401480028180078114002112003000101c020400c100010508420700070004c0411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182018138 1250 182016888 182016899
    0x80a020a06080408031314030711030f0d120e0f070b0c0d0e0d0311030904020711030705030105040305040e0c0d0e0c0108090102041409061207030f120822050114010f 73
    0x903640319400c11402d000509043c40f01040001080e25403048001080ea100f2040134242903084c1021250080010b1200164500c00c00c02e0000742c040401000b642180c0c1450b000301ca445481e0400d2011610000300440980c400301c1d0307c035400140701001c81ca003c0d1a406900d0091190824940e0303001000103240001d02c2100208013004181c00c000c0042c60302040610107440041c002004c1000044c0070001e62000a01c2c84031401c2c8101c80748414014011995008030340f810701440301d13050744d41510a00400d41c0014039424180100e80c4101d50564074a0700c0c190800c403840441c101c0290800765521401c0c0a8803003103800912500f04c40640040c0200003507003841c800180502002881040340e071340103200400400307004507030180b426641203501c2c81e1140e0700d09021414419107090b040655124011300007090103860b580820380e45003c1d02d4000503400354004240d41154065410390601031210340d803803104043c801078890b1498824000461440304129890f14210700c01e80142020310071540c000c120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182019388 1250 182018138 182018149
    0x8211803061305070f05130c1403090c040e0c030303160c06020403150b0d030e130906050c0a14031e0c07050d030606030b0405040b0c0c03270909160b0a03060b0301080a02 75
    0x2402114085d040c2c2904001c00b142c01c41d040b54030f001c21119101d5481155150044400346010384564400c1c5890b03180515055507036800c59600c8500a0f49001d0444820702004186450b11080c064020340c610303107030280050000240341202c1d60030480051405030016030740d400204002c6011395040405003114502041c21110700c0040c0d41e205428030001d0400094110f103030b2041d0350304101c84491204019958610103404686001010645410100408140c0d170714081d01c05840c0990710b03601d044522240c2c10308107100c181c0c0c44402180c09203c0034080503505019140c0d018044103011801c00020703076070b480c0ca0103460b00c25a00c0803030b80394070042c801c103035240c8079031002503004680500c11070401d600d45a091a40240c1507c02c002c1c400100c105401c20200216407800706140390402c1801d1212030821303450507603168603074400c40b610004101a002d0000340c0700c40c1d108108200802c2e41c0e290030440012540496074000900d51540c10002e5000410030281d8000c2051501801e1840c207244100803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182020638 1250 182019388 182019403
    0xe0309012a06110d11030a0b06040b0403230f010608190c1404020405030f060a05061206060f01031d030c061b07080c100f0b040608211803061305 64
    0x2840107000c18030741d66503010854140d032903654202900148403074200e80010042d129410034525460305120010039050700c1d8000551007940004400c125290b007200400c48548913600c03680541079001e10080c004107201800f0b0381c1c1c101132440b1b003803621018000202411324170301c90b002c4460390755920010402c00710141700900c080c00405154105241259807500350915241c0107100100201c9080c0c0407894443e50704840151030010101c480c006881407803c0c0e9680c1d400c0b00d50071b04080c1014081401424001498010510690003401c01c0e43c1e030b200240500c0342c00e10780c0604c0c100342d2156401c00e0440140e10b0012074120401002c2d60b520050442490724002000d80403c078800c441c0c0034100e00c000001c0d4145e4480c50790103241140e4030004404403c3c50000904c1c140d40c3d926180030b940000e0003401e90f010001030101074400380415681c4013882500c0301c0c0a804004c04400180d1a6082070700d0840006010710740104c1502092800300300b022034500300d002c03550071000660005603a02800f00401011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182021888 1250 182020638 182020667
    0x9030715020a05160503040302030a14010b01030c080403050a09241403090a0b0a110a05040312110d0c050f0303041a090105010f05040504061d030a09060801030c270e030901 76
    0x561a2824102c002070a40c85161203030790302d0394010100442048401c0c41254000c0d50001d04840f800d000301e04140790a0200705c020b41e0481d42c601400d91207d0350180c003913403945840c03980310f00940d03940c1c1d070310203803443e90203038841004200440a001c6490f039041030b50032951043c91100c500b00d00c011001d02a281441498040441640c02d0017080712002e4006400000b15a010404040546581150a025040074040c0103460803011030030700c0b032150340310380540200c0740224060701781c1c00310090050b110000e60070069082c54000a10204e0141c0c0503404484420380b140040b911f2600c0500c101c6400e5400545040750180e0491703013000d0b10f4075001d80240e508a030045000304825450034001c402c03020018400c0c0703030080d0348072070000d13080c031100e603000c0480340c040c00b0b4112411003c04030600f40c881d0b0005c0c14510115200c1c0002041a030311510040b8107903507000f103d01015509001822030108203145c20300e0700c80d000702c0fa0300742c52100040c0116407410035502c0003181c440c0304500c005420f10f902e21021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182023138 1250 182021888 182021891
    0xa05091207080d023723010c0e010c2a030506040c0e011502060a1a0909061f0e0a020c071503020d0506120c0d0c05060a0c1502040503100c0203090909030715 69
    0x18032030b61125260030b1a8900c0d00400903c03940700d0174a461080007142d0725103d8441b0580c4260102d9140c8190807c0104036500c0c0d5a0480c60210750005492507040f590010b0520903806400c9101c090b400d00000e000b140b011000000c01d65902d42e180c500e464012101201c0400c02400100800c00c07003500c48902420400585082401444000035078590300200030f200220340b1810b4000078090014005559500c6c064940e020b02d10345801400d40e23581064a680040151206008401644120f45030741520182503110050f510b807490f0710b1029412080c40c56856024903500002c0e2400102c2d584c2d660b10f680307500c1c00b503120120011207a0444070028002c0c0e0080c11102d800c48003080b4003140c1c41d42e440c0b400715000c890702e200798140103d00462903040140c12101c00a501090b0399006400780071014440d0790140d074901500c05812081c1e010f98403a6a405922503640000c1202e000d0300300c039407200c01510480e0300342031201d00017a0542c1400d403102d80c1c09400c0015060280b11035000e8952444604120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182024388 1250 182023138 182023183
    0xe0c10050708070305030c07021003050609100807031511030106110124030305030a09050102030901020705160b04050d1b06031b0f0e0d0f05030d060f060f050a05091207080d02 77
    0x22030084074803c5620003410094008005900419281c2c281c0760005e03006441101004500c010140c014a0300b600c0b114030503c0b96100160300c41c42601010b04c00d44410002908141d440c66494052413110351442c05400da880b13140e00c0d0f00d134984079000f0354000c003019982c04c4c40000d1910406401c5a040c401d0005444a0064075035081b07074148441001100c0d8949401030b5203556a00300d9000408100400134490750001090090a45054000c2d040c0b0300c0c000c1c0c065581864481105880201051040000985060004010a240a641818001d400f54100502c800d03503502c2c03410744900c2950011000329591341a1252079243c407422900e074121003814000c4000f03220f400090018104040f070244074580302710204040007140c0e41840390352a40801240c0c3c440c03008024000c0a8100c0c2e0140e81e412840710800000e04038400c8c8040c1c140148540c0304c140c50003500750340c00c55080d0321406055070080e4000607c6010380d6010402d21004142c0c80c005040c4040302508000e0401086108401d01c0082c81c14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182025638 1250 182024388 182024393
    0x41805011b020a0c0e04020103090c290c0a1e05240a02030601021b010c0b0408030609071e030f0b060319060b041404020703020a0c080109030e0d030c0210020304090e0c100507 77
    0xc01020646241c5007810302d01d0307991480100c01400300f5142c001c000701c07200788001070014cc04408990f40c10680b42a802c3c1c0c003000307900801c0c80900921400c1d07c2ea5501201445000c0349054100f480c070003205000500c80c1589644480c1d02d40b2030107400900302c0d00303e030001c20b49000c054808056048032090350b0640c950305040000030341c1c403c40c8215450f8400a01d502c1c86070715070300905c50f0640712988044145128605418501480c0d002100d801d402044440009041e440c42599002555009000210b402000040c0d08400a103c0840403e441c00c0c1d17140505046643e420000c0c6118846142c0969a0284070240200c15a90340d0b030b100600d0604144030901140440725001509400141e500684a42150900f2440d004a02c2409404441880700216142038190804484c442c001d03255490340002c200180f080e8440d0081c0040c1c0021010b003200030040c035081105403136134481407044074101601e408a82c02110030348105240d4662080300c082280d400e005000381625101c909005060400c0354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182026888 1250 182025638 182025653
    0x20306060108060109090606030207020310060e0109021303020d06050a060510091e0509130c050907140306040b0603150901120302030403080c0a05070e0901050a0e100902041805011b020a 82
    0x50300d940d05104245001408591080300004020001040c0a001450780d07000e010340294490300e0141d000303000e100001143d02c030841c00b502080f200324143c0d02e1116840c020b51040250840d03402e409122101c581e0010259451200f81e81c401c030b004000000709401c28000740c5040f54200d62055000d0450300906185032130f00245aa0102c420703007404c000050075034003802503c0c6500f45d00880c0d402070254007485001340140325800207251164058506c1e00d0380f624100800075000700c0c0c40c40d000500e0b0b01296010301c0c0d541006550003003005400829062082000500345403c12501282d1a1600141c4480a0720701100301a004010800300241c244c000d43c4c90081d180e1066000140450000240150a18030708010b2840c4041d00f01042d240029100e050301e945510342501c1e581d40641c20309010806540d0607100744825000c0300740060ae03212a040b0a2100030340034454042c1e034400d948000303481c0340c1d02010f540c00d98a07030b00c0b82d4000144044005101e11602815a0001085510110340e010009000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182028138 1250 182026888 182026891
    0x3011d060a060f0302070c0806060102120c0303180f010606031b08010b070305130f0806010314010b030c0108130b0c091f0203071113020a18060e01050304020409170c0c0405070309020306 82
    0x5458030103164800f440c4103078040c0c0f0507584000c01511810b000007a03444000304019020b07a60036400d0b80d655003400d0410400754000e07588010b28a0b0400c20110752060010810341c0c01c3c209040d002d681e041c2d0201039400c0c2c02c49000745c0c0080c0100780c84032444629081d800c50742021503241c0e41407544495040500c0801140110140241448000a1482030848842d5070310002070900d00281400c640c0c4524042e40c4405081c03008031020000c44080148185041c040c41d008464041d009100b05072034240115182040a01100801002802a44080348000b003000d84a03e802048082d941c100040170700000f020260480700e11071401d140f0b90228184e001c4100c40149800200c4118030050050000c0e100c490503081d082c460310310005010540580002e0145010210144041222039039000159841d21a51038420300141d82000041c0051a00c4ea10011809000304001d07000703501200c8000410351722080418149601c04c944550040ca0640120366205c200c074030301802039440070380c0032030381d40c480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182029388 1250 182028138 182028149
    0x4020c07030609060b09131101080108030a0804111306051305070912030e06030a0c030c080c0406050309030c070b070b07090b0a0c0501271109071b1104060b03011d060a 74
    0x21924030f100284129500914103030b2000034214256814026030352480d001602c0003c440748000f400000903590700441c08207040f04c0714207020b1482d00c40c0c4a403045500c281c0060003140c1c0c1340314030700a9400c107807904401802da10700d00620004030607003414104010306401000c50500c1c0c0d41000200820540d118400c50203c4910880d841d41904043c503060701c07124542100725070801c0000c010400f580c0c14a4108221100c0161820401110695403c8076400000c0b103010211a90802081000340c0c4a00010750380001d03c182620705002c4000440f0342803440e50b1f8041c0c0200740c008500c590a110490141a40000003428805c103c2468081d060400b03001d10616642440071101e800d100307100d029042008903003c5051460360400c0c0c007082c0d0b0039135400030314001d60301031800c42850358003410711860031030140707800d03031290010401c2c0144d4441d8010806281103407071a100c0c0d0f0b0040b00680300c501840300500803d80105481e5030421170700202007003060b51504200d45011040c071040d41c42d00102e0205450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182030638 1250 182029388 182029391
    0xe03060a050601051b0703020d080d050907050616140307060e06180c0f06070c030b180a0b0a0908040b1207031a011d0105040305070308090108101a1e0c06070e04020c070306 76
    0xc1d0750905d803d04045d102e40c00a5004a00c0c54620000c0003007103030062000c5044900100b180b81c444c42c170740c0c82e03964082d8043e080d04540200325560b002d600a4003032100d00e40c82450005949006981c00605640003e401220556140c0040c084990000d01c103c40d07000d41180320041007188010861651800c600360300078003c80c45032441c00b0b5961a58000c44040c0d40e041078400030b41c82d0762032900e990034031400c4a2020041400c54a0400d82001c0800e0481105400100e0030302c032034484050b00002071100c0341003254a54070401000400100c82d4018281402088012111614200034050281c85c509507401155004110b0901030503a0800600000030340041030b010854489040141c03114421600050164891048e00200304000c0000030720410300c0031b03039030098540c40e848880b5201c102107004402c002c80c60001c020341c2d035001c00d1014200305c19408001d00a2031411860b15511303984042c1407003c0e2900014100281d06801c810007038481c038800d0741c1c110310707045051b08190384803003440c0001041d15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182031888 1250 182030638 182030677
    0x905010f0519090305011116060b030307050a05030904060b03012409051908120304020d06020c100204060f082a030603010905010e1b030a0308070c0201020a060c0e03060a05060105 79
    0x80c85102502c40e00708107150101c2d0311030207094003c1c202810740d00c4200d6040d82070030890000090040309403194146404541d411803417140d031320200a00111072440d03800d4442440341101203401003051050303590189014690320482031013808284c40080c1c2018200c403504200421403289078a0003000e00c41180400c16412120201d4101e4804000d80d200c1540409080c840b0020050354138200000c941842c42103446c001510000f056541c041182c010b58000e441a81d150042540d9800402c41003400e901510421035aa45840049070059048100003c0e6041d115403c0560801d003c581c00c010710904e0650f5004480504240f001c0c04003164902442000c008181184c0302504a041925400b10003804054410f4841303035540c402c0f801010461f44407400c01051181400300b1403402c083c0e011342e03800c4895074903103000303403071841100c07004a04500c500800140802e84510820600000c01da95203905001407004161034600c014001d921030500c1c1c442400000e81e000f404850703901c0d1301c00311010b100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182033138 1250 182031888 182031917
    0x161e06090b03044205010e090309091b0f1215060a0e0a03021e100f0804120c0b01080105061512070e010c120c02040e0a05070306050a0e07120201110a03090501 70
    0x80d0140c28101c2c00381300d07030010307020881400300522000049000346000c0026aa84403004001e0751026240e00303803250010459503046091000072a035020032240c682c00030700e1011541e603032a00d9004107150820310401150600054003185c0709260050504d4020644d04550030000230014443c20904c1001e0084590360001907413101c0399560011600140740c4184807020041c2206254560256544a0100501c09513040d501910310803814013200c2d40d403100395907519500e03640b881c0341c49400d940500040105690015800c001e249029000200001c989403c0a80c144141c081050024000001e03080c8a0007034600110202264003071020715003240c04920000c0181c40d801002e10b80a841c1c5508a40b10f030b40c20580141001560341d109440c200102c0001c80502c540b22845014010555044503108101040c89604065004842c10400107034402500407518a03010181c1d110500f01c034000c0c2c20617425907801c90800340c2c240031504c000d0441440030b990001c3c2281c06500846040c8000007224145 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182034388 1250 182033138 182033183
    0x1209030e060903070e040f050114090601090203060d0203030c10060f050612070c080316080a112208010f0515030304051f0314090f060702010b030a060e161e06090b0304 74
    0x6100c0007000c40340c1750038581040e010741a081c031002c2d510740d03013051506101e200a50a0881c41050001d0103850306074240b07031030640139500107403905034440c01a085e1100507076410b0004010307040c0580018841c000c51240604181c80e040e03401f201084800510030001501c6440840c3c180700c141c0e190025055903138903800c0d42c000c00e1070403014081e80c00100c00c01c0442d00d50240429000604d03030710340780c0c030558968a5410075500022560034081318144900e1800841841c4100113550341114401d40c242d4a4540b950308482105500b00d03940d40c1c0300c105000301e6000c040c0c0341004240040d800f640ca458184004100c020b10b11201c231204054010700000600c5100307038040300921900101c0800c182c01d000f10303526552040c90f00745806600845003c00c1c0e07090b00501c1400b00c44200a4050280d8a41070b841d0003008000040404442d4003529454201211074180d0b2000580760124510000041c020300c4896561004e1f0025414051103a000744044110315080d281c0c0582c0c0800c80310442c0e880d0600815 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182035638 1250 182034388 182034403
    0x80a0f0c0e090708012d0506010c060203240402160209180313140d030813030c050f0105010614070c05060702030a02040c030b010f0c08040e0705040e040609031209030e060903 77
    0xd40501c54001402100c01d8042001d0080b2840c44c8020303c86100c48428003c1c0c400c10400c54017000c0508010781c0040d4005e42d821840d405441418041d5540745203884100c00d0b640100e07a030311500500c00340c0400c07840c601403050f8803400c2010f55003181000b0b07540d0390f14403840c0032200000c0d12611b02d0000123800c600c18600605402c034034490942c3e80f0f030841088090ba100d50745000d00c0703001c4800c0344001d2030507052440d443c40d03100390943e40c0c00000d9101d450031176581e034403505000c0e420400200c0c58100415004c211440c1200d21460000980d5031400c90f0040880884045041411400300541404150046140f0041d00e8084414681c0c0f0080e174400a0b10342440044021f4126050400e00d09005070036510203140420207880d4040448410401140c007910034440040c200f02c0280810f01c6094201014a81e01c580d05041561405485903a8104c440303d045404545850301c0701102c000301540000710901400c18001e00307229460755a0f40140020b550090181c4c043d140c0800c011f00142d07010800728 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182036888 1250 182035638 182035649
    0x1707080c010501051302031303050d090218150901080606011404210209010f0e0c0a0c0b15040c050f0d0e0705060403060501030b060d0506070305061f080a0506030601080a0f0c 77
    0x40d510880198464081d10b024810113200c1e42070300c0c15801c11720342c00d4000c4074850072002078448241e000b40d58003a03c1d96000001100b00003aa95009007005845103c1d901c9034581d0300c5400043c0034600f11a190b241000e680312036a020704491401040b00720000283c89810a00034201462840d07054011012607010b29400880d030b00210190304900451031221081545000390381d03070f00c004d0b0380b507424009000e00d09102c3d0940c84850000060070703019a05025100da00f00303501d0154902c18550f1514a4960415910100003214241111000d0f182a00c90034400c01d0241c24090708044901d004251540600b900f03501181c2d0b1699800018890244900b0020300002031500303886070740324200036000384030074002141d11803041e10100e04549080d9175020009030303102004203403e60303c941e400c501501c0c5c00b80c00c3c6a04225030703081c01c0e01103000002c031440e050042c680d10000710b446e15003002c2040e0b03140074045171700076009400184090070b07002c1054940c29401c1011030821002c2898444081000e1b40d014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182038138 1250 182036888 182036903
    0x70306110d020d05060901080d230c030c031903140c070303060f080309040f020310050105180d030f180305071e080a030207061106060109090c05091207050a0807080a1707 75
    0x43c0c40343c2441036100c54003c000c25142d80d60141c4c5ca82d4038561352103c550344800c0215400f80c0ea40d000d542c3c1c2084d003c0d150060040c0f0841d040014a84d601ea00e1500710700200c50654101141289842c400e40009654144052038240312104c1c005103000046036000e022820f081c030001484c1800e0500a400c00d400078000d00c514020400d540300820b07505c0341c020180c0d140c07007142401d00d00310b00e244c4540280c9019500710050301c0e03082885d101c01941d03033758890303d51450f03001416403018501e90f5030442104449800380d2903003a40710b0320b403110080180e10308500220703490b05482802d0001c00c07400104041039500c070941240c3c041001600203d440b042c598054041c80c07040000310000c25502159180460710a612a624071004c40d8509985409041b1a4180014140d000c1005940842d800407052208213007405d600e00340d9101d002c100356540f00e08041c030300d59000802c2003160342002c6c140040240300c80006844120305000032551142803c030303000b03803188510140d401d0f44225610215030700107038003541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182039388 1250 182038138 182038147
    0x112140105010e1804060b010e010302040b0a03020a020f030715061d01050f06130b0406080108150703110705010903110c01050a05070b1e100305120f07020d110a0801090212010c02070306110d02 85
    0x2404c9018010000800b03000030709e4190228802d5001c1c2c0242c034169010100300c503003001d100d00b100320001d41209800c03108601c908450881e480100f8001003030030078010126011030f401c2460b001c40940789260701408064000c03548a07440c1c004031b01e8005040d03c10807111071031981c118100290050103001c0c1e4500d034140789980000303103c5211100610440d0055211095107070703643c01e26503440d0541c100c0e03400c0355006074100040c20207220f80d0102c0100c0070b044140754101611600c40ea03003100c3e841a02107010131240340d0741c202d04400c1001140c080c0c07030003460000c0c504400000000d0050040e281d000301800040e41c00704004c4084040d40720080b0b014445403003103520300914035906049192009440d1070207100c0103151031107080e204a59040070102c403058a0000b0342e5090000d4404c2c030b10ba054030681200043c0c1c0c01999100115100203000c504000f0488101c00c2c01042600c0c5c00d44452510a03a1401101e000100c0d00410100f040300c0d0080c40024003119019842542c92140b200d0450718140b0025 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182040638 1250 182039388 182039393
    0x71404060e0f040504021005070f1502070c0b0408070605090a030b0c03041104050c3a140a090b06062b020a0806010207180b030102071a0103020112140105010e1804 72
    0x40580c004948111025441051600d060000304e8009039030203908040038900c405081809000140f0781640b2a132003004200d501c40c0ca9501c03690011014442e4101d400280e084181b128400700380000c0e081103003015241034913202c125a0348002c80d03c11074040c0907002c110300d0801e50342c0c418108021608807805400900d401d000e100c00551040302c04888410405811a100d410948140303803180d070754040380301c2ca4188140034484414100c0c4174815440c01408101900c50700890350141c9290074072840c00315a0307140106000148140042924180394946590b0b8404101d050345010317007043d000c1d91403580d1041c0d40821040c08851a008640b5020401c2201035101103459000b042c0482240d41c50702090b86588004a03141c040521550700c880f4280c80741603003000d60703960008482e900b00070001071512080d41e681c107030058007248082015001c648010019560041072031180300340b40b42c1c3e003042200f01564041d130701d139181030080c21704000a11000003031a88032480c80d2041154406082501d915161 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182041888 1250 182040638 182040647
    0x605040807020a0f050625051c0f081003030c05030c1506090f0714090a03020306100602071e060e010c022e02010b0d06110f0307050415170f07140406 66
    0x205089001c1e1000c007100003081e18552020310140c4a0040001d484d04001f0404103041040c49100202c100c9202490070b0001202003041d0303c05035074100303030402035005200c3c0007070311808030514200107100e1024108000060311008103410b0303e41c5800c01512450309800c00314035500520490704003903c10868070203040314000c00321902c150f100311981c401b03ea4074805c054030852015138804000c07036031030a21802d401c50504083d100c0305c0f2000e01202d14855480d000241307004815502c01c0c0d1300d030640b800c09000f010740c14010580038002c00d00030810b01d5a17028856040e82d05251103504208203000d240000340360310481c4080103542d0001c1c502103000d0303584007081c540748440e005140c0c00c044904000500c0e0b00d00600a40040350802003031404200d5164031780001405c440301c05d90741c241e50100440c80f841034078840a58000c01d001d9030b5503074507141042d040380341c03814110403400e050203402148001281c0040b816142d1062800c510101c00f5220400d0985000841303101c000090f1501203004507070607601 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182043138 1250 182041888 182041897
    0x1204050d2613050a0512060f150607110f01020a031b2f01112d0a06020705030a14040e0c0c070504020d15050d0b04032106030b0412030507270306050408 67
    0xc13110b0203215942d4100b0000c020000d402d2030020f58014500050503500b024044d943d0001c074540c00042900e4a080024046500c85001140d4105c800c060b00c108504110750351403a0705d0000c0c0000c002d942d032a910701418074188561281c046482810b007903010840c0301c000c140501300e0401c20000b6554014010500500101c60805001503000d035a410350480e070009a00302640500d00f0340440c440110004880344261111060081d8440d001031440010024070040c400b090050004d107444190480c8002c107070000709040c11524020520083c85000c1d2600c80690300500c02c41e88080d43c840010824609003915a40260760103071002c620922040402d0300301c903044a1460040c1101e9507114810004040700d0080080c107624150340010700007134017400350303843d1003c050780034802e01340ac9070b4460009844403601f088650680c9242403200300a24032000c01c0e120022400c05202c82d1500001c000c10b80490030f00e01595100020b000c41007103040c0d010f440c0c3c01554100105102915223030910f00300310b500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182044388 1250 182043138 182043149
    0x80405030115060806060703021c090317071101031a0d0507090e01021305040903020304091803080609060f1009050301050c0a0e0a080703060207060617010e1204050d2613 75
    0x800c1d0018a102e03180100d20030035a40140c4a600007a02c913034050020a4104482c00c505603c82c500c00445d481e0058103aa4048585a50762003841c0f03815842c040180c5080300f07480f0103150006000306c100280d540c00403a01d005a0030311707000880420400d9189050200c280d440340d04a44081404410300402081000c00d42c0c5141d60300703001c10380d40c9011042c200e200c1d03910210368a140602d820b00403460b045c0c0283d0443c030b010b403040b03c0c00c20380c507061903400716140c1c240b05103003000070200803400701500640c440e85e00c04001c6071548420f250840106039443701c2c0721600e5101d40116503e05124034092908217000c5c00c4040c0080009142085507000c056002004560100340003050904d094508a030449081e0b030071040140c0850341c91981c1d21400394004040c1220100d0b00c48c1d4021490441c07482803141001c054800106440c401c01c1030700e90501d040e8840c07003803101404100620070781e100d2401840401e50b01c01d031882c0c642002100401d515038080220300f5a0b111001444824404011500806480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182045638 1250 182044388 182044391
    0x4020f120d0219030c0605040804050a090c0206060f0d0b0912130302120610090b01050f0a050706050c0f091302070507031b06090f050105031503030406030c08010812121906030804050301 82
    0x494410f04000c80701010b440050009142d002144d000038219002603801c6441408441c1c20140c41d100061a0708249411032641c45a0341c1d4000180b056040080311f411002c1543c2c1c41e6940b01c02100420b210155882004e0301c407101d81310110b104034804000d008c81d80e250580e10079440b8140c0307010703840d0420301c2440141c0c814501110b90b62012000440c0d03a9010b0150034220458035860056000c001e48031500650707062000601c12542c4100600000304071040d0159106070740c075121882c0c214121000075050b00341e030044c140072800c1107012501c02c641160030102c404135034414080351a400648941075000b4400d010304e010000c200710000100200c040081000c2400491303c2d641d04484030030891061140d6003103081070401c180e500a9000790740018400b08001d01000100020a20b5948503038404400a0f60f2400a0903026500254040c007500201e00900300c42d0003013868a0040303004561100c0301d001c104001003100b0030f041040c14268102c040c0020701001d81d0b80c0c2020001c41c0c00c24840c190007075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182046888 1250 182045638 182045653
    0x28030206220803041d0907240219081e0d0f020a1d030703200405070e041d0703080f130602010501330809010603060e010204050a080f0606040504020f120d02 69
    0x410b0110589094841291084621000120380c030000024080c2103100140a610404103606c01414049007034002c0c0403221008030704014600900d48907e000e00103825008100d001000140840111900f0080b0141415804040c414561540d442202e00580fa09840c00500b68480d400a4000d014100750340d40381e2022513030340c0c004041207448030303008050b40c1600594418000205440e103002c1b01c800700311420042001001d00800c040b1a410398581021034010b0810381c0152a15002d080740100e00c1405400c1d42c0109200f0301130342c449050000800710b503c003146541308455101c080d00c880507284041c1490640d56000080d0082c0000c1c000c005480d14554a0305904042c03203000300c007030607400307000085c0003580002d000c486081000d40a04020754a43e14008041a21801086011000b880005030755914020400a501c10181e0005495401c070004a003450300011480982c0108252030204455460b40b00003409080e03d40b5040d42c0c0700105170500707030304c800e00022080c4401d4513540884070507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182048138 1250 182046888 182046899
    0x304170d02030a0c1b030b0403030b031209090c0307261f080c041e09050714030f0d030b1f03051905060607021504030b130b0a05062803020622 63
    0xc80c80f03550352440200d034070030900200003078400800300b041000000f0044000c2d500c0e9698611040740a8078140c001903113584000d0280d1505101450556035000c40081c50301d1a00000b040e020300780100002c500c5000031000404c8680600c011000b40c07640c1940c5000700c01000c0f1109610403005864101c0c182d4001070513017800d12044072551065400790b400820b418901441080003810804120407140c1e03d40c4041a0010881b50091070340c034911400c0075150590030240301100240d0301500c03480c0301c0c0d403003059030819000300410309640101076071402249500c42c29000c680b03903401d0440440912403820001203510f030703856131150b80a1f0b00034a01e540c03101c00c940c0500f107003650000d90f00030703502610400c4840300501e015405035122103c6500d145061550b40c0c0c90b12001e0640844100b0410105d1240d040100304402c0e011513800001907404002e1420640046464001000e440300d14040d842e40b05006209404807020000710b034010b0041e0790b5030341c1200300010b1148401c10b08003000889070308007060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182049388 1250 182048138 182048143
    0x6090601081218030c092a03040206030f0405030f040f0618080304061b15060806090604050a0b070309051b03010614060702010302031009060602060609070c031403180304170d02 78
    0xa60118020720b003424092030800d203064400d0b82e60181c2d68144500c10042d030160700d412034074030300c907010b11524100703501100040407001c00d41030b00c03100440440400030000103030790315000e80303810036003850071060341c0d03520343c5411032440c42a500046190100800c00048200562100070141c40e03442c3c0d1100e90107194203050342e00ca5030a50260700210b80060206018040c81806a085d81c440d84040d9070740144070715150140d1811061020361000b549403a010311010608110450700050300c81d000300740500e801d882e032946811002c90002c2c07016001202180310144290003c0e1040c035041010f0b104000842c00703488091400d0071507594003e5007484400950000010801211034074081e004030f1409840342d00460086d400200081c041552441e004210b0000611901e009000ca58004010a0400f41301304840d0b079000400107010007a007081c9180010703a00c13003040c080700590701e0100e523266103c40494101c00100c13002c0c58500303032001040000b2045580001003241d80354410030389800c0c6020101c00c98 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182050638 1250 182049388 182049403
    0x1031a090a170403140705041d0a08090103020f0c0706140c060109090201030908030403030c031401030213050c0405120a060c02031213020609090f0a0f0516110c120609060108 77
    0x16401d4102612580c00700d44521804030320286900d2445190503140d54580070001044424030f409540891418000d0341014443c1840e40011900000035a401130705140d551456012401044e601e400b05030700c01e40d640260195110b10764540031558841400c564000d603030b40400d1185400041943c44100940380105040302e00c00ca60343d401a040b1603017020464009800c42c1c01c1e00301d041542c0c8031071070b01c04201c505000d107000358825a00820102e0345240000c094541c0041d41001c10f100b15001080141c2c2c801500302c0f04c800c0c220700b01080300e50700c00502031154040d9602c05038220b080259004001c0b40049240a101f40c0320710001c000480160008030390b070307004940c0d4a0301c080600c0000708465042000101950740e100424480ca01412030000c01c00744101640d81070034681100c0140401802140911890b00d07508280401080c0b4045030400308420040c141c05090216951540900754024011066061000f0b00030040c10005c0d411504c0c0c1e04c4804565641e8540a60030000c40c0c1d803e40402d421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182051888 1250 182050638 182050651
    0x30f0912090f09061f08150102070b030105040f0605060c032701080f1914010602010c030504050c040207081611090702010b0604090f020c010c020d020706020102090a030b040c0902030f01031a 84
    0x101c2e4210b9a5006115805038043c0856601101d6000b52268440c100076a032107503519075640d040850306000702c442c0342c9034416001c0e850541d0800c160a001d0078502d41c0943c2d0441e1801c80380450340300c0321900c01500414464100580001c0b00040e410050701000009090307240c1124022a420715041c0c08550b000301010642d240080c112502007059128200e0f14560046181d110a08002417407180364002c076540c640d119032265040d200104001a028491000c9800a40c02d0600140c503003661966102d5281c03c912511455000c41c114090000b0942500c002c00c6914801000001460500c0041c0904800c480e91254500c0d0000490b8944103018120600f4000b4142e54102414041494007410a40340c010081c03503420701c109044240b0034001c000150312160050b05004240f841d000303003402c0c181c0d000700056a004000000458503404081d80c11650000c00c1414a500e0f10302c1e00000a448030341c0038460a0b4004400e000c0d0180e4420b803114100c078455100e04480034100540c4030b1100c0f1003195003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182053138 1250 182051888 182051899
    0x207080304140f0f0c10020a05060123120303061203070807030c020409020415051e01020c1c08120906060a0e040f061107080d05060d080703110102040b030f091209 72
    0x300740098082003440c4039100548050b0b990300101c03031152a10b00703100d010320390380e260340f00241461a5090812902500381c405201414041031030362511075847c8410301c03c01c1380d001f0000880360300c4e8058441002d9118040141058003020700c908056950b9082503d0b00e80c81004200415082804008210750040e40c1c004105030a011449c0c50584505900c0441039030015100c1014a005035514440c2c001d4035111749601611b0035040105200f4943c220746d9240d140c078100c1000903101c07680c000070700c030281d1034088901d444071100780c2030381d285404010300c0000c008050229089220001d9400340342d00c69042e040480700329680381000c100203100f10388580044840c4040120b004656004c0d40c690119000da800412541e048a19254040d0b21001050301ca5138408600112216003c0c059103822031000c44650b6031146107910351204030b2081c0741d4002c05001442c1038003041181c1c207406850041007041812500d13858001d0189007a0402106d4604017401030444914000c50840155490014060f14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182054388 1250 182053138 182053141
    0x2031f21030519080403020c1e090c0d020a0f140a0518041416021b03070b07050c030601060e04291003110a09080f152e0902040f0902070803 62
    0x118106081444403003602000420002c10000f445010ba072085619242d43e60950186485d0600900344005502c142c0d224800300243c21203010113410416100450803603041d0b030103407241d00c08030600340300b0054114030540c00030070070800700b542045d84803c004440fa01d0714444010304034100d00e038a00c82d040c0e03c00b000c28010b100c80d02d0100840301c002c01c289c0b0406040094480a0f0b1844021081d1007150f80800d02c01418054540c05a8184100c01c840154070b603030700313030f000f185640065141c200901800c1c00e8200c01060300000e12100f00410040c40101506a40003540c4486004118024000440f4080e5041c18080003101c46041c500b4241d0b9440e1404c26405415204104041301201c0c402150070141c40b4140e008800c440c030401004400c0030380c1c4603520304518260302681010070403a0046450f401c10212a003184043c0c81360543d108500c0f04225520403c100038541e01e1202c4e00c0c0c0210480d0050007004102500e05900400035180e044503e11403079036440c540101603100e041401442a6810700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182055638 1250 182054388 182054429
    0x40c151b0501231008010b0d020d021c0b1b090a14010c0c0f0504060b0f03060907030603330605150f0715050114010329150c0102031f 59
    0x11108021a407090300046400b202850030703c0806105840d82585100e03158080c0b25001d001c2c0c2c55240700406401009010982c0030308001481a001548080d00a40915000d542190b40c0e18051404886043c241d0b0b81d08a6001e007801c0c2c0c051902101c040601d80040d1100030440e008140a4681400b8010041c1c8105410500b4061200310f2140d40d0314107000140d9210b40005001d600280042d20040f40c064a0755860581008242c031142c0d40a00c80300501040b00644200c0c5840449030311a8064640c0c181540b21120214014030480d40040c02140c03144200348443e050340e840041200751000340e14152001c8a05031441122041d00c40d00e40d0000100421000c0680d004001d03000508290100d14184410b54a4054641d20001c11002c01c441e80c0e080148005c1070304041e01c19159200303203800c000c100c500c2c0049990710f42c0501c0b00b018041c800c00d840c0005a6a541d05101503e03000c40001c19101c2d040250764a020b500b0680300164204852080d201d0f8441610a00394121003038940ca2948556005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182056888 1250 182055638 182055677
    0x50108070512070f140408010504020f0a030807060e07050402120a06051509040519050c0c061b03130224070c050d050715020a0507030c0e0703090206041401030e01060806040c15 78
    0xd52144c00340900042654035881e000c002070301c014020075001003207510741032040108546801b031100d072207055021001d002088111042c2d038134191744988006600c2240d0440d4520380704456011aa029000140d2030744205000c00c10607006a10500041c44015103c0d030401005003400201203840c5402030104205614243d04840e0701718040826000c2060317990105441a038800f100c103598001e170005202d040500040009981c0403103a914a5050a0096101d12034103100260042c0751344001d0541c4007042d50b0b41e1400c000314106150301454981c442c407450b1030285811044054039104404580058030342419040d1700041d5070300c00040c20388213080c81e46030004021012065011841070260b2480014001c0124034044c1d8080c3c400c1d05a200d2406032020000c1100410003402c040c01c010aa00058039040148c0d4145d0301007251f0105034998960048008100c4290100764541c01d014001601b0640412641e0040703000311201c004050301c904124118070148241c00c0e0000d603502c4014075000700807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182058138 1250 182056888 182056907
    0x270201140a0c06050106110d0e133210060903020f040c110a082701092108040e090f0a200609060a03060501120902010203040e060103180b0105010807051207 69
    0xd0708002c44000100e840c0e0b102160001d03002040400c0c0f0015031150320390f404001420100c4402c3c9007400d87c182c1d9a101040c0f640340205044961217458948034a6503020305406070f0560401e046060340920700b914a10807002c0000d03114682813051412001c10300d644250b10000c01e0380c0d0003038449401810303e501800010440b041c000020816010002e240c000824440248505d02840c90b064440180382da4100212800c12028005522031803005541c50b40c10078a10012101c81c070003001c102007958168014900c1d540c07100104007407000039011480c5080101440d00900801045904420040c1c041c40d654500000007d0894604110113480c000ba040340c1404000364003400a030300f030003c10300205908cd08008a02004240c60700c1d4244203959004032880081d03d42c0940910080e80351f074001135100d200b2809240003410031200090703120b901035045900d00d00c410b040340590351200c1e810400c0c0c07000740a001c0d0900180100c804102e160307200d441501c0300140552a11642912009000d0710840351 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182059388 1250 182058138 182058157
    0x120f0e0d1110020a1a01080a02040e01060906180c08010e0c0d0b040e010f0b03030a0903081b1c02010605010c0c0e04050c12070302091006080606070305040e0a27020114 74
    0x101d40480401038032003864220300c0209980040500301070528001400d4288a6440300c00c241d5842c004102e0180d0000b04c1c02e00301501954005403401500c80d50318054105038014a02e441e0030b04800260302000d880d804d0130450406801008020462041203d50742002e02c20003407032203055808609000007120003001d0b420380b404400501d040d0050040b405a1703d40601c80704040e5980e040d1038a8800d841d0003101108502100074518010f0082805440071b492404040c140c540e0114840c41441c0c1e0400980e8112600342d01111016204040c030070880108036000362006500300f050000d19540150756500805a2088104092a04142c100040a64000c1081d550391203030a40d04107103622034580c85681440c008010f8440c01c0d0460060011100000c1c108100340006150b0801c001d50780030400300c5d001981103d4190b65880c0c03604040f10707540903e42000070142042c40c148100990540d00002035480b9004445a0312198420313864103200300080017074045200142e0000040101e030000b00351079030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182060638 1250 182059388 182059403
    0x1050c1005070507021c020913170d0606090e01120818040f06140613051002071706010501080705090906010305060d0b040b090c030d21110c0109120f0e0d 68
    0x205488150825207400b600d2482c0030030303030000314801076091806080ca1440c4051001c0781081011381d0105c0c00d25580140f0180d641c3c85644069800c20824009003025a01180c0d40203071030b4880903640c08010b11072840360b90003003031034800c000800401c2c0c45441c50481d000e00050021000203501c8001150744626034848950505491107072140e66144078422812032101c40009280f8200100701c8100403561018034480c07a01400300d1902c101040e044a01034540a0721a211b980d0369401060740340000360b400c210300365402c0d011340c41d20102c4c0001d80c00d412038109a07500c03051078450000a8415114000506401180283c0066241c0d4000c6e04003a401801c007400234001c942c0b05071944004240142c070704407100d034000c4090007075000042040400222007240644854610000b02401014040c105001c00340c10500e083c01d072844940c0e012840d104501ca0890390f4030028544050700038010501c0803141c0a1208000f91030344c0e44079100c5d41802c40d0300342d11205d1034200c00c0c02c00c100384041401011158003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182061888 1250 182060638 182060653
    0x40b040314180108011422090b09060a0501051005070b06030c060d020c0706090e0714070b0114090705030702070e0c160308071d09070305070908070b040806100503070501050c 77
    0x3480e01005010000030a0407204803070b5862000141800810b9100e0b005000040402c2c002958407002185d44020031546441e4154290142c4200503092600001e07180800c8181000074003c000700e251445001070708000c000582c0c0b18410801d41101004102002800900c12030001503030081d201c40d084000101100c1c0d0500301403000a001c0d500c00030001418540200d1400200e000400010003c0c20217030074401c8005045c074500740f42c1c0720340042100c402c00002500903441d0f5001c1d04200c442081c0c00c94400c004e01c0da110400d5240c42c0b81c40c08840303400ae0b110b15001841c80c40c4114150b81c040c051a0340a8109030f80380441e840700c0341e440600f0141c0418410081105c8442c44205198480d0f4421303100e000e040d185c400000f03440d004044005802c5100381c600061500e41e950094103500030b4a5080004064562440c1140d005003160895a1180f09a01c07004c11018001c0b000741049800e4003085800caa520707540002d000387c1c160f1051907056402440144030a6000e00090305110580200b1103490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182063138 1250 182061888 182061917
    0x415020712031d030f0a1b0218331c0506010501030902010207080601031b0609081504031e0203030912070507151110090611130603020d0204091e05010608010b03040b0403 75
    0x1994440c42c840704078500c002910316006e9030400300d840d0f035410034030b004a40843e90b0760300031414000c840301c5451003003a06200004d0180c00742d86078004030740042c4403840d481105200400c510760400c401e0854441c20440304810158854034100c1180c5030b0b4044054110780c0d10b4080150060049004100d055000d04040425855400c0100c00c1c0258001e181c03400b1440c881c04048684001d90703800442c10050a2281070164010004441044a42842500040740c0e81d030304045038040d540309820b00404042c8101741246940c0000907500800030712042d02c013031220315003002c030042c4140300008199420442040101c08194002c0c012800700b1030615102000280c01c0c440e0808805800c0043c600399140d110030700340017407442100e8441c0320900341c039440d2458440c03034103c14803014400c13a0205500003508150400b460b0701554010440500c060019400c00900c0306100c082040c1540303500d030300c1e140000980c10302c600202d81c102c0f040c1040603072030340d12a45c98810460030000d105906014111454072003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182064388 1250 182063138 182063143
    0x106030b0c03010609120302030a0f031b020f060c04050f060912070e19020304031b03030204050607060515150d020901020a0b01150315060912060b040c080415020712031d 75
    0x1c90450154480c2e940d6040070300c05403001442d070304144942010f007400c00700040d0700041112080c2c16075041800c180590034004402819605c03141c0c030110601002c00610701c80d00016104d4880c0f040c8009e8070030a550f02e00c004000c602070791042075880303900720341062007508040f40108648a0301400ea8280317403404d10700052520b01190300c22482c4090390010041800224413450408841a80081d4036504040c1c50060075407511010201500e0010151a010540607a04507402001c0180800e0f80b60101e03400d0540081504440c91080b641c070041da00420351510484001104466005203802c2c181c03008001381c025041404518150f116140c0008080b07100c0c6841a4001d044051060500d4200044024280c940380c0800c0c000d4001030b00d000303100369038008d00c08030190781d40c206164072060a0707801c04001400b070128801c1e401626003083c2030030321503011500510035405072500c100d09074282042034040340b0650201400b00f071401981da00c0c107507100350048101c111000000343c001524441d00d650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182065638 1250 182064388 182064391
    0x170c0403020406120b01120803270708030405120106030201020706142503020c0405060108130204020706050903031006020f190614070e0307091401030807031701151d0f10020106030b 80
    0x244803103a2140084c2000b1808980c45d0140120059484084056584120403404050030345080c0c1034480099203042c1c0070009210990301036000486420319915070071103845e80d10a0080300c0c050284a8590740a40781c0501402c402c030303a0b042e130003420102c1c58200100c0368085040c444160030388003089407000c060b026100a0030403120380703003441c02006007603c1c000c0e250081c1442d070a4059400c0c40c0400a050f070304507103030380c0d4090048c0301d107011910706610000b0028810388400403d031900d070006202c01c0740c0000010798031452184c0000d492017a102c800682e50b4000e520700c04242070703001d20680c42890141e0b441c8144d84a1059401083e50b60100310821a070010403289200020590925001103240400c0614000d11140b54100408481d2a4020915443c140000382c102c0100242100c00c0500c0340340d0f8843c80c1490034210a8007541c540804156420842d4001e40c002100b09800d00c00c110400914100c0860006002e445401d40010502c01c01c4407410f10758000f595a80e50002000c9402808500e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182066888 1250 182065638 182065649
    0xe07080a0b0912180a05040e0a11060d0203010311121203070513030807030305150a06050301050402090a05030706081b0306010203180a120605100b040503061f0515030901110a170c0403020406 84
    0x1403921320100701400031103c0d040c1e00540c451800d040308070059030700129a01f40b94a40043c4800084641e413400305502d40718100380c15004c103200000000074000400304410a00ca0100e45101c1c41f280d00505060356442000c441c404062420004107581c00e015000074044054101100b02000d541c0b0385130808180c100ea8420380100b52901e041000340305052400d8a020346048684150380740c00c0800043c480d000c14020701c1d002d140c0c00601603013a50340b1245101c004107030080440e560140c86d0a0000c081e50000e0ba9007400380039048007140210300c1b81401b6240300d4881a401141010300706000140d403010104030490304145080da0205840071102400c40e0840d008100200c0d007820032100c1100d44166590020154441c01d00090020b030f54040340341c3e81c0107002180074102010061030b1410304c8039034070780c000c940c0304a211021107071000d0b1100213903100b031030100700230040f030701e02c9841151441c0716165170007000504000c1c0341b01c00e090b2400d40864015001d0000b16050a449601107011030700241c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182068138 1250 182066888 182066917
    0x160c03020a0b0a1d030a05070305030a090602031617041703040c0f090e0705030703030801030803090c03010c0e01110c0a0504020a0219060603120f0e06280f030e07080a0b0912 77
    0x310356000e000c0704000300130103020100851074680840001001c60003440002000c0140c00004200b41040c542c01c1620803913003061045540e414062582e8030340845030100b8001050381d643c050804640760403d03241c40350f074101100f80c10301203480581d1801c6a00050040301e420080c040040741e100420250035015114000001407194040900c4030300e032600e01d6001c42e02c640d002c40010320005e640f1040641c1100c2d80905070a45039201ca400b480e0425030460350907074040d0f1030401c20b10b800580c02122480031550a0322a80c0c140c01503122404e848d280210300c4550800c026103c108070034142940101210282c0d8410f48450640720351528400c1c5252407001c2d10825254501030040c044107081d01240d0101c0c50512409000b95000c0141c002140409890701c2880081240c15061040c40301c2e00c511100c0100090046500307080c0081e11100e203082005001074900040880b80c000002034480a555400c0d00a00200c201c03983c801a444034010f12401660180501c02c46d03084c4007140192000c100414513 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182069388 1250 182068138 182068151
    0x10501031101091e0b1303210809150402010f0e0d0b0106030509030a0801050d03091e140411090f0a050310050a0507081311030102090d060b1008160c03020a0b0a 71
    0x4002860f50b0b0019200c1d1004180c1c0210125800c4030b02c5802c461521421035140e41580c2402d4501207480e070300240c90744030a50816081c00c900c500404074500e2150302d0b660002e840f40c1c0103156440c1880c0704084c1c00c21103008049400b40d03000d0b0800f60004212460300515000d080404180c000b02000400c841060711a001071000a8243c0601035102c03a0b848000d60804840a5004080e4a810b109450098081d241000141032181c0400c4000e404001000707000c42c071440300038082d20280b80c8100d0540c4a240500c4280900d03080c0202c1650b1102c2481007810302d0650000c01c042c840d440380c0041d80c05560040005030340c1c1c8081c8090080c503901e0200c00181440c0480c188000d8a80040c00d40080200310810004c22200101c08103c10b1070f000b12031151541c9042e8086802441024801a80902640381900402625412548a180741070720404401c041030101500c6264003907642d078150754101a13003401d0350391149901c0b24405002c2e10460351522410744070340759580819500904206e0f01d0b00d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182070638 1250 182069388 182069423
    0x130606050301090c230f130b0a09080c0303040b0c160e070906080402010c03031a0301051503100204050901151209080c061005010503070f0207090e01020a02060f01050603040210030e01050103 84
    0x1103203404600042c1455841200042060340c101c05c083d82030030040040100c0c00d135462002a100380e41c0c6c2d0f0301611160042c2c0325150302c604c050907002102c00c02c000401e01c900c08100301d0030100301c0392004100500214200b07030030f141c80029240c0009a40001c00d20484a005c00410b5541e0078032402401144c803141d0403401d2140005100180d43e40000f010b02c0005c07803d020060341e104055101c92901072400090700c8810807079003c5c1e0b2802690007107905600300020310444c1400f011420724501da0403011500054074440182061740928801d20780d0000c0c82c00300400c40c2403c00140300c6103454080c501500380720403075a0104115a10f5900545034284080b0300b1600010081102c0c541000741c00c50301c480d0991504000170704503c0002c0c81c1d081042038480d0100c6413180200304800c06400c09030f0040c48250302c005111030003504404112401440390a0120f110624101e01c01810f07100b000d0100307481c41e50740e80c080c406019200c4695404045d41c45541c00141c00080c03203014083c40c0318401440030035810b603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182071888 1250 182070638 182070641
    0x1202090303131d010b0d020d02090307062f0c010e06070506040605010f050102014109060f1303020c04020a171611031c0c0207080d03060905180c04050613060605030109 74
    0x14403803c0d220303a0070b00040c08026942e80689040c10540380015994441c07959240c0041e00a2a100e13680611440c000442c3c1144c000303608031860851203c0380b4a40010b08240040c3d144514000620305801c80d2200d52101e51250401c50f00c102406850145065516541c0d2480c060003160151022543c2e1300050140f020420040001000240300034864603035040c0d04d08113001d0f010351100000700440d500c1c1281c02c1c0301d03c2e00800001102030307044080700e01d0f0500702680c0710003045603071340709c0600c80f0400100160301c0b107982103541c290150300801a19900c5000d1100a45c00b80c040c01d0180040894406503541c1104042c91180122211b50a003140f0074400141c165400001036a419805c03c4c002e00b40c1e03502c6040c800715580305160001082c10b15030210140e0810300d054001d4041e600482d801c1c400c51580542201c0d044a01480d401c10140d9203060240d00065020300031403d40e0780002050869514103030308080c5d04000020081d400e00d02c40003400380d00715080e036400070000c20f01c048010480c1c00402e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182073138 1250 182071888 182071919
    0x10b0411090d1e1b050411032e06050702120106350609160503070302010804030f0921050105010b04030507050d082104050606150901120209030313 65
    0x589003400103041880e0214001e006007010705025411040107107003846a003160f600228502c1c160200f481c21140e00340016807260100004c0003010030404006110f0806200305000b5400094941e800d688500c0e403252000403a8002c01a40302103040381910260701039800c618001c08150b107581c0c0d6910311510607c030030414040f51101e8140d15000d8208400070391040b1009030100c00d0f5581c5501840d01c1d4503102c0b40400e845416805c10300c605410802064000220300204140e9a1071f16040c80707a4070400c041e41c0b01194000280026070b80300124000900425590440d2445401c3c0102d410341c80f181500400e1421505600501c040c00b1100c0b400e01c0000c1c8181800b400000000900d01403e58071404c0c0c1e00c052500c1864010351501000b0340501171260241c40e4010f80008240103140304075091848502c6003a10260b940340a15030100e00189003011030f0310302d0700d08041696420810484010340780342206620003100729408114010740d65405100078005800d50200300385010b82802c6150f804443c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182074388 1250 182073138 182073161
    0x1b12121b050f0a050409060603020903060a0506060f25030801090e010b21030409020301031b0602010e060a110d0e010e120403030c0f11090a06080f010b01080103020603100b030c0c01 80
    0x1040c2100d0040e40501224214420031294641d10300b0340c10b00880d214811a4840000a40ba007000030400e580c3c150010303c2e10311812012142035885151495040360001d44145500074420030034283c1740174012004e003820318924003504161105c10b00e014284401c40c500210000f036003c10050211544034406e8825400c0342d0700013001001c0c0f486000c03c00801c510294503504944484401300000d20400c1103031b02510344414299142d594900d0006004442201d10030074200c10000e0102d4994414407481c6441c142c10f0f0001d140c1512030180d07850040000861089410700c007040000d50880c410b001744c60a504000000017280c580219409080119403000d1900c1441c01700070800100380d0007180d4008035500020040401800b500d001074100035030304c01a6800a586004100c2545419440782c0120f40303c030390642c3d03152001244042d00b00e801102c4040e001c80c41450050026003488400f80d6400b148104280080540f20b6a0f000f540b60002c8429840e00103001070081c8110301d0a0150040220 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182075638 1250 182074388 182074421
    0x19050916091706060d050f0a0501020405040b0f0d0f0501060803070308010e070e0a0b0d06120f0501150503030d02180604030b090c101407060b0907031a090c07031b1212 74
    0x8044003042c50b1600c0001c1e01061213400c1080e0f080007803180501c40c10070284141c030202d03080d581c1945030032130203504503101e190310ae9881c04c2c1c1030440c24113000c0c00c2d042080000610811021104e031740c46106a1600110659a540d40c648001c2038041d0100010b00425000380c81d900d04c19803502600007043c4100400781c104101100c40029030a888002140d8140d5601c8844d15450312484002d48000300000d81c0030501e40820207241c04280018840c45080750f07030080000748054010400b0000103135000d4442d245d0154030400188003000c1681d40940301c0303034082d072017804864040c1c0780001c2c05035002070300305840309480d0388144004810100541802800c080c1e03982442440301c00c90280c41200050b061001e203945c0000d42c0402c0001c540c2c0080000c42c001400c00c0c05908103480024001c006210040b003107408500c21030107151800c499024801c1c044500c6181c54110317030780e804a079075600c3c0b1a1460318815134200c000c00028180034210582100b01c0e5035004040308115441001e582c0144440131440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182076888 1250 182075638 182075669
    0xa030212010b071707031119110a03021309020406090e010501170f030d050903071205040602010c0201290a0b0708190f09031704080f0a030e060307050403021905091609 74
    0x1005040b01c1800c2c032a544500a0300c0d110682000e4030800c01c44080c0030070902500b540407031074103502301c4500155405075031006c608250213410300c44009444e0102075071080c41c8042c1504000855007029000078030207030010540c03030f07528904141500c0b100c504040d0720303944540040c80200001d51640201c00c6a1500a0440c0200101a1610381c450856224903260301e90b00002d4034100c0c10021188015071040c09413070708141001000b40140c0003405030000650074649100c85c81803050041840d15409920450842c0c00400d036070510f004102d55400d0f4000c0302901000034016062000b800c038642c000d140040d941c0c18170146001c070307aa10f207124000c1405000401c03076101d5070307020300d0910959521405c1e1481503054180c0c01a041c0c019680700030b0203407151429501c8400d001003240d28402d403098488288410b41202000101c0c0800c0b100303480095000d1008002500c0c044001b1555501c082c407242000c1515a00400d040c0c050031617002c09060329200560031082d0384148901c0040030080383c0b02116 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182078138 1250 182076888 182076893
    0x20301050c160209150d03020a0b07020313090b0d1a060907030905192132030f0615030c070201120606050406030f0f06030f151505120f030a030212010b07 68
    0x1802c41d804800381c00740c03450030001501c02d54810107074000140020304024030401a0b04c1c00a42d5600760001c12a20401440e0218a0305400003003920700031002c0300700f0180185e0600400000a000040845900c480114070040204090183c50110305090000c10320840c80c200b000d021b030340c0b00017a041030201882c0503035540114034003144a018258244c00801603000280c1046107032034903911445072261310748010315401240c0003205404850540414402c40d4284071650704090003680758680c1001c0d90070400600103c2c8101c4a45a2281c1c008080481c042c10f00d00c41310300305070022200444400390000f918020740d078005800344102c100207001845000e00f8140d008100b40118843c04080c03603210045031044407110380146482106203102042803503900e061485078001030010a864070304290355080d0012046001d140401407140e024640038515080a000030f01101c0d80500115001d000400010700ea824002131222000d690b07001b40e26054646405180150183c0c46441c642d1020000c1c0d500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182079388 1250 182078138 182078167
    0x512030601051204240b03060f0903040324150e090c060412031b21020a050a03050f07050105071119050d0c08210a0506100903061e020309030403020301050c 69
    0x2044840100000700c2c40e184d078030b00800c04003c6070000e0f44124260703030100d0310400c6040c0e011182002048080725402d07103031030010700f0380d0900079260103610340c2003000300b800812465010010036840380c0c0312243e008180760f110741085400d000d09404d0080d100400c2040080820b1801d160445036003c003a009060036400003a0390352246200d5504180c2c05101864181344c000c00d80000340341404500c4580d01101c2d4500b001c600130001000c2d4681751404200103260903c00507602010940c00001002e01a560741c0f01a912030304035600c070501c106000c02c10f400020b1003e00450340226800c0c0c44881c008901000007905021070300a04440ba0500c00c84507401003413001a141c0b43c00609820420007441d503e04000d0312034802c10002203c040c0f0300c4040108038540d00106148102d04020040041303894a03800c0043302c080e100d40340e50020720311340c50600208469a0049401504581a50f01d12801242900050f43c00031996201d144c2c002250070400c1d403d081c010a903100902c08015031a21180228862 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182080638 1250 182079388 182079397
    0x308030c1207182304020d0c02010501060c0f030e0f120d09060f02060f040f020907020c0414062101020c070e09011d030a1223150303030108101a0604060c051203060105 74
    0x1c40c03030000045509400c02070804404c81040c40904190355594541c416003014007404460b1200642c40c180c00050918890410700c5d40d850b80c01042d0488404864a0072507002101c40c1c21a40d006150702c0900c020307556107415421700a80e405018207851289810040d00201107544840144954080148170003035000c106541c0c8a100044c4a56180e00c4038100846000300c14207000b500b0180900601c00d810781c00041c04d44a0f50301c21038043c00200c810700c031070307200450064030256040002012000059081c60602038080248240014104130b800c40c2404d00d040d07100d50242584100c107070709002c1498420301801d074400c1d26501c4410f001d003404044941d564814400d03202c0c100f1480e000c10306040d5456401110542551079900114003038041810701800400381c3d142c10100354004800003c43c02c022095034102c031001b401510000c8850030140000c0d015030908c103240f6542c0382507980341c0c5940f058040c00c0540003960f9003c4c0c0020007841c3c2940391980858280784200000d208201140c0e0b444404c58 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182081888 1250 182080638 182080649
    0x203390c0f062d0c09061c2a03020328020c010b190e040c030c14030f0604020907030b040f050a091209030b04032601140f0406030b04060c090308030c120718 69
    0x122071030341d00c11300311100c0ba005681d181a404400020260b6820700040d5a030000142159020028030b0400d1804031080700300305015100080340900d0300759065000b64080d682c000c1ca40608a00020f998082d03d80d580c00800d50502d240d180c0c041155403001e41d092040740c0c4a40010340b406c0340c0c00200c607140d407280c42d40380b031245a00d50541c038000203040108841d645401140e0000428070b22907220300c24580d0030b40d00040814001e224040c140c1140590000e5428080c80c2c01034944103071030301ea540c011005072048400c8a60020f860310f080b411840001d220b1684620003c14001661201034504880910442001c2000b0408941c00520100c1d07000358510741c00c00d51508103940d00600c52013503520400942c1002d64480343c41c2100006074451000c60401d01c018046070b40e004010175039401c20089508134080946007e50303030000100007a5103030f880018501c00d107042c111240c0c0c0e900e03a1440c0305176004a0300020b907200d0215540500003d001d00d40d48d00083c00d410500728007060210010540c1100703200c1ea = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182083138 1250 182081888 182081971
    0x3010306020901050c03030106170705030708011a1b03041a031501082e0e09030a080117030c030d06080c090702030703031a10090e0a0203390c0f06 65
    0xe0140b07138012011141303a001c0140a503503d0350394611016196036807a17440c1451500a503000926464404c0081b01c0c41140551180301e096402e20500e01600700f0b02090421481c602001181101d6518605070b845425569000755903560400301403064006c1d502d4612028400140709000010303a00c440103000243c2c0a00e4101c1c090b0f07840d14103103c0d04010503182c607441e48000300e1140c03180c3e0072005080310030380300c4265429411f0b031214540d140d9603114808402c40016240300060002c00882040401900b09001c1182d01b000303100080282541d0000f60b1410380555518401c000084061040e618240e0b0100c80c010305500e001c0c100692248100d0a00404040d940c541001d0070443c20000c1ca079402d04007078440780503c0d29140b8050100c1185004901350180782200180183c500c500891348103c5c040c000105441040300302407001b01300400082140025901d807140d80103ca014044c110900c0104001c00040a40c0c2c00307020b0030060b02524907030998000c0344060792135054001154004001540a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182084388 1250 182083138 182083147
    0x2090f0402040213080f0c10020a020f0409050303012c040206070201080a060e0702010e011b050405310c0f090522020706090803040c080606031b0f031002030703110304080301030602 80
    0x2600070300c90048070012489829102007061034000a81c0b91080740d00c0c030110340f41f0b049070908014648011540030401644084401c000508252221481e0f640002d0004641c0240b01d5840c3d504580098002031205555511065001c0252081ca100203030b825400c03111aa050a03004542540f180310781c007905108100022030902c0c2050fa11440041c14824540b040a08052310f009000c1d00c4500c803698415824401e42c011481d2040324a50381d1440c0c0c988800e4613241c50700c0c040c804003411000e1100c180442d0030100b03100c1040389004680000402400000d40513603400005801650074615007000c0101617042400540c0390718106001d8013201c4d1840001d0a9000e040e072074064414204010a42c5040c9800d01003000041e80295000c0d41c8140700b00da00d4291600e80343c540d160b00440310181c0c15071000c6080b00150200d2101501ca80d8009031034455001e40c03100c042444d01106604000340c1c00da00104000702207505209441072864002042c0d490b40c2040d0703d6000300f502041c040036081540c0001e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182085638 1250 182084388 182084393
    0x906060504170f0f0d0e030303012301170907033513030f060b04180f020108040201110a0b0711030703020a0605130c030c0602100212040b0705130b0405031902090f04 73
    0x8908403c00307841804580d5052240340c0a6074071400d1001c1c0d6480821601110003c1616000c0b055a040c2c0b8840c845040e5400c80148a0140c400030b0028268180800d80d00c03602c4021302104107c40c4648600d0703004085603440e40c5421061000039086c0b01c4c10f9070041c10f0806905a980c200854540c84411030610380312441080060821312060b40014090030364851494100002a00030702c0d94510102c408200c44441c015044050007000c1310028030300314001c3c0d400e0300198090010141c101d4018984032a6580c0710013081807609203000004d69242c3c82e50300401c40d07a55480f500842101c80214044c5041c105280d40181d40d6181110b4001d0405450780c0c0002e1071008074605c0400000d8000a040060790790300d003000340d035100d96801040300500035417901d203001f070307a0300c7c000c03298505141300404c45580e0762601c4104105002030048030400904000b0903188802011280c40940b1503044070643c1d5515100c10149000540c2030030b8151400c01c5910b00005d030b84c85588040d03210301e0741c3d4103500c802c1e80c891 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182086888 1250 182085638 182085643
    0x80112020d0c090e0c120a170708070605012301021c0311120403091a04050603130303110d060503060f0c04150302040f030c05030d0c020f042706090c090606050417 72
    0x15002003812910300764035410300050000d0a4405c0441c140d801c00c003042c2c8100c07119911941d1025015010b82501210074001d41c2c01d02c40201035442c09015400e007004090b07501d0300140d550030392001603a8214030007620b40d0f1401c024082d41c8280024001805070006860740200400a44503d080606546040d400201c09a410450b8480f1104107200d43c040e1800303180c090080d00c128090758a00b11401000c40d01e600e030981044500b0780b2401461141950307a001801c902d4852401e404508160b1100690400d2004090280200c030340c0307040c00802d0543c1010141842c062008214640b414014010b000c60302c405441183e040c0c1d101031042e10500d074802842a4082e2085900c2440d2468801c8800405d102c1160244400e4950882c15500541c44181c012217a048400202962009070134024404516107a0f001d80246107244420b1040c3c8840040d600d141e01c061504103940aa803902c4524080120300c03044070b000703848070150412000b82407140080141c007403805071b00c08a810b075103501d03605403008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182088138 1250 182086888 182086913
    0x1b0301060e010609030c06030612110102102a050910031d0d09060306060507050c01121d0604020f06030c12060f1f020106060f12150308070302060402030c01080112020d 74
    0x100000c407080303543e45080041120540344415180c8004c0031101041c2079100c0c0c001d480465814500c1740120400781c2d2a10040d05062140e4141544221404407008d440103014020754100c100041021550942e40d008130305500c402014010484100003440003a9240100d8815003295482d000032204c0a14411001d080d2904803110f480344221112070a24640c004600705c280d07143c0340d0707040c0002681c0c1ca0041d2560b00803038074001c000343c001040c03036865540700d8220440d0300d0a0921000c11120f00c44005040f40802c010030a60103a00003904010541c00c005a14400e13562056503202e1462a0034011390000e802001d500c02c1c284c242840100f4202d9484945140d480e101c0200602d0400701641b4400c0144081030401c04099400c01d8000940c480c060341d07411404140340c2d21031801d20010209220000d011744580340520a402c503101202050010016000c002d02c02e800500e510704003401058581410307064024104810301c0300500c030026204129072115541a140d0250006282c0b40800c10b01c0790 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182089388 1250 182088138 182088149
    0x140c090c03040f05070b070201021b0d1403130602030903071203080406201204020f150a110304120309031104150302060c0a1b14031c08090c090109140610021b030106 73
    0x4c0d404003041b6505100020030b00c441c0300b40c0842d0a0000c000e105c2c5002a08071070500f503070051501241c1000328100c40341c0e00004034143d40603640303869065198810b1541c01500064016840854410241d05003041884041c00c017010a100c0c0c152545c2d5002400a400200000c0860f40c031150a5040c0010130490010950645e4072420780751456841115035200d021103081e031040b402400d9031039881c00c0202d0100400d920a43c0c0151800c1491601500c840c010900707500068401008000f481c440c038503240340841480f17503850b047e200e441c60408040030800202031a10891600c14034440012510990804a0b0360503980c0d50744800b0701410311fa08126041c000581103082102e03100c00f140161184140c00e0b928291009904400d8481c01c0c561f480c04000601c622040030484024801401000025400881c0d08100c86010407150041000c0140aa0145c142e15440e200e0040348041060441c07940960b05940008010030300b500029590124040e076003806003030815940301c440e1401c1d00540080c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182090638 1250 182089388 182089393
    0x30405120f0712210e0306060f01120902010903053c030405040905010b0a0b0a0f0302092419030b2b0210050403080c0a0201030b010207081f020c100504140c090c03040f05 75
    0x40b81158060905105e0141c154480e000300c40000d1001d20b40114030410f04001a074071070018160408150300140b040e20000d9040c8600940000300082041098407200c110034000707407020381101e882e04030340034100d9944051801e01e0001d0070300348001c00100f95000c031002101e0102d45c0880303a007031660042102522440e000b21190401203400901700006002070b2540360b0340c03910280c000345400c608078040c9a40c015480100380c119200d60300400d06154502c450706124003480c00b08403140e400e48502c4440c4003100403a495001034940c0c1c3c94001100d403190b968020300b2000704c445161040d0001c600070a00280b00788540303140e43c44040e10038400c3e10065035018074120381c1d8001d0038043e02d07924485904220f00190400e01101c200d940302040c16021a0840c8005181c0000d03e00b0782d00c1030008400300c4a9000603402d10030300e4084c0704100710220310a282c807500002c16003041c3c00c00c41d086110703d0600303c8c0035920015007891a034032806047c0d81d1181210030990349984807031170440e03158049007101900030b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182091888 1250 182090638 182090693
    0x30c1207020f0d021203011703040e091c090e2a070507090f140106050a02011404030f170c090108060307090207030206100503070501080f060109090e030405120f0712 73
    0x11500082c51208400e00c0504480d90401d914100b26a503807401d040340500d030841440104402858140f0344814125000e066034109602d880c2204c09028041310003202d158020101c4000390142030624104000c294540002d10380d0800c2000e0342a100c0c09001405c0e022140c00001741c6027465800340e00805000101c505545a02d60300b48140d4a03245401500071a604c3c040c1c3e106c030140c1ca0f034800d52490362100845002961310b056004c0d541030b0007841d43c1c21b007555250385403d03080c2488002c405101d10310a49840e018130680400051000c6480c00044103080d00b42d81c01d124070100c1d01c2060702e0918101b440c0c11000c079600e00e000302e4181015548401030148c0085a96020107402051b0f8500c11031049244c00c440035030b92b03000c05985a102d8807070140803920340404a00c400c8101414a940a141814100100c1e0780d6409454100c54041040301c1c2c09400200d01031020f0700c0c4c902c07200707244503003180d00400603a42e12443c400e448600601ca44000b003103c0c590380304200030f07406030310f440f60345003504228102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182093138 1250 182091888 182091901
    0x1504060e1018181e0206030c120f072f0601091409070f210b09010203220b070c0213060603020a141201060e1c050c040e190305030c12 59
    0x28603159010b00e09058401602030800c1d2282c510403844070508a00c0c2c9002d82c26020340301c9540070049040351344102c0d00341c4481d180c0581c031140011809440701c8480550f0701d0103113038444003412a0242500002d01440018091840d5011454801d00707110100d40f598901d0f500340c80c18800c80240c0880041501808000140400060703001038054074050f105040c80f99100212103485034083e001e142092894503006008444004100801c24404050075084900745a19812003040e001c4072802010b039000410003858910b51103071403083e4440400810300d119900d43d29190b81560050451082091000405055540c2c001c0c01c00c502d02d0548104004c541c0d10350318010041e500425480022800008050010109400440300d405207440d0086180f40d08198044900c0c012480c0c520364440003880504910440f002800d04550b8482d200406100700c042c0f050006807826107010403000d40050f03c54400d00420000400c50139a4503140c110b90b280d452244c510264060000e82040d40360b4071604200c030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182094388 1250 182093138 182093161
    0x209121507030b060c03030115050903150402030c010c08070f0219090506010801171c03020d020c030409050108010b06030f1306140405060f1003020105090f04181a0606031504060e 79
    0x100c5031550280f000c00034450501809108410404003103070f004100410556452034150703000c1c02440d280140c034002c603040000c1e2600305c5101803800c00c10307070f400d00f440210300c0c0800042291a80030f003824019007407a0f8580903d50f01500f40f000e050041c00c0180f0f10115a1843c08544020102d8080d041c1001e446500b8400101001c4a00300d021480000003c40c00803034401d0761072010720b8100b0040040b1513000c0138904c61071800e4a400c50600d0b17000d00020080c841030740080c041d40c01c80d0030005e58640345450401026550182e0001480c0c0c1d24001e110085134642e0001c036607019804c0000503416407982d00c40c01c44820b5144001500281c50250100ca43c00d110b40111800741d80250112030594523000030708151400706803842c00400076040030410055019401800c0b0380380c0300500601c0992800c401280c20f03503256000701c444468007865203c04014040016400700750001c1e1125506d40f0784080482c00c130b4030000d0422600c80c000240300c00c58641e1180c002e00d0180101c80f92401c6a4100442c2e1507070f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182095638 1250 182094388 182094391
    0x120c03041707151404050d0f0b15030c060a090519030f030e0108100e070c020120030903100903050306040f020d0e0f010f09021818121306020a1502091215 68
    0x500c000168200505260303c00c1004124402001d15424942840c000070004c0441c80d00100700c0c8d91800400b03080002c0703a4a03040c885d105a002d8000306507003030360b8042014103151800090078030888042c81040404c6a20001e5581034580c280e50419540601c2d2194402002c5664802444460200030f0401055071145001c2840c820030b8840041c41e444001186d5801c0d00e0368024000c40121510014008600c0fa020200700c9600605015000c4002001844403a0340049444003865000080402113814100500c0c01110b0006030200104040d940c0c0092135807201903e560b1056840b450302c0260202c565040f5200311b5451081000100681c2d1016034490303d1940c0e42c000c0c0740d481c1c4407034500d06074454011400c01540c000c280302c0c40034404c2801c8141c14240900403044025400040c0110800200613074000d660900c2c000d103848041d0032240824001703050b0090f5017150040c49080300051800310803410603400081c0050b85a09011012070302202000820550b14842e0718036806141d4039150046 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182096888 1250 182095638 182095649
    0x210708070c0603050a1b142203140f2509020a080106090906061b050c09011404151203142b0e0111070303050702011e050f0612120c03041707 62
    0x303001d140c0e038034017940c8120740404407420140401c4070651070500e4420b461489107422000d40050808015003901203800307080c52008800032441540034814010710082404110300324134001d110042c04182d003191031750245004100120580740c0c90014518031146120042e001d601c0c0c045445208060f0010004038007880703180c000c50201c01c0c0c04210b200c81d9001724810b0750025210740212480741c2b0034102c0400c41c031030800d85480c01a490300340303695a9044421030003004106030040030720030b061040004445050441110381803030701004001d0b400c2c0341c809940203690107080000d40541c2804000311540300744001d90b407040000700e11f02c0901028032440d103070070108003000400a201c18410302034225044200d600d5400d030020f1050b240060300c04d0300304a03808091807001155181c001401c07140f8000490718001c0c0e1241e10707841004030214010100781d0340030b0f008880b04022aa450900c00ba283e42003101d0080c024900005c0c42c0003900030800132100144050640c0291624907600007648130700003802039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182098138 1250 182096888 182096891
    0x70b07080117032b0c0206070f03060609050d060e071203030e010e150a09020411090f0109050609061b060a020403120305040809090a0b0d030e041805210708070c0603 73
    0x4100300b416400754031150515040218a060070040400d0f68021040d240c02940030308001c0128503002c2d082c010004a0314030b540051289081207900075040000c000100300405107494410000254082c510400300d8400f80c400300083c00c1c1c9420007101804407003850710820703ca05840024145009070521910a01039030b820040e1a2700441e07190b00303a50743d0301c0d08007503e84d106220308201001080d4015800803034600300090343c49540c0c0e0110b0103071001c11b104118040d40220701030f130407410101c0c00d11104240900e0001c14050501c4000703180741c068805094041d41009c2071b103c41c00b008070700700701e001403180c01d04556080c40c02e00003c10280d401800203e60408406044604c4c1c28000c0c0550303070040d0b91010015041250800603c00440d0b402490168115100d02c44502c040e02c0f03080c1c0480303050780281c0e24444010a400144002d032410300c041c090a2003032417210350011610225078446205421845000805a2140525003e01890002a00d180302c0011448200400c20110104a9400707440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182099388 1250 182098138 182098141
    0x206070e060309100b0a1208031504090b04060203090a17070c0602070b032206020d060f050f0d080a0905101d0607120c0816080301290403200402070b0708 68
    0x103200450209690780c5000d41e1100c0000c5a40c50150781103c400c608000d04003224047c1e56650fa200c0c000402c1e4000e5540d00400010701c41c01c1e5481c408020305001d002d031410300c0903250a6407602c0c06031100510143c089079010001c6020036206000004034603812120000b030458820064080b0365210820884d42803038100300005100d80041030ba00e08891a030701c9070300d0643d5103a83c0d05440c2500c2d5014403145c1800150b034410006a102d01c0a044010b9000c10009509400c0c80b4204840c21030300d8104501c030f2501c40c18000100c0d51500840262a03501014039515030340306400a54003141180c0229030b200344c8402e8013428036a4040b42e050891030480348105030300c5110a041c886184194440900f07030100c50103101040500590742e403075020f88506002c5d807408203881501743c5c40c820084000c551040d000001000482c4030f910154041900d0301c500c0d09054009001c01101d64440c43c0b100914a1070b60354174803039140c0412200e441601d40003a005540c1d40000b880e010642e000f0440c0c43c0d00105030b00d0b20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182100638 1250 182099388 182099417
    0x81209040b010e031207020406030b01080c0102010c030b03030a03090602040e07020609060a050c0a1107210212010501140907050405030a0606030302011406240903030a02030705071a07030309020d12020607 90
    0xc2c101c1102c590f0140150503440c0c80071220386900d43c02800f050740c0194441a00000003924030381a40d0082c5032900140c101e01440314002820350749061043e500701420500200c4a641d0040100e58041c1c1d6942000071711040940f5040d03020740910707440600140b03c100c0401c0401500801c49502c5003c3e014203451a9554111884080351410750f040c038076840b4140409040309008035001c00c0400d0a81048491056071a4500398011445446506095070310418500c114204021841102a2150f000b48840c1d814110303480c0581c3c0c1c00d03001d0301d48918460400300d8205401a02100d000c1c0c580071303050b50340074802c900705040503080034070080b0b00541c85e10211021310085000c1c050301034440102400f1101c0381941c400c20003515240e0b1030012a030300800c42c0300e1040c0e40800085c507400000350090b684412650034a01d0506083d5400840700b009544090808044014120350000d68182800240c001141c00402c0f460400a080206605850101600e0240d00003c1a0b40718118583d19500b584d807060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 182101888 1250 182100638 182100647
    0x50a080d09030f050114041506060e150f0c0601120c2301051809040b07090501021c2316060f11090f01020c0a0b040f050105070302150a0204081209040b01 68
    0xd9050000120084018000160b91280c0c1864641c01240081405100c0382444c1032850b006a40c100c1e044c907400e0b002c0e0501c011150090000402c16410050040412140800c1c4152400380024036442c5000444070284d0018405540001d40ca2004481c095070b1038421464a60b0400c034010380b10040c48035000600e140c42c0002ca501201440382c1c0e0125802c0740040152420f81045040b00c000490031003d54035181c0b15601c81c10300c070b00e0085008160606164801034a1320b807040e0059411504101d2142d00051507002031601314805528180b1496130000082441101711031009454000d1f000910283c09409002c0d8008030600480f001c00c6451104401c0740c0440e421014050162482802112103900e0200d900b02c07200801801070310000799203100000c0d1030300324503085201410800b10782400f05900c0c44100c140600340c00c1c00d00314134003185a10040e641d602803142100c0c070700b00c0020024030f0341c0c45148c060307400a080700000c54040c41d54107003000c009030f04011600d0380554a010480c05256124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 182103138 1250 182101888 182101903
    0x311040b0703080c04080a0510050f0108070e0c090a031a0903090a03080c0709020304150e070e041b031524120f0602460e01030c0c020a0f050a08 64
    0x20986500d000940c2d54180c41030b490003465500310340f00c14400014140820300030a00704038450f401a00c0b540c4514501c210032a80050904824042843d006110850380022640c4c1511a03400f80112160745415900e0301030320402d0b08031508081207410003c2000300032007541e45800c525100030215580c4580c43d61350781e07000300e030341c00f0b54000405c4600f0404103007004014401c0914000030790386241c0c8c951b51020180d0b40140d40c1151081100009241708250b6403003a01d840d5001030025041051503c400507402c8031b4050406031140c81000c3c0030820b1900e10b0003d10000390b500001c9040040c0342010880e00400c40320030032408100409402c055640c4981805030207172a0035010400780c4a480b80c0303a050441d442e41c00304892541d400c00c2140340c841000d00c1003008407400d4039102c09844044c030541c218500c6001040c0071100c0041b0200c140055000703101201c1100080c40c0024450400e100704880c41c3c40c2d00103000e50011980500800c20791000b000b00b4040c0c0e141501c440d44071940d1084025543d404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 182104388 1250 182103138 182103149
    0x915091a0306180102040e040c0e0702060f04080901210e0f0c06040603051b1204060f050403091e0905010e151906080c0903010f061a090102150a1d01090201031104 72
    0x700302c0000d40300010210145403c68000d030001400c1c141c0361980b500c20400240d40c20b0341d10225a0904008100ba12656183d00110600c0a88041d05240c1400e07020214050b0000f00301c400d0105400c151a440348030000b10f40284511030460301ca007107001c2600104403040c0e03415114003e8590b211404038000030001c04a01c0040d08103071800345051130803001010007a000603054101c8480c00100040300801405402c11080c034809071a0134140380403411190903c202940203800c00d001c0002080d0031211001c200c03000301c0c0c001c150251003074030324800c020840d4000c900c1861416002003040103a000403e44540540440103407a502214108800c036a4010a40e40440c080e858041c00020b114008071600030040121450038204408000303425510000414444039585220410040840e020040032000700099001d00e030002d00e00000b0f440d0300707230060304901d401c81030004600c0078101e42d400840002002c0d041c00c0400f4004681e85070103400c00d800c0690002e07041c4507480401825441c216412544c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 182105638 1250 182104388 182104393
    0x30305040504051e011d0f010b090f03010e03120f0f0405030f0906040b0f09041109130504140a0c0609050301050c030a09050c0a0b0a081b040605070c0915091a03 71
    0x500e004204406440000c0a02e405402801e0704c004400340354581072806440091010000113036460036442ca004c0c5c0003800a102c81a0340c4004000410201046135000c08080d0303124044e001b0450040303805004148000c078103c0c44000384180000c2d81d036040e8180100214518608941c403400d03091400d0400544020340309420400940907580c560070010a41c5d440c000d0425070402e80d0b00c6504141a4001c1400140d2810002031100494642403085141c6841d002c445542024992004100004010310700304005942e03560101d01800314041c1d41a400101e001d04032021841107190800742c190139441000040ba04504c0049214035042c0502032144005004040c11a40c5108c05103010b4000c00405441700e0007804c44007489625540c0c401b8010b00030010300281ea44241160007020b41400500c0d03070080c0716442201041484500301140c040790b156190041d10b50440d400c10b0050300809501880308940380c203019080c8040c0c2c2c52030100440304004810440c45100e4080002c2c43c0d220b01c4103280e03168 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 182106888 1250 182105638 182105647
    0x108030901140c0a020307060302041e0315020a090b0403081b01020304080711060d0e030901020f1203010626040f150209030606090a062d0807060509090c0c0a2a030305 74
    0x2c4040714041c1c08401118800c50361805090b4022a003024050f8210100003a0005014460a444045a149a590390002800b900b62560300c1c0c4a01c09845103001020858001a11510941c4a10210700c007800042c400943c0d9242e50f031600c651182d1054401e0740c010b501c0e1214143c004c402c10700c213880c400c1e41c010001c070703103488100d41d01c01002415a01d004d5038071500c01d001441c0c40d03030890b108502e0340034016001150785003a00b03400a403500b511201442503650110700390003142002a820390741114030509000c0b0744207071075007a0744003050409004940801c031440c041200703000d4590f081c01c06050007400d0440d181181015107100342d206034110a60990301c00c90228065091540c0c48550203a64540c00040c0e041d220003081640c0c0500225550000842c2000d801c82e08100d2070030b290051030741600510200c0d14117440074190b4014003112030b1240d5519400502e55038500b0007190500001403050b03038074080382890880081c00c248507000740041c80c1545880041c24403e948001982e406440d25400d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 182108138 1250 182106888 182106917
    0x20a0f062f06070801090e070b1206120307050606090c0405090f0601020c030d17010503030c07060c0206070f061a100c0b19090b0906070e010903060f0e030417060108030901 76
    0x440100c00c140c94610000c160285440d10501c0030b240615403e41e81c04000b0351500c00048181c1c1c142c403c840502e81c0000341c080010300c00040480c0c0300d10006903001145955054002505411750094101060100080c1d030b8040040c041303800c1c0d00c540800c6503050a552038461804640f40510301032250401e66010118030390308950049146d1080051045944005076540400c0c1070800440d00303e8007082803c00040180282410858090802500194184403001281c0c80d501c00b11071007044107110504050005648401040390a21604070f5603e000108280c5809801001520290400c3c0c6200c660b56144c40d2030075a482c0c00e0104500d5403041056101610f8680300e0020207031210509403100309820200500900601402034010800c0300c15030704c0c2259070b86040840080030075081200101060300303140c3e08902100d080c0c0e60081c0000131460349454880008048002d200c1c03001e0b1001240000b51022b04851015100d8180b5060b101c1c0c6e40d0340c1d0071100d55640500400c1705e0108140001c01c090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 182109388 1250 182108138 182108177
    0x20610120203070b040b090a120b06120a0602191e08160c0203070b1b060402030601121b08030409060603020306090f0912030f0402040b0d020f130605061303020a0f06 73
    0x544500042c191019903070344a82d488034981c0560b20180080c5408200403480380791510324400100008260700300000c882e03643d8814080030040c04144107100403000ca145a4a0401c4180b4030203520010840d501c1080c140c00541d4031a130484440d002510703242c6000d03181e5000c40a800111482e0741c44032022502c0d51400b03401900e8120700c0e002c080202070001c04c800350781d040240d4002000b103105026695281d0380c50b84800d030362080200503401d51102040c8001030304d000421604441e9001d0004000ba841403400c8061040b07180306841c221900181e0206918030084024401c40340c0d0703d00c00b00445640d4a0040d01030340411030340640d01491880004d0902c51030401c540e988078201c00240d0302d43c0d420520103000343d41c00954001c500c40ba0300000300800c6040521440317407104022078900228403a250b00040e002046044041c3c001c40c07850318000301c0c046842d08404040e040007403400c0e031520a440e00c6481d09561502c03040c0c0c40b440084800080c00100c03102078a0503070f04150380300902c02a442e00000c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 182110638 1250 182109388 182109419
    0xd020a03080c1323090103150b060c0607090e06040c050412080c030c030405040b090c091e101707030c050412020312070f020306070509101206030b0106050a020d020610 74
    0x54400000c00c03080c01c91880c0d40c3c04040180c110070b03280010399502000844513080720b06400900500d0510010b10104200c080003030b02c1940d0740940440c0204506010500e0707405217051581340b600c550b40500900c0c5821041d010280c5041d0000c844280e0744030010081079642c3c2d01848004918100402c0c01043c03094a030b4032031214040c05c2000e00d0880b001030718614580c0300340d82d1049281c1011a040c40740c0c1ca003902941905510465424105061a54890240b4841c1d114001c0c800c026080802c0c0fa12146801c403808280c02c02801550015008500545104c1241c03c2d03c0040b41d218500003944a4024403c2c20300302c58007665081d04150804404880050211b24180e1313262082c0c55070100601d01c2c3e08002d10b903561040700c1000c0704c5105441814035000300501100b061210a010880c4c40c0d459101d82480750319543e00e002c207040f84071302141b0b04c002c001e1070300007400c40203616001040040e044801400d079440151308486151880403412070300c42605840308901020110b8003040300160703003011103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 182111888 1250 182110638 182110651
    0x120a0e010806030f03120a0e070608060f2101060303020613030e0108070306090f06290a05210702010902030607030e070e1e070f02010b0319080a021c120b030d020a0308 74
    0x11480e0015131411145103400c0b40b0802050940340ea003c100003420940900340a0f401c2032001091450305000001d0151103000f044070b0701906041d000d007030140d9281c031000520400000a044582c2145d03000c80d6004c0c00c003038003043d005441860041a5084402d0034048143d07501503507070940807502c030001162501c0014001c80e04041d10341d4008110b00c1600d11440b107514242d00000500d20b40381103c075405946106807000c100c0260010b00310b030380c1c5040078100c4000b94603a150541c0e82e244480014400c580c01c018020b103c0420340310400c4001a01503114012840c0200c00311161a603c9000c00c4099951140f800074252308140820000c52016241603900b1003075a0040da560300407100c0404c00c030004203d80e081d000803950940d403c00c0740e80a00c544c00340644264040d00000c40e40f18041c0c02d8240ca40b00005214280020300210f4080c424407076000001600301c44000c980d4180203006100f001203d0358810300038078003054441980b900042c100034000841d00030300006503e603101602c40b2000100503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 182113138 1250 182111888 182111893
    0x4030b06030f0609162427030b0604050105090c090402070f02030a120908120714120a030219210c030605210115060519021005041103120a0e01080603 66
    0x1010b55000280300182c40348540400502036008480726502040c40310f58440650168a500341c0811424403001c03460700e41000381010b4125980c0c00302c2e1120050702d8a00c41c001888403c2202204000c140610313240030f03401c12101800300da620f9004114042d082a22004800c0c0010003811400f0700382500917095040c02094001085941900071a0414422078421588041c2415001204503007002c0c507030300600411002800d076140090092740280c4200b880c081d2402120107000700008008003c04025000c0ca400001e44408007000043c0280d04440c60107000b200307050a181ca0170310701c1602210340341c00c0203801d03032100d0350100781d071200007002141070000c1056151440410b1075240d40340700403580035001d141868400405142c280c2101c41546020b400d000c250402080015440400d880d40c00d0904026168600c048220a80c0740641c0392904030101d504100400051250064060041c030000f078040d00c104449240d5099000d104580300350f008181d4400f01d500c901d500c610350705a44007102608 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 182114388 1250 182113138 182113153
    0x1503020a0b0901020f070f050f0a0b0a08010f080c0d0201030203060f06041229010e2e0603050a0c140a0203070b0a0203040218010302090f060423010503070b04050604030b0603 77
    0x499110003854019618075007000070b02c00035650703040081c07034002c0d11098098000d06060004560041c0000d2140318400c403039140e0200044e959000004006156000c240b90b0b0312040c0000c0688030305000d1044aa05e41c044000008522402040c0340c00000b8000380384000104240d80190020340002d03102c190022000c2d1014030250301c42800800241c6924910101818010728214100c11400b03800d60560f103154000010921548400903810744800054115196a44564003100000c2030031640c0c0d001c0065020210600c0005500784081d11040e0341c1c18051961900c02c2c08064038041d401d03040003d0301c40e4400d1400345403490060401c62047e441660315094842e200d8051103402030b0350f08210a9400000e22045103000c5101c1004441c88000041c0307258591740000303001d0700e001046a0100c499400010703a080d9510f612007800001c49148144140b0800001282d05401c2401040e020740719060010400102d1a01a03030100c400c02001e40e072500d411540e403100d25400251059805200d00034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 182115638 1250 182114388 182114393
    0xe030706050106021b0d170f25031119020f04060317030a060e0c0a0804030c08030f090601060216030602090607080d020a0e040b030a0b090c03030d0b040c0f0903061503 74
    0x1c2600808580c1e00800c844c5407600e00b088038800348071010510880030310f5001c000185400307614200000034140d809442e00d401c4904115039208113400414920712000340e186002400c19140c8251602a90b14040400006549903944000c900b031080c000ca10806c21190040c50700d01603885c40d600014001203401940c0303554031f40910b410940f0f408401c0201000304840e5404031311480004207561001c00300700d41020209000c0c14407880340304038104040074001070709250140011300c130f100c0d61111130141c3d645440700389241d80341e4090310300c64003600034000001182d500c001101e041c00e804c0005a01c40642c55550f8140c029441726500f90340011043c422400407405120140100100344200580c5e10284080e00a1031121031450f854803403454003040070020f480c0016841d1103140c0c0005100055214185d806140a1640a0700c80d4035200002e400d01c60003c040d08400e00c45003080c1d600f0320460882480550b60744005a50705800110748030340810200e17149802003044905141036240c0c0c142e490740c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 182116888 1250 182115638 182115641
    0x90414101404060e0102161b170a0c140307090905010608120408060709030f12140d0e070b0f0304150609020d050f070c08090625060c14030108060105040e030706 71
    0xc041c1c8007900e0000c0100018080d15005821035803100704000c41c03074150266040641d2505040700900055a41d00040012079400d142c10b84c058041c1084030400f1412604e10142d0703604031020121a07140a11200003036594500104076a03d41c001005070103101d041c111071500a00111030190780c00e6407640400100c60b8070501000e90503101c00c90382c0235a100d0230114401c1c501040038103084c04020000b10b0800104501194060701d41d6400615071608000b085004c81c0c130800744504072166180c000030459100341c09a4032030050742003004103503500c00340d640540100c0383c042c8441d01090804104000780021340c002d0040d07901c0c14a0310b4800161103495600020498005a2010f84c401d65100180820300b1007030540d060f03019025160110038545540d031049024021200310750301840b00860000c4041924030481c1d03190601208070030b1240c0b00c0740e080034000f600304c0c3e40d00000032034a220b101a0b0304600d1441142c0c140c990200060250380d28140a0100921070700466620600046c040c080001d5410b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 182118138 1250 182116888 182116901
    0xc0201020c09040b090d082a0d0f06080f0604080a0e03150a020d05010b090a0e09010b130f14040b0105010e2206080705041404020904080909070504080c0103090209041410 75
    0xc5113014164540039216501c2c0813203103006030092000c4802000750245c403000030092007901c03d007112030180d44403403110300c0c1c0d034000c1034461042181170980992070300486500810840c2e0845040308d507000700765407090b80c40d100d0130790b0050040305007040b4440d200c9000e01c1d28900540c0000c0c046924121307100f01c130b80b04400c0f400d031580c0d44140c4e00080c17100c2d1815218056030b405800030241c928500781c101c60000e00080b449200304000840c41c1000510140800c2d403100440400c09440841c103400ca000660004140980c94010160b02d070030000c0d80e1a1b1400100075100e664001e00500b51642080010f4444101080e400c0e54040c2407a0301c007103174101003000d1a054a14440d100800c00504022815042c400e03a600483e01803132801e080c00d1202c000c0b036412a43c0141d016640c0300a940c440341800c5580d48242c1c05c01c01c2e08100c4000030b02000c0c543c0500180210b81c4040103491141200344011000c0c1c8420440c040d6101c0d510001080c08103650854030007000c114102250026808400005c09940c00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 182119388 1250 182118138 182118143
    0x5010e0114180d050307021e01020c101b080706110406140903030d0905030306010e060f07061508030a120b1801210b07090f08030304080412030c0b0a09150509030a0c0201020c0904 79
    0x41000760031030420f681000056036a1001450311845160000bd680f80001420700d4070813550780d4185524035009468007007040d10034a803480b4004002d414907034003690210708102c1d98146410103161a402c10641614182e4941da0380c2c40303140650208822955420001c40c0c954140405c001c8081503002034400c1488041c030036805181c5074034060b80054031410140380b1a5014140c10848001c910210310100c030b1105501000008040c2a0a0b1070b00003615005e4000480511001030803004986d000725460854070f5002205104008102085c0b081035032180340714848010004d801408028040c0c0403519540300f40c2c503403490007150700d81c035030049101c416100180441da59090600c00104d0130762008020300f9949008500d1420242e485000e10700c90707485440b00c00c050b42d21303c6200f01480f443c442e040703807074021000c0341045c1001d10859004101d1103200f200d0040354601d43c00780e929164000d040c41a00040051428031301030090940d15030a641c20700301d046005426004076141d8a00300c00310300450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 182120638 1250 182119388 182119393
    0x40519080a0309031509080a0309292203020a060b01020102120c0a090806040b040b06190308131403070b030a090c090c031d0d0e0109030602121005010e0114180d05 72
    0x185142080e80300c45c0b01d10b40700490194108070007907000c103440204403051501240b43c0040c45041606288005840071030320f0b09103ca18a81c268544e955424a21074059500b030009c840503142c8240d40e0418490700c03200000c000d0707001450002c000c514a070340603034034500040c000903181039410044103800d01c2c411102110041004508404802d50014203000502001f20081c1801e0805842c1e640b00d540000b40001c1100710701c08001784a035203c2c0064407006e41241d4100080940c0c503803410038003d42090344a1070885038032107400283c141040c0b089644000d4064003a15440c1d050941603030151f44010301d0055900e45a00b8842c000410041c517101c010311b10a030001030b60b59046107004040d90b84040e842d40b01c0c580d046060902c2c1403404134a0f49a00030850403c00310b61010000141e0301414164005080d00d440450404810f01d4644000ba1081c000b8260188041d42c4500041d120f1a41080007a40010942c0e40500e070b2000c0008010008890b184280b07000c0c64030400000313058088140304c1107a454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 182121888 1250 182120638 182120657
    0x4060b0d0f140304050604031209051306060e06090907140c10020c101509271202071e0605030405120a0c0c140d021c140a020111060c040519080a03 65
    0x3040b115080d085980b00d40165150074604070025560b4012030101074070241ea500b10380c0005c0303401003c02100400001e49852203407100c000a00c40200701ca8496080400c0c0a1910810f851401000f21810000018140790103601e504a007250540c1100000c481c0104007005040c034044001c2003000c140040c00c03100903a0351691f030143c9901308051515000083e034201080c8040300c0040c8040e1311b05850040a00181c0541240d41c041d981c0308403c03030060a80c1052038480024084080e50790128030038541c08642c02c00b5620404d220320401210884042d00311860030520010384030b0b0001355042805501101c0110110855110065001021704404680300d0034005c0b00308050310000b80014000c3c0c500b01c43d1560303510404280100348100000384201400c9840802616140c1c10181a02c0e07007000000d80e080c40e0880b801d9942d482d141c0740982c04140920044418042c2c00502c3c980301324902900e090600c0d00c1c0006200038680ca00039640900440d085020400f100100300c20340718940660341c0e0150780c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 182123138 1250 182121888 182121893
    0x1101030b2206120203070e0a1404140c0d050304091109180906010803040e0a0b010c0b0408040512010203130807030903061509140709230306190b09040b0f04060b0d0f 73
    0x85940e55802480b02240980106000da03030f0201b803000c22100d002c10490010380d204525100180955000342c0e03000706000040c4800d010389050300190781c00c442e20458104203200420801713900c2100d6802421640300b0402481940c4140e0042e804000381c10041a09200c1c440300000d0b1007504a08180d0400706e43e443c100840c5c40d0080003a64014100800903510f00ba0510035040040d040027818240071940301c0d02032001c00c2c1d1041904040d210b40000340754215091030b02c1c5ca481554803a2107003600c80d41000e0102540c00e0301c184200c9000701d4008410340c004850f03903510a115508468015414000da031140040800c03035500a0811040154003d00c41d868100515202183c00c8940502440c0f00d05d0000c200039140c00003110420781c2c400f03180340500c02010510640d1550300c231501e01c5415000c0c0d102803100466280b148040c40e5810740d01e0910007104040d042c00840d0104840c09405d02e00c04601251029005000c0c2e99000b901a400114098000c040415007001d820f80084a44d905400c142d03606 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 182124388 1250 182123138 182123141
    0x20702040513050d0e060d0c17060a0b030411030109150516140d0f1d0703020f0d0201020604150204050a0803030f010b03070903021302040e07050d0c03181101030b22 73
    0x6020044901c0800201c140c2e840c1e056484c0c0d01a500384051000b003290210540c0d540c83d00360b540100c41010203002c420300210008100030701c981000c0f14194415008112517143c100a40700a4410803800d160a40d030351525002c09041d102035185416560301d031942004104104190841c041c1c8020740414541080d0100c4064a0350704040d82c01080b00302d4180d0002c80034400202c8002e074405820100b100910800040d0003001902c0030500401184078030030310345c518003240d40400c60340200c4100ca02002c4030300c207014a460344000001d005802900c0000c00041510b041c0d25110f44680720300508117501d41002ca600001035401501255002104200c4080103401c805030241c0001c6103e40d041d400c0284000c1c0000842d804021310070105101398181c0c4403801d9054800526005410054604103848090601e034031184075410054105007025a07110301134015000444850800005842955218000d00c2d218074402c01341007503200c10000340d481d0344080c5600410b1250790103500100354440306410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 182125638 1250 182124388 182124391
    0xf030f020a02090a0c09080f0d020601091416090308040e180a02010206010506090303070602040b070c090905030a540f050d080c0303070306030c211709060c010207020405 75
    0x85620101c0030038016201c03800c0c450b030081e81c00e000c0407400c41c40c03204003074034a6111900708401c00c1c0b24114a80707000520004509015445540070340f603d913629803188009442d081506c020f15002c0910204400701c203101e0180440801514081c94071645956920304140d106507ca0803001024001b4040b858105204c98a02880e203d001441e9091075980081d46800c03052280354800c0c4404a00340c5d0107038800303004413400c150380650215502d68031a440f03003040d600003e000340c1d003810348420b0105a41c80300b072281d1a5519044001181003080c1715400f01d88000c29801d0294403d010421107100d07041c030144851100b10641d002e5100c0c4004035181842c0700025004e114148014005000c02c20004003451600c1a24000da030100a07402c510300742018607110300e020101c441c3c40008100811140d0560248066034800c408404020f951140000031000700c0c00d225180841051822000107140403080342c2c045450074240360f04041c0c101e4000351032504151a40c00303107650005606001c42c6003030311606 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 182126888 1250 182125638 182125667
    0x1406090f0603060c03070c020a090c200709051008010c031e090c0b1317030d140601050a12112101060305220f0c060201020714060601051c06120f03 65
    0x502461500e0400203035140d00260011100c1345000001c85d8089101c0d040c141c5403640c024141c03070752003030362508550020040d010074000001c12030700c42030760340e40c104452000301d4074503180007411f456040c42d503002d0003810042c0c204440c401c0002c1d00064500028000c4100541707041c0c400051039004450103c0554100003050120980b604a0341c42c0041c4103407266078140c46c00183c04540340d2029219030300300c80140360409051100c680c45245588900003005007440f0304140824804034221090460780c9401c20b0724668080764092010040395440340c03480c24020500e40c20003240c1806035840c16070342e0b40e0108801100a813000d85035180b040c1070507030a0600402c51460200300601d40402d0007a4034510381400100a03840c1009008140907101c440c41c00401e0304882000002ca54400c0041c0c003c0d0701541d01100c061451400c0345800a0020540c184a4041078440500d010600341810030841200f000301c5a0440c2c0e1800082490307810030200780c40451088401d44040262418090300d41e100c001402c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 182128138 1250 182126888 182126911
    0x15380103060803041d0a0b1203070510060f0506030702420103030f11070302040f05040605090a0203031902030d0c0906021501060e040203040f0203010c051905040302060f0319140609 80
    0x402411035807980f170b1003030703510003c0c08803025840d10903404020b0003090a005030301c20081c0d10351007801400440141545d51140c412215040c23914440b0744182e800c180302c0c55821024507072080110f401c0c140b0003103621022601c1601d1614424118803603d03600003610303101064106c8200d024440d91880b112140c0d110800c018020550315542d03004101109480c1070204100c00c03041c00c80d120b040e003000054051a4001c00c01c0c130100d11116007507001890708076030541d200c506280100701c0c84140800c0040e40d0f6070300070707025600d40030b00c40c407a148400300d00544190461208100d0181040d840e8400d0301810300d010b50f1500041ca150500080c074005001d842210300b54000e1004120882c0c120f60100d590008c141c40140c0c4076540c84c24035048a064181d80a9010350809100301c0c0380c65800801420340031044e0b40341c0d8011034176620045606005a0100035000842002440003649045000e50b41c8003040100441d0034041140800041d500000e10b207982c2c07000c218080c0b01c420700c2e0522005522901e030166 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 182129388 1250 182128138 182128147
    0x209071d0105042301050c030a0e130b0306040b06031603050d301a0612371503081b0601060e0607030807020705040e0a060c0c15380103060803 63
    0x82c00c8185440c1c01302c030310355640100340056a85901403025030300111165026207460341c602d0386025201405400b4800d02c42d84c41e40c4410b01c0301c07069a1241080c6040040c004000e250788030740d42d43c007245401510455252140000700c580b003500809040300654030a601604000c0140b43e4090001c03070308483c0585203100c04003021805103108040d0600740444d0800c0225035170701c06450003011060703644040d6402110020321010103541890b1110700481001250709410342c041500d4001003c181d1000d1112504030502211012401e40c02a810308082c0024181c03845a403580d410600354410000d048801c1c0440e940301004000c144111030040c0200d003002120000c104000130b05a21508100809004107000807401940c170810040010301000307001003000e02d101500031540c418405004403445414540038543c0c161150000203060340c0c0c4001c03044500c000032403840028101e9881100302c20310040850201855940e040c203001004070000c901c01d0080100001030035500990040b00080c1d00400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 182130638 1250 182129388 182129399
    0xf140d030c03080c0d050a02030912030601050f0c070e0112030305061801090c0306050303040602100f020702061c090501090c080d11030307050d02071b051018060e0105070209071d010504 82
    0x451160302d0301e05654542c0d02e0400c140c8840c007070203070440111841d000812030400c03c260300450290b0105400c40d4802000640e00c0003661008844150008405000c41c2107120040300c0038092500110050380c000d15141c0031a401640350990000f403071440c143c1c601d942416050711607690411001d50349901101e10440300d4007a901018414190066a82d801c0701c104984a540144040d100c01002d807a0380b1543e41c2c20081d52680d25141c000344291400d004c0307440c0080f00d442220b8889030701a020f282070000c40f4840c2480009400c1e41c1003401c1e6124060303200050000c1c440d030788865100d0350500d045a0308110350b4600c0c024084186405014034000300b050130310400010b986e400300301482d040340d903421000b0100c8040d008540d8020440652001c454030041d0224090800342e42040d22401c00c07040c11000304071000400d034070049880050481c0148280345c41541d2030306110b041810620303d0401280d001c690b20242c00c48451001610380e05010598030703c0803911400340a000d19005042c5828039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 182131888 1250 182130638 182130647
    0x106030b0f16050f070501052d1b090102100222060f020a081617030106030b0334050d05010605040b01050a0e09180d050a0906030e19060e070f140d03 66
    0x1c82e41c800501034081100004440e01d04120303040d0325070090080c405030070b0600e44507000100c0d820003c46035904604040703111948140401e0311036902c40403032541c41202800b840d1340d030354801e0b040306045008440d00640040da20313000038020f195013074081c0c0c08040200078a00b2a440d450342c0020382002894080c0c04a416800500324441c540c12000c10790b42c42500d01d8070640d43c3d0002400c01403003d0840454003040403240c0c0d014604a8102d0744040c0580c9020008244d11000e03240b01300c001c0000d41e4480340f42882d140d0f0064900b00c030310760701450180b180c40700009031a40743c9021040b50745a456850078032050500f80a0126400000e003085400c2243c2e107540502001c0c1300d6500580a020000d001030200c811000b84130900312013020607120070151240700113005a11500c1c1d4040031070380c011400140c8a02c00c2c8115030450340a5405001c00482c1070302ca0400c01d9039100800c4e14001e446190142e1801000d00000f001402c6000030706a5081c94000700c2160307052090006441039070101d040b1000f1a400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 182133138 1250 182131888 182131921
    0x3020108060f061b011b020f0a0f0303020d1b11030319090609140a0b100b0304030305060d1209060320031801020d0c03091103060c180102070504020c0106030b0f 71
    0x3201c000068103020800f140307490050000c000002e00c140c1080b24200301066001d1814801503240b20313a03000700941026640d40030307508982c046da5406510701030003081445d85800700c200e100e450701500e806c107100d681105460043d40424501003e1040341c515842c0c00280140c07041c0d0944003d107007036141801403000340c911991b40003400c041c0c071181100c00f00446a2700c8991542c0e4081e4034502c4200f0904d2805a950a5200f412141c3e1840c007004104d283c0301c046040812140007150682c43e550b1103035411009400c0140040d600283e4850320900021000c5030641c00100c01d941d229090305142c032400805655001c841214500b002000e03d4000c031a9044c01c03242e2050304800c615203602c1c1000038460080c814094078200301d515041a81e4030070f5900d074000c0c1001900a60b01c0b040d0044c444c2c4201503d465094802c00301c00c40c4108903481603843c0540b840d103841c0c841401030f143d405c0d42d54070105017a684010303440682a507581d1303010b00412800c064901c0c0c01c4202d10000714150714105040dc0441c040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 182134388 1250 182133138 182133151
    0x819030c200c031e15010503060402010c02190303020d0909021819090501140108090f070515090301090b220b060904080d14090105071b0f0c08160303090603020403020108 75
    0x4240090703520050400240c5444480501190b404000c980e03800f4582c1044404148101c3c050301d100c000405019505072416a04010042c18180e1120342c015500d900300341c00300700c0e04032400101c274251045c047c103800c0c00258081d4002c4d24031100c800b403004001146580185a07083e05c103001d18035024441d1280415801c000b23a4089200f404008035100c030401941e44050651414540085149108030012581c80582a210080719484104016490310315030315024205a100324820003162030444024952440072005640c6812000d20100e42580c01d06031041d10140c5445e011700034924110841c4424981411904200d440c64958520213020310190115205440000c081b4013400a40400c440054000c4030003001300500d044600d02141a00b2191484154a4a400251010b00400c00d2241c904806040d5012550580d610110103030001003040e2041c2503040070200d42d803807003040306d00c500000315502c03056090310f123143c014481d1040340c1181e010940103000400040c2d811654032a003160 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 182135638 1250 182134388 182134427
    0x8090d11030f030711060109020d0515130518010e010603020f090c04060503190f050405010b0603010b0d110c2d07062c0604060e090a02040e07050d06080a0819030c 72
    0x100c40c000121800b8080c610485c40d280500000041c0c06210b9034020144048800b109104071f640f00300170165400c803202403aa8200d1481003044541c2c041c542e20440d4860210302d900d80c400d600418540703084907544500b03145039070364504050003980b40c01d001801d690502213580c40d07203d14140c98021032600403845580140300780400495107580080d083c003050206441803c0004100070030502c000340205440c00d640e25480d0043c001001e092003000ca034140c0f00c014407031034a403440d150f01541c02440c4403107a28141480034401e50340f0700241489a103000410702129800c94155200038400d468000c00000902d076403240000f04580c41e044144d00d004100c4150303195100a12280d801c03400c44081403c1a64084800a07000c21070580000004800203000d5a00c90700c00d036102c1050300200e10884c000e202c1c00708070980c0000d180b688900c005081c2060710302c00c0801c1c0e5a41d0307007810500e803041081c0d0031110b041d800300348030130102a031070502c070710341c07903080c0b400348400c58030a0400740000e8100c164502040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 182136888 1250 182135638 182135641
    0xc17010e03030705090108180a08120604050601050f071b0e040c090b090115052208100e030d020f130308070b0a1416020109050f060907050d030203040e151008090d11030f03 76
    0x180c0d48d24048003161105000399605240c40d8030300040c05034441c0100710380420303128004c5031280c02c0030702c50180b0802040c0c50305458500038400e07407070a81c0c000c158100c4851150408000001706940d00000c02000c0d2941100c0c0035051628100c440d010883e0441d8a000f450302465039074690f40d0054550469043d5207a04244000e2807000300c40c0340c4150080407420750744101010741c111149644030011621201d00340c6282c071009464400648071142000c40166100f4003c11210b40350301d50047ca02d600030300840b9490704403000c103002d131502c0c40c540c4166080035020841d20140080b60152030762260100700300b00010a0306007900b058490001d400c405168a24040b6800b040d4002d6009440702500041141e1813a1010700200c5c2d40c480040380d44102c24012000000341c64104200d455403402d5258000e0360074503050001d02e01740310b4801080306805c06500f211180f81c6d616185190510b070301c3c035a138030303410b00f480c103d9900303840c1921030984c0d0400c00107a604504032140010087d01c0403c0303000d010142c0e50b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 182138138 1250 182136888 182136901
    0x6060a05040902030f01050108090a0305040306020a27030606060c150c1b050c03070902120c1305040504081e0a090506030a09020406060504080d0806101b0c17010e03030705090108 79
    0x203600903500280d00481c800018401000c10900c2158100d50090366080303800da581c0381015841d40a02d51000300482c006000900000f10203401910001240345404482450841142402c0041c1c03c406101d9295034031030140180919805840064041820040c092001d90340d40e210460342519405886195500b808401185c03055491f6541c0d260040b1f40100500b4803418200d440d4144842034030321a102d08000058680058020b407032014100082224440c2e64030403a2506c0d540c05042c82242941e8a548089071981d110322810340190b000764030302a168201010103c19401e11441d00460100060010400c01580590341da070589100b510020b031280c80d82c0e10303004080c00c80740304020362240c10104045601c56100c000307401264124000c50324681703980202564400c106450f556042004075082407040ca000303400c0d40d81c1812842c1d01800c0c2034421038980c03990585494000c010161300401d50300354040000d0107450300c81e00b550400303545141841c4001030b1040c0300300043c0e181484640c8001559 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 182139388 1250 182138138 182138147
    0xe010e09060f090a020a110111160512070803090633060d380109030b040221030d0c03050115030b0607050601030b040204051f0303031e02130302042306060a 69
    0x90b00b41010b44003245605040c0c1c4944040e40050070f8a0300020ba808485042d01481401100c0c6102c2c0d48543d005d290400b409400503188130740801c156040d2060400400b0004120710041c80c6107406282c6036600d03400c0401805052000141040c58000c14110508500030034126600f0b12503801003030005500c244000100b0254060b030711140300141c0c50042c01054540365040c1e005100c050070303058042482c82442d00c1007881e0110921041c00551140700910008902d00702490b00103000810721340c0b43e243c54a240c0c01d102d00321000040300540000c95622080d45003400350300580710b00350600340301a42c10022030001e00d240504140c010945c513410a00c11a88808044a00580e0030606403100303503840741480070031584c1c1a03404901403440c040010710b29000180000c0c40c1844101440445649151400c5014140d4110f18120104e10360200100f0261148010482c800121995450103461401000100c0b58400e01c40c3d05000ea400341010952206185000d500a904680d05074403080b80010842c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 182140638 1250 182139388 182139409
    0xd1e02070812130b0708030c092b0312090803060f0409120f12020313021306050d0311011a03030d0c0903020904030c02030d020c0d1103010e0601030b04120e010e0906 73
    0x5941c0c0c00b035000c91070740c1040c07040c00900826022203002d004440c4d039044201440e1040b444042d0034802d050000c14940762a0f04010201340100919080302d40c90640e040e411036101c40c2c040c0002d104940d40300b101c10076070845080e0381100703d2030004000700406031720794041900c4020b2809104050512488005607074690150141c69000341c3c003c201d10400003c0a000007520038410320224108002019914000c1d00803680300742003c200c0700700030550755403c0c8000001d034400107108554071550041529101d940900101c3c9005c0e0b515140210050012070307084440111445102529084210409403400800c8509a58941e200003940b1540e10804550b1000e81b46c00082d8001c0d112000e0005156000030755421090080341038407d400e09004050769208070302c0503c1908402004440000308010700c03001814200060000701388001301e81c85050800400340c20850312083e01105000500204c1c40303005841110341d08003019001400000a00080d0486141c580324018090004006444480c3c450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 182141888 1250 182140638 182140649
    0x5040f0606080312160f05090d06020d09290c07140d0e100f0905010e13050403050c0601080606060301030206031f091a0a0302091b12160e030d1e0207 66
    0x4100d1640c640d00403075200c4e8400410507605014a8000c0f4400100700035a01540b1043d07500d64a6000300d544e8002e481c960000f40741117038010f5020700c1ea5008941980002c180844000078001980241403030305102d0213000000e034044003c42420180d800c0d40300e8043e8180c1002218044544684c03540c9821003801a1552500c0e0b8940a00761503581020380205045030b10040c1210a8403020540340030440341795075444402800603540d65410091940941c09460705070402400101c06c0310070070b008502c03d0b68020303181100002d4000501c90700d6500c1c1401400d025105e0031001e00350b181811000103551b8003041c04080c2c411031001001c1004003880e001080e0801c031441d07151003111139450728090000c06a00d101941d0b000f07604c0a80650500c9d12401c84020350b07034020310355002512110110400d44c4041050710351511001c10040302d811000281e654811000700100c0640900711020040c04a541081c07039600030341c082c0461a9095401c080f050007841402091625410315020049181401c2c65016 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 182143138 1250 182141888 182141891
    0xd030527120a09050f06120f0603030d02070b040b0c031302040b131b090f1809020613170709020a120504030e06040303080907080607050714150a020c15090304030605040f06 76
    0x1148000d5811460f51001c60300f0403510611900c035140d0500000b4815a40d05410400c035640016400242c0c6e2174146030031003030113001c5906203d010300108080740c1c007643d400c0d1b0719210908100010000658051980804038044850a43c1840c1c1d001c2e120380b10104d400248120f44a42140d02036485a81c01c454034404040b01c180060741d40102c4401c00992814240c50005c1d605110100302010301c0c041e210211030490440603401216103000000a2451580c100c1e88480204080820b04003040001e0300506290760040101c0c400780001c081c40d06105610003030089005000415189802c1140150307204942c0102190359a030302d1030129500480400c60b5540014041008003c2c150310054491150318041c0c11214041d84821006548801c02c407040800100204210b6000034205c0d00403e6950b40408100c0b2071482510014146003c0c00312a142c000c1c2d0342c0441c818030602f40c10040000620000300c41d0105d81d04000d021191203100342c0c0005004140c6884c0468208860401c0008126800010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 182144388 1250 182143138 182143147
    0x4110603010e04150b030d0c1502030f09010e1207030e030705130b040513050c060c01020c0d1d01030c1d03030f120103030f0e06030103150207020a030501020c0d03052712 75
    0x5189911070b41039900307650840c840031000081d03040900c240701769240010001d0400800500b4121108002900704031610592030f074007c409062140051402144900c001c0d501034035208c0b00040c00c42e15101d454080b6503008001032040001042d003201c0c6000d81500d0070b0301c14040b00c400803e01d0b040640d4040d0782c0150b0380401201d50807405174040d6088500403902442242c40d0200c2041d150212004003a0160700311004900941c0b0303000c1c000b804174525680000d4107191350f0f1051141402c40301070141000c01d1800228084008810310140c050010909040003c80b182c0b00e00140080c40c0e00c29030030100ca00070b54002c3c140e90782c01c1060365401e0044e021090760b58182402d5442e2007210030702c82200401ca0300c0300f401e080540108105016110b014018508680c0395854000350810351090910110b40e0070403200002d600c40d005140003542c012000546d0310201b2034650307072800103002001c404161a00050000860b8030703207000c1c1c0c0703514141c030fa544110340740026403981428000400744507800380c00517 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 182145638 1250 182144388 182144399
    0x9030703200328030f060317032d070306270216050105040f05070501110d0e1507050703110a050604120201021f0b0a0e07080f150604080606090106030e12030411060301 74
    0x728651043d0400f0b0b5400d00003800074125960560700c00d070200030400001c001c04061400404005517a0040d041c820303003e83c0c0344c0c40c401d020300f80690300d464078603121414104100c00150903010382401030868540b01c084200600c0845c2900d1035401c0c00413072140c0d4000441005c140c00c829104018141c01c130f00208660b080c01c4c6003141c038034180084220f90380d014041001559600410304140e01c40869806005c07000c02d01030703085030040001031610740d002e844003554000340e03101c1700d01401210344108000c020360303811402c101e4074046507601c086200ea1559032041c840c0340c843c00256801c80b00b03002400392000d0400d1005034102840503546401180032030700ca18901904582014070512800e580c807882d00d07511403801040d40c0c40c04071080c401040798100400d601003400010b140d400000b40030b04800001c00c410008480d0b42c401c0c1d01c49070555008000344802445c24031102c40c01480e080c18100402984444e01613103d2540400e01e00c0c9281c400b000103824000d10007080391040000401e400d90f81d40e1a070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 182146888 1250 182145638 182145697
    0xb0604081f0e12130902030907090504020418050105090c030c0f0d05010605060304030c030314130b04021f0f1713080d02090418030318080405041a03010e010c0206090307032003 78
    0x10881500a02d202c42000458030420306c21a03024405040107480c849013000c0080b805030101510480e002951946030101e42d0307101c1c02d203618426202724008074403801c00c1c0455619141c0b9505100b44650080d24524940740c0c0c2c0c8070070264a00a00b07541110034500c450030003500400c00d5900464121000104210825074483c032100003d901c41c1c8c03001c010340d205134031103138810b0242150102e6640350011181800720780801d03d1980d0140c40104041323180312990303011715110100200c2020100e03074030f0215805000e0700014015044981020384c00e84610708000c05444140c3d084802034400f0303d0008440d100a011501180d5024901420034403031400d200d0b0041c0d124002804080d000a440c11080342002028403044000c12900803074002e01786404c1c0070411000f0174101d139018600b11071003604c52045031402c0c0200c28085274204000a0145040100a410000010042900d54200b00104c00c0026013020f1000002c0440910181001440d10784051071407040c4200340c8203a0030a207910407000b0304c61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 182148138 1250 182146888 182146897
    0x3010f050412091d0606090609130509120c0c0108070c080310060e03030a0210020a02100510140105070b010311012007080d0509030c0f0d02090c09040b0604081f0e12 73
    0x1030740d550315252036541d40d159071079106400d07010313541c403012a000c0740031071400070007a00b2036140c003d00e00d41c5002e02200000e00c1c00044011504c107019140c2d010001221424070024441c901d40011091400802d040c501b5200c0c00c1c4c28441c141880030000c0451030759071084048100e1250f01c16852036407401c0504134081c90000d1489600e00180d03005c10720a20b00d0901009880e000c44868008000c8528190540d8001c5d4100240c40d008501c12070b11040c0040441c0d014441c000c280a040b110120307070824049a0a490031080b500d4140a020800e0100180066215034110b030b81050b0159560803030703840100d403030460f00d0000451040c0390800d001c1241c080452450126901c0300111201000d500a041e5070500038035064607815002540009220b05100c0030b080c0d4004002882141b0300e484c554000341c844101581c8681a50501003401c004600741403040044a1400320b070b41f2400e00345130500c40e9540e20795281810b502070344480b500f4a820300c0e5070780000f000c00080340180c0b04403040300c1c4010700c040d422 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 182149388 1250 182148138 182148173
    0x130e0a03030f0f11030a0504080c070b041403060402060403111804050102090a0f0b04031112070b041d01030c0603020a0e031023100b03070e0a06120e010c02190203010f0504 76
    0x41e0400f40310510149224402c0041100312049041d07960300241040100340062007902c0280080241c20090f1100340030f040081c002c8100800d4840341841520403502e00c20003071190180d4405414040540d80f050141d50460b43e001b00c0b41c102000c80c100200b0b40c0c0100780814441c203581c194042c40200f19064000d080000d0b0150740f580c00d007983d10f00400310162800e10681800300d030100f0060000c140344108901c01c1038405070508110261a01600345000f40943c0304d8010380501140c180021030006070540001140321140146a50454036004d99141d105c0c0318000a06600207903149183e40500280a0b070503100400b910781115201d1000b170050a4070341115288201524030091510841c0c10025000340310902d00c41c0e4005040ca14a01d4507076002400d00000d1050000800341a0f503106403844000d01420754450801c0e204184840e41a200c18407151000380e41406c041c0c901c0c03583d00281030507000c134455400102d2842d140c0046401049850000c0013020f081008005c02d200209041103141c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 182150638 1250 182149388 182149391
    0x5130501090b04050609070e030f0d050408100507051206030a021809100207050d11070b030c0a0e030109050c04110c1603170309060c0702040f02130918080405130e0a03030f 76
    0x1c03104040004440c401c9405d242d001041c00301044259100b212558103001c2c0c060115006072514003a031915041880c0380700d00c001200021705021010b000d005400e0005491001070189003440c0401425601600d40c01e4030441714071070300080c2e40355020010b00b408a500605401084001e41519010b010401ca412950034426209600c00011461080f21300d031580181c040c000001c80b0311400c0344c040c10138407507a0100e403040103001b2600070004001507005081c400c0c08659031350440300010782480c1b051031285100b42d25200044c030110b0300200b9540da140b241190300181e14020b140b0308182501420303c14403802d100d0b10480303072038406120f524030041e41c1c051230a03a1a01301c1c2d5040309100b60b01c8111410b28894001401081c40c07030501101034085c1d60300c010300220b01d429011032400101d030000b05040c244151075400401c9010390921488a1040c21001401e0300c0308856201c444091040303115007402036000e50a408210445031b4000f0000d0151102520000581410020302500d80d03840704c4136249 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 182151888 1250 182150638 182150651
    0x90607051005011406090f01090503030c0604110108070804121809050103062012070201110c1e03032215050c0a12050103020109030602090a0905011502060108010b0603010317040513050109 83
    0x244102c01104d80114030041c202d074038101c400343c14001408a480162414030002d00d1001c92155400e002030b02e0000c25240080911780f529080043d100190100014180a4403c05000741641e07c4107926500c03681008001e101c0c5099004211025620480b10300040071020740c0226042c070182d0411030482c0e004520074004034450114206000c540581c0c119a081000c120070740145401c8070300c866000015000004003645842034145c541d47c00300c1c541c004150800440c2c4400242d0201c1013101040d00100112b0540c40c0c0000e41100e8003145140d4105000d101000550070049041d40c00c40012800c600300b40958101003500c1c0a0681190f044800400e031804a0300389040740320721840b41281d4050703554001d40ea00d940c80700070007940544107068215074401000310380e00280e0301440340203012583c0c0c03105554a07140c5001b814a10180c111a00c16410404030071610740d1094252815039401c06004003450321203026002c0f99100c0c650046e42c0101c1c140c04411080031880e0b00050484004820078802c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 182153138 1250 182151888 182151899
    0xf0c020a0f080708120703110c04090c050306090a12142205011202070b1909122307020306340e0a080f0a03120f06091a0108011a03070509060705100501 67
    0x16002682c84c05d1340d02010034807105004c20700c5001c185441c070288005031901080410041025100590011344d100c0e0f076050f5040045003010070606510100135406001d041c4030b665200015504654980c004104558401250702c2c0b03286001ca0307104418290300115000c1d041820641c1d580310611400c2d01080301c0c0043c00441420318002c5a10550b40074840750316070b0340ca025a45000381c000c580400e00e459902c11828000a8201c4404e0601c01d0031615858401801d00d00700b1400c040b08020780c42510b600900a01c0011707240000c0e440d400c0402000999011480c1c1c903003040070b00c1c40541070a00320303171001d5802c1400c0f20f03000403007500105810346012100c0b5485845180c0d545400d008040200c0c0c1c40415007202017881881c50080522500f030300030801317a09c2003088005a41c45500440711180e40d07005020410100e001181446000a081607922585400c0c1c4280680c0e200400c0d0a810784000400030b01a00c0c8920100d5400390001801e031504d4407440d0074555074a022200140101c90328180002c80d9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 182154388 1250 182153138 182153143
    0x60906011805070e280f1206110c0303280507020d030902060c1b0a080f0703060b0607020a1409010f0f05041a0a0b070b06060702010806010f0c020a0f080708 69
    0x607104190321032081d040a1010103002031500600b05000c00082c0071021007165500c80034001d515001d820841e040e0001e00c0c410011410740d80d0f1009800103540041004412480e00301c032180142c204c40002080600360384502d40610400c48a40a50b010000c2003101706c04002040304a9025540448d141d000c802c0c0114600301d60b01500c0f003c01690049583c1c25240348030307030008800d075031003d0b01190a280200008900e00450b010304491941d141c01c51030307849800e0040900000301000741c002c1451200d800324840d180c0d9124040a01131549401103101e147e1600701c11200745540c0a0000c11405541d091012000c0c8501155a4403450301803000080501d21000c881003070355103004010000da0301c0e200c200001000c1600510700340364005680708403669240030250005140c4501d40d1a0b8840180c61b000c4015a03000302010b10403a018000c0d100540d900208960340010f003030910280650120394140c0748101035050095102480342c80108103040f64504d940202c0f18181d0494050a80302d403001c68 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 182155638 1250 182154388 182154391
    0xf010806160507060e12040603020c011802150304110607080c1501080c10030603060e010501061202030f01090e03120108100f0614042705070509010b070c05040b03010b1c05060906 79
    0x4000382c81802541c000c1084da85c841003416140b00203c40c40c0310000041c0b201c10340c0081e4015400702e07601280e80c182000085c010201e06584420540c032040303410307034009051100113040202040300080700280400c07044a40d4091032810040c01070351150300c140751000d510303808a8081c803c240039800440c0e403030b04a89035005040c1ea1110000e405c0e45103c1038140a4440e404140c500b041540714200000800c00a10460204110880000c2100d42c1000710152900c8001e00c41091414410002c100d18800065a02410f6668420011498460a054031803440c0a400da07590020140c6d1400060b1608001500c01c0d480d206864040c05150403550005084031010b214158800d0b0000d04034003d1032505500030202e401405121546410619400d1a6203204821040710b0951020000f40030524280e9a014010304d41503180320320b01000703a41c8441204020b8424180500d8070780124803031981d029045014020000b030008075841a100e4044044042d941e0020382c0d06010f0300c0041a030b000310104849 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 182156888 1250 182155638 182155681
    0x906060c050a32060601081e01061b02031005040209010801090b2e0605070303051503030a030b04020d0c0305040c0801020a020d08090715020a0c0603050603070501050906040302090f010806 83
    0x108520b8000d91a0728480d003460324040300b44441d0b0210b40021900785525011100c0345020020400c600d040d00c00034010f0075001c0d21808402c80745048510010030074004840c1920340d03034642800c04210052541094584000c0025031500595961300d81c032840c80d9001e07030310843c021501c1c45c000340d80e201c207800d007203a420071809044581482c000405000280740c041040003003500029491541e000c02541c01544c141e000100000d400240e00e40034564180a480d030400c1414100745103444070880000e80c0e902c0b078000c040051540314010b40722560380e02d6041d0740c06640301d0801400060035101c001801480100c1e01110580002c0c040400e078081c052096900c5072070305070010406644031a400707990450000380b4100c0c09221b280310101d030309070000000c11443c0486070010300c0180f5181c6440e03100c8403031540010040504c1d100400c4129940018008202c03002070902558881c60f80c2c0124030300303105903000071703400ca6500020320441461100034181210303880030a68030241c850510b002c80e080c100c154403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 182158138 1250 182156888 182156893
    0xb041802010507020a05030102030115030e1c0804020112050705040f0b04031101180302060f0703020c18010b0a03181101090603020906040902090d0203060703020a1b020d030809250906060c05 84
    0x8680040d40590300400400d0b00080481c042280e48500080c2607038001d8201c0354040001001d2040780700d07014090104915034041c080c11312410407032582003c0328100d8148004102d11500401c0a590180e000d448030300c41c24000605c0285001c0c2d101800950041c42000d00812410600054075514441917400303481c2d102d81c0611500d00d2081c011201e00b086100c0c0040300d20504800000160f036804000d21030a11601502921001c99080c060304049070740f84058007403880c5015120510010510042c1034504005509032180c20b40b038011002402d0100c8144146040202c0d03901c1407145c01003142c00e1070b10090366100105501c0b51011030590058981c0749402240c21700003404903e4183d00a020204400343c80c416040045400091030608141e1741751002c81d0740000d0071182d01d9808610640b90f4800844105c0701200740307501082d000304009901500b0448441c02066102d8400e005401100780c1c040620488101d5010f985d8804044500c200840b4600c0d003440050403074054680501d896801001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 182159388 1250 182158138 182158181
    0x601030b0a02070c090e0123060108010e090106031703340e010c080a0e1306050108040b100b0a020708010c080103030e10050f1210050f1c05120705060a0b04 69
    0x2150740a0740004000f114408a000c8012a451a161080e0321002d85604004030f505858611001c0413403520044e4801c200e620f00702001490398029422a0440f41c6008410b105170703494030803d03030050078280c0005100050034000340349400e42e00e00245001c2d2005105400552400d448400c20074207200381c10484000540c0100341d2254040c000c90781c0f105006061485800005580b100d6441d03210b01d240e540801c210118003181c50805151541c0842441c8800308100c40c20800041c0c4401c1008000510045820001441c044140f01e811402400144003054a0f4440800d001c1d440e4015801072110030343c6040502103510340f1904107941201e800d61183c080c4441c02d44180714110503500c458209011041041c0100c100000000f0241142145124201ca08010441d010090b2240d400940f00707009803420b51804da500e004034142200c034160b1502440000e10b14146092148803202d4000d5100c011920740c0911001240309407040d01400c804012914800e020002168081c0305034204103000070303d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 182160638 1250 182159388 182159401
    0xf060f150e132103020f0d09060c0813020d05010b03030c1b0f01080f09120a031d030414120c10120506010f02120f0d021b0607030e06060402031909031d030601030b 72
    0xa042c02c03185060f52030090f06c1c101103c840032001d0390001d200004c669558010b50010f02c0302c03c0c443d8551400b0340b880d08100c60308003403c086001030f0782c4003c040d104020710401c1300100802580601210700d00a815039031036949641c481511260400c1d011a900e00030b580124a40b0302d001380000610902c16114007220352201c6101070700c80d040080c20185640b0035903038069a4400f40c00058a0750f10004d940200d41d190160784c0300c1c1064102082940b81c03503407060105101ca40007982c000320441d90207031501e0421400c00705240c1e01c0c0844501402e600030b2050000c0c91002540705407103c00b84800ba580501840d01d44200440d070808429550302c00580011049a40b00604400202801e605484c02c0900700f1015400610407030340700c9898129003214041d090400f52070b090091a9010015080800c0340c221030290203500c490008000a22550340000011710411403040c0004003496440c400700200101850007070080014030880c00c689040c4024242400d00d40003442c0c034141d0380c0c82084a1416140c09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 182161888 1250 182160638 182160683
    0xc0c17030f09010302090d081309020301120602090102070e0a2a080a0c0201141905070203180d060906090507180b061605070503100b090a0c0c0f060f150e13 69
    0x102d1503604054003000440110742c1c1c0d401c118450b10b40160011541e4100701009900554200d42c4008240c6005000420120302020042011250490030240e40c402000c40101d042c420150054040c1c000c04000340641003c4c540d00c030075407205040880b541490300d00c01d04034080d60111401700002601c2c14000801c002240c0e0018901c2c010140004640d0303080503954007840c020112503a50000c04032425050700022035002d00d942081302c42c00914541072002075031490344800004c109001f14850031882e01040074540c444603240390171003410800f07585140f514548401c0d032480345180c600158540b49209a076a4030031602107010061a1501d0b180780100611500c0c11a01010755140c002c02c80d0002d81500c040c44650b41c1584103000002d4032030b002c0070400400d140c7c090180c040f0586080d1800340403641000c02c04883c540c201000f1040342d5520724005000c1c0c109403103a01d9849040c0f241c40c81d12010a984054249c40144444c12100d50382c803ca5800c0c480c80c52100038054a1802842600b00d1154 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 182163138 1250 182161888 182161897
    0xe031b040e010207050105060307090507091205030f0301081501060806010c0f060605030115080d020703021e03211309090f1e0204050103031d0301090b061e040504030c0c17030f 78
    0x341000c00d00d024449009070072a0840340082c0c9650b51110200070aa02e018040000688200e8004100d80e0034500001013955400d4051601e411580421190a200382082503c0150b4900340c83c0940da50b84071240b15856510707130110304001040600000c95402c0c0174070101c910400303040e0760b00c0035440f90546a0b02d054a40500c829140d25030381e582c002c2080e031403c0c010041600c0c4101e411408451074650610701e8100048807400840d0010f110500040e1f9a84442070b0070b00c010088404400000900000d040080c4400c104003120500c0100000034200003001d0900c549640e000340d0b000c640d56031000400c1e00d590702001404144c0d0400341c01c001414074005214854000003070005040507503404a4219002a0800e4000c680d200c818249600c99425075001850320a4000f071008462a9490702e101c500b010305403a1203040d0010542d6080c0c0361b0b0300020454210000c1c41409242454200607090020348001174410750092440030801d6004204c0450308800d14074001c0d440e000304000462440d811 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 182164388 1250 182163138 182163193
    0x515031f0e070605090a0e01060f080403030b090906070f110a0201050307120906050105042d1e02071101030507170c0f21090c1206010308090d0b010902030105100e03 73
    0x20344120000c56120100203401c0607040c0c5841d459030b15480c5c0310401164138003070345c007000214428030018040503a001c1c140d01c181c1561810702c00300b01e490b5231901394054001c810415801c40400741c200417103c000002e10500401450b150358449103812041142d0480800742c001906500204008006501c9007000395403101061814280160781c014801c800c1e150b4103036046d035540d038562005028620b401d10801800d5103c07440041034105d941c00e00142500012060b01515a0b43c0703101c18074191040d0304250701c4640b50080b0855880350649088148180d4499480e0300203482e00f400903203030324010b000704090b00341c042c220721000340d0f81c1d0304612005038044008690081414804804548404002d01584a007203503545505440c0c242521131500f130100c01030500ca034030440c01a42812002040185c1500e40001035183c0d40d01e00f030404200c0c000b4003102e00400d25031080d40000340040c0c4590155042c0d030000c0b25503e4071031080200460311591a95010781e4503800c840c0000c0000c90424054654084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 182165638 1250 182164388 182164391
    0x209010e090304170a030806010302070317040311010f140906060603150307051f0215060a1202060f07030c12031b0e040b031b04060b04150f02070f06120515031f 71
    0x1074403002d1011350854180c00c40f40c01a4089101035040580116000d80d201e0400e107011030074080f990304c004001d010b0310711040c040c1c2c080000c08242414031841e03442544644500c02805000502c1401900a008080c03100345424805804100dd140c03000c00d0950190400030304050954668900d9004000405c000140d81841541e01c001600e884500c6040121044c58094820110b0350450107800c00040d12140c1b9100030404080094680e1044410000e48800301800d0382c8052880c4045060b03807107004403520700007001180400030035500c1080714810718890b28294211544c040c80907020f45d03da120000c1c40a4843c0260344c0b550074800d2491305ca000c040240085019588100400e080011085c5400c1c050956020703807400c9070400d4011701000306124014030385003506c0c00c040000c1c0410040114000c21400e200c41c01300301442004020b0191003070384145810207542d2007000d80382d02150000304500c2420f00303000501103200103110a80030200a405812250755120240360304850b000711410790103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 182166888 1250 182165638 182165647
    0x1a032a090a060f060c030f02070f15021e0303090d1106070e01020c0d08031005012d050705060a23040b0114040e030f0903150705040506030a020910020a0318030209010e0903 76
    0xa541140640f070061000c0c0e00c440c41e1106441c10007c006004000810b810340d401a80b0030400c04010104520888062402400595100c000c4c22800d020070200841038041d042106400045808802113006403882400c891292984003010794214181c504540c03a01d800c0107000640f0580107070f1601d02c0030041423041c0c0365610b0740000022410100114280c544803000b10810800029606444000c2d00f02402c5ca0040360919640d40c2c1c0c0100c040c241d00150040c0d0070cc400300e1050380920b00303403003426602000b920400c0ca400045900101600d0b25090308503c1134071071090122001c4000c2600442d0040030303492180c0e0030581c3d01d03082449004a0a604207503681c0303402200070000d00c05070070181501540284c1c0c0c1d49203030041603d06080380c0071840100c3c81e841d042c0225150800115001c0301c03400c0d01c03e541c0700d94580050308001c0c062142c0a07900b155281c0c650989856001c00d044016074843c5c1c680700c0c541c040302d484440b0004400e00000b500301e40c1c0000103000700c40b80d6015407544050f0681c126442d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 182168138 1250 182166888 182166899
    0xc080a090312020c0102060c07080403230d03090605060a290d0c020606030d051908071b08030406111c0f0603020301091b0b0f07030507050f011a032a090a06 69
    0x80a411480c2c0c80300580220f03086140a690601105400281c040d101d142440640e0f11205242e2080344801408100c80c0c003400d0404035050718110310000110000c3e940c09164020014000d001d15030030440e4041d03d0321001500500d041220407013910820042030401006c5a10940703144801c491019003262030a0104240c680814050044003003001d501808160038941c0a1514010189000c130741448414040c860340901c003080a04415003040c54000d180c0d46a401080c2c464038040e0205c110100f591103205018810440300a41c044d41c40f600b4200320f90151441055a1805800c020f40700843d12504260003043c1e4642040408a030300013400a5981e07583d50002e404c40703440000c01c2383d07411800a00f030744200e00c46000c0c440080542e55809480e00012085550b050303c20f1440042c00d116000c92103a05105040181c40c01e02541c50000300701d00c20312005038440440c401107640b4828403030800600690322031520105290316203916880c0300d1900b900208000d810b402010086501d980d200300141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 182169388 1250 182168138 182168153
    0x91c02041107050114070509011b17030f07020a0503030a0f060803130e09030403030c15090c08030d0b011d010311070b070302120a0b13330608060306070c080a0903 72
    0x16851021400700e81e5521140c40c2041c01c3d40c0d501010043e0440e489030405c000a0303000401c40b84003010034600000c0d080d00010b94184004010303d00505214500b46581c485031400500031070040c0c04981e40a11143c0c3e607400101c0c5d45200b00940140a43c10502c0030490350b21743d0742c2000b0444000c000000c140c4c142c440c0716503403442d00264104d0f50103186c0e202c0104101d05072100240c0d00080d940d00514034150442d18098a00340c4c0c007841c000c0245018900703d041081c8194000c004440c0c5c0140525003056544520a5603a0041c8072210b800d94503010100b200c40d070054500c0b00180491100d0300d840c1c1b0b22807000550051000901c070b4502141c08212490005402c3c070402c0784106c40c81e0300c0040e101e1000e10180000c00400510304440309142c05500c10144e81d0fa00b4101401000026001c41c0000c02c030440c064940381d400c900301a070710740588040c1c0601c1071801d40c0c010983e03143c1d54680c4010303a240010143d4809065401780c0208034007407000c2002c12040d000429500400741051040265250b403100c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 182170638 1250 182169388 182169401
    0x3070c1a071505060f09040b0c250b0108070902070b01141215151c060c030b03010608061e0f0c1305150c1203010518040609051212010812091c0204 65
    0xd0b1660350401c0084a01e4104800b0b100d89600340c4e8a1070841c41c00340e42e0010300007406001c00a2803240400e550b0075940070461080012981400341c0c5441e025070b4604101d8800d001c0c0101000c9010311f031008111030009200382c41416808c11010f54103030b40ba2015641000c201da544464005007809210002058200400c408994076100e42c8055803415180d40c1c803410010381c800320320848018980f41040407070790a02d003c0d87e641140c000560581140da040c0c0040a0482c001a015403c203400080c001c44c002c10500e01c9110740400b0000d526074034201c03012000c00112640254010790002003a000100580070780400810769261040345070310368000501c0741c06180c9620140d0040001c51041c158400d002c203490349041b00d5040c40c00c5505101c005103885000c4107031302650295050024051011079081841280d4003c82a90a846882950000307164800340b04450500c14400c0002502180001d07109208003200181030b0a0100c450100081c90b0460981d41d00d01c0d9452f5054400566168032071003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 182171888 1250 182170638 182170673
    0x18021e0a08150105010207180507030e0706090303080a0203160f170112050c030601150507020a0f03080a020d091401050307020f1e01140c0d020307052b050903070c1a07 74
    0x14261540492081800058140c103c24115006903004004040300660040000b20b03201c0300c082758680d0b0b44041280141402d5403450514804e40000042068028100d0030940340203944110796550342100030740580c802540c080c40e903036642802000410f482074001c03c03000c1031b8078074001d0040c821480340d101c07010724280c024912483c50201400c00300941002143d05038241074010704150f614040402103020214110306050100004ad144210340d03d1711800c00c043c100b48540500303c252242000103080d006100c10402500c110501c8411060141002200b2205020748100000c926100119580d41015040c0c1e0309501c24403008240d80f00b030620051003501020350b0807419415001c8030359401e5440c0950314880c9154140c0520841c00c6002044030038201021a0250b680d4907200c2c1c0c200c07158414001c045813000f109007070b8151410305c7c1c58400d1055501e1800d0a00c800e4482c22091070712407243d1000181110361042c401c000c180000c0c059000001c0ca074041c0c19041400720345841c512000c03040d401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 182173138 1250 182171888 182171893
    0x50102040801050609010801090b011a0d0912030b030f0c0d080903010e1c0504080303060d0c0302090406090b0105181302010207080f0f060703060605070303050a0f1415030118021e0a08 81
    0x1040260701700300c142d05004081c81c00090012160b01c2c1c81c4c8510b260b80c11700500e404540907181c0c500340020000c044610b40d80402d80108140310761130401001145a80301c4160000e82003500342c04081c90300058000c14a03002170003074a101e600d65801c12060042a41d000c85070070106010304115940c0a00c520050000c504014011000305a02d0740804079003c0440502404004c0c0824080707040d0004c15203501280030303a001070510822b4140000010103990000f1341c0414081b04010801080381c1180c000d0b079110b101116210398803101004a0a0901c0c038180c18180d2103040000c82d01c00fa80030000007901d006005880103a6111040d844c280040000000003690000b0032074080a0420082e69a104802d0b180c208801414003500801c0391050322400b404060315180402c11094180d400345140c020303d4002080812045c40d810340070284111003019203c90500e4003a1098107060007040240602d22000540d98003d80c2d08200781201d2701c81d00c08401c000000148881c688821403040080d2201400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 182174388 1250 182173138 182173141
    0x14040201031b0f080907090501080d02010b04021603181701020c06060409030503010b03073c031a04090303020f0d060503061501120b060702130507020d0c110907020a05010204080105 80
    0x74098400780711030341804601c0105140e00c2c840d4803500c560b030580183e1414541c6501c810000c4e42c90301405400c0304194a01e000e0002a0841c40081e00506809617a0001e02800071410100b10032805a03501d44400d111610b440c440011344a01c200c12040c050120001c07003100c0d03c580c0c004122101842c0000c03210307940001c41c540307164030400c003060b4841c50403a42801940083d41c0d0040203400180f1440419040c04404580c8241c0a8000400008410804500c540340051421002c0c3c600d0088105a00c00130341c02c803a0410380c0703e8002c0308405403c900500c09500810070502000b8030801c2c1c003d40c00c240d402d01140d002c1e03c1000004003464030400e84007040d000e040900301810840003424400300d40310f0001c50201180d81001e094400600710400001ea1060b003800030491500c0391300c1000707500c0745140d50341c0343c035591044d44400e009502c0307582166001100d00c01c0903964508010b030040c1c00780c0e854031009021445c014007140ea1100039803054a050125940c3c0741401da07001900594901d0351245c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 182175638 1250 182174388 182174393
    0xf021216031103060303041202010207090504030c1211070311010c0506010e27190c12060c0e01030b06070602030603011103040b010311102319020c040609021e0d0f1404 74
    0x9242d44074204101014594104440000d68910071440342440069901c0780c1c0d04c066a00900c501001004440c0d8244080e240c1031500a040034482070b01142c0c40d0b88100200702003144160f215518000341d04004100240c02d50301c980c01002481c210160400020601482c00545d042c0311190007010f0b5050389281c1400d11001700040d48481446d8401c01a08060a000c007001c00001c0e0300b408644d43c1ea1507044441120b06000c41d00c0304854000c5109030b60071030084400c0041907444015503101c159200340c40b440c0f00710011000e072035035109601e80c00031080c04540c0c00705690354015500405d00a000160b18509442d0044082e001140c065680300008001002840001c0079041703209503040314200d124a1680340c0107405000308400300a00389507011030040d48000350300b0849640c07a40c0a440341010307841c0314800965415058050794092405c0c4035000602d1400760096030349404120412840324108107114204030307000b80e580015141d840340c1001e01914851310440041ca01c0c02d44440200f485e2a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 182176888 1250 182175638 182175641
    0x3120c0106050a080102030603580206010f03021e09190606171f03080f091c0803040305030702010f02040e06041503050c061c180b011205100f02121603 67
    0x164007100d13080c2d004204101050741c6c00704030282140c00c030740a00709c104081038582d402020740e4020b029441e428000b0710204030204c101c02a904282610342d005a101b50340e284e0880c1c1b102001c0c480c0114a8102840a1006181805002c2107a601c143e46094422002800152069505880010741e44d4085143e01c441d641150088070b002e0411790a1050b4194001e80ba81010707001c0c01420046040d0b42c411490200009064850300155084a40da54842d0141c020b1600590300050300c5034812400e151040d51664003003032501c00e455822003c2c590441da07494a040d0380651009010a003103540c2c50b84031012980845c80030f00083e000c2e002146000e450b080c4c0c144002c40e20b0341154a074403d581d03e0001c000091000801d0f00c802c210580c0c600e520703080d000d116840c07500b05128104c400c150428407150310720300c400c507054000240038000e48449641d8990f07001100040c0c121000e00036400c2022030001000840e004072040b031420210061034135036081c041314400c00341510809025071405c030700c24200070380c103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 182178138 1250 182176888 182176909
    0x608010303090b0901091208090409140c03010e0309060a1b0302060403030f020306030d0e0f0607061a0628051c0b0102160f030f020f0907020c21190203120c010605 72
    0x694031480e291a000c44c00107010707100c19115110041ca8001c20a00410a02c10b065407038040e00500103112080041c58a00106581c05452059510540803d00360b1031905019041d00001114051842c0c542044113104a652121100000780301034104905c03513801e4415076601c2480c0c000d6000d89428201407034006d041e5020381214075192030040c801e0201030742c2c0214036909510600e0030f004100300800d40c0030800c0d603410142640d41c80000807480b001403200b1500314525802c0b960811219105102d03080008034007072115548201142e111401084001d10203001803010041d06040d400d10004100c00d0082c0301503110f03162038481c0c13100002c10444d60100059601810426120400b06091402d024403013885071202a01c05201c40d00454155110301038540c81d0000302400420440c500070328044e5551201d815864069060714440c020060b410503460900c1447d00303c0a00140741e2010700f24401d01d03004d10800da038140568154001080700b20fa00030111210038400201e1f10528090400808481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 182179388 1250 182178138 182178149
    0xe06240316090509040206090103050403030f02070507030c0803040b030103080309010f0c1817102c0609070501081005040506040f0204090b0901170d0c0c0f0b04051c050607030c0c050106060801030309 88
    0x10084c1404010780ea0f200035035103084028030300021142d4580c2004c901411602d04650ba031148002003a00602c03402290540c00c0c0c0e406100c1b441d40c001c2d60b840c0d44559901ca280306003d00754000303000502c00180c4042c0103681100c0713001c00109507620408125000c941c9895055004a44104840c40b03041d08403191580080520600304240950b00076400c58032407000e40780d050105580c1d2440c1d0001c003c203035154046400d00c203100030750110800c207511a58400007038904a00324880c040002503d58400c210091141c0c2c0c010b560746858520340002d100c0500380c05071216500c1a10b410010840e20240c0c809440145410280800e000e44400c051080044068110300030002c1501e10841050900065000034001d540c0382458000c512400d08181c84480e0707800415441e1030080c4009130501c01b020241041c1e80d0101e842c498040240b03184541d29070701c000740003030858014a0005800c24081d50140d001c0c00420300b48100d12082d55030b41c050071180c1d580c00210100c1d08510040c0240366100d0800780c0500b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182180638 1250 182179388 182179399
    0x10021204020414040305090d0303090f060c0210061203080603010b310b09131a16030b0d0c0605030c04030c0305071403030c1506060c0f100c05040e062403160905 71
    0x404d500c000300b445c0f081000140c0100315a00702681054400d0b404032034125045004040c0340805440c20300e02500c0200d80322001403040003100351023600d903841503004651415007200104141c0c0e0303505a80703d5034000c01c03040d85950385e401103009a844404840352148590000766129052820380c80c0400c02c0d80d2006100e109260010b002499250301c1901604a00c00036540c0ba002006880c002030b005001a0f08100d10a00307a100788040d05403680e402d000340d0700781c0b41ca0070b11000030080140450408102c4000e0084a018001080b0060082c0d0080d0b17000700e49010110b2420742c0725211b29001d04150f074000c40d1160b020303500170030900d05001c0c119805400128042c618201d04142d030b1941c2c40c1305003155416802000000320b0304c1ca5440e802211084034280064440d0114451180c0f92949030400c840c1410600300300c0c1e41e018062051084801b520304107450712006441d9941803000c0006040300d81150300c42c40088014032a10f20201540c464210140d020b06505001c0000407d6490158421030050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182181888 1250 182180638 182180641
    0x12100509160806240a0509150f03040b0c0d020c070504150f0b030c07021807021519050a02070209010806041b03080403110d29090f061810021204020414 67
    0x55400b0080b00d07044034040390000c40512800c0e01c2071200510311210250002e0b4002500402c054000001c0e101e080b4003102e030742010030883d81d0101824422490b0031031580c00f00b040041c0001d80c030b950300581c00c208040a182e09006480d545441203038413410f4210f415610541c4200518546402403e91010701020780112903460010001282d2149004103030000e54080300140e10040302c40300b540d80b0150001e03e40e45000420030085120001d080c0c40640050061ba61101c2000071700038511401a02c000c200003e05440c14403108001f01006424045003607001c224032000f5035164000d844c0a4010321015040906151418254a400e8061003900c1d03140e158000f0000b140700481510b040fa501301c03025a03240320780400050188910402c0c001d00d84841d058200340c49000030906400311340380d140e90b40c103081e44500f5503440d6921f50040d80c1003055808080000e41012030b421b1a00f11b070018000450f481d0141500c904401c0c0c0e00034500244110300400e00304802e51030240a02004101d030808280c00c05e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182183138 1250 182181888 182181931
    0x90e010c050403120e0603160e100e0d0f0b04051c09050306060d080c01090302010209030c01030513081b0d030b0103060902090109140f090406090b1b0406031112100509 74
    0x1074092072002a2040c8050200130101074010301501c10780d25001400070fa41c03443d240b2850000b204426118400094000d0071016450a00014203060340445444000c40741d51507501b008445000d000b4100d601035044010003001400100c045801a442000544501022103a8a0f04405200c00c9407204221800004010a403004108075030080010b6a10104c159090b080000c0c1610400c80c0b4190b8170361919540380b05066040d07000e4100d440d804c60a882c0301044407001102034074415654084150718203022031000550040c02081d0306003450f49007060010800c5081400c18001c01002c0010030344580d0403140070b41e410710419014150764001141000603100000b0500e40307807400b40c0081c9030741c40c0650509558680c00c0140d40140010a06185840d02d450240082c0040c0b45c000c888180050020903030758000490401114580d4620030350030149410011000383c80e61030b1418105040c01c000e250741c1424a6644140300750104040c083c09a464042130102c4814010801541440c00d08803c541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182184388 1250 182183138 182183147
    0x9030912150a0c03061503060504060501091424030108070503070b0301060503070e0316081b0306010303020a061a0a15110d0906030e012301090e0d05030402040c091e090e010c 77
    0x100807090410025011450840130740050140b504202c5101c01c03540d8290000301d615030081c10655106440511500e66a0001550303500c0c01c3e8000c460005440c080010302c142814054504600310512001103004403030741440e02d950b4420782000c826600301100c140030b00e003410000d841c000e007402c010503403a6600d8000c00820303d00000e02020b00308482d49960031001e54042003400ca10380b040103401a1a20f030b49044050390b500e1a180c034510140f000b240605114900401c21504882d0150040d00d00f080303d6940da2001081d40000110100c5841c108407039041d111440e01070040d02403414040170740724035441c01909100303941290fa00399500c0201c0454406500044100c11601281004100030b42c4045109015042082c4210340342c0000d441d10302001100c2d100103a04a50841d0010041c0959411645445903500550000424010008070340181015403003290b441c0303411b10b0f0001c4610b4480286242d58122560302680c4030b03040400a1182e004644a1b00d2440e10030b045c000c02860904000181 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182185638 1250 182184388 182184391
    0x90106060206100e070e0402030114031b01140a03020c0a0f02090a060609060c080c030c0102071a010303050304080711030f10230a09150e0102070b070c0201080a020f0408060903091215 81
    0x21361040000d01049030f43d8040c4c1d0221580e054001c1041d034880d0f842d00700d1260741001407801c1c01d00c68400c4403a9403064025401004080c04010395440050b070885404003500d9502c4443c071101010b500b0080c0e14030100701400480e003520b126900c00c075280c0da454010855640d101a120600c2ea41c074014040001540208540044964034184a4545150f03030616054500842203071022038040050a0a000c560650040a500b4800c41035003074411541d8210041c03c2c0d07800d01004011400c02c0010030003140b02034019084491041840741e0280a40c40c0110b03080041c008003c03142c41e07001200b03080c400e4840c0e005a010031401b84050125052044005010b15000a04810340c0c0658899410042c070502454240c2d030212210300a21401304000e401c14000c1d40603010642e04072074542c010551240c8a102c100c808150142c0d04e198041d00c0f400205002540300000f04040d0301004c210001b070400d0107200c00c0d40309622410286859030807034001e00a1500030308621200036001005020554420070350281d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182186888 1250 182185638 182185649
    0x1119030209090a051801140708011e090911270108010b22090203060c09010201060f15210c0507050709020412030e0a0b070b09100e03120c040506070b09010606020610 73
    0x4c18241c0f02c04440ca840c10030140b94030302c1c06500300080d40c108050304008180c028501350399442d0650307130f0350405005c40c0b00e688620010020814001001200160303000803541078001c0c400500400c4104000a0345000480d00e1070309407112110a82c41054080401c840c010f01c101d0b4001d00c0103148e00e40000700f100200d109080300b000c25078820003083c100c140d40440b41c41fa50140485140303041002364000c1e036400480d070560040d0308000b804180e0300d01d00d81c1c0003011100310744011002c0e100150301c00d5501c1c031090049250410341045854040c0044c03402000020061601c1e11980d80c103403420004d00700142c68002040d843d00410082164800782c81e65103680942525259080210071000240d01c0055076101e528400380119020040c004803407042c0313000d0003144007250040e05900340c2d06001e035440daa1480800340c006022a101003203640303808603805201c3c008824507080d00c079000246103401c14242034441c00b40032010404882401d11584024110030300080c601450700143c0c4000120b03860040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182188138 1250 182186888 182186891
    0xe030c0406062a060221070201060f0e04050109060f02090a09020f070b15041b02060906010308161b080a2603060607060216030e0f010819020309101119030209090a 72
    0x114940e842c0e00c01403c5030650701200555480f649007040c410a0304502881d09154403400000c240d8141c014400c220484840d08425400a03240121140c00e03c103004209481d1035480700981d0b800500180b00b4010008030401c0c1c0145c0765000401400043d600503000030034050700c104514202011504203a445c10303a03101110308030071744e44c80050b10792100ea80c032411604281000426200701b000540381000051541d4211015642d40c40c1c038603641ca49080c070018190070802c202c00c8141e400502140321105010b20f44080d01e20001c44a04400b000c2c1d40e61140300035400c16440c840402480141d5102c884e079100c40d000c3e900052503c5c52141a200141129100e11400146802042455015240070a4461424000000140c28041c05881d02e01c52428441c460038000414213600449801c0c2c0507144050500c81c1e5507808010120003540090142d0100e8828039004083c18a0385018440315032842c601000e44807408014071600c103001a803406410315005200e10540b5440300c0b1030131984010640d60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182189388 1250 182188138 182188187
    0x9110603041a04112b0201050306041401081c0f0207230907090e0109020715050702010b1005070605012403050408130e090d0201020f070308060a0f060e030c040606 72
    0x1881e1202c0d42d01400c40034400c81160040200307104011040e9500104191100d02c00e4005407000240300c015045c0d00140d084031024071010240d4800e00c0950350200018000040c0011b22001042100b40d0036403210030181d100d0100c01c6046110285c80c40c082440b41e08290100004c9030b00041d45810440c02100c001400007013807102c1010300f60a5110501801030248070460410b520014040040c07402031001d042014030001801154a1003120320250300440c0441100700011005800b40c000508004110f40d201c0004180669a034042c01060b081e46480c0c00d0317950f005500e80301045c0c0384140d1003e1030b007000b05181c072000c0691032405141880d90354500007800366031781c0c80c0c220300d5409844c1448141c100045408240528188500c5010307031082021240483d940f182d04078281d201301c0071401d00783d520034084440000e005112094000d24010008503119841d402001d00c05681944418001a02c605100016090a00032120051401e40707091100740c2c1012009031000b0405042c680c004170600c0b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182190638 1250 182189388 182189393
    0xd080615030c040b04140a051f030e010e120d0f050103171c0507030903020712020a33051209151501050712030603031205100b091c05061008010911060304 68
    0x100c0f40613080c0d5801c12602d0341c0d294a1000c4104004002c000d0003404108404101445e0075100940c0c040d0000308215042c8070211411030141c01d00d0b40440f102c645d21102c0918074040144080240c03002d407810440d0b10360901c01400802e49080202211a040c90100107001050300c01600ca008000801901543c403174007500100403030406180f140804074900030600410f268542c00440d1841e0296003224146516804500d44024208100950010103c0010444c1c0c91040e8020204a83e50014400c0081c08034034208445020105060f400100002a0001e51069598606811800305001020011a482d801b5043c5440144c440030006100101003226a80700d401251a034507441902e41d4104030a0750409409454a400304602041c43c401c080c0c00f072003180380300b524415840064801ca050780382924250282c4d00200100703400016418a079484084c5010550b00c2961040000f06201d10380710b00d6a06040000303400014869040c10404000306101f5194840c094004541003552030702c691 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182191888 1250 182190638 182190661
    0x906090d060e03040812040506090f0109090609051806070e010503090109050717070b0c030406140f0c0705040608160e06030c100f0e15161704030c03050d08061503 72
    0x11480104914100510845182e4020000c0c04c12501c0c00300032509500982c09040c9214007590290130b4000701d050218480c0da142c41ca0200c264040103040c050b080399281c850b40d100b91205900003a0f0807580751014000011020904a2580e01e009800342c034090810881c020007015609100d241008404008911044004e5000d0640280c1c008104c9070382c0340e0b4581450f62030300c2406d58154424054240001a0752242404642d105800d11700039614182c21700f0300c03d0307546800c4c0000112402c0000d0040180c04080c202c0100840d205980040500c286840100030507198642c0160025800030780900040381004c103680000d039010070780c0c1030309269144070200e464107429084140e80720010038115160b0b40e8200c0c0403902e0040d4030382d6804505518520500510070702000e0b000300c04000030000040c0341031442c100c8001003846000c4420843c40d6948043c802c8d50001e400994013025001c500b0130404c4401c0003011012019400c002d40103103410303400240c1e00125407080303015010f400000078040d08c484 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182193138 1250 182191888 182191909
    0x307120e010e10090b090a020108130503040e0a0e060601020318040b040e0316060c021c0f020c0312040501030f0501050f06030c0c010615110601080d0e01020c040f141b090609 77
    0x6000b1a48100d0f0003216410140807910015503c012840c0b0102d01e1151000c5890310507a07806854002041c0c6600181141c980d000003429902400f0510010418129640c1c40c1401450500c10100304013100c40c6107141880c8c8094040341c10b42d8010884c0d45007000942c0d46c4680344d1142104d002170400d00040200b409402c0c114420b0495000008041488842100c0b18060807802aa410001b0800301c40c0305907960038101d01540d020041040030790400a1140801009640151064802c0201d800e00400d241c05040c120359024400080340c140441c1d41e16200380d88060520000502c0154500b60108100d0700707003200207501400000002a0b00d00300c2e008100d5800ca91080f008000459481c1c00c010003035101a5030610001e504c1641d07158071101e000403070a06981050000d400c124400141c26100c40f034405034884d0643c001d03101c1e050000c2e0388510400f1240c070a10000480c03100e24030010f025902d46e000742440907424079008083c1c601d0007840c05a50300030800350755207070347c1d401c6c1e20b0006804840b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182194244 1106 182193138 182193161
    0x9070e06031221010608180102041a07020612010306050f0f0f0a0c091706010611070312030b040b0402070606030201030b0406230105120705090a09020307120e01 71
    0x80b00307006080902442d00629600c001803504160700303100c2644000c3c08904841c003044080044160b8815940c007042e17000b1450305090200c0c0191a82e910040300400101c0410410119142d0008440c00780081040c05443c541c0e4030300d0510054581100d0010030780040d44040384c00300302010100ea02810f00c0103107600d002c0c2e413008449001000000c2c013400c20401d001c0d000040003050380b0b0f030f000c01c0c80e07400c42c0283c1255818207101416034006000011455440800e00308081402c0313004c1403100c3c525910300803605074070001c000f40c0130b040340c8059240d00030710008003c2d082185e150b0113070003100e200f80c80c01e200306403a840170002100c7e490710440005888800034070321404d00100104034a0b0b50141483e50410111220701c2400400c12100c40010601c009100d1055140a2240000628070075100358070f11310700148001e1150700ea02e41101000354441000d0701c0ca01c040cc0d0003000c84000d = true := by decide +kernel

theorem cover : BRFrame.Cov 182014388 182194244 := by
  have h0 := BRFrame.cov_init 182014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182014388 ≤ n) (h2 : n < 182194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
