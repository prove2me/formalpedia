-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4679
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:23:38.036707+00:00
-- url     : https://prove2.me/submissions/ba4f9d5c-a04f-4372-a016-8f3843687f05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841366906 ≤ n < 841546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841368156 1250 841366906 841366913
    0x141c030605030a020117090111030702160906030b190b042a08011802090a090507032307020d0e0402041e1406210901090827181801180b0103 62
    0x60312004000035001450b100b10726a002074901c40c0c9000503002d1500c940000500134040c25008441c04040d44030807075581e070a025070700075101c2c5884100407032a05002d44000441a045124040440e038000082034190740711a900d404000013003412400881d070700d41d0f004103500c3d5039500c41c0c442c099841d9884528620907030b0221750103400a811030340c014820443c00401090030703690700c1e10348480703010ba40044c6e8951003080090182c00f00e503007080840074503180401ca01c10717070181d20003410300440350402a80061b880600c0300c042c0d81c044961400580101c01d00c0721600b80554104204450020030140c01d154032021000079014482c0040602ca0500c0342e410010441d5030000380303d00caa810703550380b407402c3c0302c002d1410030450781c906000170250603000000740342d94001e5006c40c2070b841e4443c810719600d281e00f06084101d00c098000200c0c050b100904248050f103000c54481c9400c441c1e00c611409241d8400400c50340a00b00c0c0648201c5030b54a4110807800c41d401070b40b8900c05103124050140442d411400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841369406 1250 841368156 841368161
    0x1a0a0c150e072d050f01050c100c0525120c1103030f0307080a091a0408160623191805030706052d01150c1e06050603030310030f141c03 60
    0x7200a054019585014841034031820350040445e80b00b801d103582d136003581c82d26040c50170740071100d080b0b10a440c1010301c070000340c0c0c4080103101031000d488401540e006001290034400340100c00041501c0c180011801109000e0780c000741c0340901451011030300c0c89204001ca415a4000031560400e0708001040102e02c03904000d80c03540004111004110440301640c881d14581cec00b681149016040c440c0005040103000c4040b035401d8824540b4200f4003000d1843c2c0103000d8040d09908203544609a40c01241d550341c40c1a01511038841516068500340034214a8402880803400d9001c0490364041c00c90041a010001400107520802e0000382342c0c07420f140030b4400c04041c0403400924050040280010101403811103065800c9148000703900480488151201810254000c000300400380a00542c108107400b5000954000c00d400e00995840404054aa02c01210b020385001c802a03030501c08100e945c000d00c080180306003050700f07040350284c038030301c0c586104582c80700c040d100604c3c1703000314243d0b060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841370656 1250 841369406 841369469
    0x6180b031e1e01050d0602090d031e0323071421010e01081c09050406090911220207030302091f020f21160803010f1a0a0c150e07 57
    0x80c01158010b08180e008065003818401c0b203114035045000c41085c0f0469030b04a944108008140325007080791480e029080380d1080700d80320031400d22000d02144140c0030303002d6800c0b0b5005440201403a42c031201001140e12002410543c07c100308581c0707000d84e01d1000402000e01c1045444c0d80c800140c29800d884400103016000100d5055209004005070b070800180e1204020340c900000c1641c0300000c408858000b000d902c8558042e007005400202000a50700649205010301030002584040d00184040c2004040200450000c900c50034010711055500ae803a00901c139140141c0b40c41a100002010101c48206c007441c4880c1807540940c0b03041d01005a6007131121150701600c1c4d42d48020303400c81200e082d8a5001c809500e000034601141d010080001c403c02c50384445103944a503190300c0500400c6013a809110400d00718021100c072130038443d005441014515980b22221009507541c0c030180d044540e4207481c170b06600c80340c03055681d00342030010703078040d20703c40d20b0800c2100d410b61030140301c00450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841371906 1250 841370656 841370671
    0xb0705100c1e030b13140906060d02060309011517010b04050705030604112109060c1603030b01110106030506090114060f0f13020310050a05010e03060106180b031e 72
    0x40c409210201c9820045a036100103007900c08240907034004105402030030701030446950200f1078140030030540056900c4500c103030090809000d03003503941d0344150303940e1481034412079801054081d149005150001c025940310b0344110001c5130000380c512041e403c210040d0002c2d55220304d850300ca0244203e0910903260001c5003150140107500b088030025045100c098441802140c413100d1003101111420111803080c070b94015030806141c0540104044090306991605003401440086540003211206a80400c1094410403000105503a01600101480151103060203c8101e4051400300284140b00081d40184041c01c410b00d0005201d0b400c40e0203c0402c0301005101c481446400d464007420090018010756400030f0030500d0380005001000440d010f00c00041c000010080c40e0034650321048101c803800d076820710840751603074010743e003911a21000a4040d0300c004010030180d8410300c100341514020002d0885525210342e044605a403003100d0500f0300306c48190b00001030455440d40268480c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841373156 1250 841371906 841371911
    0x21203090f040e0a02090c030105010f0203030c18122509061d090309030d0c0210170703091b080c2106130528050607030c0225050a0b070510 62
    0x5030000551020030320304000d01403507851005000c00e0a0400c20404010340007000b03001c03541b8002e001c2c4200341d44240209400500300b50030084820b0b0000096034007488030703445910300b0305001304114440b10000806550380540c1500240d00341820a01c00341040308202c90351100c0c1c006852101028070b900950100b0042403030001c003004046820705d80d020311000a0025042c05813150391032545140102ca41699044c040d0448605000e40c1140c02808054401e8035074140440084400383e42d01c98006100076402030f040b5000401043c0f1940c040c440440c802c050158940545a454500e055102e8011f0101640528500700070351a121061000350f0745a02c002240c0c40d114003a15507100d1501409a501c01c400505480c0c040050910074a41e0440301015a81643c14014080c03110001d401081a0342a02030000807407811440f900501d0081c85082c1c00421024001d0607403001e80186250180284440c1a1404903190795848d020000416042e410300343c5401090400c1030a0101100e41c17200c240b803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841374406 1250 841373156 841373167
    0xb030c120d27061107031a0f010504090b0f180102031e061f120f05070305180a030e0f04110c010e0706090608040b1f0e0702010e0a05070e0718030f021203 68
    0x541c450420a4500510f000e20100d041c044000e89480c5c900e81000f0450741810307100442d000d0480354502d124051580b150561644ea9100740400c480d100c0c02c01910741408500010305541c00c7c11003951300590280796041e4500ac83c010740508982040d40d200181c0140e802001c807040c41c914001c146c10610441c0e900d2003024001100c9003602c03280d14003070310520403010480c01400d4410340c070080341d5156440b01400700e454526801001400d04641d03640120480035172038000034000286036005d003945a210051a440c1d22400c200d011088000c141d0381c0b054890065043d505001d01c060411241d94000214500c0c0342ea01420741060400e8000c0b000300704000104011007613100c943c0d1038200e5001038402d0f1480d118038641d0310f80d1f64402d5207101d40e200c6558800040551048000902c107100030fa000f080381d4a603200386561035108140c0c000c1c2a41d4415601441900d0360703c1e000d01d03081605420601d030088000080b41d030720400c0d107900c03d58031542806405825810b003600038041640b02c0a01551415 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841375656 1250 841374406 841374467
    0x60b040e0c0a14011b0b0a1410090218030f0106030302060705070c0501050d0227010e0a050109050f030a1202030717190315080106180b150d0b030c120d 67
    0x42a5032180c000e03502c56250500d440d03640140d00366640d424103181c00101020040c204003044c504180c407e1841d42e0700d0410714440c900100c284a41c00751044d198900d200b1454040400c0107904007203009682d02034080740c50318499070104407d1a00303441200006c00e9070791860030064181400103000d44180181040004001510001844d0980740700b424502d4442c20040b000000a0140341c0d0060b01e40f0305002104400078410741241800c2000c240d89203051038103268180180000d040c401d040c041140510140842d10341031004c01000380c0064212110101c0704e444181400505400090160b0400248802400301800f079400c040c407017a046440c0341011800c44020320310001083c0204156582d00c907280c11141d083c00740c0d401008800c00134802d06440301c81012086003c00056a80c0e0703842e01e643e000550074002c454079552010302c4246800c1440d16003559019007100c0009076814080c2e00b00300c020304d5507098035038040165410024641d8000300b120142640b40801150401500440402040e2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841376906 1250 841375656 841375669
    0xc05030a0504080d0204030302101b0e1e060f0403031101060f05060a0306030b0c0c0f06010f212f01170a150b160201080f0708010b07030509030a060b040e0c 69
    0x3000455200184030740c1c6900b800395841c0100614650f0b228000035001080c15800101c44900568245003048504121202c94908130f0440b2910341c0481c0c1180c184050600c5c0c600c1010308031284400a030400780c4c0d0580300141c50b0b40d03c02a10f210034141e011a0a0041c59844005614800031020003086428200350303042880158030310800b40304a80006054402c94407a0b007099005560041100c40c5509205a4151b81900100b954085600ca44000720b2540c050024803103048070b4081c90401d9100e4240004050340c40c0040b41aa146912502c07180400185201001941c0c001c5408143c5107501a1400725844500c0480c40c481c100031302014070301c803003024107809035411051a0754000b81a0408268600c9661061340c40004580004622420541e4840c00c0c3d25402034400da80d40e104a98844d40803164900058031001d0000c0d0030b043c014403282d009000180615030203402e205042000c200c1c002803419161100840c0c0d5aa1a01f14640b540c2c145401001800000b041c060200302c01440c000c10170 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841378156 1250 841376906 841376911
    0x3090516030b0c03090a0b0f011806030c1401110304120b0901051005010f1205010b0c0111040f0302010f0c020306041410021e0904060317030f0109023a0e01150501030c0503 76
    0x80e443c000002148441100704003006405074840740c40d02c0580b50228141d08619800d204407000606805201e2110401074401c000c02e80754480c4c10051501d05008854200c410054119418084060342c01300c100c02003080600010401c01141c0c2800301d10615054a10320f070090000c50b03051b03050206002402c0b50208502c1d066034000e203820312103207102c440c04503284c00010340300b458a94603080011034400300c0200200140c1680100078001c140c841c070620105c620862156850303040d507901c3c01340011b6100355965602c5203454a80802d90840d50b800290070400151021a101a040e00001c00000d00030320600000c220b2405046080808950580d0b0741c11105000310041d60030006000c002903541c5a206030051600300205600c2c55080c400a103006a00903126004920b000c1130001590304094001c4a041100c3c002d00f2400c12000303210048403030b00d500405a40421004040b8101e40b000038810083e031445214000b240000f008401001003044075045203040505002d4003940302a001b02c11240c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841379406 1250 841378156 841378171
    0x2d0a0b0a030c2a0b06031603030f0212030a021306050a02030406030203040203010e0d0c030305010f030c030210031d030904051e0402220c030c080708040b0c0a0c020d0303090516030b 80
    0xc00c000000c4003240e141e15614050f4110441190000c8090011070348810f070042e108611402140c0c0341c0744101580c40710302261032000248100f0b41813001a118018070125200e05004a8858140144518195030400c46404a1b00d5501180d8222120050348464000341403500301603103070111342d5078000d480744501e000780310030700d81c00001140454809610644240050740242c0f8201d40600c4c01c01403c0b01c120078015400a804d0200201381c032800d902c01902226406601400a1803443d400e1044041a001d04003081c1580c40d4090040e40c0070171200003602011031000b075540d034000c0c042080304540c0058504500d240c05850b8416010a8000000f508140c04444c0b8a0400402c655a418200c00c00c01e600c130111030401a0400c01c5035096080045a8500b5449521041da1502c10444103400202d801504495070706c3c02042d4411030140003044904803526041e4070950a603008038280c02454901207000903990b030308010a200d003e005000c030610400b5010350031245503880c0c0f03c0c4000e00185c001d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841380656 1250 841379406 841379411
    0x110d0c12020d0f06021308010e030a0c1b030302060106020f070810090804231806010e1009032f0a080d08060406170a050c0111031909052d0a0b0a03 65
    0x8415541c1d0101010b14140c2c1c01128000001c0c00c0c0d252a0000e03400c40d9200310300400c0903000c04941c0c800107026200b480b010f40743c001c5061030b911070021507107000c0c3e14000780c4002c110400210011140b0a02c3c40b8040c0d0701a030018601c5525244000349800401d07100072070141c00101050041003008a0044640805950b0100c1d02080710304280c5001c0c46254015910303440b40c546104000030030452004c00040c0100c0b0340e200c0907035114085a5015108a0706940000e012800070b10380c0780341144940d1b00344219071800410080d02ca03500d2000d0004460300c01c044049400caa02c40c480c1c048240d028122160940d00c140d211864007452550343d00c042c905440034480880001101c9842d658840001045201c4c00c140e11021b9030000c00e40c540d09581001e40350780c0070b03180110140c1c0d4003614900510046c0c040055180508200300c1a601f1880d80b2003001c20095202d80004855441840300a290700002d591010088810824807200300050345882c0d0040100c03020410142c09040c0c240c42d001d10280c14007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841381906 1250 841380656 841380689
    0x9030f0e0a0812130f061d09060303030f1f060507051c05030103080d14010306020a02060a0c05041703042c1003030503040b0601110709020a080f010308160f0803070c110d0c 76
    0x4440f200345608a000060121721000441315400210b404664840c001c0344006211148144491040101c031a150143e200b000452180c800312940c455004052001c000d0245010180b2100c0603541640001e001500100d074260070b20005101c000c002801e004590f84403d0800030b000341140c0014400a01b8098000c0b07041c019101450300304800e514140a058601503031a03141400094000ba00d00750010710490001450908441c8100b01c6020f07807070703192541018607140d036507503c078014214500c403240000e200029803444034211000281015684807000307002c040c16040c075280c00081401c54001901030302000271070703046011171b500103400c01c0c40c0704040e03643c210058800215620303900701144980c003000280d8000795406000c04545a95400e43c40d80c48103460b170040c8081c03e00000d81f24800c10003160b0080c0c4440144042041d1250203a082120031540b1040000e800440354440401d26111541d8100718900e1040c02824204403042c4913580f00d0340d199074145207094040c0000c0320880695 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841383156 1250 841381906 841381927
    0x1d0f0d0303180f052e09020102150a06180207030507020108130f0b10050d1e05211b06150f0102121c06050a1a030606070609030f0e0a0812 61
    0x44009246007200b0b002c424040b41c0e18102e91070034410b11040d202400780b048140e032500e0100070405401040a201607000038114004040101301c1000c0c120b05500c240d030140a071b030040c0007003074a1151004120002c0c20300c0c500083c1c454100c1640c0f035801c002a00c10001140040d8103c2c0595201980a103803c5949680d0040c17403c00100800313401a1495284603280e00c10441e070507403030764400c401303e030191040a5520f80500600c111000c5005001c842c000e440e01c2140386c4242104140b190085044488030000c1218941d00e01603001d02e41c00a02e440040c0716a14901d13468041268039400781c0040c02185003005100d240c880c247e42d0b20b148103025203e001c11a0f1380c03080144000194548407401d540d052038515800300d0b1500c0c000e14200c1507003000c0c0c0000c0c00b80390039140402166956401c0ca100c050518038010050b44c0010a42e551102081c0900008109903200d0002444d210792140d811908125002401d072090b8401007500c00c8030000d4040c041c0c50401b08125042000c01051151200319121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841384406 1250 841383156 841383161
    0x3120408132102040606020f07151e0f0e1e100203092706010f02030a052506090611040f180b10020a030e0612011202010306030204020c0d1d0f0d0303 66
    0x2031020611500402012141a052004140c00700f4400c0710100101582c8407030a03031b00e071038000c1a5810310381c101c2d202c20408074580e80205890840b031860100b07000d240d02e05010540340c581001c0c5c1400a002c0c2940145ca10340c1000040c4040a801c03907120071035842e250740c210403181ea140e46480c05210301c0045c011a082c02081a0740345560020110180224642c000307003030f02440c2400c00c00f1701100140200d074003940500d0700b8594a92190380654641300c0803900544043c3e10841c40120312041d40c02d603e800c0440c103c50340d80c2c01e0600c0340c000031508420504040007954800321105124010400c420000d0358501c440314422554030708000c800140c0d1740e09800e40140041c20020390010003201c6591a40b641c0801c0c0c0d0f4000324030a0711083e8003202d102c4103021701030081070461011402020010302c0043c418054909035284145070200320141c984c0d0100b0b0903604060423a194a40c0407038150301050f074116040c0c0e90f00460b21000c040c000118240000c0310808003088041c021110702d4402d20905110340c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841385656 1250 841384406 841384409
    0x1c09020a05061804050f040809090414060f07120605101d09090c01020d180e09160807050a1a030105010e06041a091507210215010905180312040813 65
    0x18240340e15100fa12107103140c00d070412501103100b11715000c0081c6141d01000d1125015a4018400314201207194090114050000e0826240204140d05c03407c80c030142000000c0c882d80c42018060380c242040d2601501e500ba102d0741d42800309041c84001d00541c0ca40341068107845403135150461000351050100341400444842854100855108000d0000c40010b18410065000c0c1e084810307914046134201c2d82c0e00d40c2d0310440321903284501410001803e5886a0035005404502500c550007059403011007100c41c541e001d500300d134120307900070420b61500d80e404800910103c0440441c40d10801d848481c0307480140286414031040c030441040d00e03120079080c4c40180c040100740401c02840e07500c9080c0c0d00e40000740310600c10341e0b80073795070a20300584a080d90001c0d90300c0140c04080400100e039024090a4180010701148180c5400032a96030304616068002d00c50100b0019040c10074040504424400c180c2c0340c405a841000700101440e032803641150b0048d00038100c140c54500908641e0b00b01e00d0103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841386906 1250 841385656 841385659
    0xa150e010509163006020c0a05070509011403061803090303040315050c18010c0204021303110a050415060c02180a0c0905030c3d1101060b1c09020a05 66
    0x8000030012401400103c0d1080c1505440c0001510356549500226001c02d1800380c3c14814999000b0382d140c0051050240d080522400000d41094a143e030181e1170000c40c440152407642c04007200308000d0401440c024003414800e41c5042c40c69103e0004a50350720005040c030302400c05000703110069000c1c1807007a5440385e80003d080d80c3c1e50743e0f035a0030086541804041c0480e205880d1401090303d03150188100c8000f10500401001c071078550701c0066503074150012082c2c0e0050340801050804000000010002e180300e820404415013610080c13110256007508400d02880c500314801c407983c82d00d2030b0342030220b50325171a003090f80e84d0291001c203c1c5410300300741c4030000381c45c0c060900002028503040010120450f50760790a80543c0e940400d0b40d01d4a00800301c43c1c00c43d1605840809005200f105c1c215428000c10b40191046803801240c80b41d203c41800034400078004190090740b190082c01900d0040412803282810440080c40242d65541c103982c081461070b96078141c9104544420386080002c020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841388156 1250 841386906 841386911
    0x80702041401061e08130803070210060b071502120609070c051b1e01051c0b03070806070809030301050117280f0c0801140607022b0c060e030a150e01 66
    0x80d61440544400c42908420b0780c1c1144856540100301d10481c480c900c02c4068183c03104981006d9203611540b41e20203480c440c118040c252a0072048441c42c041d130b10003400100001d6507200c10900300200c2138255110306c0018180108140a40c0c6824400001d070040c00454110341070344c492980581c4c45000d030060041c060701a0700c5108202030300d6040d100e00d0402c0c0a41c3c04011074a0f08404903001806070031034250219200380f01d6514801403010400c0002019620005040285640028174000c1c9540c02240b0035401482040311982c3d1281189400030b0030000254110f504100010740112070703003aa1111880c0b40f160004010004501250001c000f04058566864020600d4100a00795020307c07840704600300206020054402c0341024100c800046010300302c0110b42e000c1040c1c3e9400326500742d034800c41c1c00c11150030884101112600f034800b1403613410803540c0e95140004407a60141d01400074050300340031164030368402284d010040d6a114031f0159100d984001000c00070081d0383c00c04045580b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841389406 1250 841388156 841388159
    0x18020c1e0102030109180b1b0714010222180506010507120207080606010c17030c04030209130605061c03110321060a0f060f0c03020c0d0f12110307080702041401 71
    0x1810342c011410380c0d0409200713022200341c80341c0480ca080c69160300100200007040009010140c40400200c81c94040780000e450b0004a0b11842201141c01c100300e0710a03540013952070301201c003028a4400f200c0e20301d41e040b01490701c0e0041001310024035185007075405403940e0018406a01c80d01c1280d01c40c6030301c205150920f80b000c6200940d0340c0458043c0f03580c0c92058001142103580954040300c1c203154428000750b01c00000d42d60140b0386801c06408500c01880900000c8016620070300498460344c24009143d4101c080e508100c0d040d520094610750245600c64045422482d106144210090301410711601001a002100740f5500c15001c0b2591019403040300c85240c5240c528406005d89070491300006150340312500002d40408901c50748011070b54510960303604500803021048a00c3c0a40150388024618101203000122410000c0342c11030030100d041e808103d030300e40b410400500c851408050b0030810728401c1c0e0344d074407407408081d0544e000401d03420219683c5e604040041c9091028008155 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841390656 1250 841389406 841389463
    0x90602121b090604050d02120d021005011d0f13080d020702090903041212110303131a070906050f0c0703030f080112081603030b0d0804170718020c 65
    0x3010607a0300160301081c011054034800550416241401c0c8002c2240d4038051400c03040010340fa8450304201c0e000b4030200301c040c0110400b030000303810040150700a01005c111107144602150016080031101445450760204100d40c00c510081c0c0c080c0551000c45042e4441152440c0c0c8041945002045101c0004040c0a0030b10f181d00603014051090b500d001243c0c5480c481c1d6034990145005140e4508900c620300000300f002200500c00108190500300f40201122411a04552003120514848402c0f4000281003042c09500107074250b09003d41d51180c0c1c10304400081001c01a4488d2008215011a4110362816000111036240400b1021038188940c3d0385030140c00b0142c41d0015002144094000169443e03000701e1581c10070740d04c5603803185003421550440e00c101038240d2069040580da0120110261a1030844a0205000d145919241c03482c0805a01143e9070310322544004d908500c3c1d04000d500d15500701542e6140100001503182c0c002c1c120410307e00b041c8619020280d11030f0320f0300c0d807540707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841391906 1250 841390656 841390687
    0x71202090d05011b17060d081603090f060305090705010f0905090103233405181807060504300b01140f010c060c35070305040f0f06090602 61
    0xa01d1381300d0f6001d580b00c0c00405080d18840d00c000c0d020305140750b40400003101c5240407400070300001e1103484020304000c0c84401c002a2010b04150440100c0d10012003801428a81c54403840149000d1600703104c40d00d410100c251329000ba5100b03450500011190044200f030007244074101401c0040d202c400c05d07680d0303400c0403042141080c8281c91030590740012009694004103542503d441035041c820300b032902c03610b203580080e403440f482064500ca05030008140c0d076550b0351419003034111242c04e8800505080206100ca8801c1a02c01c0e4030781c0d4002103040240c0c03034201090b0b404891030072103000c155111500d00032100840c2c002524840806140e942020003009031f03000d40c16914201e9028002591040c02d01a4056811203050f0100d2407030354040d4009072241e00b01c122000e271585010480800050b000614955024611480004200c907004003403041003c1041c0e4400603501c3c0601c018103260310791420b20281817a0240442c004c50303290609116080d080031b00310a51080e4115aa480e1000f110100b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841393156 1250 841391906 841391921
    0xf110910051608131409010e0a02120405010902030610060905060c07091104060e04020f03011211150a080a06290f03040c090507090e0c090109090e1c09030308071202090d0501 77
    0x10302c91241074086050b03170b20100024003408010b0821003059080440012681e003009028440d40c0b9004c0080100e41480c40b0001400345d40700e00d00200e04001c0b00d20416003005002088045464180101004661b50020110b42103030b8003503501544d02d01c606460355042906603003019400d1800d1583d8880c58070f4112004200321240c5584108481ea0480100016441007841002c003080060006200c2d4840308186645c1041c4200804034000012802080344003280b600c407041c02090104400181c03e4018903d658801c1103000c0c2040072505080421940c1c52000006559028600104040b00311103901103c4030100c6107142c807134a9103854601100c0780d0001d03010f00b9203482d05100c0403800c600d01030440300e001e031110252200d110b1358a4040e5050950820700c84141000704e29500040d05911a20a407070810f41d00c4400342c510b200030035a0303c01e10030441b200d03135408020b1100c10801c0460b42c040350f09500101d46140210300005d00d50400d00181c0614030240d9407020340da081041c1044415800f149 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841394406 1250 841393156 841393177
    0x7050c041b08100312050901031506050a0908070f03140a06050f0106140313120212040f05030d05030c070b040c0305030307031409010b0a0e0705040b031503010f110910051608 77
    0x30380039601c2008003c0c50010300d110003001a070b8444030344104280260301171700f1251010f142c005402c00650720180c030207108030b92240f00400c000180c0c80b440154001e1443c0041c4c0518001090078600c1c1821280004000388006824414040009401080144003000d0700f180c010301e041c03145080036610795103054402c3c8102d50104030081d01f40340d003929035603040d00c0c4680400c1e4030400403079400d070711040056017441c402207085018660126400f0300c0b030bc40140024000d4005d58070302960424052514100c02d41050b501440780030300800180340e1881d4111801c26502c196449225159440d01500010b0281c00041a40c0004020021a83c0e81540100740c0e15031449400341d055165034280701c0c00c80740d80f180256040071740f03000184495400065030300d403c0403280c80c00500c5d086c4d440c01c0b0400306401c02e542c20100c03440f550800108034542409525170300401c64a04009071504030158601500c200d0329102e001d2041c65000c852010300480545045c1802a0155641686036140c1080658880c16001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841395656 1250 841394406 841394417
    0xd020c12030f131a0612161a040e070309020d0f0803090714060a081b0304050f07060206010f1203120c050409060b09150c0102190e01201207050c041b 66
    0xb18009404a0f0364030285070808a080a8264884c07021011070310001d2509401460b071b002825418201004204108400d800c0b2110840b42485105d0000d4004c86c0032482c80f8507000c0c081806003011301c0b14201d400080c40c1c00c0000b881c401510200307019924803d0080c0c105909a84c4001c107001c0b4800c01540f041c0204810740d0392146e11814403079080b1125400280d0004001c0c0150902140280c8906800490300d4407a601c18a881d5484078800760301c00c42d002c54050300880703c0d10082030f404101d44005859240040c02e415030419007462003540d4540305225520505001d14030078135009030400d170003080d81d055050008071003005015000358040e20640d07000d24030308000000e42103c500240d40141c4002040364440000041c0d401003250850b0038540302a550800c50b80c0415004402032120044284c1c8807054161030310701c00904007141e0300120010703002c03000e580c100f2034290214210f55045d6001c20310548034695810000d01d0501c51400c410340003460304040080e20303803d14000c20794440c00d903681d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841396906 1250 841395656 841395661
    0x1208010512010c0207140a0f03050706020d020d1227060218031b04150f09090308060102061603020a0e2709192d1101030b01030c020a080d020c12030f 66
    0x49500f2550781218901c0103800076a010b104030030f19514803246412009019021854903035600e8488030070560300448040e401111304000e01c5805100d003015042090018089180450001504001d0ba03031b0032281d281641d40da0000740901c10021030000c1c846890070500e0400c40c15280520080d404038107a04402100c060213010030340790004805107140d9858601c00c120078106014080640780b10403803481d01e48040b42c00414000c81051a4200504940d2004100d000c118100030700200c902031714090464110400b0000030a111804102100004e4600166910804181207030090b03503c80e245540840e01c50a26143c040d200200e40c2203010903c070508880d0f440f140a078641d15005900504001e0040251180c04204441030b00c01244000782e1a00182d4002203442d880f96000009084605025400400c14696454410902e10f00b10a003801c019500c1650300c0a0b50f62040d18200500105e03000071125140e4042c0d806541c04c03e80c0c0300c000c403401d0000c108000c80058104031581e4006650b03c100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841398156 1250 841396906 841396939
    0x519060e0a0213021305031b04061d07110309130e240114010903080f07050609190813030516030b070915030b0102011b230a050910030912080105 64
    0x1d0000c0400d60080c0169000c00a205240019401c1700b890710b1035402c3c0780c840001e41e0b03881c14080f4018150070050429001c1801ea810003003156010b0b0000c1c03c00d510b904440170589407150880030340050950424954800f119070078103140d88548912950003a407015030399201d13144c043e0482c01d00c100030740042d650781c1c4503034010350034003580d00003040d00d2083c02035001040a0040003600e502c08420602d00412600c2e104d856030b0410364003010150424542c00501d17641807000900c10396030083d81050140082c149400e1003003002d44040403000d42031070070000340b00c4410154095242c0c0115070120035102030301003080050b000c01e401d5100c2540c2d151103450004180d10b2007520b004007554104c244095030140740110840041c0300e481d50107030640d90ba1b62282c8100c0c0202d8500c070301c42c1030665681d041002caa5500402081c4d61031031200109180140240360206070441c00780e40e42000240c1d800071345050362420480241011a00c064500011080c0341c0c6402d542c001c1195040c2c80c0d041c1d810221400d10240d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841399406 1250 841398156 841398163
    0x1e030809010c0906183506090c270103080c1002090604150309150b1507020603070e190803090901050d0b04080f0d060e06010e060c1c03090519060e 65
    0x2c8001c0024800300e002e225150003880c400b061454211070034000349885039852548240c269103000c0040d201c3d210380e46c0381c000040c60300c454184518409090f541c180a11315690700c030003840310240b05c1c904d04107003100450141140b400c040e02603600b40c0c0103c1d507036a080255059100c3c0142203114090006040c019540c14000c441910201401440c542460b022440365506041084407041585403507414000c41d18141c403000038040018400107040e09400c04201c0048110308403100705402c140312040240c2e85030000d03641e1100041c200b43c6203801020f0001000d060301c1b0404580b43d44040d110208080400101030151900c051300d5540d0a6600e8508116500741c262900510809400d40064006290140079155031801090340c64140500051a0000e4071f440341c103e100350201d1501003102c903682c00f500004a01c44156111392500e002c07040d40ca07480300c400e82c100c086005699a4031141ca1842a0720401000f5004000c2d200350041ea031a0344486040c041c44140d60590802038510f40c038113400f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841400656 1250 841399406 841399421
    0x9020a0509040308060d06020904020a0e0103050a06050105041a0c03030f041719110c040609020309010f090b2a0c1e03040b0a0c0807020907020a0b0c160303020d091e03080901 77
    0x6132684802035031000c08204200610141c1141c00c10340a000401050726a40040d0034900c0719901ea1401048218000604a440051424050b607052030020015a60000200d9080d909004002c80b451440c0401c44400b40c459560508070611000007000442140f500c0414016071041062142001c043e189018003030003118000102807124490000c0300a006100642c1c041c00304005454000d18038000207070441d81c46038000c1d400903800004028030720200384620120404919000c002c00e00c50750b01d030b820489400902c0c40003031038401920001c46840181444480350301da11066507a4698030b206160b210644020985101c5c3c0c144a000c44a03031801000b0781d02503601600f0340c1803c2180c1c00404940412030741800b83c5032004100b043d0740158a071000401d2090003190010845940d05103007a078203000e4000c1050b504d0316414407020041d81c1619180803209134140ca40036840740c030795103001c10003805000b40060806901c140b440c640d20007161503070000789010342c03520001a600c40010500741c4092 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841401906 1250 841400656 841400663
    0xb1b070f08120403021f0e220506060a2307080d0605130b0f0d02061e19030204180902220c020c010c0b010b220602010b0f040b0901031e02030304030609020a050904 72
    0x15600c41001410702511540300f00344030f602d040c40800003548081820304040c02248482ca4401c0745200303007d423102e0300a0641011081d107410385400c10b008001440741c840b1080d0840b00c4012104c5000d4064480000d884000ba08100100c1d40c0320381445041004018600c0365900802e01d80c0e0282c141c1c000c01303101725511030f400a0550345080000c0000c0254415004004070703401141881090090b001c03000c0c0d000002c2904800c00e0341d82c1d51100d07580380c40e00d00000c1031a0007010700401c401d0210b41d42c1c07000c512401b90002600441d86c03818510016050784070034040c583c2e81070341028030701c1940107454100100c0d041c001d40a0343d84808a000c0112081c0c80901c4010b044124010b004204042400008001650048014550420f401c60f801d01d0030004961215005170344031008e00b07074103142c07005414000d03200844080000403070b0540401da00c55414400a08841c015a0800c1c0250840280c4221059402810b480d55552a40303001002440c00780c009a000d860303d084017080030300302080780d640501c1c1c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841403156 1250 841401906 841401919
    0x20d080109020c072301201203101805060a0f0509041509080403110315071b02031c08011a0702010804080a03090209010b310b1b070f0812040302 64
    0x2400700a0700a03500940c108503003480741034000a00042c40706070f0f010304440c05029a00005221000040040c121034004c028806242c42c05121244000900640e1000d480c040351602d0380e64410840e210480c455020030041c1140d403150140784155603200c644550004c4406642058070b03441c240c44003c5250103401d4108002802207004503503c0c900c030340c1c1581c0300b00001103010401c9580300403c1c0d400c10303402182c0707403081c503042c0e0b1303004d45824040b90769900e481e0300e0128900d16141d240202078a220007204012500700c5c850340c0095490621114820200302141140d0354400e4000080c0184001d01c1418500d440202c4032a00c1270403c0b00880c0e00181e01652001e1302d0351543d444988040c0d1003006c8040c07d2540c0e4007000c80c0140c031080485030081440e41c0f025a25102181d02481e012800340c081004044013901c03250408054402540e015207c1c074111054403482030300c1d03c20b6403203000c01d1160005441480c0c40080c80c010810140c005548590080c0e613400d800030a40605280101c0c00000d50198 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841404406 1250 841403156 841403159
    0x30b030d030e010924050601020c090106030c090f0f050910060c031d0405100302010e0108010f060e03010905060c03091207240207060e100c020703050a0210120e0d0807020d0801 78
    0x18801d0300700a03084400c20000003540c1300640d030380717600e01215640150502c0c0c4080d90309489403038140c03203401c4d8015000e00291103482d6003400020f1007a0014061a0f061540d916545003490740300d081008064403044508140c2c203074131640629900310492280a1007a004240042c0c611142511040c046407030640380c0b10034181c07041d0303410342d0304c07c081c002903508580018a80c0c9200345da0714091035010b03d4040040d021050b046000041c055421603407030b43d0500001350010005514542c1481044034060b00d0a07a41c3c000703d00b0700080c0034183c20f4a0107407440c4200d40600c201488440c00550080e582c03881110302404ea096088440c3d4011132340080d146150401100c002e0016088005086100001c001480c2c02d0341c9a403903000b1034020340380e00318156111030640e1050f4401071160600c0c0710418002030540c031b440c550390107a80e004900c0c4020700440c1d0312800c4200c4940510240440040f5804082c088090144802a500c80400e01c160b800545804042a80c450004c80c41c0300c00c8101c00c1e0385000c282e0303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841405656 1250 841404406 841404433
    0x14070e0f0102031e0313050106030c0906060e09060123130512070303050a03050406020d1e290607050106170d020d03050c160809041503060501080105130605040303110a1e030b03 78
    0x1904001d02c481b0480070402501d0000803428070846000e140f00d0700c140a07800d41401c0a2801b1a52250441c405010546d44500520b54509110703c1c1c1c000c0092811080703035580b14a070b5207000450009146035104c004208001c0c0000e41d07100c40c90a403441601d0320a1049004841d141d6900c1c11440003a001c240c3c100104000075200b60010790f40103000e03010140c43d04005070f05000403500c08846402140240c4240c070b0104074124012103c2000d800c1019114491007200410500c20030f40040a111321400030b504001c0000a40018004000d500c6032110b608000d969650b071550344902d29a0014001c2310100c504050091003441c1c051008040c509040c03007101e550444004c0c2d00424244c07410b200503c4a894243c0e9a4014100780d08021403295025901e185070200548a0603000302c185a410202000200b42c44920190012030304818017080070b40300c0c0c0c1416002801a55003c00c114a00003072281502c607040354007400705408412901554000d464400c80444803042d0586905070007207415034000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841406906 1250 841405656 841405717
    0x21b101e021b0f40320f04111f120209100302090a0b0f1b1501031101020a120306080f06010302090708040f06050a02030426041e0b0705010e0f03090a03120314070e0f010203 76
    0xf03440365041c1070304122014001000007038040e01045802702242054001182c3c40000c120701c0d01800202981051695000140b107484c03203071a0b40c420160b0206000d400d561700c0c40c0340c00e0000d00f001060309072707150031388400c440b0540e10415080b1040024480311503094200003c1c480d421010f0690070a5103030342190303035a1090f094200c4103941103114620000010504d001c0455070f0180d0b460320b00003206031405500508029182100e1440c0b900f00900402c00344c1c90b0900d03116408811340c54400311075039961402c4001d6214102000d01400d2a19040000a54041e0700450085000d41400c0360b4003586811100010000e0f40c0344a001d603c0203000800c86c190740c0d401d17045441c80d220440ca00708641c681070b8400058000c41025546e41e911a0300e030755400481070003941959510200a0340c0360044102c003240c10000c0314440140092441100e4400113480781c1c0c485804040610302c520000d0400403030050070540c200c5685031003000104007102c1d00e58000000c40b0200c80300e09101591041700d040d1380100d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841408156 1250 841406906 841406911
    0x6140711040b0306091c031e02090109030b0a0f050105030a0f0803060109120c0e1f1505090310051501021b101e021b0f40320f 56
    0x100030b5110503128a955806024107482166000010248883d84c5214500b0851030065400281441e19400c480140c1c01207440e0f0704528403040300075a691400c140100d4480b401d035407001e04042240802d01000c0104d90700300380d0742854042424030280e62034004242c0c0300d21218400030710b40040000d100c0e0008000c00040c0d03621103814100050300b19501d000403041040c002804503400d14a0000074810b681e00c4101c015080001907001d0040b8418404d2807062295007401a480707090358211b0642c0b403142c4500c3c111040b000c4041c06540c1c01040c0d13041c100015240039240d0303501d000c500e411088501e52001401d50a000c20f00d00d40103c240300d85a00340000766804500d804100403051049030503c0c07100c0035114400d45c00c07590041a1035000c54442106088041120500c25080b840e9907001d1559120880b02c85201d01e82c8103100f49503441d03402e039000f001044440d0500746541c5941d03884004066031204108402880c046091040c0700c0e603041403285400c080d10a080b52040000c101800c0c412644940d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841409406 1250 841408156 841408159
    0x70312060504020c01093503060604150c15050c09062a0609060f1501120e070909060b0306040819030e060c07210801171207030e010906140711 63
    0x1034125281c5001c10140e030300c040c100400c5130f034440782d00004028101c040c000d202042111241e8820035850f1050b01c1c501502000c030000c0220210204065503200c1c0e003114000c203601c8031000c1e620700300c000010317150b602d480f1070544031403030400c4800f00303d0300e40e502540e4804c40510358018a442d4008003008201d0b0800d01c1e4071031020f20805040ba040140600383c5101452402005100b5445c0c217602d840e142260040c02c001a0600039403d2103401020b2284600000e60242071001d512802d4081c2400202070020b4a0b042620411400090b880758550200103468003810050203480022020f06540c2c200c20346000303008140c1080728800c1444880da440d500c10b60701d8903000c101e0b01000d075002c2c2d2070000d095581c7c00e106040042c0d08d004004104420300390160401c844c440c0c4244d51034002800089052050f00070240d01030014101048040c00340a031051030b02c00281d620303007040341002008403d01452140c045180035002061450080f010b4030361045d421302c140ca14109450391401100d42d20100b259 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841410656 1250 841409406 841409411
    0x3121a01030f0e0d0203032509121514090d020118061e1e0e0a02031c1107030503030106020c0306042a2c01061d09040f05060103120f1103070312 64
    0x9042021043c802c281c0c2c4c0201950045480b0704000d120012840c080414190003023070341180c103c4d921604a2540003ca68500070100607804580c1014010300e0003a130303462003640d460103800c09040d481480a050180d0320f2001143c2003030144140590803140c80380c00c0020034001c0901050f0005225403c1060a0b4405180c0c1400e03000541c00a4000d4400035100c144402e0101d00340d520346080b10344500158403030000001c2c803041c1c03501d80109071148034144014103d400c003a001da4507250b0007044900705040740705c01203d020035030b2130400344c2e12038000303006080040c02100040c0465240000300c55016940000c2e8288602e07002c02d0540e0598bd4484031882411818030310000740d03030203014400c0e00b030300c1e888054200290026907001070020030b0142c02010a0019408860700c61508200080400d01002c1e40d281269403036906210b5104169104010030fa4401d0200100400c40c00075072008000465484081c00d04840c507906032402c660b203100020443d8800d018010209200d49000d110520186100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841411906 1250 841410656 841410671
    0x105070b07020c030c0402070f020904060e071202030c09070f1d0607050d0e0105031b09030a080f18060403031e030b0a0603020403031d030712031101090f03121a01030f 74
    0x559851000480d441c1000da00041c3c140d00c0700741000d001c00c034440c04044404600c1c00000d40d441b800c180303460240190250041d00001010030010307034003c040090320b0400300c1d04c0c075503910356145251002c2504200e000340518441c80d60141008842c00d030094100740c0300c440314034100800446443c064100d549011996440c4114141e448a1004110b19802a00070303040f0f401080750003401d04901e583c03130141001410004c0058140504e441c04a40c0c03200301509a0b034440304100081d00e0284240030241449200003001070001a03d0002080350178106841d00c5d074900300c0d2408108080c02948809000300e0f0390030041400c0031001c1040307035414030400e00340019010b0401d4040b441c0a00140c10500120390300280500c245500030000501080140707601000502180c4003103601c0305214070581100d005000412000c00d0f002c0d007130100303200000b023000300240e20003404c00b416008080c0c00181d0124603410744c401c40801580c000c0741055400031610000c4e500200303004400522149030041c20180e6034068 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841413156 1250 841411906 841411913
    0x61419050d0305090901140306090705220608070e040c0902040506030a050a0e07080d030608010e071208121303120209091f1a04050a050a080606040c0c060c0809010b032a010507 78
    0x640c040c050700c440711f084804240e0241450402d000e0041d200390f5020030810051a0b4903451483e40311403415035030481071508403054034007070047ca03085035060b03018001021401c141c084906512650280121562060fa10b0350030104921560043c0d5030131210400002d80720617030320f812084d00302007610350000720702c4180d0351614203007203003904050303003035002140c0d4682e006501d8016030f409048208020004280380160391982c880451182509030100300b51281d00f030007201019100a40e010406640c51842c140c4101c02c211701140d0003c03400b144c04694904040303030307140c400e907a500c52001d0850041500ca0220308101004680d40f5551207a81c40ca0b40402c891528051480f45c9c200c868120503200c2d410981017101000c0590001802100444000c00581c5000510940c01c040241e5002480800c2018120780780d001582c00030342218184410f900d40700d83d128403950300ca482401c008000e400441820540c60717081001c5180800d16088180c072548041441801c0c6042c18141003051030b00c1c80315074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841414406 1250 841413156 841413169
    0x7150207050f0106080106050d0611090d0c0e010608070516020f1c060b030d02070603110d110309060105060c070612021908160201060b0f03071809061419050d030509 73
    0x4034100e075036420042034040910001d000341405058660000c0c841c9600341004909949600718014000540340c0c0111b000c1c040b1400d00326074440700b018103103114001d030506086082c14007074840c0702d002c800c1690000407080d21030f04015010b111070380c1d038061030807000409010349014120310a03603200844030076411055a80c80756031102500c00700d0311105810801d00740395085880da44803182c0a908041c11440445601050341000d444040c200010501243e108002d02c2e130040c20707038020030a4584110302854042c00006184140c64035412580c07960b80f2582440158040c0003c508070781e0f0f00c00707402440300c5030148900e138001700b011050042c00c0606000c24a880c0841e0340400700c0c0803600280034410b0a6120b41c55404c214500e0b40002d00c003c034540728100710399104455044403129004004160b105229841105006524906820b20151102100001000d5038811900c4000c0051018910790401a84044068070844603000c610740c5064107000c01c8940c455070841c00c100c01081600101d40e43c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841415656 1250 841414406 841414417
    0x109080718110901020d120e03070b0f090705030705040905250e011d010320120c041a090c1b160302040b1e1504090608030a0906090e0c071502 63
    0x5034a035100d64015003440044401407841c04420b2a410040d0303408a90b00068800043c071180d01d008403010711880c00a800810700805001c06502000607514140301a84112900075059500260300319190858034a69444941c481c2c142c050b08848000c100a252907404038041c98041c40a58642c043c8130014940b0102441600e04101d0007140c00070700c1060034003010076004d4100507940070007030040c3c110880001d000510004141038155880d03010500d400707200318401c00001034150010800c0608503692510b0020314401d005a2800181407a045a41400c914400c00003425005847e110000c402a8640c424685a40d54410517104501c48010800c52801e100821840c40c0076161304501c104002d8541c880900b512510328030a49118805058150143e1072034210341120185c052186103401c40d004d65071003200120b10300100010200004001030030201c0c0e0590341c0032a45c036242e1074151020342090107411801456a4005040504040000c1442d1030081da01010000c7c00b08024000f40d074440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841416906 1250 841415656 841415669
    0x1f050408190c0e041505040c030609030e1f200109080a03050a0c030203091c030b0a03050a051603080d0203040f120c0303060512030a1421040309080115030f0201090807 74
    0x1400c1c6810501078410403003805460034080c090703003a0619454100660161540b0b00303100c035560341c0100d4208141544880300031984404103101d04011800d02030300c500c04c4d411005010300f407c040c09482c181121a40003268100c10749980c10381c0814088060082051710b072410302d09659485800e40810f014502410030a0f00b0f907a40070031545880008101076550300b10594003814010300c10320003005004a0480352024403000e02400e0072800000071800344c1041c1602580103a15244040203028004c0349200c040e41c0680121880e0340c0584009404103056480003420380502440760a0107009660011b58100c0d0080d444074090f01e03c140c5688003191481040300000c503009603e8003081540500a00f0010a0202c600b2140143c0301d074102d40e241d2160040707078010009040c4410014031080b20545011100ca44108201c4685121380d8655940c42a941500403504d2000001103800701401000d0085c3d0341c50500ca00b00c076245994001c0d420705c2011041b41480345540f40407810a40800c04900203010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841418156 1250 841416906 841416943
    0xb040305010605010906090905061302031905150a050d050309150408011b050313260403031106060d0308060301090614150105190e060d11090a060c021f050408 70
    0x510319026085038401c0d4007541c1840014281040001d41120608048030074510020a241d56200000b94107045100790070300281740701006000354214010840000281d400900b00b0060300c03640c40740300300b28840080d244e03441611f505041c009810640e00c85d01529206408a03400d00350800b002403956002c914a440c1c002201050402124009010705062452052003002d0001503025009109200c014600d100c000c1d00e140c1282e08000c42030010b00e0f01c07110400d40d44034071041082035401c02c40e449880103500083d10078066034600b02c804509280154401172070a4403050890f40d0a8a6815000b40001c5d499543c13000340c600400c01c03034000d89101044100301c5552618180a114010b0502000c03007504200041c02240020f8140019000180c025410101c43c51841d85001860070321039545404945420100d4000080540740c0107005080001c03600c0e40c04d0f20303840d2074007100ca220707010a010390b2000c550341c0590742001103030050071022103440c82c00505d4a03480e80441071502103132490340c442992 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841419406 1250 841418156 841418159
    0x1e153e0d0207120f0f0f140426010506011719090615030314310302061603080109020f16051c0c0512030702030f0a05042d050103020406120b1206010b04 67
    0xd42c40032003e480c2d10780e1810003510003c080301c3c0c01400000404030100c07d100709500c00150001c2c0d41401d44008100c042002e82d544560081510300342c55030220685035540c01d00012501c1580a42003d40305041a0100c2c136005540e040c07004064441c5081511040c1075a940ca5a000f003801402029040c0c00359050001d45c6074130f03500d4010300702001c4225042c02d8080c14040d54030040990134482083c504040b84d400300c03106203201101c1c02007620f940002e600007400243d00a40c0044c041114040034041c0e10b95445c00d0b80d0343c480c12020f80c8900c5048100608040041c0380c0d200c0601d008064030785001310115070315007210400039034071a0011111407021542c10b0fa00c0008003d030820084090151a40c41c0b542503082480001c2d540c2d0180815090080802003400d0b0400d6100748151002042404803413030101c01c00a840b0030507100c0c0841310b818400e0083c40080340d40d5000c0c0c000c075011950b09640d500d001c6c86519412500400c00c01c481c4640c00390240942c1c2500140402070640a02001c002895485 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841420656 1250 841419406 841419443
    0xd38010f080601120e030d0e1020070f0309080607030b150909070c0311100b120a35030103050105190504110105071e153e0d0207 57
    0x5244055480401c5100000c0100c1643c1c49010084000620403000c185c09408070320550950080c0b10b450048181741c012601440040000c14103004025444108010200a407086c60380c41154000707004011000c01140c40042c1003140c49800090007460149504da4075100e400781060010341e0030700700003500c5004032030719803515040c0034144501a21900e07140c156000046401c60b18014000c10921405c1c15010013818092100126044130720000c0d102d24017001c282c0b41d030060041c000352a000d00110074800106d0200081c00040842e081119a240c1f00d1000c000e01164000020000c6021080c43c898417464002207030185020710b00c00c00010070130703141c00d000c1c0c0841800d4066803180c407242450180408113040e00c01a2101190a10b0140d0345d507212070078901807103501507120070059450b0900400c01d00c042e4071050b0810b0000380c80c003800034038000d41208001392840e0074030101000c900d441041099000e8240f030001c60940c00050f5003480191100a030880c2c0205200380c032800c2c0c0d40c0301c400202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841421906 1250 841420656 841420667
    0xc0d08091302070c091e050a050f0c03040b06090a240303030e060f010506091c0f0302060109110f0a020c09040f050c0a060806010c05070b0403050f0f0109080d3801 72
    0xa5035103028114140089501c0c0d1640711301c49441514401543c60007054500c10b624101010740b42400701040c040d03800c0c404105030040900f103550440085058021aa550404c001280c0c0039030340054125400340c0b1a10104802c4042c00381c502017000f540c1e00c8500c0e070842e503c1424009048801a4480802883d50402905032084840c2806c0a0741004040049001055031140e0542d0320503540c080e2141c8070035001c600c0300320182d0b501d40f4441c0b0702c0a20071070400c5054580d00c00d42c148079a082c1c91490340c0c3c441c840c0c030079610200042c410540041c0100051814684040c14160515104039100f40b035560000c00c0d202d000c16142991513444c80560356050200410914006240a54056088918004004190b0440a0302e0103041011a031030316414480c0810500c3c000c0c1803094600c5507601c0c2e0304c2c41c18a50300d1300d01d0f40c9200c0d414010703482e101c40c40d078906109800c1408d1b04405044d00e012001c44504004000350701c0301c5240d41d001c0c04c070306c1564140500505860f44042440107441c85030310038005003c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841423156 1250 841421906 841421929
    0x216060509010c1511040b0304020112060807050634051603080301091d030c100614030a0209070201181a10051c11130b1005030405031206030c0d0809 66
    0x1801010450415141d81c030020f031000c1d0503007180c0352010381119004220050202ca0740300d001e2040340410040351031030700c00004501440c400d8035403202e083c11110411040e50b525100b0000190480396041080d420104001c0180007188498040079500c0c80c0083e07500000c01e200400e40c0c80142984501c1002810054000740503080c1c0400a00513207140d0f02c41340c10b40700500a010009840d80c94480104540f5444030712400000c1094980380d04a60121030313994182d1481c003c01c4181080d0000910440e0300242141420001c0c02425002c6400d4083c414450340107031110085660752080703515110382e00001c03801000e00c28203050250320046081107504d40d030068200003d80f0b2050000b0041a0344140c0301e0141d40003070300070082185100d420900000726604a00e1500600e44e03004a0080030000e0f409115101400c07210b8550300300423802c048420740000c40700100564020000303a032040c2c220800143e40480014200c8580c1c149400c0496107079039000c08201c030070070b4000c2500405407506868012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841424406 1250 841423156 841423169
    0x1303060c0807030614060a05120a051e01121113051023030a110102030702060414090112030503061c0f0302060f0604020a020703020405150d050703020f0906100305070203190216 78
    0x1260300b807518038039172410018242486118000348090550340103070280c50385d130101c0d5208030740b403841e08210500c0500b81c100c4545081d08080008010201541d000703a50503911070560310350f407294140d507440d00d62107035890185038009281001c43e800d0100303d0043d94407841c80000107542d076500d44004012a51003c103204c80007480621102000d0f40c071300054040b40f181d00900d2150311001c1d4480103038118070030490081c0d00a8000100401d034080c990000280000056400c82466aa13601d10740c819004030000080028070104082000f610706420640b084000101c101c85060301559070700d00311503002e030000f00d001d41c01440822201038109110940c1c00503050700c041d407920103820002500c03009540402841150b84801152218600d00d2515104400241411200c3c2c905400c0c029a41c102500c000c9200d100040501d9600b0308040b03100e14003a00c00940903514040c80f049090b000341c40010b01c071004500c014003400400400141600103208066000b400c940c00380c02c00104410400781d0040c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841425656 1250 841424406 841424411
    0x1605101413030f03060f0608042d1b12060506090135100603031d0319080d0e030d1d0f0d081005030d09140904050309040905031303060c080703 63
    0x80340e580d0300500c007080a80e0b8107203041e8840c1050000c06800908054100c600d4030b0010040202e02142c100309481e005600a002c01d202184003002241c14940700d8994507038980718400307030000002d82e501c004081004102d5814848094a07003012009070500540143c44c440e0300d4600f440039508048500b00e016054006102380c041d881c2007080c000c0060301d000440110840c031182e10080e00c1c418001848071140c00d1005111199032400e004082c41c8130660341908a0400c1408041c59207800212810070708035890442001a01a4450f62030603000074031903400c000d441c0c8241403030008040c4010f000040082c08001801184480c5400f0002c3c035071400520f09901c40208201da1a000140380c40606a2034a440304142c2d40d2424144100744c0c032a4002c54140c410004150301c019004828201500d44080d060500c40d8150700410070000025140a40b0035041041038200706d0030550005c8040c02e020340112403604c441d4160140c134044456000fa28520750341c5200c1071a0301d9102d81000cae00310311249800d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841426906 1250 841425656 841425661
    0x18110301060e1f0302090c0307140324030a062c0c031b011e09060e01020a030914061c0c0806150d090f060507390807020616051014 58
    0x30300030b003444060200240c0500401210b281d61240002100286034090300288190500c8903541882d500151500b9001c031704101d803001d8a0011000569100d6840020810782039a102c0c4902203006200e404920b8140c082c961400c0007003980c50003500100ca2480c892900310800d2100864014003071500c000c00c564001d02e40c8040150b0700090f48042d00703200e0364120b080c2451504016942d064042e00040086040c080e0b05140c06904100d61008a0f56a9128480c03441094401281c542c0030982d001000b01d1860b030800c0c494000e00440a0f108a00d02410040ca004103074039140d01014110b00d1022400303511541805a095400b510403034000d001502c04030300f1009030300441035150042a141100c4159a04622814814070812000324590401c004004a0409000042c0741d1058281c10403983d84400d450340c4446910107845124075449a007105e00703880820355034040c1650000070140d070f20a40600482800076407403e20050300078843c000501c11603444119103000d03124002c0382200120300c031504 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841428156 1250 841426906 841426919
    0x52a0703140f0c12010b0a060203030708130f060509011806060302190605070b0703020d02070501050f0c040602100506060c012313082a011d0c09010819080705011811030106 76
    0x50f03c1c4105441180c03043c940b5010480c540307004110001030b040d802111248001584c80e0007000071406191582c4e41ca807030030354a55900112450756541e00400002c417440c1c15401044180d4072498000380480004280c000e140760308040d8150038804242c0c0d0580c0d80d40010802c600d48009031420001410100d60f019a251900140a40c020600042c040c102040d00050040e846641250341c0340141c220219201d414900f002c9008010440f0160303080d5511030082100d802518040c0d400b1a00350780c0c010b190b5004c034008000003410b00a030100d81c0250052050b42e00121080c05a540c4800b91480800120b104510725001c80802c0a031800001090003014031000c03851a0307044402440555410620071031040c4011030761402d030944049003039443c0030606003201e005105821081820318080300c2d400040d040400003c40320030f108031900360f070100a04030340052824401140a500545849007081d00d541c85050940e8445061102130b043c030102a034040120740302510030184801d030020810b10b0705051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841429406 1250 841428156 841428163
    0x20d1205090d0f0e21010513080f0d0605090406150608060f0409020f0406031b050609090a2c010f0f091a060f04020c0c010305160f052a0703140f 64
    0x10803003003000f140c240c0d055043c50041000342419100582a0101e138005041d03400070b0945035082080565003050040303003109805008440d0069080300742e9505d0400031035604899580a00700304490036031540c100140c1030f0f0b90901c082d40710fa80187ca001c40c40c10402d41c2c62a44410720740e04640b0074481c5031414800c841d107a08029101d4260309440025280100c0d000007864103200f00d91017944a070034040003000b0850b0201099001c00c0e20500101c180c15240c40801078140108801160071a540c0400141c0d41180c40d046244030020b021006100e074a2034020741410704101e411200c4c0682e4483c1c000d418401c00610854144c0c94070501c3c10060351318103a0f2028400074207200c0400c806072940010440981d1404e658502e806030041c000c6545404c444030468442440c05250360203e0310348400611241600e4010079244100c3d56111440b403031203180180c0d80b0380c1103500072641882c0054910202d148a14071035032404002c0d50010b011685c610710b4104403045843d1480055a00522602295001c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841430656 1250 841429406 841429423
    0x1504141c14070c09051005040b060f0d0c14070803071d0306041407090f060306050f013012111e03040504090203010b06030c040f090203060d061e0606020d120509 71
    0x30300c102552008030f8200980d0310480d80d08411104d030300d80810b0040c100c0b0044529012204103036010310294052000b04501d6000c0c401000600d44800c00c14081c40b00001d50010103d03c54038204414a0100c08510038074541001004640b034950010900081580003906058070190b5403054110074048040407c0d11588040d20003800404510122020b401703051020102030148400e007002000700e101c006002500a602c02540c01c280743c540410134610b41181c085050713440c1c016428030603840d40484110442c07034124404c0c02c03042d500e0ba01100000d01055010701c100c01d09683e42d001243c11a002581440c0c03e0a5120901101807402e801030341c2c402000b40e07001ca0f00c0880c1c00041c291303098000300340035101050300180d000c0800020132100d50000c801807c1641d5144200c081e503a902c0d4003001e404c80c1303c00e071041c81d44191954401c400082090f0052030740160402c03005c00a140c0c45103d4002555610381022003d40c000008421010307900c85031b503403080800c25138180480e041410010f03840d110712 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841431906 1250 841430656 841430687
    0xf010e0c190e10090618060e24070b040203061503210d0203040302011b0c080301030f03120510140d170702030f060c0d110a09060e031504141c 63
    0x410808425032809650b50540380305019091845880890000604000301170180720003103420240d9060080750703010f4a10f016210749880d14401d2003810340070130103907031010f05c0c0194858126007181c1c048441c280001d060344501c00c0f0020206400d20344101414120018410216500302810404482d42d0010343c200c0021040c0d0641c400f00448003d10440920404040c103a41d1030002050104040d170561140a1032406803044600c203100c201c00c100e503a0080108003a000c46e20900040c808504041501c6601c244030342401886154208100c1d4140e41d4101c5801540815000003002056603100101020000403550410200095a01c1081c00d041104a158600030082030500031502c1c100200c1108401903011141c451505d003a203c41154485410b039034a0070b0030505004040d0f0869425982801c45580314000428203044040f103000300220800d59240c0b04484c56000c0717200c110034415000e1405880110004540320072081c5c82c140d06e0b40f00c0c03044d0740ea1114103ca10095401108010050750 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841433156 1250 841431906 841431937
    0x2802070314070b1501091a0c01110412060b0f1806010206060103090803010918051c0e220903030b1302040906080708120a0e102304051c050a17030f010e0c 68
    0x4c1d03603004030341500007900009500c046003241c18030007000540c05850950b0043c00240810840850b540c80c450085200307480007414943e840307000180300341d0030446803120060130013800c802c860400030b8018648844400c0a0042803400c0c4612568140042c552004083c2000d122440d082d5031001c40522051044584403603a468130b043d000450b1041c407425107508141140c039001280c40c0500101c3c020720081101280c00c1861035030990800017407940c2c0c2c000c941c03086070020794801501400500799070b80d0114100340d03403500300c01d000c0c0da540c50180350050410400161250308210030744045032000e03041441141d005400801c00d480340050788628640700c0e44a416154000f00201f81c4110240f0714002d60702407079030755005807556484404a004204c002c1c7c40c1210a42c510008c0c4405480780b4050b59401262840c9800e80c0b2140c1c142e0806105440392040f203002d8103d646424618110601402030096400001e0141d400480082d41e800f4007450000040c150810038102d04a602c101c440100341c2e220f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841434406 1250 841433156 841433191
    0x50106030b210a020406150306080a0b040b040c050405010b0405120703022d180f10082d0312010f060e030307030e12010606110f0606030a06052802070314070b 70
    0x902c203000c0c4050399507014000f4000281c44091035031510f030711101c12030f000070325006000a62103800508140c00f00e4000c0c4031442aa141d0791201e515241008100f550900b01e0210002134580320780c400e060017455503803181501d4a0401040001c002c49260010f2099408031400384003581e1071007002e15048404d1841d5065041c103011280780001003100032564000d40344000c00656224486403140301349144c0e01c0701315040e9164844102c51014901410050f58442075109107071a0f50500d2901940482154010316442840c0f4454a10350181400c2081c50384840e004001124a01c90f000c4090b02103070400d104c450107c0310200f5500d009250000d8100540703144030150075102c4c0c200784403201f403601d002400f60310388170300000d401c3d01150078041642e80701c0c0c1300e9050f084800110389640181401030181c040d440d001c0c0c640b0005000050206e80d0301301c600705c4401c40d84d80c85604078200348010f607240142e04d036242030401800e04903994440f50f44404040044000040c0c0640c0c102d980100e464801c206a603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841435656 1250 841434406 841434469
    0x611150f060a0305030408031305010c0c050108090313080f2a010c1502070f14070f030809030312010e060109090501120f0c050d06021c02040503030d02031e0712050106030b 76
    0x118a03e030710140c16070100050100d91004017000902c0605016419480c00d90360fa10300448820725404800741041e8100301e0148030a40c401d006140d08032403410116030400d24490b07844800e00301c680c0c2c014040d59210040d010110b0b81c00788000071007140d4000e0408901d1000302880281880c400298504014040c8041000c004000703183c4607070040b8841c411511100d240c603000084001d240b2050760354102c00c01ca408800c0383e0001c1d01d0401e803500f400d40e40741c40601c0c0d566000c185400c190a0a139043c002440005101d0b42030f00d860500a252200054480341000c40c005814403149403c1841902d050030014403100051007414404250300544d5054070350a2030421301b40d80d40e0701d5081107911880d180b040405010580c0c001e010000310400002503003000e10440d844c224400e600c150342d0076410078000d4050640c01035001c0c41d40010880740c0200034031802501440d90140407100280420b03960b01c80c0c040083e1692140d540505041c2c1403c005101004001404e16013804280c401e030102c601da001d0492 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841436906 1250 841435656 841435669
    0x31515030a082a010614040510080607170702010501062f030310090e01020a0c020d050307020a03060507030507080c0f0f090405011412060f0a0f02090907030203010611150f06 77
    0x14a0703000507046444003101c10801d200501c00c9818000f00e48180c0080440b1000c0621a49040300d400310989117a034604441808042c000041603807211a035403603800944000700b4000c007480f80c1e01c80c2e555102820100c0440350500c240260070f96045a15110050100c0e40d040ba9081102c102102c06001103d48551800702917100e00039951a558000402441a002045d40005013900c0783c4000a0028504074034640d0300700c0c01a80003600006681c17111340300140c02c00250420035180114117591501110b5004280841d00650085502c40d6a410420bc401c40d858440c0c16017012040c0b0b0841c0040c1002e0604045901903042e607440591070018000e03c1840ca0801100c3d03283c880640180300b0343da500c80c40c0104070b22005800314052411f08001c52440340380814000d10566024036080d075035844215070b400042400720300031a000d550070015a0003035524084454850320150b5000f594a42c10320f00d00030200810080e101c14141e114260802002c602c159050340c2c07251100213018501d50711400003815 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841438156 1250 841436906 841436923
    0xf1b0c0a05070f05010f02030f04060c05070b0a020303151e060d0b0a030b06010f020d0819060306240b070809060d0914030301030605250c06020d110705010b03151503 73
    0x1640305014000800c81000f01c0c0700c40031200c1c2626a810000d16944017a6124480c1400036034440c1c0c4104130074410135003c0d8219800d114080c400f11144607444282d10200d80d84002d4441025a0021003000301d46140411080d0a005065503c2200144c0880204c07210b4141201550701c03c0c86c010862100100e903507800f1109210000b89904051035aa0620021000040d59141d00080300e8441d00034500d8000120700c0300d00d85079903a400f001d96a5400c6011485800c102c069260151a0040040070070317428000e1a80780014201c2054030b1164984512007481c101d81d10101003060240085408903060200f62901d0070b0055402da0f50b540c1c10701401900401c0c19000080404060800481c440c640010155060300e01c40d080c1040725460310540d0b0020f8403468040248900000c0034401200e610030019024251710422025040140e640d144d54103a420b0780c000603d00d68008100642030180034010005d203080160098014204201d800500c0c02d4001024105070141200c0b03000f120761810042e005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841439406 1250 841438156 841438163
    0x2090f0609330a0801051216060507050307060606020633040b060403020301050711160510050738221e051e0615060409111902150f1b0c0a 61
    0x3980c50fa0380f110302070032a100c280030303581c020040342c00401810440010060b048a50302e0740200076461410504403850340c090402190940010300502002a6280c002d000c040c00040c0c001d411a8541221801d46006400090200813003161040d1100005020981130319000305403070100b2413102e0000411498802da40c80250150f281508001a466211480f408002c10040964008030520b035400c0076100c1e6140540743d44103900418071480c4030b004000610040d44107183c031021302c2d0714040c01710b44c0a107070250301000112900c0301c600c4c06503500180c203103521600030010500c02c40c0c020881a143c6892080300100b030314041c07500050b44417250f640c003501c01d01d90140840351f4090701c0400c4260408900420b040c0c0e50310440002c203e00544000c204850000b0203050142000d10702030300c0e0f40c09031040940e6012103442c20810900600c040340e5000150880c0d0b0b030014010340c40e0402c8442403809000700291444c0403944140400c00c030051080b41503114110201c151170308000405d988c1030611090005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841440656 1250 841439406 841439509
    0x1a090d0914030a0b1f1a030a0e0a0b0c0417030309070515070c0303170133030e100c080f041a060a09090f06060501020a03090302120304051302090f0609 67
    0x226544104080f480c90300e608100d83c4402c19a2650170404450401c5206c01302e034001400010000051584118800400b0b04100c2e0881c03d6151120040b03040c0039034424449590000301845103200e084204e10751400594000c0d8034501c2d01a01c0b081d103c01960080921820048610255201510050f5401c1c0c5410541c1e0b01d110960b03a00e8054a903c0606401c105510498000007491030544c1100440001c00000341800361a001e50700f240c212904010b040080c950350703255481040000700400c040c81c1d034038500001143c0b0128800640303246030007409920485041d01c00c0000207000c4854607141c0708409082841140c5540c400a604150785422000c903041c036000c160f40501c82a014049a41400303100204080c5890780c5c0120307168800020040c02044c2c0d07442d400c20050400038400908440b4010569051649441c0080e203e80005064500001c0d0013048406643c41c0400c3d4507014800704480c03ca00c5d080100021583d15640c8000247c10814250f01d03c07131441d42c2180e501c01882c00300501c030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841441906 1250 841440656 841440661
    0x3080a0206100f060c03120e0307051f0b150703090b0f0909010b16150216050313050a05010801150306051c030e04061d070509030105041a090d0914030a0b 68
    0xa540e140116120300110501c0b000c00119400d100300064150f4046554490451480303032410395400d421407180c685019507170700d2103804c0c044040c009000f0745445030015154a074000c2c0700b100d402c01d00b80320b0009001860007114658a5442c00b07a100c0c0300000c5846060340352612404c05880c9070035030344e0084c10181000503080b40c070f5140c58402000100400c654401c0c0d42c0e41c81e079400e5101402412409118042c0700100d01011030b04000200d1030b0024040d0001d403402d40d0504042d5103c07444030300c0071191544045000f5098610002400000d41070940e44003a400345401c2c0000d00400043c400c842c408a400f50005007458030075040b02c0050031014100380000406040c0c150440c141a11050700010f6043c03841100b00e142030b02502c0700f01ca40c00c24607001c180c003000305200401d55001d450481408400c101510b0661070a01034248034138040c4404c0000c41015580340c9513408001051031110b45c000015001d01e00b47c2201c2c0600a1300e01c540c001c0002d8560791301c003103171601031011070143c6480b424904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841443156 1250 841441906 841441927
    0x1e0c0a03050d0c020c151608040e100e0606070f050c0d0b070324150c1704090e0c0a09111308030408010c0908100f02071e021906170403090308 63
    0x40034020aa104204041542500c1c02c81e207500c40b58922541c40010320602c086e041014001a050b2078003480085000442555104c8041e544161701c03a644800700202048401401411303120000c004030300c100b41c180d24006c40003510038031410000800102e80794405405000f010042d4484020001e0b107203a201d10079504100192007000c9401100103403e0a46800304814040442d00c200e0b201c0c280d40880d094180302103012814440300341340c0308208000c500940415413403030020020741002d5842e40d99030783c01e0620718020f4440340b500302c0e0030b40d0303201c0c641c8400682c40306801c60301140d030140f100281d1404500d0740691f01d8850000c00381c0941552007070100700e0880100051044804a070000c00507103619540681d61200180303d640d03215000990041c281103460327046914140344059006103408000d54400c0080c00075048201092a40741141d0021030030100c1d611540c41c5504a81007008a00d0500020900310700c494105c0c00e04e00c0c0000c0420b0406001d0140403002d180d0105403d0b4503960200c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841444406 1250 841443156 841443167
    0x8030a09060b0415030609081c021c05040b060d020a05031204090605011403070f020a1211070b16080c0307080403051c03020f0a0318050615040b0f061e0c0a03 70
    0x4400307466852a041030070300140350074400d4200540b8081c08440c1002e02d59140c140041c41c154006a5291404111200103111103105021040551010050303d0710300000c4441840303d0f2058241240340d160030180008214048203156104004986000603030301c07030344045825230005901c0240c06100309540e2100310b010325400780042c2c032503002c400c0140e1562040112111040c4404000150b5001c1001c2070850344202c0c1107407482813217801114504001540c8040000034000412000a00100400c01758001e06001d14002808041c460030308184c101410300c00140d03510301c00103026100c0040e031882482424410740d22000e410041e41030b207607540c03402c0454984142d0009404c40c20120300c3e02c0201d0600a01c20340d910b040405082c5810100280000e80c01866160003d50030020109207140002e2010025280b0410b00342c9c5100c004545444207110540d4004064030344611841010041d498640800780c400a07814442019246030304210242000d00c42c0e0f9040c10784c00e0181c5001d0605158101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841445656 1250 841444406 841444421
    0x30a1d010f09021c0201050306061303050a0303020301150801050f0f01020a06020403050105060a091512152f12040b040f120309171207050d0f180203010e0708060415020708030a 78
    0x94807900c80032002c0b04421001211131000082c046001030000c07503128203100d009001d408034558410b07040d050310394a440d4035140715443c048000a40020041c81842030700c00b2400481d0540d4149050b16504120000700d0752026940c12500a002e02070f01d0b02c425a00c20014044025000700d021591941c03281403540c040c0c84200c40d0341e03001e1459003100180c543e4052080343c40c03d07503203840f0941d5007a0900d40e41040e401010242500c1d5001e0946c0c81c00d02d0400781d0721607403812082000301c640c0b2111001400354100d80f01007100441d00030b030612040da081081c812080340c0c030a0703110040006981e283e01c1c10545541c100680501815601c03002d0042094141e0b01014010b4041c0103c40a20b19170550003444510803002d81ca860850326401068220340170380050820246006c1c4086400b0a900b02c001c0d040320309000320088011309604003081541028403a4215100110010f05003207400d0400c11543d400300944002d01001419000e80c59140d1964160707090107500044440d0390707040115080c4050040c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841446906 1250 841445656 841445659
    0xf051623122e150b09040507030e01290a033207030f050601090218041a03030705520e1303171009020702030c1207031b0605030a1d010f0902 62
    0x900f21810740c01e5074840c00d0401140c80a45002c1d1504820a0900020305006000d24003410303120340c5248000c81c000c0c01112a4800c0d4142c46040640c0024260702e581042ca40d50719004054440c1d05001040114046007a1a864440c400c6030300024500002e0001500d40140565405203403008001c102c224800c11000c81d0241c021101680d88681c113450403880761010903200603416a0a070a10f504054020b40c0c1c620721640e8514204041d020042410340c0d006520803151600007441c1c41050f900806a03955600488803200a1341c1340701d1160103224924000000c0c0d100c5a008a0765028034201031404c0c00c040c1801c0301a8808a0400c2e01a0f01c803440103112048002c1403880c0904804561004045441044c1c040a006405407501000400039401040c042c0e80600940c2d41601042e03c801400c50b0501075410002e15900d481c1d414940003010503103001c0455410302a10400c40e06a00c101a0794019000020001d050324044007483c2c0419829003681441e5402e060740060101d0040c0e1102000030300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841448156 1250 841446906 841446911
    0x308060406050d06050720010606090e09031b030d0219020c2b02010903080307200303061f050c010606030b01030c09051806030a0f051623122e 63
    0x8520040006461042c001c0d250404104081000410302a0f040540c000c0c000d8100f0704c0c60426903100850a480e079403202d0660682d1507040c100000e0354040c5282c001006948060020341c10b102c4a01a100e200380007070024209580b28095811220500483c0c41030241d03943e045681303044140c0d0301007401c4009002c1001602a4110620310b82c10a8001c0c4810002d078a80d880c1d046c64480a001001c0c0b8101200503410021000c1020001641e0a401980180c155443c2e14a042440043c0c071501103800703034030214240e00107005102ca55142c500045000060115441104414443c4215407500a200c1e400446608047c070009095030158028280c02400380c0e42440003d03408241903030ba69055200c0c02d40c00c8003410012600ca841c8040410703400400c0102030320102d0505464070040803242141c1650140c0210118208100c00c1c4a880b02c010500c100400031682c600003d001841181c65203c2030041c0941500c0028006090100c3d0170402004041841e4800e04071660280401040d00110100391 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841449406 1250 841448156 841448161
    0x80d0c121a010c030311070f0807050c0a140d1e1109060406060905060f1204060c18060813053c151302040b0402040603050415053d0f030308 62
    0x1c40249030008540010b0f142c3c45811041e42c0d804a00030050182c584030920010300c208400a07140c41d042d41141401106c1080d220a0a17061807800c280031406810304c501d40741031042005003600c00d080034010b80200d035289481e41070350500006c960007140440d105003910034400000c20000c1c0f25416a00700054030b40c0d0f032595071054244800c030344c2c29005a8000c601d51910801061801308001c0c600e1b05551580d007402c0c20007041054000c0d241c02d07541103d021b504d0f1a080204030341d001c10100607040c1c070501080405880c0050180980a014102d0f0135503803040049101800b0003080065001040440d40720035070724801420441071440c0d41d0005a0302e03410030204200d400340000785070000d000000c056034000d482d103911403440841441e034200d8001d601d880130700c2010f42d51403018000402d0640c8000c02c81d450249428420201490041d241d01c0c0c1c60722040c4200c40c0b807080c80001402e43c00c85a086810345010100c07211382000b441140403200000d2402054840328090b048045030311948540304a0f8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841450656 1250 841449406 841449431
    0x51e13170d171504180503070b09010f0902010c0b0403031b05210402092701020a030605040f05040b0112020303090406140109170a020d151515050f040b0304080d0c12 73
    0x442c05450600407201c507101c0c1d01005240540c450189015201703e108404042903a89905581114100b504c5813191041004840d00003801001c00441d2140c0e81000031241650000e07040080c114405401500800c0020701098020360001900e41c030700201c824402d04490000514540c09200450301c0c4d03000504400c04550700b109415070007254010300104041c0da6542680801005581ca00c1540354040c503941d881c101e03400c0c402080e40d8070309030340c02280880c100b1007800b040d21100011020120329040401c008942800801815208914528240c1c0701d90350000078a54000daa072010b034003500e810b6000a0009208281001000c000c0c2c0314140d0340c0d9590b000382041950420343e45030040d0066420b080041c5090400d1034840c522415400000c091a0840042180c0f01d0300e60340301004407102c0007400030b24036101800502c6991842d03c14039094802c030348181c6030702941c890b00710103110120104042001300819141d1810a06408014428542030000c0031104114001e604042c0361042d4000d09 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841451906 1250 841450656 841450697
    0x1b0d020d09080c012a030f0e030f150a060b0d020403020a0e040f060f1d070e0a060b0414010e03030a05030114010c050d110c1011010c051e13170d 64
    0x1103072582005003082800000056500035140c0f05400c14060b8125020310f03080320550400384000e1b01036510703d010000c2d00540984102200c840152207030b804103100070b080c607000098040303511107841000021900d4903892480a4000e54020408282c80440c0401080e540d03036014208881c001c8034101900c5175942c49a0044241c143c4010b8071500c1031045003400305103250032020b100c008246000489024000a54251415040101c0e00c29005604c0810644401000a58005c00c1d104010002286049410038a41c451381c41a0080110819034003100d981c01942c84600020001d81641e503603098541c00100a41d10900400318051501180030f110380d4444c01c00b14182907800703c010105a006c14900303648558800c10b80341c13114810307540070020350f840d0140d0341105000f10b80ca401c162021041c66440c2564002c50203a000c0060600a5160301c060f10401d800e01c1401002d000c540d9101e20310141c9880c035465401c40b00500d10590b84d00c1042c140d0000701041c40922039940c12201caa82c00343c80b0b214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841453156 1250 841451906 841451909
    0xf141506040b0f091519031406070f1d0a03080a0c05100b09060f240c01050f07050304120315240c0308061e1215070207080a080901051b0d020d09 64
    0x104544c90300b000501112000003601d000d041d00803c0042000e256030319445003900a60000c0b220a1804281d000d103c51042040d5500f00c042820542c08101c58060000c140d09400f00700c12801c0c81e40150704e0021074403042da84034051034001204560b41c01070007401800c060081c40003110340c1c2c410b550b1500e80c09849403154640d648002848000107448580401040c1d8154084184d40b1082c814004c403000200301004206400d0a0301d2a59110850380700c00c1c0b4211800202600c554604040401c082c1550000c100d9500c1070f4030452541852944803411401482d2813142004582003406000c12404d2860054200c2c10b1843c1c034008040c1802210f08440b8410410b400802252550740407880364036054200e190455000034000da0801c0301c1c1310000c0d40c6002510b40b8440c86400c0522480340304130801104651040c1280001c0079454940000e00d50b59a00ea51005400e03002e01049030121a8400c004481c4024100f6244d000c00000c8540f800d40c683c604da42c013000144c800d09003414511801a40140d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841454406 1250 841453156 841453159
    0x606062503112509270c2d03060c2a02040501060302090a03111302160203070510390c091803051905040b0d0f06210f141506040b0f 58
    0x2004a20780b001d400c000e000c4011491104a200590b8000000e00030440000d17400d00075141201c2c01e81c03034030060b9203410303e190724403851303201c1009000400c0c40e2108030700b0307000c030307540202c0004410418010440704d06072072060102d4040c07500c40c1040e107811014039400040758001c490400c0301d079070703501d40650032803141070940760b000040c40a04002044101a80444081001e81500b002c10f603102102801c9a000d00c40043c0c20b41812400d06d819414204400e0700038140c140c61104105052000282100038030b503c01c0104140045810200002c6644019600c0201d4220312500501c0341d1804690a9406010310a04640343c400c03101c1100070030064007800b080d0103841d0b007031400c0741c041100340c402c2c4803118001e424054100300005560b414031008000d075410000c000100346a0300e181c090180c0e03406500803801d541108881d5850404400b10000c242644031074406407040b11454086441038401c0000072a9016442d0808010b60102c0f1a55200d6001160100252141070040162030303082c004400b0f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841455656 1250 841454406 841454473
    0x1020d0b0406271b020304090b0105030613020f0d0218090703060b09130e03070f03080c0301050604050402070c08010c0903140313031e05160315050108060606250311 73
    0x800f00c80b115203662040e60480390004541101e00010313031420034840300c00010040c1d000103420400da01e154410110f403100c007444c256145060610003c1e0012860900046c01c0540c0002c00001121800e0111421010031540a5468901a00c1c0c1122040c0d060400203020f080780b28001480c0700d120740301d54410756505410007820320311a00c0c2031041005c421208805004c3d500c50f499001034408102900081e1300c0356500d003840c09601c0ca802484000041e004803e0180c2c2440180041e41e40c1c901a076064440c2990b006880f0380e2141401031550305213502035079040d440d041e4082150ba0b401070903a01980d0082c07200c0c64100404110481d540d01c2420b00310300311000c4501f0300f0300018064001c0d038040d5412184500190301b409441d900d080c00054000301d902c1b0604014204100318001e084640414407a1504002c10761416030030340c1e25070b03c000f00280d116481c0040e84c020700f003100111030000007a2103005007000006a1401800101d007460080300684112045007800c1c900000c2e110044d0765101c07030342 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841456906 1250 841455656 841455689
    0x106141309120c0f060624030c0504030602090f0d0606140d02030307060c170702011a030d1e17101d041a0c04031b2c15010903120201020d0b0406 64
    0x4035100032030fa040c102c420340260021200840d0140c000c28010b00484144042c502d00090f1041200300b09031141c00c4180350a12188001c000c0c2c00c803043c0c4040313940162015a458a25a0005925a400c1248503500c0380340301600341c09010440d072100c029644c6040342d426641d03410008200c19084503032402585640200500e000041c019000498525090300345a9030580081480042c481002c5a440c0d005070354480014800c2e084007008006c210b0001c2c1c01400c003c414081d4010304031680e403002c41c6940034440e000c03103240911030009080342c00a1899480040e0614a034449090b85c3c2a12070410b9200d80c10302c001c80c941c4004c41c4142d0146501514005907240c10482c0c0110701d41c0014081c981c81041032000001180e00d2410461042001d5500703d102c00f4280300400f08021203034854035403c80c070130301a040700d41e1010001141e0002c0c500e400b12517a5448103c0100e4052049800007422585d01446000906030150041d14564010360010311481e82c0d40c10500c01210713854840c15140d11003d004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841458156 1250 841456906 841456943
    0xf07090b0402040807120b0f0c0304330e0705031504060f0b040c03020d061a040b1c022101061e05030618150109080115060809010b030106141309 64
    0x500034000c00500007500b000d9403105401d06000c865484400d50004042c07115040210000f9070341d6005680c20002007550038004020240c5000040000b03010a640341064120f0034510f284803141105001414211b1000c81c003418030107002e43c03c4241d01580301c1d001e0049407a240c04216034004000740b4000c1091951180c0705c082c060442e042031256915621030011403a17844500841050304070a44025030395001581d000411141c1c1c4e0351040903248030744020b0302c1d030b0450004119001c0302c0c816603a08e80ca0f034003580f180300404940c450603804101e01c0052521100c1c110314000010842c080e20101180baa61060b00765003a8000101c45114034400c500e4469107180194041c5400080190800c907000d0b04c44840c064a1590660740c950260180a904500c15a840000340d0043c0404d000280000b40b8844420440381455000303030700c1448030001c0002e459a4003544000c1d840d25009001b8090203540f0381d18400e036041000c00c030500400c480f0110452041950040103501c0d540100143d510114450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841459406 1250 841458156 841458161
    0x9090c010c1e05061513050103020f100e0901080a05160501170903070f0506090706021203040308130b190501061e0f05130b030916061e050d020d0606030e0f0709 71
    0x1102503203800380500c041c00410f10030071440e4813030401c0003580e0805091240c10000803082083c1d81001083c149801400182c4404d40510015401510084154001e00d00140c0b8054100d0420a80120f06600000f840080001e003804034a030140c01030310840304006800c180130341018000c0381d01186a65000d00312440c500f2454581c413680d4401a2030501e2503e03038510715020b1420780c0070f507196803051040c1300305000b00b8071561009241500003007420440000707041c81c050000030805000e02012a00041c84131b801c40c0d18114019a01119515041c43c100c620705840b000c0c10b00746410060300d0040049222405000101d00b51500c0702da034030105608640341141c031602d028110108004062060b50010303407940303412401178002d80c001c040d100e00d03005c1403040c541403807110740c10074000007084200615074100e900324060b85002c404103071078440d0051080e00c0502c50021050203c41c030010303081340c0d40800c0f40c0c0108241c80b480d903001c0c031519032001a080d9a40c4038061440d10203800081c010002c200a80d0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 841460656 1250 841459406 841459433
    0x510081c12060506071101080c07112b06140610050717092d0d021003050c070b0f04030806031f0911040c0909180b0402010e040b040c02070509090c010c 67
    0x190004942c40d626840803812542041200322401c03203000000182d950b8002c4946c40d807141d20207405a00f841110740700c100441c051444080e0243d0040a110811090400d003c000031607102c08030320401c2c000ca0700e4440020081071283c02c510710003006c0803aa04c4d1510149100030045e0f169100360400c95141c80c0c1301c3d0210480440d82d040074404110300c50040c0c0b00c48840054003a5807540c41e40c01d400f4184030401c2004e07101102c40317104400c00708800c00165035202a9555403605450006001da4401c8504034540c46180400b501c80032410b01040003030155800c10034400d900c255124500360b1608800d142d0b882040141180107480f81c40c5080b80c14001c10742c411002e0381e000b40c1030000300000c076002280465441c040800009140840e040c00000042e0281d901d101c070030603810540c000800e0b1254032602c01c01400090401c449080e070a5903680e602c0e08005424600180300b000340c40c40c18a4040e5a420140c8034240c00f410883c80040c040da900403400d00090039041c0c45855115107160344221540001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 841461906 1250 841460656 841460687
    0xd0e131d0715171302091006080c03130f03090905133003091b09050f07020a0308220c0f06030b060405150715240530010207050604060510081c 63
    0x7488031440542e1b150034050b0302a5040240603072405041134001840074038000c20b61140482c08000303120490002c03440d0000107582000402d54216040d00d001c43c0c200900d5804508042d081c541030000388803c2e00c0340c20350742030b220340c400e8a21640441d9886101d501021481c42000b01401c4c0030041c014040d81002d184180305030444c1c582045104400310318107945810168065541e60104420f46c6050003c094000c02e1500040c020300d825590000d000100050180318448004110808950a00000100c010742c0c842284920617446e444900081d00d030b0b500c110400682048200010f9040c1903049405541c3d01a00d804026a140b03202421181d0010b04121100c10580b101c41d5100d0105100d810000d82d03800400030545043c25070180e00655158000e2407095805401c80195000f90700c0c0c62007002000f145102d98500340b081c1c08140280201600034090340548402c000c100403240d1b20240c89648801d01e41020240c0b43c101407603841d07060481c01c0600801c2200100780c102c2c000d0448081d244035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 841463156 1250 841461906 841461931
    0x80c031302040906061508090d0518040e0a022404120215070c03051608030a0c0c0906080303221a04020f1f030e01020c0d0e131d071517 60
    0xc40d0390104040394061402640c65554520080c81250241d201c01001c030300d000c1c82e040407541004e0300c0c0d0684800c807081012043c4040043e000c40b400181c4990280d50107402001040340155140c0c2158a40d8201d0740101e1060004000c00c00204c01c41203003507440d01e1341906455040034200043d11600c1042c1440585c2d00060003200e41d012403c0b0240100311462040350303500c41c01881d61924900d01a04c46800c1c102580022074140400d01c2d0020a80395907100701d291440050f0418103104e00b0f01c003070b40d80007201703042d003001008a10504000011401501c142c01440c036101150000500300090002c0000d1918580c8007028900ba100c540b03440e0781050000342440240400349001a02480e940c4504609094000740170681c1c03c0d42501c5140e5030561048000e61401114000e000d4454680c403e201e414801c02030300c06080b0303449900d94600e4030501c4504c00c0001c040080151501401d86aa80004520070868081504c55007405204002d4100780c581344032000034803030843e04250004184291480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 841464406 1250 841463156 841463191
    0xe01030e1501080a0c0905040b040204051f060207080610030c061404150c03020c031528020a020309030d02031e0f070b070305190510062714041b080c03 67
    0x41120070900e00800303400005101e940300b689000d50b00130750316902040c903c615103010000030405e0b00b021568015411074000516035a40c468141d01c410103056200c5200e808403601040c80340d000900103054a140710110340c4a81c2d100314880c1c0c0b51001c0780c0001040903400780010040c0c18055440e40385543c0540d55854140b94071035a021000414180004c000540c0d414505030500d5014400e64440c03102c243c000d1300c2c509503058503180032464043e0440c070340300101c202c410f41142001c5045480c01c80d00c1032801c0d5514200240300039500d400007010284a4040d611103140300500010845912800511056070540c60000d030f409999040885e5510b604e400801c82000015071826289100d4916038800142c0349c14a90b00d018200012a14600160740c6003801b07000c44501400310343d5046891514000e07a020300b40c42d001c9203813920240000f00403004254000302e0780041d020361910351100d054600b041000c000f202d0060841c5914205000403d5400d408260945c0f0f2030700c005c40d44290080298001403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 841465656 1250 841464406 841464433
    0x90d0311100c0507060b0d050a0b0a2702090c210601050c010e1b0f220e0f0609010c080601080714040b0a0801030209010b04150305091501081b0901060e01030e 70
    0x240c10080200001810000d0400200171091252100a40c003c0d17825040d0192035943e60740c0d44051192014040d0300d6004002511003486030050781880c071701d118042d0110041d0980a1800b0b50031000304a2256072040c0000311883c4c20310040d151641d00001c210711321074100041c0741c50200d001030300720303030401c5410016000700040902454000d0042d000c020600803078900364000044040e02c4066200e04910400c444882d550319034030141d01d82e00442c2021001c4136110120008000b090381120301b90142030320100a6050124640740f1540c003580086c05020085001126209421070701c0782c2c045503144c4d002c5881d41e413080d029041d0303210825805500d41900d42808a1080c0c1203280301a000854080c014800c5040c00600e4900401d241000603045c10704040c40c80c100010503454201c01c0654800005482c010300304180c1a4000d0000900092540c58000c2140c95003071080d054080355041c40c05c441040e0078100082c50403141299240502c000e891030044018100e400885000c500c01d05c4c903204105c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 841466906 1250 841465656 841465661
    0x302150603033c0a09030204020315100909050a050402011e17011205070f0506030c031302060406080703140106080c0c0c100e130902011403071709010b04060803090d031110 76
    0xb030101c980a924400d0040642d0315141c0d148030f907003016442e0180010a400ca4200c18400181c84c0d040745d000d80c42e6581c082407141c060045200342980401c002401095541e0099010700542e0800f480c103003c3d555900200a00b035a0701a2802800602064074a00c044028034070702105401c0d50745480d02400000d0300c24015160002c4e0066020240c03140e111200304441004504000c258202600c52503a2400d00002c1b2140402402092243e9001000030b19070a20744d0301543d03c40e03a00500842e00d9644468009006010807540600401d03e07080b0349203582d03917060750aa8100c80e500d80e0351308920360711a500c42685400842c80292544181900246507540e881e45c0b40e4140307400350b83c9110191108004005540f4079890582c65682e142c14010340160b42c1c804491095118006100e69413070f102c05200301d9071140807008042031880480248000c11006403c81052050b00f1501480041d071180352898883c4141014503a000814a85030b0000074003c030719244881d103144c4180c6007081080b841034804d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 841468156 1250 841466906 841466947
    0x40c0e030a12092312032203060e06040f03110106030c1403150903091512040b09010c02030a120510181e09050a0209061c0f120c030215060303 63
    0x800c54190700528a0719035000d21403c0042c0403080c4480d00700d11340d00300c501448403882d81c562802503c46801e1110001c5003081100c03964600601c0381c3c86c0c502c1100d40300246c48800350008958880c00e241040c15251800a049030203182c0140c41c82801e1000c1d59400e88542c1802d41941003195221038002001c034007114071b490020280c0c0c2400440c00d07105c8d02c00301410302040480c0a0750003e951803c0c449904800800c0d14036808041e5440c040c00d055010888101d40907000700c030031402000004010802180c4004c1c2801540b00b00002c0c4100b403d4a502a6100c0c0241403c03540011400c0f404041b1806080d000140c00007000047c800000c0e4079070745000d5101170084025402541c03a4912409092000c0301400802d100008040220300c00e555034103034a079440c43c040071b881400240c021a402c0d42d0340140b80740102c00c0360b00280386418000e14000400090308103050b12061041c440002101707000d00c0e81c048445900d503016004000001c4440c10304124050401c0d41c02d4172050040c04074200300c079842d082 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 841469406 1250 841468156 841468163
    0xa0513051b0c0d0c030201020d0f0905100e1f060e090d0206010504050c03070807030e0106090b03060109020306061c020f131401020d09090c0c0602072405010b0405040c0e030a 77
    0x154614040e070000700114003001400241c04001c0101071080c000100300728034800024641001c4140507420101d000e4012000c984036500c1c0341c0b15072490390004640c089514035100740103445030b03942c0d541c030040c007240c1040250b144230f90000c00c0c0030000103c83d2680c0c1411200442000140c0d15100d0f190180d03141e10032076080340c8540c130600c010f40400760100580e030b0040c001158207120383c3ca003503503e0041900002e0103c50034014403002045646000b6000310186081d10710080010300c1c2e4424440c009020b8062400d40a40191800403c48a0b458002c80f841808090300d810302d0030030005105800402a560340d804000d80c2030181c0c6820a00340d1000740307002c440c0400b0119010703050040c4000315a410000190640d840032040c40091604130810300e08503040f1410014500c803a80070113845140022074010003041c400101d200030044000141f52100c460f00d90107503440c2031300444d404100c3d0020b0184101480050200700603510323198100315002d440d149443d680382c01040303001c68601107038804110b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 841470656 1250 841469406 841469411
    0x60602070510020703080a0201021c2009040e1b0415050303090609060c0a2405090604081305060d0203040519030215040c0b0c07081b0a1a12010b0c010f02180d020a0513 74
    0x10071800e8400cbc5441000000014420000301903c031005000d10040c04044441100b0085118603450340c039644054980440c0343c06951440070810040c2000c629580e0881d403080b440d0941d0012400407150262040d80c40180c011450210a1002c2210075000150b505602ca0f41c10003680e290100280300394140c2c0c911071852078004880204508142440b05084202100d00d005e04200050301c000401a40203500a01a1541d80c0a211111911600190401c86d00031400180090070882c955004500c01c86c094000d86085550300040c82c0c80c41038002d4005001a401203202c0c0c2c4050f00100b0280d03402600c10710340d1009059884000c10308942007a28240b50b5078000c010100034100d03080c00f02c11103020145119419040000f8001941103941c1e01a840706480e280f0003030307008541d0315412203841c868003001c48901036039a402da06955501c60001550103500f031a00b10010761406000340c50300c0500950100d00b6006409080c0124031000c1c0700c1c00e0307a01906e0450001240c1e08c4021088860800c4420301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 841471906 1250 841470656 841470667
    0x18050615220203091c05160c1208180306040f14010b040c05070203100524062206020d080f070e03100609020c01051003022b020a060903050f01060602070510020703080a020102 77
    0x128200300304541e0151105d4901801400f01c0d40d0b11a044035624240c21000140c2242d850800f103d110240e42c03c0004201301c030000e48006c0c05980c00291144004103104070076488a0903090540302e400940d03009090312a850902400200f15155840d03186003840d000140245042d40001d09580e5840f41250100358000756103c01c0d03050912441c0d06141c4120400e0046c0c0c140004101181b0414203002d480c158100040c40402c7e41c0c0e0390301240d000c1c1040c814410f02d8419043e8003100004143d1003560003511420120f813040c41e000e80940c0d44128a200415120b6035501242500c03418680c0b00d1403070b4180104096204512114894500980381c2070b500141c655212090460840c0d101828500042c080c02c082040143ea842c42601d00800960111160720300c80c086d40f0705110f540c3c8a400070360104030f06402256280d4017922620807a4020713001c070350440c011003070b0107402c94241e4011500160030a020501007030800c0901902c0c080d035030b84100c0b46105c1d82c0b0b44512a8541007080c6e9000140d400248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 841473156 1250 841471906 841471921
    0x50d080c1e090910050609040f060e011d01080105010b09270c0307180b0a030e100e03070b07180312020a150b01030b010504081011190309020418050615220203 70
    0x61540700001004c6410958284000a002da008810700c0038491511604030448040c10794025500515020b583d800103540c440c0340b0f105029402c4401e080924010f100006035129050241c18102c500360050146050910700c10310000d107240c4c920100c140641461700312510855548680d03c103148100c0841c0e2a410031100040c510029180002040c00e0100020b00c285c102100c200c450410071030400040213402e400d89507082c01c007034802c0240c0ba14034000400e40031540c00700c000e0014a210741c1c03540401e43e4800790181c5019400146940c0706e084080802e000003003003444c440c1042c480500454146a80301d503200008c16130000a44400681c44480c0055256054056002c1c2c190090910900b0542882d81c41c641e2100007103054503e00f42c40d480030718116400d41040701c41c82d142c03005007c0e002a482c1c00c4050080c20180204034002c0d8a8241c441509159000100c0d5096a02002504041c0c0303401c0d640410f4a10303980d026a50140c4038544480782c5072003c1d9543c00160b6a180c102603146c1c40c2011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 841474406 1250 841473156 841473169
    0x30b04060e0105040f06170d0e100c020907120f02040e06060702060a0305130204060902030712060f032604060804030224010b0304060e16170109050d080c1e09 70
    0x901550801005121194100c11000d0540ba8140c3d80010400340c0440801c025009543c03140383d000300d40400d41a907800d40402c1d0f1112400032610b42003124408102442401c10914039082d00040c0314a421000524000404640205007860311000c0d8098071100f6200b190110b00c040ca40c060740c002000c101440c560890301d41d01207070031a145030a22050390080303981d41c820310100c082059541c5001031190000d0046030703005e681d005001086821380703d1808000a52060725640003040c032412002c440c41d40640038241c140c0d516848051100c0385150f81d4503414102c001405000880c60071160303001c0034542c901030720040240c1c1d070b9003845908150a0107130520310b01d442c3e859044250038402c25600c0c128400d019044a00c0e030100b895507aa00d504060000306451500c0415500038440c407010204084070061060b5004045000380d1902e41080003800c8900781040100340380c201ca1080c100c000e0090480a0340502c2a804451a090340c508840919504005030a950140d020a01400d2814100d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 841475656 1250 841474406 841474421
    0x501050105040c050304030807110d0903050606100e0112110705070302090c03061e0310050403051803071406030712020c070303120216110d140105010603150b03040816080a0c0303 79
    0x41d1002c000f41044094024064480100090140590040400c007807620036140003941d40c0425058480d00064228000c01c400c03501c1c0f02c1528144145408103459191641800d00c400403d81c50300c901c1d40c0344100041da4228100221024400d0361f4058407070b520842c0c240144400c5d4803038005450841c0c210310401c400054050500404401c0c24410403401313464640c3c12038200c000c031550702c02405101e400004e00d04007807000c10030341260401c4140020160842c0180407404001c0441894600c0c00605040c0e0700d150b03c0c440c0074244880f41850003e40e00f0943c000b9174000b001407610160b551007082490050380d01012101d1065400003000f0030038958000c5924410351b070031a8040d440c00340303010071075105665030500c0901000c1c6890115443c91384c03000303041640c86521811400c100e03080040000e000f09000d1140801003400d000c9050082c41c94854400141c96000b060b8509544403911a580349420051040c41020191b5a141d4040340c000e60203030040300d20f10740e5400440300140c030340103060700c64a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 841476906 1250 841475656 841475659
    0x9080a0f080f060405150607050609060610120b030f0a080405010306090506030c10050903010c1d01050a051b0a150c0e2403060307030204061502060f010e151810030501050105 77
    0x310310900800a46180400c0d0f04228201c8010503961582241c6031350301004c500c800350f40240700041040c100603010231414807a64605040c3c0300341c0d603910018095510b05411081000a1400352070080200c2e49a2001e404000040c046803400a0300e4410760745448202c0c0800c0d02c0f110400b06041225603810700980020308200c00091000741403100c0803d550b5180d04880354422070802c03005446045c411019224260001002030201c603114090282080003805200710b1020300c8080d40c142c2a501542c121601c25a082c0c1c0d5140c41c0440b880c281d000303001c0000c81007011500801134000007180d410400f0b015180200000055910b1890b42e0162400700ca226905004010031400d14540c464203800114008090b810400d580b42ea130500081d04241039600029070080c503041f400b10302c4411103c00544101740b40d4085407041e80740e00d03044070200802441804c0079030b02c1081c0041c1c088040c0700110601454060403c1c207074200400301001600004551406529000d0441001808003d00407207006100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 841478156 1250 841476906 841476917
    0x50c12062418131e110d030f270b3610050d2f070506010b072402031605040b1b07030807060911030d02101d0109080a0f 53
    0x24090702040264101d05840c05440c80d44100086003042e03140c60340420107910800b2403a8050001c4465404510048411349216183d4084061107041c036401c4039583c15010b80790062051074001c41214208066104441e404003140c1c51342101c0340c00c040e8400f014010f1400383d00c1e100c185030074003500151101c50b00c00c0e4010560349180d5004070502000804028010b40301d0740302c0500318100c01c0d81c0302d1096460452040e4030f0a1100c1d80c070302440c055400c2c19044010082c064003616038a031b0f00b0b010f0144c11405452034001200400000b030310500185101031045070711443c02003d00c041c4e8107028540040303101034282c0000070440a0901c1c5001038511003071034108a400c090170180c0c054828080c50300b0490360200c82c059241a81c54040040d54021903000c05103607a039824a2800001030041e0080865046402c1400d403980c0386404510010f909810754024500c6140980c03106010303000081c00102028001e8080d00074040c403c3c0544003265001d0b0f107649680d4084080010059034025503440100070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 841479406 1250 841478156 841478221
    0x6020d2403110307080318090c0c1002070f210206011e090507030213060c1b14100e030d171b03011505040b0a0c020414150904050c1206 60
    0x45500140000341c035040107001c8400c0300020042844c2400030f800c070090074880424016401e04030ba403200b900c6914140d0b031000654444072442c0c02c180c0104100805960451100750300700b007900380e000e85911402003681072030413446500c402c290010114146510010070b41050400741e6010000e032401005800754411036501c1550799100a08034a0150400d02503c4201148401d8820740607500303c61070000d500c1c400030741d0301c00300540622902e074001c071160b11881da4800305002c0c000c80d0f800d0031038000d0701c40300c00500421001c02160302100140b01043c005c4047c1d514210740c5003000b1001c0701c00c582d0340740d65444c2d0188001aa400b8000149442078000180310591100c013011401e5a044654000e03907082055010081940c481c080e07a013201101c450040749401c3c006622581a0201500a880822181c0d00718110360350b40c2d45080758030480c021207019400d1207600b81000600d40c018095402c2e941c6040044c000524181c24003440408103138840010b1003200f81c455003e04240c824000c000c4201c82 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 841480656 1250 841479406 841479461
    0x503060604120c030b160e0307270e0f100e07260703170a030b030705091305010902090a020c1c120e03120702010f15140904030203040305030706020d 66
    0xa110354081c1588902c00c4801c2c0c0401c00403182e2490b03001e0359000306441041d1401091558440c03500c103c0901c0002c1c44250101d0382030502080841c142e4262000d100e1038249060f603d41c42c031000c6000a140a07556a254246003c0814403441000d050304401800d5078511804204013520400c2113040c103140c004440c01c2040c8860244240620f0108075840d4041c4292815501d0400466031f01c060500c504034480000c0b000240c900412380b0203025101040b1288041c0180340d03840f05140110307a00000d044002c00d04410740b00f0000e403100c074442c100115200d00b540e40400d1a800013940d99481b0150041101000080144036801c0c200303500d51440c0e41071030300c0c00000a24080702d04200140040c2c1d10304946c4c0c10600c0500c1103034000c01990580c1e2209042826000780281441d1411448461608100b4442e507840482c410048aa514131044088c0501c174081003560f10700a04114103510081000100081040c400b0b01450b80c0903c10040e21220f000300c0501c01c0c6c03803a50806213070070b005031210040710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 841481906 1250 841480656 841480669
    0xb041206090302030c01060e04150903120218060d06030201090b0f072301090c0512010c120c0c0c0e16050a08130606081e070b030402060a0806030106051503060f01050306 75
    0x12540c1244000c2100e44850034240c0c00c5202c0e0200180c419400c0000c00304544010407111070146105408000514079080301c41001c41d10301c103800070000f030090b100140f0b002a190300900aa82121030b4001005a030540004110340d01400b00e40c16026240c000800070b542e0001140f000915000040c1c40c40c1c201e54030039882c0740d841180d034010101e032601306003920313568081d403003142e900446a0020054802ea9050068503c42070340b0501c1c1c41010304c094844001101030240b051032a0070354032150354038103900c81414086c0581c0092442042000c8000d400850113a01303045000301741881204907242010025080c4003082213080105006007004007132003480e4030001655010180c82200020031086250000160145511040003403044006210310540b088400300e105030500380440761950b642e0f00110303080d0300040b900a544540b05010a45a25004250351075100c1c20050001402c51703200d10004e65441d4a10300c62000c000c0021041150b9070030b0000007040c0008090034818118a08100007a04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 841483156 1250 841481906 841481939
    0x30e090603030408031c0f020301030f050d0e03070e1f150914090c0c0c03030318190c03080d060f03080c19020a090216080a030506030610030215160606060f02070b04 73
    0x81481d60403c040c0000f251b80d82c081c806c1c0f07850f040c000355a256541e00b8208400724071000305840a004800804103881d000f43c10720003508202401800007540342081d038141482004015602884042100705050001000f03500060700d081840098262103164000305612015000708500403140c00f00584650391f854046a8080050201f0303581d00c1388980f460030b040c08100003c60760144804803d001c0d0030142e074000182c0d03d211a0088440018100548040c031079640303200034001080d802c50520124154100815040c04000703030104400342d0f90148402e03482402c1c0d100b50703103c05000c03070724200004090040c001c05104400c403204666a142d0001000040b0610400c404c03507500045881c600f6482e040070181c04c0340c00c685415102c421203003015001d0501101c4161007030080320000b031940701380c1c070200c242540c0c5c0203008024401d0103d03044110540c0014070307507000850440c0d44000002e0940c0500c40203030a2950316a010f800d43c003140a4030740582500080079a0006000501240e490000e4520 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 841484406 1250 841483156 841483177
    0x2040e0f09150403050306040b060405241905090a090b130c030603020406120b0601090e040308060a0b130e010b0c0c060f07080d09050d0305060102100b0604050d030e09060303040803 80
    0x220380da1100c04020340350642c1e4401564980d91100c0800041c160428051751080409940c240070340b100600c100200381c419802031070341c010030740c41d011100c4036280205000300300070120b0714a15250040540c62180c00b10f422100c4001074001640414900305600503a0040062520902000491000203120b41d22100700b00e03010b482d60340c1921000c3c2c9110b170f00018001c40d00640704001c559101c501261140e41c1800c0d054590081c0180481e03403035480380c510941101d00e200340750407507601c0700d540c00c03104918090f21482d44070507c0d00e808101204000001c3c80ca440400d030020001516021036050b01a4050784a880c40000a01000706080b0001c503040a0040080720350f16a203141b11070a0361000e000d0581c02514400b0081041c1a9042450b4025244c00c0d01960440c0c0d4105c85210049040d41c104846650058011203104829001190810480b44a009094504003030302ea001080340d00d008c07000d080c0d0005040c01c59a60181c104407400981001040d406140382a0809040950300d1143c100c044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 841485656 1250 841484406 841484431
    0x30f02010e06190201020304060b03060907061d090c0a2a0605101e0303090b1c022802010c18030c03030f09030807081c140109020c011e06150302040e 66
    0x400da902e100071242500e400190754a003201603650000d00030740084800b2107131107242c019842100e1400084482c85404140300800103142080001c99000d011100b400010a03202140481560b1725402c403c0e00ca0440101c0c650340750351204100404a01084503080c569400d00d05856a11b00701c04c8003041c01080e04031901043c9a1150000a41c0d81003855020012103441e010028660320340304880541205d000e1740d90000c2e41a1610f903203c4051240c0c181c0100718050354647c3c45403070f140a401500302d41c4094010051494401151030850008079100a00180d569000c005166908030544000f40306c40a14421790346425640e58080500309804040c2c02c3c001d1490008264512600400c000f55a1106916031a041c0314030300b020860b00801c0c10754031902a402e4040d46809214072840d0502c98811304012000c0e4600310441000354001e03200c021455417155490000c0390450f0190790462080e56600003401c0d403074405241c155000e581c90b60720400d80100000c014880c410400240c0003041108603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 841486906 1250 841485656 841485677
    0x1819060c0503040e0c03100e010e07030b0d05101b080f0703090f14070e13050a020609040f140703050606070c050108151f021207050a0f110901030b06040b0a030f0201 73
    0x142c6103004940c4246810680d0204000603038a003140558000c090b22101e142c8095101d0390400f4030300109000f25035403101710000107000c0328070036005000c5010024001c045060240d8907040d04100703840815902594680d2100c0c1d6402c0c82c0b5030300740c0304038082078901104141040081d030489032001400c03520400d03071141540020300200309522000036231300c0008090342c90f51307518601d80c8460700303481000d181d0340d000d1000031040c0e0041251b401c1d2065106d009401021025420010300c5c1c1c000c0b24ac00c0b50050380e600c105500c980110712a40300b1035150842401c650349000e100040556500030b00c0180111001e100f5071000903085004a0160368090904001a40c2e981003450116070841a0880e404109000640c0c1094217030300c1a003c1e408225400e49818100c01400c1c0c0c80700f031190300350091455000708500e2001c110704c0e0021144080c8a15103512031035241100050b0a85030031b8009980c4040c11500b80800d0385000d104009840c80f060751601007561954482800351355424402905018103807c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 841488156 1250 841486906 841486913
    0x31202030414151f0b0703121b02030d06080106061b020105070204050a0c140f040b030a15063b010302183003070c0605071403030106051819060c 64
    0x780003000b407a400e4111086444401980b0090304030980d804082c0e0141040030605804130b0011140c00d40d4040707041d662a100c8280d074115152026519030540703955856201c0503050640616034005901194011603c410b640c002140444002e6440760312941e246c440100311f0250402c4141600b5440660704070610180d0f0300050310940300e003a000079801890842000f00c0c0c41c105030b10820402c0701c203559661082c0044005075410f0700c9041c804c031603105801d110800246d030030b0900856000b469800c01103074241c2080e510040250b4030343c00c45004101030035a42c00440005440800c2c50050550041400d143c0072590014491044440c80e0704168001030300121740b00b02c1307480121350780c00d000d4403013004040c4140c1d0310315020303203d404136103e80b200702102d4151020001050310412a007022800c2411441d02c4020f80c0c196011040840f07492440060350805404144041c2d070081080c2c1d210b0550380c166049404080304c03011900c00e4444c41d2030301094502c01a0042d500d40035100b00341480c0e81689050305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841489406 1250 841488156 841488173
    0x3021203072c060a0302030103050118080f09210319050a090e0606070c031412120f09160801020909090a050a0201080604110c2d0a030c0f080d1509090312020304 71
    0x742c2d01504100e001944200084c0c2c182d0046040300d000700b008002002804040e0715400e0011070005d8104203040c44002c000e01c40139001003100300300c0108801a180d042e185000d000d81404c401c8176031075800c0820701e501003108410070000d0301c0c075013483c0039403412500140140c0065024040c0c541c00e101603500142d410b807501d80031074031100c0c0c010110b07400c01750313a924090b1090f982d121000c003e0b5000d00120308074411100350584041c0260201c88040941c0e80c075000070380101c4000d011040c14403c01340c038000107101e4041c248e03000d040c0220025945044180038407142c1140a400c0c4405030340b000c0800f1000c40c00c080f807200200e0b0743c2440c1101d0705844e10400a03001c1c2411200001504400040c2d5200002000034040001c641542c040d061034115900c080003100a2a02038032425004140d03900c0c00a0701c201201c8070f10a01c1014040c4d0280180d84480c604d0b5005400801031040da60280c05088500e1843c13440010300840c182030015080720740e001009894048041c00509401001140c100030301103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 841490656 1250 841489406 841489487
    0x7090c03110c100f11071403040e0f0106180308030a051b0c01020903240103080f0f120f01170706081009110319180212160b070302120307 61
    0x240d0071034403200d02d070380501d0711580c071000b000d801980390411180c0140c586024182d60941108882c50600f141c50b01e0703120311041646540200f0b400108008210040020701c55030140388415810186076041038006001444580800881c54200d43c000300005200141105d92080342824041990381b0742c0d40740c1c5008110b11010b81450315001140e14180840154090320141c04110100d0310240b00c100030360080710741c9101c00504944503500050011a0906000f00080240580c0680c6444c1030880f8013102900b00000100ac0c0c848180140f0040e04a1926030a01500703101442c801c6031040314032510b0352288a44103103000e00c101ca800180607601a0300180380140b0740407400380001202070060b131706903510840d0580c00101e4040c4c408004084144075811032480d0707003a20011481c13001d400b00890006540c004d8021031052090b403410300b44451103500d005102e82c2c915180c03548410b01d8082d0800315460804101d101090040004840e40000c420307074400c1c458894440000341c2c40c2211019070004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 841491906 1250 841490656 841490681
    0x10309231c0203070b01050a05011707090e0f0a0507021204060c0c08030403061d0304180b060705010e0105090d020f190302070308131a0910030b040b040f02071b060207090c03 77
    0x641e032011646580100c02480c00710b01c6503100000d103a8035501003002e8501503001c0d0707a00040301605003469040452a4040e001010382c1000c40080d603441c0c0d20304404400840d040c4810014a406101210000b402003d4011869001138407004d5074180640145008502c110b00c100804a080e41c401c0c440e681503403c02600b000001e480d44d9075201d05048002d408890b40201550b80501500700d14004044141c0741035500031040c4030104100420110b0140010f00841a0310040c20484d150005000344284100c50550f00004902d030b1a001c002030381030409082004065400494606c8030400012075807100800e500c01c0d1034203a05915080072480c043c0c094000802d01d42001648a0400030043d000008582c0510406170700c03603409a010034940d020301c4000c00d13001070202c07518a8000e0f0082e0481c40300e044003d4000105403031030100040a64402440d24440c081d40007032060b080c00390810380300b01a0801c108403240240c0c90480025543c80092285410150380c8072400701031503200b900310f510a0a40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 841493156 1250 841491906 841491943
    0x20933130b180a2406020c060a0215180a030f0206010b070b45100c1b0203030d092405010b03190b0a0308030a05012102130e060f011401030923 63
    0xa401440c003001401c60003038174098820045070140b00d18001d0b0444200c0d40055014041c42c21850360940c4c1c4402000e000900d411910100210400c0000c00030300c1030721030087c0e07070751008034004481c040c2c00d00c0c1041c0c20207503012030100b00b9800420703c01c1000641106900712814410700802e07401100040c1e440700c80c50884040740808040000319403444000c1e0100f4841541e00d41e00c0000024412030f48140072100c0883c031000609000140066070380003259002030240e81ca0000c03444a4081110307e206011181d035039010000100448003d40d20705c5140948600c01c0005504003500716410303000c01820b4100115001c145c046441c0e88907005827020742005418249840d490303180c5202d8540086980071080d902d002e0000501c051440c401040c00030001c10360b4002c00c0c0007502440441490048881d24403600c44115204600003001440c3c80ba003030f940c0c0800040d504040d51030800a803440303c5681014200398811021400311000805400c16210580181d0700310458028103002c0c0280d2005050324 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 841494406 1250 841493156 841493201
    0x403060915050112020f04090f02030321161b0c080307110405060406230a15230408103b0c0301090f020933130b180a 52
    0x2041d28903480003580d842024056a0388800c484940d000e0070721800b070340c484080819400c450601d036000314030460191682408030750864010070702e5540b200c0c0070008942c00f0307046440c41c8012281e02c0681c100604240401c10a0b8001c0c900600b4001100d1103405d10381030b4038009a08000c0f0340840e1b00010b00c162410b803500c4080d1030820202041c5801c28803406a0b0030a0002400b6151505c6000180d890f11240002c22148858981420071008071800e07801040200c00840c644400d060000410030660340c0e07100c01c07402d880c03c0c5400b4021608101121109040c0402d205004002c5036800d43d83d40210743c00a0840d0f00b041c400000d22500841508401b81303035440b419074484241ca038611590a0110845001c0d00c400028103080321200040501000c002c1c0c50680e00602d4040080c51300002c041d50b803041e000000004114408810900ca000c00c3d03009200d03c0e40031401e100001a5401981a808000002010020617032017018a28444024980040020551800c0d6801074484180e510b0600d551803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 841495656 1250 841494406 841494413
    0x1c0207030c0e09150c0706050906100b1e0a0c0b0a0f050c040506040315090b0c0307090e24010302040803040f030203011a1023030708040b060603010803091504030609 73
    0x82065020594098a00c04804030303032010700080c914001c11841c0e000b820001028a91100d510b1030240c402001d5040030440403000c182d0710f004081c000c1c15000b0182c001c1e0305106604420745851a8810204c00300d003405180c46040c0702104081800b42042805680e070641e402003200e00303100003107008000e41548003e005080c603940c1d0010341c802030010020445a240c2c88482d41035801540300c0c581d80524200f1042c00000d2042102e0201e1030690003010680c1500c9680f46c140c80c1078220703140c80c1c10100c088200000d00c0d920150040c0103040c6d540d04500c0c141099080030f10780c410045040c002c0000d40100b10940f81e446a8101c0d4001c0c40c509003901d40700c6407070ba200f2542921a5100c11fa00c40d43c2801c600750480c40d5080d0101400f01002001c040c0ca07885480c0042c0c542d1075214016110800301e480d1424100410580118422040c9948031a034a143c50310302001904005450346000340c10500040c02000c0b0004210303080d000d0b04946403005e61024010050170f0307100d076402c010405070414844c5000c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 841496906 1250 841495656 841495663
    0xc040504121116180e0303040b1f0f170a050f030912070501080f1503070b0912010509060a090c050a0303020f101817091801080123070e031c02 63
    0x8220150340ba042880404a00d40d652000c0c001121900003c80c0e840400510300f0b26041c00c0d50600c515000407070301904410f40300307045810440c0d094a80745c03125010004001d410a1342444101021102c008a042c20155146100c00c1c43e070003880d6100c02284081c0a100d1004c00441c039031a50300404650300702a540d11041c1d140d4100d0b10250780600c11070050300715401804a6042e040d01c3d03040e581c20b60305588994950902c0080a07100314451800d15030040c0071610184000806803840c0950140d0391120790003070015200c0c3d908842e1900d079161000b8848130701000f00b0030701d42200c112a0040740ca581141401c015800c1e40c0d6000d02d0f803055405c48000304058001c1a03200000841900b80d410030320350581000d00b0f442030385d20282d1780c41604c0501c41c40002d050703958600140c003031781418a04011224020a403131903064241d060502505400400558000340102148003010000305c401d2041407081e00d00508038064220000e00c001882c490005440c20400b0256803009440c0f026103608101e00040d44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 841498156 1250 841496906 841496933
    0x3020a210909090506130201050d02070605070915080c1b06090d080f0c030a0c140a030608071a2505060a0905070b190309020102010b0a0e0105030618030a0309050c040504 75
    0x115030708400029038690940f14000324144c00002030182c0f5550f0b20011101524012000c906111060003071061006052010308103d5202d0100051507040038803024043c400d10f68416140000340190700c8103c181d000006680003140010003a40b944c0d0040c1c40400c400c1184a40f014051080401b0040141c50001c0c600a007140b440c1c030741241a444c3c050154007030000864000c88042001c001041d80c0c00015402a1130407641c503d0a0040c3c080384480b410b80641c410002c6000203038840905101040e400c0c01a90300411020005813007600785100700400700d00483e21503180d98404450450b0031414008010103016501c902030311810310701140824000d180e005001d0710248600400843c1c229030101c210b60507100301500100024a9500c806c8000e418820400ca04554076a0a023800c140c82c1e8199500160011001200b05507040800745407514100134410440c503a20406d20040303412000c81124040201c0b864040b440280504000e464284241c0350130750014688004c100610900c80c42910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 841499406 1250 841498156 841498223
    0xe0a05040e0a21021506040f0204062c011709010f0c11210301030b09010b0402030a0c11070608010315090f03080402030c0d350c06061507050c060703020a 68
    0x50018486401c90041840004100b00940c1c01178041c0b204000c2d000005981c00400140003180900c1c03170315140c0069801a51001010a0040d142d00c0c040750603280e00e000c803c24804159450300012340c00002e00320f10400c4981040b101d0340d100450502c203000c0d0851071024800010900a03402005002400c2d084801e1302c8030401e005100000f0b0319200c0c41400000e00c40c00e0180c015080d6401c50b1110300020001600445a1390b5070340f001807a00d6140d6001840c8608200280010104aa030502604441d10801d12000b1600045018421560450003072810f598008401010b4100c010039150b00814105c0f2001e0441d00104400c00105507100c90305601c941d02c00d4007690a80c5144a09204e0a00740003031005003518400e40c907104d01c000c041c0030500320301050044903800198034200640c110368420f11501902d600032101700056800d141d1280341c541401c00c03070038038a48421030b100d82d92500d01400d00307248911070015041c010301d0b200f046104000f68101c00610343d010300c60901084081108400d14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 841500656 1250 841499406 841499423
    0x31406161e030b0a151b02030703060b0303091e010f03270510090b010311010f08071214040c14030307111c1b2103050304021c0b090304080c0d120e0a05040e0a 70
    0x14604d450706c90892106a54041d00034000c041c107560b1403030b014000b000c1e1442c2c3c1520040c0301c0000e40740d81e41251034032600300d006108106403045c4000100440034801016060608052040304a4a100c00200c0341801c0c03100b40e041c071130140c03500e0054108100e1915103001541046c0000c814002c1840146041700d01c150000148400680300645003508443c3e8400040f8450200003100c1d58000c00c81701210b0200d0300400210985000038040e82608181c0d800d498541c2e003110103009403084200c450407000c40490056052140325903514002450419a182c0100f101d05803002c094030550703424258142e4019988800315810790042d40d40c080c0c0d144540c83e18a0307400900e84402078260b0340744807101e0790142c0c0c2d428515502e41c1c091024040c5a1408048401d00074500c01f000301d0a100c8440c0c1c00b0702c040705c0145503182d14100c407217860000c81c030314030512441d0020080c6001640348220320010310f00c242005002c03c8a400c00007078a83c100e941c4000d17002400c043c0e98802c1e84501081040c3c00c03501c40d1540c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 841501906 1250 841500656 841500677
    0x30221070906090b030f1801090803150d020d032105150915131505090705070c0f0f06030506010201110d0204030b01121101050f090a031406161e030b0a15 68
    0x1159410b0780b078450f04418680400104046ca180c44125030750006c55001054080c5103600ca641e42100d002c100305946c500340100510201265581600342040c1040750011080140354000036440742a4442c028240310400c000b00b907500c031101061514068449400b0895494054600d540c3c0003101425244908030a100044410170040160150344001600f000e88442101c1100c0000300912440b180340d0300041e20f030000d155070302c165141d841040c0540d101c54807049240340809840100360411a041c02c1c055405000410300d0341c0303088045880d2482c0c0424191164001130b030044c01c0307001c1c04003441c250001c0c80c4c40c844005a0020011284505140c110a03a81c0b0100b003055500140c0008041101c3d6405035521903109602408465001e155101c0c41c082c0150b0000d4090a01350b0310403225482510003540500505000301688907040d0a00c0c00c140d041250703c001c00c40e030302c1c80c0012040c41c1900c3c04a0889540300703501090005d0000ba09062411b83c84031410048081c3d045070030000101c09401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 841503156 1250 841501906 841501919
    0xc060615030c0906021e010f0f02120709050102150a230709051903290405010b0f0118060f02160f0821030424021c0e032502010302210709 61
    0x881d01150b44544c06421070f0303160b42d56410707510050762011b20030540d2030b81400d910413184c0384513103a4402051000180c1c0d42003401c1030a8202d00e002802e030f00a10840400812069801180b00841d5042c6414142c4140d40c401080070014520112041d02580c801c0031003042c4104140301450060043e03498014400360394104121703040141c00c128071048824441d003040000c80340c0c010031603140c2c0156078014007002c50602105101d6800c940640f140d079110000d10b0420704111000038108003080ca003c165250405c1c007007506500322881524208103840406010f01442070201603c800c03024070042d50510b40d1902075007030542e4640035001e843c0c0502151403a40c1e01400842d08181c0601c1078000d402c40c0c1e070f69102c0d6010044401074080c04c40c0300315041d44640703928501c000c0031000c18404441c510704a0340000c010484241c9000009640c2c000c200003140f243c0201c01049030103480c035107c15449603141c40100d000e405489a0024045028a000b9074807030408280c50b4030800b035554900900954910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 841504406 1250 841503156 841503167
    0x105030c060412140609010605010305060114070f031b08070c05010c0f0308100b04122d24020a0903110a0b030c160c14090108030307050f0a0c060615030c 68
    0x10a11a880081080b042051525035490103d1a034020901140c0602070207043c94240ba0b811a1141003a954554080c0202c2d0b0b0144925908103000303107440e4101c1c40701c00720b9446540c0b00d542009841841030384400d0701054400c010f03941124001aa03040225080352034150f0f0560010202107558081800009c1000e520400d452032003c0d17008043c501c2d001015440a43d803c06010348400b0b07114589440225004e900d41c0002e100411208415825103049400c04100c2c00c1081c3d182c000000058130341245151035a03240c020748550b000700f100b024210300d05280d45090341810b08019812800031480c5e0b001039412a5035103003204d0240c40400e0798041d01008002c04d8400a00900c101080c5c2800451042d44000d80640b01e11000c0001400700e5004544410841003581d50002c003252080030070103c00360038030000150042c840340780294213508040d81c003d010f500982d214410820400714110001910620b40c1c205a5600498100202c1c0c4e158400c1005018400e2140c01c003080c20701e68054600f600c500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 841505656 1250 841504406 841504423
    0xc06050d0513051c0e03070b030702010b04092a0504050112030822060c020c0307090605010306080304050f01142b0b0102031813060801150f0803042d0e070c0605010503 74
    0x40903010200300c1d200e19184c01c031041c090380c404100c608072010031191420450b480c040c01114420325164540740400a0030b40e9030180c3c449000c0c2d8103018100c00044c10200481100541e0303020003210b4520080c500000c2c2c0302c0542d001035445030505000048240341c5c0c191070303c015802955000010b0391602c9022040d50074510f210889050000488000300b101540b00b02140d8440384151155024a00000392801c07196030041e030300d80d50f0780300c108009a41c0c052007650018074412025505240c54800015107218110103941c3c103004e103200742e10712441004011a01c400c4001c5001082900003000c580b07114826180d0705002c2241f43c80c100796050360001081e640950b00300d2400b100e130b011901080c002c0d440c5545910140481e02c41e90301050080702805549040c038082c039080d5101c54900a80f109502d10349a0110f5000d42003008144140000d01000355950f42c40303064400c1c5225941c110015070800613900c80041c4800c910203111481e503209a00e126480c0c020075090205988410804d13850f450013 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 841506906 1250 841505656 841505663
    0x50903040b03010506070201110a1101022418010605060a09080d450e040203070509071202030601050915120f090d08090307020a0612060602010b0d08160c06050d0513 73
    0xb800100003510b4100010140c0078411302d051440707a01131a1f030a505e44025010300300c501c5c4202c6a000e81b10b550703040000d04074144504d03220205c009000c00380590b008202900310419010040c1d1002515442500200f000b040080c0c01a952411071010044c416881400384044038003c0311910540d1034800d1f54014108064000b141810f501c010002e0b1721582d405408080440c3c820321190700070304e400500799800a0100404d0a07030b049c6003510405d42040d55036000309100e040e125041c050450340c400701d0f5400812400000503640e0b15010b0058400740107992101c2e81c000003032a50301341d2906c45180038090503941c0d9041000e25854429007000141c604541206055004030000c00806208a000b1504043c172401580c2ca071070800d401051203074509410982c041000311200c205080c2d5144141c100400c40d620007001100c46405c0000d030100301c501e40c060102d400110b12a0501c8054841c5004c00c03d51041003c0c207880c0d91240007500740c2e0040c0341030b605203905d00000034109000265641d080140e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 841508156 1250 841506906 841506929
    0xc1a090a140c1518091801110f0304030c08041e1403011a1e09070f080f0106021c02011d01150b0405030a240204090515030a0b01090507020102090418030305090304 72
    0x7251119000c40350448850811603a94851a076800d45e2030340b0884a0144060000390045140e40b516501d0a44100c0030020f403841c0c034100321006034210718405590301303d5414500f218545001d4200383e4040d00945d0000b000c0000b6039002d4210101e03020440b4400c54640398031403094500600308041c200c881010a41c1815214001000858a0300300741700441002c3c003c15203011a00321402140044c04111a034401064982210445054005540c1d81d807001090012512641c1007640003902d5105001044a240c60351500a000181c004c2d0405504040c030b2450140e81c3e44542c081860180403041108103081502040214407030b03202e030089a06451000c0c0c02092046595601c2c81c803503042c5620710700b4684c0246030601b070503140b803030008100400c024240484c0c9400c01c144c00044041c80c0c01c025a02c6036001034070060000e0301e04284541140c190300300000c3c143d80c5425051703029200740308486a01501c0c152904400c69101505210301c54042d68080000b5521182c2a5540c4e1007a0300500d00b8552 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 841509406 1250 841508156 841508179
    0x6010c03050d060909050a061811041a040203041209051203040506030c070507030b04060513020f01031113081f05070921021309060b011e0c1a090a140c 67
    0x207014000600000c400310000140c02c90f60345800b9411191100021521504100d091000b80035060150b450b0f80210205107045100d2035075158025804c00004144c0219103499604c625078583c0c8040c0004032002810941d50b1386498540364030424034004030140805c1d051385000c10b050806034a1b40c003498031041e0043d03140c00d003000100001600002e244c030180c0c003002c0190700d001032024029240110311804d65185942044c1c82c010303007034980c000e06030156804080002c1000d60b0305c10488107403005d0203090000b20a6624000307038070544103082e54903a000c03020b4140003800700800201c1120752020f0300340790500841941c592030300340c034020b85d200c1002500c2c0c21401e0004003601da078118526030400301d40204240700c170f601140c241600021000a039560b6040b402c0140006801000c01040302441d149454645800035060050044000682005901481c4800300080c9503503c00284461501c010300314a03201c440d99982e508208001c8544099041039200d650100086c02c4400300c0c1c0c02030039a074181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 841510656 1250 841509406 841509413
    0x3060e070f18030f0305032a09061c060609050111030c0606120321090c04060e010605091909090302071706181c050408071208030402060702010207170102031e06010c 73
    0xa1100c10040d640510b007108000001940b2031124003880b0310070b40702e543d107c0c91709034000806001005d109030031035191446402e560b6003000046583d01d00b01210081d071981d10307402c041e642011034820700c0c401881c0341400c08a030185d04240c100c0e007104c909903100f203110f40200e0516522800740c1c100300300c8181d104001007503940c5403030800280c4619080040328100001840310909541b280c4456640790300168003444500d1006112100001400760341c00d0004da441c0c05802185443c051080108200307001c580007a1540d00c2281c1c41d0140104c144854400035280c2a9540040c0103010040303000d40704541000941d18080c1c403140440840c484040c1140707540d01018946109045108030800340501040c2c06a610740c1c8090461145405503a401d0719141080c1809190110640060f017104075002e28510005180b842180d07441a4182d43e0079807203420030720040c0d1401c84650005107807040d50004907507140d04154090f40c440d119001c4600000700c0e5040c07044e110084d0981c0d205000400c1c400010300030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 841511906 1250 841510656 841510667
    0x30b06090d15020a09030c17061504090609051e060f190b0904050a2d151407030b10050f0a0e0109050d03020703050f07061d150d050703060e070f 64
    0x801c0d0040c500040c015000a1418040303070700036851031010070401c103414400d1011130703000000500006000300c0d01c24102c10211a0f9100401410043c0c0517032081000503041d19990010005580d000381e090255000b00d180441d22090720078090b01900f401c80120040d14000064498029005000280c4042c5c40e0a0034114001441040c9400701da516480310f0310243e20f4030b202c10b0307200b94050006424494898917001c0305141c4840c4c080150584490000c1640301c0e5002c0d5030310b1456a1240802095101114450024111841d12250400118020010613641507046020021001c4030104924503000e401540d080c0107915090b40344e080b080c400c181100e0300500c1d051480400506005200035540c40008403851040030080700141c001a00c2041080010040c0301103401203100640300d170506110004100c00702c6000031955a00c1c22113100f4203070382c440001d00f0814001207103080b039a5a07075540598010f0803040c1c4031100041d00d801400030350382101d83c1405014170001d6642002c1c603c4030030011a032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 841513156 1250 841511906 841511929
    0xa09120f180305100c0e0a0e18070e07030c031509020702040e0f0d020f0601031101180f0f0303020c15030a0c02010b040f06030b011a042102030f0f0c01030b0609 71
    0x18040d00084080c031022600020304000c5208000030102040120350311005e440381c0c0030812061007454100602ca0b136403072000d0791007a683e0340c615105050b92401c04001c400311008903005a540604080410f001c451100704512030201d070344040c840d080702e44200b203080320010090181c01200030344081c0310000c0290018011540014404a15030380031003401303070800c02802e0107180c444c0d00c01080c000843d5014052b45941c4941500541030941c515101c0601302c0146200c03090400c1014a8148050310840001201800c5016046e5104070340711404844004024001a00507105500a03c1c00714079106031000d561100c0800e401d4110784030039900e4009001d0300740c0088159520703045c00742c2050720782c1d22070100d400751101d001007002451410325551351001030308130008461101912034110300342c02048408440260130b50074600c00072425140c1c1c8607103031070700d000758980115125040d94020010b000804403107242c0503a0b040d000087e005408403030b400c2050580250007800108144c1c50302e41d07034221 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 841514406 1250 841513156 841513187
    0xe0c0102060c0a120b18010f0512010513020907020a0507060509090f15040e03040305010906020d110f250206070506070306050a080a11010201020f0313381906030311060a0912 77
    0xe1541c00f071b20480d02c5070001d81140075200040c0705c00f00964a4400145185117400c1c0d40201b2003800c103406010107200c1d4403440a4000c50418000c58882482002500344c11a004025100c609860398002011039104ca44c5481c071480780d00021622402586d04094081d40301c0c811340100100c581f40910001c1e248005203d00f0030f01043c040040496030a0152500d100d01c184e20041e912500317236416200311074819100110070a0248010038848503580d04640b50345140d078640000394030a409014040007880d000007500440e001c03070001e080020024115000d0041a1018009651500300b8082801c02912038102d0759840b010180000c07601c00c1d05144130703210040c4000740c40e00141840402e4298401e452000400d48a800b00c81c00784002644400d0a040e946804010741d070044200c403101c03a0300310101c0c0005203082d80f404200c120f075200210800072599410240002c039640d04020b8184219120f4608a50140c3d1000070780913003651003080b81d52070740140c100748120121041161180705510251 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 841515656 1250 841514406 841514419
    0x604021201110406020307062412050c180f0609160302031f0f14100804060213031203060603110c030301170109050102040b0d0b0405060f0d11040e0c0102060c0a120b 73
    0xd1000801070020782000d80080d552203419141400c200ca451426944c070b52440c500242c031270310301d0104403c07080700d80c00b21265152541500f001c5040c44110403e05a100841c040b0240031f43d03006a030501e00c80c102c030b110b000b0380d40c0e95030300c052141d004400c0359566001409101581a964001c0d4007550f002800c1c0c50580c005590a4a01404814055005540c0404020f80100801e0201d400503c45402c419241c3c0500c0c0c605100e8060003804000c0c200030052900031610250509103da800c60041d034004451101c03480300094054024141c40c090840003a0810118641c2040c00d001160f00c3c4a890390011855030f841c2419580d2803002d0b10400300c105540321010b10003c9802400036101078907404500725501c030115900c41c0111a540420507002c3c50a0600b08100c035525200f030043e1034a41517681140402552611014065006503d142d110b03203040c03848104450000b070f00c0040c0c3d40c2d003a0203e40207900ca8200a90321800303056a402d000581588800b41c03680c07000d0300202141e86001d07007003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 841516906 1250 841515656 841515671
    0x60302030607020f07240e0f0a0b0301051504080606270a0c09080607022a09010305160b07120311070807110102060a0209030c04020a11160303030c110604021201 71
    0x103030401c0070a8540b480103920086000750b180f64144520343c010145054840041c00442c0802c2607001d42202c600803d02c1210202030803251a10f41c01d5540d0901c2c001d11130600396407294078007002508280250743c0075061002c0480031101d0300000300c50641d60604000c10a41c2c2d101c070700300036600c1d02c0000c003840a4807900004003000048006107034004d10350064003040000120a008005455542c0188e4060b40300006000e045500400c12070301e080281e080f203215140c0f41c0c1200300c4840306408900713900011184000030038000e0114031500071165203160580600c0c0e44a544500f50b0003231000c0030b070280b4811215401d525009a20500c12841109401810038541d13484400642d0802d14059502150b19040c030b40a035a030602c10180c0c042d07401042181000d6007103012135030303484403803d810703018903400940c07001d000d4098081d1003c11052001150700e034091038801e00d001e20300144030480c00700b41080000e00480e07010f845c034404510020320080802d13503241e800700249010f546000000c00c0d580da55a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 841518156 1250 841516906 841516909
    0x120120c042303010b0117040b07050c0a06091b180515040f020c0f070b04091a030a03020d1407171e0301060e0310060303020606060d02040e0a0c110f0d050706060302 73
    0x590300000750b42c038140399010030b032507409040c25038922410240c10404c03131488009019a990000e1394110741c02241054156540417800e41301072081481c1030056110f14904c3c041005016080350030104d2060b0f200200d0b006010320a032030b1141340b60151801d440e954150200b0000071560000d07034000548107164489018040101c0c0c1200c003898229026240c0014001d460590104104407000f82d500c801400041d140003201d13102c50285015521111b901d4851805550000b40e01c0d825105000600741c580c480c1c1d040c54065079582c0200381e0580400c001e1221400000700d80700654a025030010300802a9640c0c1000c410700d02d5010f030006216548e0403045c0003103815180400f650290605444029013400b110040629041c008885006007a003003140500000794041059a0042c906031207480c1c4903503d005a10001c0e00540d041043d41d0380000c01000200f883d41d4200009040c4951a074010403041e81c0030700c503110b01c040700101e81035a010019074044140308400600046029400001b40d094a960 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 841519406 1250 841518156 841518179
    0x101103160504050d0602030f070f0e040c0c0c17100605011b030201182006070f0209070c170d0605030102130608060a1e21051230090120120c04 63
    0x400317450080e0f0100820a03e42d803c0e504160704440181031080c001c56820a00401d202c3e42c5072034050045891315840741c1c09902680001c0030f91075104440c000030a442c1e020381110800051848490380c4500b50300036120728140c1c0b00e50343c01c0e1030313040e500c05182c034a0402104541c241400000c0742103661350300c2e4080301e04611500c85051039105c3e1a0340d00d0f002c8036400140748140d83c101041ca2040301c042041100103540141103032400e5505440c07025440c0e503440019141c550b40e03c00301900300c481310b800c0e044010100100a140302e10032030b00200049034480742494202e0040501b0700b18018845441846514000d202440e40000020900c2c0450381d214955044450250510724400f003491410500c192050a10301e0030565001007196802c2c0201074035410303a50503201c440222007140c0007481d403903032116245403455020b05e031050301c1d6166911913001c0491030200712813076510f80d403a00c8000b1748099540c4101d82e03110400500113a04081d003d0140c0074208001502201582c01d00700310019030002c658 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 841520656 1250 841519406 841519429
    0x610050d11240d060608150a1a0c0303040606030501050c0903100e01020d09030216060e03030f0705010b061b07091a13020712020d03140105150309070e090f10110316050405 76
    0x4140820003614006025002c0320f0042c15182942050715000320300c88e03e61413244021104003a01c0b080a1040260188110f40f050000c0308030b8501000080000303010084e00a18110303071141c0003c1005035200342c050501c6000303d1071916495000980e010600d0480ca0300280001244500010304e010341171441c13442161254141240940c00c108004645840d240780140020f24a40c10004d0403c00b140d4006031b22440b415002541c425404a45181400001d6111080109003d0989550350020119507100511000c0007402d0341d1060500104080c0703071500410481960740800c006000400c5000c0100d10044032212415999017070200d0f50104101060203105484260050001c0040c0c0140c001c0c00d503544001c228071290b22800041085407201e400e1003040c83c1f0302140d850340320b07107031548403a040c07103004e9022000c600100c07024440e80c03690114034280381100b08030445103001d01d002d0300a01a104408080d060b000e070700b8000203668046008040c0d82881c001c5c50700341d00d010340f200c00145008009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 841521906 1250 841520656 841520677
    0x2120715110705030703020105070f0515010909110f031903050c0a0809150906310b09041521230601140102010b0a18021b0610050d1124 60
    0x40d0008400c407000500400000d0402500549105415500080c080d48100701004140040c40c400700c100780030003030002c80180300c000c54010303940c0e5a45d10001c00c09491441d0301640c846406d1000300c185840c3c510390281200304040c0c090a50703103405804402040460450079014004100100e6101d40741c14091046401d10450760f1544468680007407003240740820000754007200c020447c00348280c0d548010794087c1d41c0b8581c041c2014480300300c40119801c0da880300500840f4240c0401042c60240e400242c162074100342c60800a119400348030740c01c41d40c0380e032250748281c11301d140d00854401400148080c3d80c900030740b002d40b0140100e00c0d52100e181c11240315200141c10020047c080c07801200350038504584244000e00615403414001803003594584145e82e2510441340380008544020780603114003121080007034901001c2d448c010398450008841d00200c0a1040a003c100d40c40d09103523503025190002846180308001e07100f0b2140b030352070040c049105041c05994142244000b10000e0144400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 841523156 1250 841521906 841521917
    0xb0a0b0310120507081203042a0314071a36060c0715050f0d20070b04110603011809030504170a05070807060203180619180b09090402120715 62
    0x5000340140c06c014018801d1314032107508000348800700e0740e40c1e00003513900c000c0100d1960041a0325a0140d29040305a0f00040c0701054007420b01c1520031004c181e139000c842040820909002b18800d080080d81301d0803580303101402111014032030000c1503c01014141d001c010100703030300e40c04040000d080da40100c00603240d607902291041c0b00f0cd141025002c45508481d040090501c1d141003010030460042c1c84110100c0c56645415118074604a201030180082c4012116583c40340c0b07050100f1301c3d41e13003114103a6000068905014503400c1100c101da04a031a940c9412424110711000700c000703814030031416410401c0500c80401d10001d04800c503940e8142c150014800215076140c00b90905106602c4090781d6003020030208030060300801210b090f1042051010080303500d001c0011400d008030204621021454070410007015004001116007002d041e2815a9642d40e4035140321340c1d0701c03860341c00c107400080b00e4000c9030042c104040303250b040800180946140070b4072001487d141c50100c4a19400080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 841524406 1250 841523156 841523159
    0x40b0702150c030d0b010f0903111305150f1203040608040f050d09090b04050114010e01050d0f06080f010908180f0d05010203071206030503120711070803090406050102010b0a0b0310120507 83
    0x455920485c00c42c940203007840201070b00c40300d0028280200340d1001038160703050903400080700c1d03440740c8801d860943c140c201004941000c06c0008050001540558020505120a081285070218a43e440c0751070700c100462900c0d0800d8800c55489101410454012003034000b07071000503405000e4166a84840d0b40c2c0d007900b15292a80c41e400303031828a440103025900d4007005000d5021034190000581c0000e0a00c01078181051004a841c0d12414001d40c0101c1d03d840d554140202081d000307a011600c010003242e24500364004050700300e949000f40101200e00402144003400e48014004543d0314000f800d42804800220120314545c1420004480b6079500004011503190040c220807010980c0035010400b0702e0460340d40315a82c0c814440d04400120a03800024a86842620781c401200d50944c2502c00c141d070741d00100b03656900401120343c4202d05000b004604c55205100312103070050010400101742d4134101f0050799903400504410540c0f0648140420400b210b031481311141c40c400e03801000b529 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 841525656 1250 841524406 841524427
    0x4141905060a141014180109061a0a1d01030209030f0a031803051b270f010b09060d0f0e0106030b1602030a08070503060d020d05010c0f14040b0702150c03 68
    0x4407005800f00340f00603008424445140d03041c640740001d80c2c0c46010000d46010300c200c005180d09200112144444800400100d401e079103035000744e41101d010804032045074810400e101d246005054036100042c014120007121450002c011490b06201030400501e000303481d6000c20b04010101006035210341c13116a1207020941c1c480405082d07101c0c1940c1c0040ca440c20755440a48400510071140309540081040b206203503a5014400c3d5560031103501c0610110a00104541170902119800030301811100005007000da410119041c114004041c07910f07240b622410031005001d016901242c0c59611307906900c0c07000d400d00c6810061030081414051600d000703a100481030a0050802e403c540050103801e00e41a044020a074100540f07041064480c0d6030799010070384d40d100398403000e54400303880440c440910030194018a038900d41a92411079a05414030b081d1402c07002141c0b85c40001303004000070050114001c002d0700b480c903c003c19501e810300c1d000b0081d03005501b0010380300306103800004215108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 841526906 1250 841525656 841525661
    0xc04030c0806090d090812030a0f060f170628060905191113120f1703040b07080702060a1d010f14070c150236040b01020609030304141905060a 63
    0xc4e8181d103801c040b01810030445a48a0303411050341800d000020020171202d00c199040b1591408002c0d104000080e0345041410740860f15210791078006128140900009001203907151061001c03411062155808038245420b0307104466002c1101951084042200e843c24080d550064070a0b100b4001c1b9652005a580119004582c03038090004040240d100002800c0300301c0342c04c40700d208851205c480c64a052000d1b5450b40d0080042c0a62000c0c0040c42000c440c103030165000710b01a04060509646200f01680c1c0c45a05641c1e07580568048000202c9040890300101d03003c65000a05008030b0102c40051400c2d200103222442c1e40c180c5030400380043e540442d83d2a5805041403405415036162516035100050301c040316403910f40d40004000113020b0100e4960340e200d0b1014a0024002d00074900d00c482c0c1d007071600c805940708030b08080812849610010f5254003a803002005585561110350703981001c08c00300c80301e1034124010001c0200808170a80c08896009006101038180c610b01003810204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 841528156 1250 841526906 841526923
    0x9030c0708012310050904171201061d030a06020309030d0510050907090e04030c03030b091305100c0203090f0f1207080105070305011202010e2209140a020d06050c04030c080609 78
    0x50f541c1c4408100682603c00c2007400782281d80c2501d0b1103519481c4c50905002d10106460403030b00c0281d0024541e03801e40660b100302c50481c2c14581e1201e0f540c4407411103070501d9483c841031441d8154403602c10708010410a03401140c120703203400112880d000750b0f10001c00503520101c075185003104802c04100040d050400829511100074544001140c1c14001d8240003024003070405000c03c0960100c1c0f100f00750295010440b01000204a040c10b450104042e440d2b410140000b12064050301880403c00001c5008004070400a50003841c1454582c80501c91308410004005134442083d0b2020005901c65500c01e00ca440c000034003a001c41401c00780f00303e0035110060510410189040010421504804850740d542582440c02106a1038250001502c00f6551f10780c0100e045480303650007101c548681d01c001081485503480c200c00680044d4031680743c464010001c0d421403130740248900013503841c0e4001a80080e0400d1094181030f22529451030510064000c01602d0740142c003800203100f0b0030006d008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 841529406 1250 841528156 841528211
    0xf110a0531180b0406091e02040f0e0307020d02040b1c050106060e060f0304150c0309020f0904170d0212070806092a1303020d03171b1209030c070801 66
    0x80160600341c200b07804860074860107446400c400c0c0100701080001d0304101c94080c2c000e03054408180500c10088662038031041c08920072071611650400b080c240340180340c140402c00d4044c0d41445265024031240c02c04010b41241d01035600d00c1680303142d6480a0341902c01d070f1910340000c1daa204c520300e0520b084034440e0304440144001c4980030707507255880c0011a904c403a80c8148041c5c0b04d031180e260172240900c19071595103165003000030b590842e0341c4c10703030000c203500c0e000300c650104443c03a40050110640c0107650140c450300c1b2152122074691901001006d20440c8070b0030062603e0850b010f1030380c40500c10764890000400d030f01d003803242c2c43c9444102c842d0080c0389141030300d040450094440501054101880c6c191640200d035806082d0300c0d03160302000a580140442044103841d10f0010324a02c1125464a00f0640c0003010490714404540701030549200c080486103019508010081042030041140c10b080c4410010070030540401e2000e64000c0000a0012a446c80641009c0f501100d9090481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 841530656 1250 841529406 841529411
    0x50106080a1b0b0304060b011209110411130501050708070c2309070210050603010902030708010f060f0303020a060f2d0c0512010909020a030f03020f190f110a0531 72
    0x3d020040f5500200d98220368132040c009881f04203940141d40040d00b21045841280c90803903064144580b41024008100048504020300c1001510f102c885009209c200b450401280c60180555401440180404e5002d640c05c02d04207201030741d48040d2071100390401c007240601203010389101d0302c4030031300c0e506129001c5900c80141d10b840040250365070004a6286201903d5001049598400394400203510b0b8000d401d0311802c0303884020b083c1c00303000001024001103181a0000481e42044d529450640e0b0f4543d0291041540c0f0b601ea05018183ca040074440d0a070b604d202040e0002d40000902125071580051040400010b41000b821200b05030441c0c0c05003c42007089404040801007410b0658081c1000080c2c004410b0000c1440801c41740c01c01001e5000030707210907080c07580000b071010031420b0160403141e09810302000351944099401c0014680391a141071900061a460001d404080c0c01400e140351329036460740090484801c03d1740e942480b04281000c0c1f5001c0e4080507048425034081c0c04207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 841531906 1250 841530656 841530659
    0x106091103070e060405100c020f010801031a0a0209060a03090c08070b0417070803070f051b06070803190c0e031207020307030321060e1602120a110109050106080a1b 73
    0x41080074840100300c001007298412250303450303903521030a0b10050000a00141070b00205400081d00303400c42d00e00300364800d64042c0c0300380200d580b00320120340c140d903406035004800c80d040307507564520010041c080c15440c0b9000d105420307050b140c0c10084c00450413695408101108103045c0320401041c02d40008034560000c1000b44801443d0204480403910f005081080390920031078164144a44c41c0c1144503180030014008d001e029030789454241c3d581c02002a1242a40038101e03011702c80080429554001405105074404545803402555100c10708803590003e1055004000d81200d42207601c80d404038100c1100349196060810044607980300c10100c5614040d12a000240d80d2fa41611000b4104074264180d201c05c00018115000801e01c0e02c0000c1c41019160701180902100480740b000410708820b203403508103440016903040000c1c4201886240c40c14024007103c3d004500d00341c2d116199224050380c0c00180003441105e00410001001d000001080e1910150b06800058114000c050b000c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 841533156 1250 841531906 841531931
    0x201030c02010e07050d08040b0417060114030d0507034410050409081201090203161e080c2a010605060c06070c0f021210050903071a0a020c071403010609 68
    0x800d1300951384101d0b42540342403100d1a01d840d1a00c075942107203018880c04240002c40281140b101041c8400c100241d480382d0380c86100c070700745a018a030003056040c2d1001d0040b00c0ca0900441c014401385009191003620fa4012180761112440010f440140004280503040001c0e200e00100c4c0d803c010280081c0e1519060900c1d198a06810501403144140d5440c9407040810440108031103101d0001c1d03241030340569645150f40000d4004458030903121203034250b5851110321610110000a070000c0100700740860405044a240100600304606c07844100a5003c19186d04180131169001030300d02c400207000094909420f640442c0e101500034a0b0502c19054108008a0b5a9601582c60301d0031003080d421714100200100004400a9000440809410700008010601ea45150031744c08050006403501810507550b07116045002d0038904007004a946400705031202c20b50088a00b90000d1b04000030500c500b0300f016500c1e80303d2014000003000503e002d05003806250b0007082903035020800300d030402c0b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 841534406 1250 841533156 841533163
    0x28030e030415180311030d030203060d060507050405060f130b030126030d0c0c020a05011b030507020f030105130b060a030809062a03120901050601051905040503060709030201030c02010e 82
    0x1c82e00030112810203000114415034180301c0c106001c55580310b0a0769241840300040004024403400703400754602d4088030900a008403409641e0280c440c82c4800304c1a02c500004010103845d9204000e230403c80000d05a44000281c07100d00915100c0654036401010100750f02c00f0303076038400c0351403010074801040f44850007900400007081c0e224081c0000d80312006440d040d407160886840026280c84000c194030307580699204a203520a4842054003070720388006480d1080303180b907842c500340e24030030f6031030b0002e0b2041002d001030520107020b40580c0c40c08540001d003590030844420b41488181c0300d454052054100380c1039041101555a411002d0840c0c407801c006220700010540070314000240c002603500c100ba401144640750701c86024100c9a00c0307200e603841e0b90004d040c454562a00101168460506124840c09044e058403010303e4103503800f1210359107e0114202c0b405010042c04002100d4509020342e070304c83e0050380d071040c0c0c41d0f034214400502152200036a0303000316894141030402045001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 841535656 1250 841534406 841534409
    0x3240409230a120302030114010306151409151e070c0e0c07020901151d03210f03010e071106040b0601081305070f090c050a0206040b0a1128030e0304 66
    0x22071480007005400607510384415080014000080102000b40760765050340550b0607240300c4401c2450150b8800011400c0e1120b60254040c0041c0e2401d807110441c2c01000321031000c1640f01609410030503003a0000b08030074401029010920800900050218085050741001003500e4054504011b0341e916102001411801901c03008000304010941d41610101507456071917004010404d00e685a110440560308502050307404184084000391802444060308001000040c0090104506402404407415180c410744281c10380300700514038901031340b01c00a60290403d03e0483e40c1500388810020001810350a115074650454024400081d845019003904004240f91000303668590000300b1140c1c03480c4e110000c2061150317110000d803243e424201201214104030040102109032101a00c0074400c881700800141c020300005000555043c04480c3c0001340008d0000308088041d040540c01d03400302d1903000001d07852503d40c0080024001c80c1c0c4c0d400040074a010b209214900040950703d0059 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 841536906 1250 841535656 841535693
    0x207030816110301051915030b04080f090604030f020a0501090e04030e030f0d020f0c0909030a0c030519030b040b06090a05011202120c0307021b0d030e1503240409 72
    0x4081d010301031104260260140c040c0c000c00822140c248401c400804018810401e1042410701c2d6089041d10751010030341040b030b40c005c2d000c0d0755666550340d510046503004552510300341c0c07070030700c15000e01d62241d80103080510310460010703061115600402c03102e01c0040e40068100000305a007800720360b0310402c0c0240c006501d410109010f68080d80003900741080010030002c075115480312000c90a0b40016940712596200060f5160a80040e0034000030982c100c41130240d40e4420402e00011500c00c1d501104418000d142c100e041c80034054451424417030381c908800000380c652280c08590f140a2251001004046880d07a182613491000b0580c005a036119950501c40030768021024640c0341e4049940d00b0203c410a11001e181100c408607180d0401e5034104014401c2416030602c00c01c1d009440c0c012090001c04c1ea0310007075003d03074044400318840c9000a410400035640c44140c24003010285008841030f5502c02e20928241c06854a500740c80b40c3c07024070440c144508500403c1007102c5812141f200c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 841538156 1250 841536906 841536937
    0x2070201090513060b0c03130902031e09070504020a030506010e030703021c0201120c08040302120405011b05032106040e0303040f03050f0f030906040c080a05060c0c010e0708011b02070308 83
    0x600c920002c2c010000340c0d01c06000760700000303036400700d4031b4000c4000e200c99420841c2c064107140d00d03540c003035040b80811100740ca868030400e02c508a06104339860203621601080807548156100c90220781a81c204615040200307441d02c003408400d60300605500c00d0700c00d054004050940c41e5400003070000c010840750b610803448550041003564400e041d120381230702c86500203000307144103113a004001c464201c0d4154014000d040b440f09001500b9022a4100d0740141d60340105c031030501c00390320054000608112100d100800200b40c2c0100210544901039030700d8030342801945811000e10051b1006110801ea280c0c208104000c0020000c00c48d400c0b1443d018a05151169100b0031003403038a12642900351000300380401044608100003c02a124034413641803408065918450b10303648204d240e10061841d000b810028aa24080d10043c03e0000e44800c004190000408007850509025410504c06a51194800345480e510440d140b41440403a05c000d0038110b00d95180c55003a0300030414107141c680b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 841539406 1250 841538156 841538179
    0xf09070303050c0c060c1b0a03172a070e0c040e0112030e0306160e060306030604020f0f280f080d050901030603121106071b020420030106050403060f020702010905 72
    0x840400149031300c41005005c5694406c081e0300e20b81d54401c00d03510100c40350307452190851a01d04020004800300c07544400d00c0221030041444a003516040b2106004d03820f03400f101041000151800c00c10071007070340500a4031203182040d80c01d44085000410b0690150003c0200300f1900101d441d50324110b44112524040c00001c43c582200ca5140c620000e41d071600c07a032005d1168440380b14100e42400c04154552013100d500700001e01c80c160000300c0b22154513030003440003d00541001159090b0880009180070415a0280006849841820703c0c0c40d22042c1e241a21030b01030030205100303801804401d080c20303039611326180e1030a5840c0b244200c1d5034200718010500310540d0b406038000c0e00103554098483c0009844591000740110901d40711041244600000300d001c09000307030940800c400b4106140c0408043c2e0782c0070302000d0880c6441c00c800c07a0b10802c0010f480300c0341748001385000c4d1540e0303a01e242d03995186040180a699003021040c0c003161040145500503a001880b45046030400d481010440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841540656 1250 841539406 841539427
    0x604050d0c030204062310050909060a03170a030f021824041202270a15030b0f040507060318150f15090c020109081b07120c0303080f0907030305 64
    0x40e241c1d64002074006007404030200c2c040600445c030158461007220806403c0000b241000144401c010b001c50200d0010458298503040c942040b0358032030000340c0440c0802c0d5076a6908210f02880ea001803000740000701d4000041ca0381805201e00d0f4080c003a4081d03007040510300514810440a014041c4108202521020701d9642044001075014132000841d448903038403400d040401c0e01c2080200c3c424000c050005190715440000d0624442071001c00d07800c03540ea04032143c8020000750750f19101010400340000001041c43d803005100c1c4851101850a500b81450600d00d84035042d08144107040c01d00310304400880094885455864001e01a4070400000030103090040c100c41451031012400c1c036038070b11000d100801c011400c44400704010005000c01c807604900320b444011307000701820303000c001d030a400c500780364500d0008080100c2a2007011343d03075554036848910b421108448121070303805c081060540045129a20100e00d041441007880d1140205440c1c00705800b00038248403000c54401c0b0074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841541906 1250 841540656 841540673
    0xa2d0c050f0118031a060d0b1b070803040812010b0c06060105280e030f011806020a1e03090614091903030612080408100b06160609062307020105060604050d 69
    0x420301e88250b085900f5440e82002031443c1c80310b080381c600710b00340c0f9030100746103007418404020099000310440300142c03528015114000e01d42c1d1000302503401d040c00f6950100700da080c001c40c080d5100e03040103944e40800d000e8140d01510144c2c08184806070a1101062558001c503080c0d6000d1824030304181c0d920100d024086100320220607080c5407500d03080c2014038154200544400c1060100e00b00d40300455003003120750070380d4028041800e4100101541200040040d0090f02e402129414805064006420f0300b54030707101c07030302178400010741c540a00105001c6544152081d40c0b441d80003a002c42d14011f011690390303000804009503000043c0e841c80081c5442a44080c0241c002d4a80c014076503103490610301000e0b0480d01a5114a0140c08010342443c62648121904e00c000502070500300025958404410035400a05481c09502c070801d48000030540e1003064030001c0500041010408442c03d40880004001c001005581c5850203018642e6545029a0b007201c500311294500741402c1e1810308075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841543156 1250 841541906 841541927
    0x308190c030b041a0319050a081c06050906100507021306080102091906090b07050c040c050c0c09010e2a0a1e0c020d06020903030c0a2d0c050f01 64
    0x829880e120445605551540000d000b071181100e0a0107005403071030351203011254007003d0642c143d12454030041185070041008200d00d0041d01522141d058a8503000c10030740c48404c0d50b40e805800b5103d184002182449101d010b130909580703180e424034102011600130304541c070700d840c280500814100c045507506c51a02000b001800028000320743d840890038044d40010001c54800c443d107505c60325800aa4810510458010380c1c5e56110061500e016001c1c02e41c01107100795640d0054283d184901c0c0c41303034000c01002d0754441d6100c13982ea0a04401c80350030a02d0b8500362500caa1810310040000056000707205402c140c1803008104440500344040444000465a0f80141c0c4400314000742d5081e042180b4405140054a0f41c81499544910842d0180990f0100035840a40f9240000104e1281d602030007010030050201c9103400c920780e8040c0e10700030305640200c0e03402c0c81039100424000c03c5203004101203062031003400c20001090344c410140300303118064107001d09200b88503040035a110b10741702907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841544406 1250 841543156 841543201
    0x304080306060f0d0f0218150a0e030a1e12030b0d062706091202030f0a30090c060201060612091b030501050604050c070b040f02010e03011a04060603060b04030308 72
    0x880c44000601c003000c7d40101003007000b602e4101c0310004042c00c1c445601000388038680485840d1144501c1c0540d0307103000030303269607070180305550030301c00012404400c071804004002480d00070413113280352101c41d103d84883c0e10b400f01420030307000d446240c03a81e09008000c075500100104018014111540c0e22580d00c04800d001e0840020b0840c0c1801300640c024003029000b500c6403240c0d11407505d001e0f40d0700e00c00c492084403145010080c01c03183da4460750310a6826103026102c101d0f210008440c50f0b1780d070b20301d83e402d1006859558500724100204025914028000790000340704451400d40041e01c0c11820070700c007410103170321003040e44100f2212868001c407500400704000415070300c03414658020203046448500451402c000f081080c201041a070b030480358018a100c807166915500c03d10a484020340032414801d0501e40c007601594280a80f0480340d21400303904028000754810001a2442e540c000c0c814180741080c1449812200404c403402c1e0790301800c04174215116050108500003526403c3c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841545656 1250 841544406 841544411
    0x12a0e121501080c030607050412050c060301180f0515040f110703020f0d1d060702042904060b0a14160c060c030201470d030807080c0304080306060f0d 67
    0x45514601d508019068079600f804694481c05804d09043d601c00c3c3c142d40e10b2001c81c4c2c01344010081c85030b8503158055a9071283c000d42c0c100610030400300c2d4850300280c000c4010242945840c0da03145100c0e20650000c090341030000c0c816810062410b1001000c101d980302e004680302c0c1042001a043c82d0005555900c1c2c401c100d41e17940c030483c10000e440700c9078982030b0005070283c80d00e000d016034451044000c4400800034800c8a01c46c4050422200340d000403022600b080d2201c10000046250205130701e10040d2a081905581364403004006c115501600000390245d8144200301d8495840300e515648030842114603030361a40c9944415200c0b11400710000d02001036a0070121344658401d014540f0903219030002e04c0300c3c0301140010082c0034030000320404d0384400d000300d940d0010702104540b0101041d0054049591140c100410741040400400b9804910361100f44101130b80e00c8201554000642c80146003075080a0391964060320014001c68031520b004114402c01c00c1c40d01c412155240200d1404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841546762 1106 841545656 841545673
    0x170c060406110c0315090c12060612151009110306011409011404030803011a070309050405060a150801140301060806010e1b0708040503012a0e12 64
    0x10145100c0c00e0300e40c0d480750b101444101d061007203403002661703a460716426003131402010007126401074142c2c90040c5982140880d05030341011045401d144aa40202c2c1e409180c81001d0070034000d40c124007418001c282c030f0805e0505048548014007400300d1314990701c02344a0fa01003190b800e0f0101727501e09074083c810300600c001440325510504000c00e4807000c80e00c46d584143c00c9508200e82d1307180000010301410b0300310000301d02440b041a00c054a403000301d0f54024805c1042d0310070035008645940215840b83d0360a042d45000d071100150045040ca0104030007002c0444c2807080c02001c4100c0c1d1001a84c0741010f0144400780d9482d100102040d900c0d040c0ca03040100e00c01003070342c0c03250202c001110541e501c0d0b0000400d04140550402c41d281c9090400701401c580520400a540d00c03094424203d8003501507002003540002030801a4080d4846000b0078550482c281800c129070042100 = true := by decide +kernel

theorem cover : BRFrame.Cov 841366906 841546762 := by
  have h0 := BRFrame.cov_init 841366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841366906 ≤ n) (h2 : n < 841546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
