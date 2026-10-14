-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:45:44.742133+00:00
-- url     : https://prove2.me/submissions/2e3b4457-0b0a-408f-bdfb-4c59883c9cc3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250539568 ≤ n < 250719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250540818 1250 250539568 250539581
    0xa03202203021c171201030f140307032d090b09060d0c091a03010503070902030a0f050c0d060e010b031b07060623030303130b0601022503111c0204 65
    0x405142240c15640b540081d600401c0c00c0c21021400703c61143d401c0c20700000c50340c40c0c003942501800985c42d11700300d11550784c0c104c641400005c2c41c820182190909021a0000c0c2c041c1c00c00e4101c0481c1c0ea10032007802d0280625400c06255005400aa00b50044050502c841e41a04415689814072041e090104240d10b41d08a0040c81c2e8004406008100c004500c1c1d00030344010742180d486800140b0708001e0381c2e40c842c810200b040d10103400100700401c0031307031000501581214850140180c0341e44a40106c00040d200c28050791008a09000c20312104032420340c02050070b00403c64040180950b5400844400c2c5024450010040000c1c800102d00d40f40d60300b030700020386c540c201a0b10316107036240d60b800080302c510b50800c041c04803074003d921800902d0341c000c1f890000400c0f030045007503180c800024880300380f2140004005085240c00705019074001c1100720214810a00d85083c0580c4e0680143d02d407021030b100030b84800001060000060a100c2d9010414005804032500980c21580030321024081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250542068 1250 250540818 250540867
    0xa060e0906211b010e010513060c0c05030102030403020d020610030201022808160213060806040201140f04060201050a0c1106010306090507170c010207060203040513050414030f0a0320 81
    0x34200703410302020b00705004036188094100682284a4182c0b03000500205254804506116040080b40e19409078417104100f11003041c030740301100c40000c0c6815030200050380d200341c1d090b600110500003090740201d001149003070b86a0868403144d8891184040345001440301902503009149200b845a4543c0120038580030064109885084076603100d5015074050121101f80c40c1c4003041c418210302d018010f0345000340e0303940f01c188502410800703aa611280c024000a0500200610001d82110107405480705c210300700120740e440c0c1d5035500b4042d001e04422510303040c546181200306904503025480380030118070080700602d400d0b330855075502c0c000e042c400d02c140c800d0720810740e0015604000380b00658810300210081c1520b19503220000e46440c40513040304086d90800d001c00c2c4903d880e20314124074000e041c52000f04040d04c445c00c0840c0c004e82c0d0749050068901000810080800f40e14008040c00c00c3d01f507400b000b061811403001e030600e40311700c1d940011500c41008541c2110945c041c5482c0d0107403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250543318 1250 250542068 250542109
    0xa1503021e1801080c0d180c08070608090105010e070e040f1a010e03010608071512110405030f0607021b0402040e04030e10030b15282007030507030b07090e01090504020a060e0906 79
    0x100e203884881d00c040441d4400116603204031f50611800e80d10440e103a3700074400c0c00092010b0b50505890717503540b50b4001d082d0820420503904ca42d0460350f0b60380180d041582034001c2000b0700c4000d51a1064080400030860307000c6200c140030b1800504052142c43c0441d19090080e102132800e0a4405c00280c00041000040080c5500f84400c00c155900c1980b00003860144655550f070704d800b040c1410304800403e034018542020302000405500424135a4400c2c0028564401c810301100c0020000d0040381c02c16071901800c601040b08242e000203010010260858491031000d110308021801c3d5042c15843da42c03c80d2102c0c03545001a500034014100040c00861410140040d204401c0b01d000403101840300000e02c044140c84038808110345030041c1840100250541504580314179686035102d00c002440109034a0014003442e1040900c54060301c2045040001d82d40d45d554038801900f07080e0350980c4654140800090407a00440e407004417110090042c010a560711400c000803022000c0440940c607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250544568 1250 250543318 250543361
    0x605090610081207030e2814010807170619140f0d081225030c030608070302030a02102708010605091e04060e10061a090a1503021e1801080c0d 63
    0x41c903030b40c501c801f43c801c441709100d0180c0c03078880c1d552408902d0440407410301c2001c01c01e04c40c0207a400030700d24051301e80c04040903030940c480501150008485808007800d1001007400450000c1d1420944141d08608483c1c0d2940c40b0a060104004100340200050540a08101c0e03038110360816a00550700403003946100b800c45200a03045420444900b2406001071360701c1481030215501849908050f24010006180042c01c50307001c25a00c4011b40e034007034402e0a80c00491000349100311300070a001d0801c1040183d070180c0e0714287d003401d4440c50003900165400c0610100b00e6003400308606108050001080c8814200441da0741c0440b0300180082e141103450b441488921001000304d1003080711500310008440e482d04d00c50f40c4851404003458908450104200010350b03544200721010703a020440980b108101c01c41c81500244100d045040c0c41d514080a40120800000060a80045103d40000480900d2801128401c00481d03054100350020300521240c44035960002001207441a030768080c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250545818 1250 250544568 250544599
    0xe07080403020c0d030c151a1c02031e01061509090e010e01021305040e030405150d06050d0821060a0b0a030906020301080105040c14010210090f0605090610081207030e 74
    0x89081509080c2d0100b040950400104041c520034003041c03080c410810403102c00c00c50b010750b103230f10a486442403003940c0317803440020910144001e80a0b425401021609215001001d00388030409002482071a5480d2a1000650710303800032201181c600c0c04da0701c03a12482d0504428200414074250000f00d01c1d9a500d0303c0007040c0c41d092008041039030341301901040c0380e1300d400308110030b980080002c0049038000780410801525100302880c581144800340e9516000408020401405030f81d210550101c84141000d041c4480391004001c64000d500074140c0030319401000110b0001c0036617010340c01280301d0b081004004d42d501c0103090343c4102c904e0085010016600c80d82c081c3e800a820510380b17a5510810300080040c2c81c94214000e040a0b2080c0d00080344880010b52540f054503001070034603403240c01d12010860003d400d250401d51040b02084035040c020341c2681d07a89012a100c0c4540103840602040740300e4001400009034081e040d0f214a0005d055070201c880c0c3c481d45a240360172048200701070340c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250547068 1250 250545818 250545829
    0xa0e0405100c09090608120301090902030a0506150f040b0109051207050607050d0305060d0f06020a0507050d0807021905030301090b040213080a020a0f030b06091f030b1e010e07080403020c 83
    0xc2c0d60341c050703480c80c058a0900c0b26001c225000340d80069075962206d030000402040b0301c0d003600c2c1100c0d83ca00700000c00314042c0c004242003150300c20f001403940c060f41c400c11000090805507507801a800352945880d280342801848221011071001c0c0d800708001060420403850040e0882d5074210120050780c60031940e500c0403641c140c1103c0c4044802d900102e40c80084640c0c14424182c2c090b4048400e00368548481e264035039810319514000e06107030303000101070b00c040d4001c1045030b51142d444412141125080c043c003c221100540d0035900500601d201c100c0e5114003111041c00c042e4106001e945181d103440300500c01404174240081d0401c6d0248102c00c40e40b000340000c200241000005401a2341701c13481080030300c04042d009032094141480c41480410003c1c072100b0b910190541d04071906854000a08400001c100001d501904c00e46401004002e51089a0380c001d003103410000c0344481a0060714140c0402c00d00480544440a00000390160302c00d102d01a0428024010b82e484091740d000801e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250548318 1250 250547068 250547081
    0x270c0d140a050a02040b041a120414060106080105010f030207020d0f050a05280206130b0d0902010e1c0b0403050c0601061706010903170f0903030a0207081603020a0e040510 76
    0x4180140c11040059140e290300406a003c080410210300c0c15040c00480901c900450080c2c0c110340e442e8811012030070076008212aa030f0002c404e00c00f682885d0900c0c0c0381e2900309580032070305c106008100001629601480706c05040c2d40d0141c440c000d5a0800c400102d00a402c202000e90703020a0f0861000081142e41440b05241d0780944c001e060340030800c0c100103143c400342100129103928a01051000390b0640368202c10601d40c112103003581c441c00510391040f07035420b0341c10044102e00000742c0d150916408d94420040c1034402e0b20303814070184100b810002c500e03501d0059150300f08042180180090305540c5050303442072182c140107050030304504055241a40903081040890040c4110b05200707018150f101d0350104003403800c0d125260559440311070400b442004440080000715190700501001c0060712221100030301165112844008000d50703551403031181e103005001d06104a1400703030b0704034035403800e41c0e4001d0802c4110902c2c00601c1c0c00e40450081c81612a4012440c00c00030a110714003861 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250549568 1250 250548318 250548341
    0x60504061b0206100e07020c0a0620070506190c080310031a100b0d020d1107020f0108090a0209040201260f06060a08060f030705030d050403060506270c0d 68
    0x581100c0d1442250030785030201015401d66000d40d0130401c802807200410b805803001c01e00c20b000c10307845844041c1e2400b407a0001030f40e0f12050324070010501651160781101c0c40083c0b03e0b07080310860049030030b0360340710720841c05840d1f0402c0c0100f00307000410505001d50882c014040c500b0230323011080381c1c6842e141ca4000b0354140c0c4040314040810414400019004038915415810040071401c089104100c5410f951051070041400884c0c007001c02c4100f9410b80e004803040b074105100c501041200200590700c40c0104920410301c07100300101d030394800c4441900c14072a81d0f00400d0340301c2d070075003c000310f101009008a040043d4000151040c0594082e80301c6961350400202c0845c6c20070042c0c48a203544001d013581d000b0345007807001640301c40d842000913810610503540001c2028251010909042c5503400041d0944240c01c81d040c220355200d4000c0080b2030062408101c903458034010801902d6454008400081c06c0304d0840d12240d004165003034000c403800c00c2c014a01543c00c80c101054815a4503036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250550818 1250 250549568 250549571
    0x40615020a0611131e0905280b1005040306050106021c030b1903051f0c021b03030d0e070e0c0403030f030216060609021206180103030c080f030f1905070504060e0d06050406 76
    0x20901c0c05c0c400b0300c0c900a48411842401640740c450911340341c5040300800d44462012032803210390502c9a95104100d0450060003060a11800303620240c25075201d84001c54100d468031000107600d520201c0d145692000c2003000300140222000100c0c00b40802040e60790340040c01e0454402176040c618000307801540706002038210284900c8603da028081084d6900030b03d070074003c8550600e640424004110000390505a8a41103104e0200c1d2640c06401c01c40e040c840d10f80003181c8203400c0c001440340b0803600030b82020185691102c4289000c1e000d10b100003004124400941c0483d0b42c000c0d005001e00f4000f03940552401c04542e1254010341d034039540006011076000600301c521554044860758010020707220341c0d9288121086441101324148030203403c001001c42d41e1420042c9010813504021903920015450b824150300301c42c071030b06040e00c2105140380c2e0a0b0010142075107a00604d40b043e200b50300c0300d9041900d000c505403000105200b0b1940d020465000010019101e8450580034138040d031030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250552068 1250 250550818 250550849
    0x608060709050108012105010207060b15120c030703091502090a0f05060d05071106070e130e06010b18060d020a080609090a020d0c05030a11040615020a061113 70
    0x5820544054000820804041c009000c1640c020401030704440382510b01081d48a2100407805e004001560024029400001c0c0d110134041b070358002070200b060448485460704511940b083da2440703005403c108508880c80003540200e58034020b16031041d81428041101945581d03903c0d040c3e202045074400035940400c031000035013490041403015240e9194401c400a0601d0001640307401180840c0d036000e0703121000258032074401c0308000102d0314000200c0b070790341c14412005000e60003260070743c134050301c401c0605448000b01d0b4020700800090a6000c2c0480da400c1c4200f0004980c400910340d07035050420100180d0503241e240085c406c901e606900182c40364042d00c8001d10410010300401d1107498598113006591101207080c120141d8111850031401c220347c600740c600d5001940c042540341c040d0700701a80a00c4000c011407060094121400c004071612082c04e0719030209428190340042e486050840300166007030b80110400e40906400a013000d20103032603c001e100e2039030070044900e0311120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250553318 1250 250552068 250552079
    0x309030b100b090d050307080c01020d0f02090f240408010e010b010905130f06090207030c02010e06030720120c0304080106060309110f1206270a121101060e01060306 73
    0x20340c0340c12071220005801103514200c81c00b10750340142c480c09072003aa04944500f08120b400c1003211145580300e9125525140c1101c8114000d4002058915806003041a4501c9105451003241e500903401001025000c40340b0b070a014113203d403d158040d401a0888401c101417400030042c000400c0c00000200348030540c00d801609407034144030b07181d040c411649018402542c9102046054811090000031188041c42c64440034240560000000303d100080321014103a105103040103040c000e803103180110445409000403071104680010002d0f00d001c0c040c01081d04020101c4a40d01ca10900300c8100c94407440400d0400d0b0702400305414107034030016040004040a00075000142680d08003000841c103541c43c2c40114803100c1030f00510071014201c034480710b9078803d8254046030a03e01c0458803280743c003c02004504d0000ca1500c0300200c0004070202c0085000640300f03884035401800c0007101c42c11503105541c4401c03c1c200c81015135407101804154000c800b00340754020000e643d0041020307460314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250554568 1250 250553318 250553333
    0x20c070f0506090d030f0c020d08030618010e0109020a0c05030408010504021906050f0705030d141506040308040512030d151701140612030f0304080414031504060f18030903 76
    0x1948498020b2205000307051043d514400c0c09441150036007003050800c00b85100440725245404d03802503010b410000c21b841402000401ba51080600f034500c1607400300003810303030b03141c00d01c09100303400d1001c5c007040c01480f0b80700d4503030041e0410076540d0401540da48400d40d04c6508641090b000400145c1d510b81c200000e524202401c442180b0f2806000c020480c14440001c149124183e440d4078180d900088600410804104462030f09275070311000c0000d010f031004c00140103042075070b01c0702400c0e03044e061b101001e140034000c0f1022a503201040c0340c541460681406140340001440044a001c01e100034111441d040c011910352900f5000d11039003403403c003025094014012451000181c0c0740610703035001041405101074100c5801c56008180c207034410b5000386984685108090108404801e04c001c0101c04005041668601c8500c039031108019428155a1000b0f103d81c5d481e414000408100441d0a42d4062101c0007145003020070b046079034082c5050302e020102c0d001c13000942004402c10034445503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250555818 1250 250554568 250554599
    0x6080f0a080a022e110f180d0203060a0f06140607020d0c080d09091a09040209040512040f05030d030216080c0c1f021b0a0e101203201204090903030f020c07 69
    0x1802c1075901b403c078400103541050144030709580c1d4042400482c002e1554500c29603501e0680d006086881500c1c24000b150b001c0c00316800b0b030168079401c0807004a0705425009205891a9002d4203490500e000e41d0208020aa103286007903a200c4440c00011512070828801c0c100701041d1510381c080407074580940c140c01c44203000e006030315004001c0520fa400d682c3e024a20394121b501180e01400c0c41d100c50820724204011100e05040040c07000400048160801c9031040803242e003101600e607000d03401030003507043e4400c0b01a00d258646c0c2c080140c100140d070400282c402c0300000c2013200c5c00c030800c05000c100c604088880074050880100340c07400005030304100c80b0701809a4104010b59010450000c00c2c0160800e020749502240640c0004100b081d400100b04010b04017490303c0d602c840010306001d403034182d40b040041a44100e4403e89469600d0004142c100d121640c04403d28051030701001c0341c001d0940541c04c4003015218952a08400000e00140c0000b040b041d025090702803a01c050350840040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250557068 1250 250555818 250555841
    0x50307020d0c0803131b06020714090403020d080c040e01062a200d06060b0c07090203070507110117250c0503120709030506010608070306080f0a080a022e 68
    0x50a0700c00d00001c07001000d5079008121010407441400c1c8134501a00015006c810185584180201c0050b0716680082c0c8201100c14241c610300d08052000244214503004841c042c01682c041100c9100e40c40c40341c00b000d0f900501c80c40c0300b281401d46890320100d40800a0703002c180007844486900d290903030640645007086148104091441800356146110340d070141b800c6c2c013107030312000340e10380881d440c4e45484403205507011004001030380c0c443e883c90500d40c0080680607418810f1203808240d080d00742c42101d0040c4070903102c20f400c0c8507240e80d8100900c8545081130341000748074141c01c071014182550303d40c0a0254891068103080301c0116441580e0a5904c400080040403c2803002064000c030445007130804d403940122460f52008025508140260706c024101d1103044000504c881d07100c022540107400a50b024030005a6491056a032503604154908494002c0c0c1c1444c80054400c0d130090112062500603501e01020840c200c00c0002e0520450315510407100e1004000c00c106482074010342c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250558318 1250 250557068 250557077
    0x3020307090b1c02030601030222030302060601020d0914040f050f18010b0a03060b21150703050c0d0515040c050702040507020624030a0609031205160212220303050307020d 76
    0x1070a140d40a450fa509032140703505003a030f0010200d8139591082c0c04503610044040c409038040b0100a4400c071a0f408039100a07401070113500045602036201052102041c00ca9698400d0a07904103801003490f210401c00059000d41d490116a401c02100c4c040c10f40325520f024146081898100b191544044c141d07450711801da45002d044501d076954820041c005e5907082000010240100b0b40400d00d03c0d000c0c0a0280c2c61102806c5550706000030020380c0e900100c0720811001d0f156200c00744154142c0c0c000b40c2e000c0c85544000c0c03101034084070844d84081c0c1e1240d5099400082942400042022601801306a5000607400918242035081501940b0b802542610003003090f481e2000c0c03040c0340700c2050b4140b038030341c001d5245034600a9981088540d00650b082541042599040e160240c00d000040001c1151130381084000b603807001c4801e000c05000b9a26401030b06080540707026a207042d500c005840d01000d90603055809060400b14044406584203031600c0e50381c2e003840035001e494085440328000800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250559568 1250 250558318 250558327
    0x515180108510f12030a05161b0303030614011d0307032102010e03090d030c030e09070c0210030902100302071704060c0c090b030d050d0b0909010c120509060f13080a03020307090b 79
    0x40c070000044442001b01480c125450f10a902d1040380ca200d0f4018004e4800840e00410b1103001c108101c21000f06c07442920108445a42c8180b4407202641a1000701c1c0811003c411010081950903605842200001c0c151540c903074407503640c0364a0a000c0c080001d01c440c01c00401441c1590244a1513011903061401076041c604854001103008600703007401410800e00c0520300e000c06000e08500f030a268401040c2890514010800402d03401c1c400000341d1003228160059840300340280b02d000406900a404a0a20300d00c0f400180c000c0e5000c0102281c000002003401591903c4000241000e0001c5a460345d44000d0141442e0104c44c2c1d0a0704008402494030321800d81954000400003424040c0e42070080e00c651013940d8400090014440c0070707800100d0f940c104403102c2d0040d130010820482e5078a4a040d1b80d2078501d50307042190b070203e686519561102e00490151505603002d1a44603001c02d5140c0c07070381c40c15030359180b0325600a040024007003a004814001e0f4907401403551030103048d007480b105090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250560818 1250 250559568 250559599
    0x10506090d212006150303040b0c0a020a120f082d030906011502031c06080604060c0305070201021204080c1f02070506060f01021c03060515180108510f 67
    0x1da000182030352084111710350800c3d64540342442618020008085601d49510f1190810354841c0e650b402c0492242c00c03441004030b030b101050510001d00302c0d08480700c611010482da0b5125107503401103044100003d6180c030b10039507825802d0030040c0c0d80b0301195441510703420244040f47c03400390184c20a554014400c0300b15105c0f2540002a1484c441244148404041084941c1c00082500f03422600442c002c100c20030003880443e80010f1a50011903404202656958404908078090700c001455500380c00340200c3e01080c80c2d600a800307003e003164251121700348207503480c402d41c44424100442d03d47c0c010034403405100c0c1c14001d5640c0118244d41c1050400e200b50300003500c0348000c56460000c260012644440d8911075400040074060207082c0340800098030420301d9050f00540e819075050311040e14110400c4d44144d00c41401240360000040840420b4543c40c40c0e42c43d011502d04442e01c0ca02d0a003070340e00c095106202822214051084100b4400407000d001c08422080d1902e80908040801d2002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250562068 1250 250560818 250560823
    0x6051c030203030a0c0302070204050f0f070f0c030507020310020714150708040209090a1509061802010e09091002040e0121120f0c0212010203090d0215010506090d2120 74
    0x4d000d92150000140c900303800000390020f005040019400515100403c89940400c2561324000c802c501e030564000ea0322043d0403515110391306442c200091500702d407000082e000d00040c0500e07510050075140c00390728009095040340c010442c01e0320360792404668010b149005201c3c01c41d0003155090111020314080c54040c28008001e08000e0241400c0e40010f02610340c203110303a440316648105a0b400540340c800602e400b43c4183d00060311414581410360302c0e01c1c0301e031308044000d10798107850701000e0000384070400040788001050121140143e640041e01c0311203e100810151954581016030340d410071001803e02e041c11411000841504005640890b0304a100c160820141e468a10000d48401d00220f510404c2414020340003c0d02c20b001d00b2140c401074016511440900044450015103008106da94110340d004560074802900c00501c03950a00030024007044c24064003210100d80c0341c0c0c1c4d4420f104145072030300b40d501d500d95082c050300403940480a1100241c00035858000f10100200654 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250563318 1250 250562068 250562071
    0x140702010930030f030c0206130204110d05190e0105040c0306021c0509030414030a080d0b0f03030a09090c030b03070e041e0609021014120606091306051c03020303 72
    0x6140803550105290001c60180c20101d0020060b01c0c070081c501c4614000d001c06003046840000b09040c0040108400c0c40020010310501d0101c40310014940c2d20b40034000100704000302084600c50422407218036410794080c2c0c9000c0c01a0b802c654002c00101d21411044540e18208030045034140020300002c120700c0400c82c000c0c2ea810010060350395080c0c4207410310310258032000307540190401b0100301c0c4482021005c1c0c811156881c040038131b1513004104140d264401f0311402003140780e06100ca070304e0441c4140d00252030940301407c5c84203018075502c0001e00d103400034803050300010800c14040c45614042d0040746216006420240042c01c01070b40000e480d41d1140c00346040b80c415030000102401007480c00d11400e00054200c80c60303041c00030b08081d00600a049001da0040b02d030500326507011481381200b070707015091500304c45040603590300c0310040c903400140049500c43e0303042c030015180744c1d60a10080d0102441c0c1400041d41ca02d05410700003038000045200010f000941c14007004640c0100449 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250564568 1250 250563318 250563329
    0x80a021905040606080a0605030a080f0904090803160e01020d050702090603070509040c0305190f03030b18181002090109050613120b0702100504050c06090a0911040302011407020109 80
    0x1604000c40d010320100900306964001c56005040c440001030340c54111031504c0c06031444600c1803141a4503402819941d003840ea2009040c01e00c100541d0034070342074240c00b0f450703884030080000c20440750a031200d245070303003040d00c810030460040000b41e18915004003440049010a0001d05001420044040e080e4020800080d001d100364100082482d502030023800060f040050151000e400d00d03040049410362a0300046a49121310150744207028070b01030707003000790aa100c410000c0344941c0c2e5804401912403084e03207035081a518121000048410139006105022140117201c0080c4501032981c50b054404d260034440e90320410540c592640d00544c05001e03200b058510964400980c000114840c0300340e80301808849410011800700910350021070f0080203240d0855510540701100d078000c4810950340204168080c0da1140034904090015054030038004140c200031740c1d903403000d81003a00c284c003508100c1c54900140070b008540c0c100c0071601c510304000001608040c01d80d80040c110a201b800798 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250565818 1250 250564568 250564579
    0x9010b0a020c0a090915020702090a0e0a061a0a05220e030c03040306020910110c1212070b0405061f0b090f04021318090506040b040503071b061404080a02 68
    0x16011028002c00190051000180240c0009542ea2a10000428014208480d41c070b50f60110100100114025110200d030010036503032031070300c0380c5040d1710091550314180300c51409420458030100d040ca20504030794240d50800c81403403032503903c01c2088602c00c580010f2310800c02ea4a01c0e499803170301101298119124240700082c460051040c1c80c1c80e41c000c050280600d407000040c00700411940f5000f82400d550181c8890f01200c00102081c2c6007254134204000c00d5500c480310b00304030b92034545044205503040c1415114001c401071562a055800200240c94204401041c44100082044041c0e40070340b1070fa43c1e40695003000e0310714044645851090b4151000c0100704881113030f8031400f504001101c000e001f1940c4c2c2118000909010070035108001c2d41c203144078034514031900d2a0180e80d40c3d41d64000c01504180d662603a5030400c0c0c3d4805081036600d84014811900082d8001054020b400140c1011074603880ca0b00038006c05500b2241c45001c803108081c031013000704910000d029400c80354115003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250567068 1250 250565818 250565827
    0x40e04080310050604030620091c081e030f0a02090916050d02030109050a110901020316060204030506010602030c010f3b10020a180b0405130e060711010b010e09010b 73
    0x142d5040e0408907004160310050015001007000f2036580840c0030001c4800c0d50b60748065111260320940c1c0a45101030740c0129100c05081508010040b00003019031080403130b00d04100c2c200e4103004454194130100c10700c070f02001040c0086408400348180d4443c9581c50250b20340315000000c80d1030354001402818281d00014401c0400c240608250390b944101c07694215180d696920070400900000c0d00c1c0709207030a103001030301135045448008440c1495010b800461a280c2082c20000d8bd80006040c252281d540c24000403001507010300007140204215401140c071920b0750045907084a03501a10301206a151082d04082c40c8900c0480c1d010342882010034003007418007480d010101c0c8044061009440c0a4815802c01ca80429070282c01c0301600d558810b2000050084842c0c5548502e00907150003103010700080016182983c501481c4622000000c00e1a800c4121880e24140080c0c0d60800820411078810180c8802481403a45040c1700f4600454440000008a01e4881041c01052a507100006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250568318 1250 250567068 250567081
    0x4050a02030408040e100504050f0106030b090c0307050c0a020604030303141807210605091617030d020310030f050a1e023a05030901110f07180b1e040f02040e040803 73
    0x14030100104005401071110345004ad04a04c2480424010440401d2810145100908200e00a00c0c4600d001c00e1127145151074080b016502900444540c0c42103100f120018801038071500c0140c002140b080c1c9000c510200c9200825086a1009042d82c2c4244840b44405020340c80001c0d5090889000e003046205070740d50341c00841e1902d81c100d0030280c481d41c100700511038001000140304040c2403500c072600c420b10703840f81044041c00214661844280c0d0003031004800071142c2e58000c6070006d12841481212980d40e42d0f580040d060f003420265450340110a9090a00000d516400c4500051010034001c40b00d141c0e0000c0e1040301c000340c1103040c09107403004000b509142d2546620b042da0483d50550010034962038456500c0e4403070054030340002c540c8080c1c1004502c002583c03a00c6190307107002070072280d41800c0c400010b2421032038261440c0350300c1d0a18142c06480c1c54000030305180c203800d01c40a44041c014148402d8403405140b4800c2684100410000c5505040c1019041980100c513296a0344424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250569568 1250 250568318 250568341
    0x60209060f0705070302030706110a11010c200a05010e030a060c09080a060207170705120702011709030d060522050c09040c120e0109210908010e030904050a02030408040e 75
    0x403981c90000c51000140001480f80003e5110f045900c01c408031030449031a000c2c116880c15403102c01c1c4e42c00d5800105046e0006690111003040340406151900100140d1740310340004115400003c00c0300e01e1941664611800c14801d440050102820004000301ca0440465a241d04070007001c0c0500d992803000079983d51103079042900600305201159034000302070410070000d6020010844400e01a8041d800038000d25000352011140c001000d06111001c03100749050301d0348a40d0007203040000707240344210145c0c8200c100c6030185440200560710f0700d001c40c20b10400c45049800c01407262224260003820305215802208c00340d480000302062a454a4121040c01d0007148002da030f20a042640110200ea0300c500340e905c03840d00c540e105002c0b821200048500301c442c11500500f07140c000c0a07201d6000d80c14440c105004020310b25202d01c101d507a40b085d4508544481e11203400c0d03504000303841881d40ca00341c022190020030142085245080c2642c54540c1b03442180b14000e800c0c0d120000046c600c580c4c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250570818 1250 250569568 250569577
    0x5070308071805030f10050f010e0402061b0d0305010623030604021606020a02150f06060a08041118061207050a140604091e0c0305060904020103051503160e0108160306020906 77
    0x1074122020340f900e013240300b920f9048029652409516207400241c120b06103250040c10ac80c4045510281c940302d540038050f4941c8030040e6400103114081c56180302240070801d100724417005540000e040d5050110080081140121480d010226030306210b4003032007424122078101d841104c0050740c0b40100089000301c1d1118280c0504110301c0851104696500070480402c0c0d08000c0400c0e8501c0e540d0011f00000ea500d00b80d40c1d00303030024424040400761a01501c081c54009000f02c03104281e080d0001d0000780c3d07184101c4d001c20309400f508030500a2504110304070700403083e003a2000c0c110a500381808a003c41074188250052031ba20ba800c3c8a8858554000304e40107400c01c0d50382032118094441101780804000e182d5800002e25004c00302c04001c1c401d00c00d144c06070340014840c1c2115150350700110f02410b03000d041c500c45d00101b031110742c407607a40410400c02c20781d0013510744250062906000d003c000c1016405032031a5003000c9940398504429800b8041038030340c449801070300c41201e9404188a03009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250572068 1250 250570818 250570829
    0x603010b1e01091a0a020601061407020103110714011b020d0206040b040c0e100501021e060601110f010c020f0715080c0a02030409111206100c0803040f05030a0915050703080718 78
    0x10240c1c0407000002c6104024205c18409070220b8a060b40c0e254812241a452540300100d001c0c03091040c0d9005612039000030410b6400300c0c001764204041600c800c015401d00c0c000c1c18141d40e5403108a03010804041c00c0145509402c1d002402098150001c06501d60100510040191310114001010801c10045000180c48500988017492808040c003500c41c07845402024090300c1003040030510a405d880201002036001c402911113601c1d05001903515580d00d15403480b241c05255111a800c2c4000d00c25042d87e081c0c194000e2654502860b001c0f81008509e422440101d060096290141600b00d03000300d03007214402c12204d60303440d40c150080b070540c003070754201c10142402c1900c181140119107018254480c895400c0030a647c80748010040d4000301c0c1202800405c100c016044007089020018660241c000d0401c0c105203651a41c4284c15503001c1500358003c00d10842003840801d0510b02c15115001a50402918010460310b0281c40c004000b4114820001d8841104078041c401a564000910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250573318 1250 250572068 250572089
    0x30705032706040f0e04050a0803130b090c0d031d09070801090518060c0c1504030810330221030108010e061603050601020a0b0405060f0603010b1e0109 67
    0x6030380d60030315895071075015407440410001012207450700c0400c0703404480070b039401585002d2800e014158410401071090b9450b0152044101c08188114002d5100e04042c010350110f0b100185003a0700c0ca11005040d0b03000c02d81c400500184181c45a200c2c1da1201600f50800e62184510103c1d02c864404000d541160001410820701401c01c0e0401d11340c0c0d059803020002441203a9400c030307000c010180e01a0020030303203a1051011840302e010400087c80e0564280d420340718003005103290080803003015103045001495080402528001e225846005010314880845525913280c41280031000d401808010040c801c040429402e4001c0091400c0e12507032078420514540303042e6102a29420034410900d032035003444140b0603907100100713615114181c04006080190f46942040b8002d060040003541544944608440816070303c01d51244102d2050009007040c0c0307003d4118000e070481c054407070b0780680e041c08c203050101ea8520300d050a00caa420700c1008418104403004851220f0190b01031940308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250574568 1250 250573318 250573327
    0x161a07062c030912010e0a0b07090924080604051002030c1216020d0f17090f0f0a030909140402040504020310140f01140a03030e030109060c1101050601090f0501080903070503 77
    0x7540071000c0c200311030007101e0001e1303d4101c1807001c44c241d40c0c840440340596080700c868040099000c880e0650417207540d1070310310491600c1e00341356030844d5218001d206800300c2484003c1030701010aa03640c0003500002d4041d18580c1407941d50f2598032a1100b80c5078210301d401000080300d80b90000140c415a110082552001d42406085864a00341d005120070040c0556070310090074078000d00040c0701042183d80c51083d6000340b0740000e01c118502810112a6004030200040200010059030b00300300005d001518268680d403030058003400159101701441c0c0e042906010f9035900d40345c60a80c0c06038040d100840e0720751b590301c0000c0c10311078000700c2d90748024684015500005a420f2a892040103940a8a0042d9803030319040904000340300310b019440108070a050000900c1031398140c44810010b0700200f030a003440d5a543c800c2c1c80d007080e100030019203100b0520302420b10034017802d40c00c42400c1c00d010140c64100206500310b5544c0d801450705102d080030120340340080030011510046e42100682c1c4c0c47c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250575818 1250 250574568 250574651
    0x2030a150e060f0405070905010305041112030301060207090c09060c0f06151403060417130506040303050c1009030905100c0c0905010e090607020703030819050108161a0706 76
    0x18a20700b07540c0b4501071607a902034203a060810340300e218091412601c42c280c00501d000011005040000c1046900c60742c1d881d9542203540340c840503200000c0700c0030040c40d1a03604000000f445d00761142e004c03229013800e01c1d000d40c1910740c100403040c05803187d074a07241100d0369090400040c04601a40c009207070524003031415601601000b1b081040d50741d242d04841251400d80e040503690401501c01400c4101c4803007107000c0075a40c2c01d000b000a0800d03c010b088072590388100060040c0c005030f006602203180014440030012040c00848a202c41d50785080012a4036502c006000031024010756002d21030307528084040714003e40c01004036681c000555410309880d41c1c80b20f0302502f428070a400c9140d8011021440f00b070804640203100340190f074020020b040c659241103520040c050f285040c0112500401c24848a560089d40c0c06841200003c20042030020100000349142d540071046800707080a803019121580021640c025400440100c0c0e15214403d107020005ca0500303001d580c040355140f10001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250577068 1250 250575818 250575839
    0x14010e0d11010b040207050601090e0f0607020a0308070c0f032a0f060c020d051213020d0f0c0501020a0818010e0a090e0c060325031104081c09061202030a15 69
    0x403640e001c02400103080361400d1009038000c40700020030300c0e0030030300041c4030072441a440007242642ca68105c60813031450030305076401d0110a59031480180c00c00784150060540001c4c0082d000b24091601910401203500c032850300404000b4010100035000422182c20103007074914951104c08002040700051031440c104420461200c4112885420880000c4409001250b05084152a92520b900c1c00380c00d010001d00648000b442c0e0450f003004c1e00554405a10f601028241e12441810b900440d86501c0c203085001c542160702007030455118204e6000041c1c0040103440c11458803d81d409102040080140c4a01c4160044550050b04d444000641003106c0e811070003007406140103641609840c58103111035840120307498001e843c1000012092500d034243c0b9060013100900d00001c9000d81e1041a03d66540142c3c00a50700707603c211080f0780342d00681081c088035180c2a0400420561070201c014003420002c2c000100d1035a400310018000000ca40c015000c2e05495a0401500c00e489189410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250578318 1250 250577068 250577087
    0x703020c011409120913091a042a0501050a0c0609020312031008240a110408030405010905060a081305160609140d020303030a230a140709060c14010e0d 67
    0x4915101e044204240744c941c440882e015042c0180860040108104014000e81403d000854040420000300a030a1103180320850040e4070422400011148804170100d00d07a8a0104140c4101c10302141080580c1e0010120b956000c0141840da810b1202e60614074003d009d01c14003e5054040c00802003d41e645160042d40302e10700c030605c140c03029a12280000d90320980c00420005030402150041c0c1800640040c4030351108110300d000c03514500c06104244160480e0b40600001d50012a0900456030440c440e00041c040c1543d407181010281c600c010711074000030380030030600c031724600c0c081c024004288103000d04210707040c034900c21155a0b410001c00302c041500c145a40142c1524110a0b01e240081111180e190020000d41c25602c0c0c105d01d0100400c02e000046401309502e0817100034031050540040d209040c0490001184180d03003c140500b6171000f80050104841c1e01000c5c006550001100c00700e15801c16107641428074111400b50040884802884144c81a40c1e4800702c2d0943c81103599 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250579568 1250 250578318 250578331
    0x40501180b0711190e0105130e0f030a020c030c09060d050a060903021509030a120b0109180903020c01051204110d080315030f03120a020c03130801060501091406070b0703020c0114 79
    0x1500c070104c0b8154071805032040342c09450381e070303104000040180b880c0c0b40100707200041580c01c0000b070003c101035200b868003181161402d00c40e04086441c0e94455010711010006041c140c2c00b8140d124407120004207103400c001d0904d03210b004c2500a0350140715040000050741c2e68005c508019076121418041d54664015100c0010810854005903000001109440c2c600040340c40d82451251011a100c001d040b50204090401c445004000f544856032145900305280e14071000441c034406040081c20702f40c401c0c407010b0602604100e911201802110843c1d4015006202160804a40c02c0025a00c0d91040c00161070040040188200101120102e60107071904804980000c68000d0b0656203a00424100b07584440794076000401201880d002006d101060300252443c001070303042e1042c101807050b00070709400da40d21f0105106c5942c0042302c503030107010310180c0708108050f040c5c0058200d10440000500d00c00000000c0b468070b900a8044e6003590b400d0000a0190b01d0b8450010301c0c107400101ca10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250580818 1250 250579568 250579579
    0xa0c0503040f09051003050a030c060b220606080717070c08180a090e0a170c1c1d0a0603020702040b060a0f0e06030402090c0f0d0f050403030b0411040501180b0711 72
    0x801e01011403990b9170401c032507000000d88800c058584098880366158081903d13119120a64200241d40c0c4201d01c000c40c0d41c044460181285641d00c50344211a041d4200c1d40078404481e0600c40c01c982c0002061051460070402c00c0d25668800f60304030b80c801c1c0300b004003c006100200d4075028101714904580824403003641c103207000a279914103000640e001d400240100e82c00810307681c0c0110b0001e20004640204420040c2d28090411441c40d2606104601300f048480070030301c025200130760004048001030092119030f68103000074800581006803621074041410343c001036450440d21940c200d0112050010401038490034000ca025107000c00600c100f1000503801007402d41c4c2841d04034143c0380a0703074000e0300e0705a01e6552082c40c98029400343c03010340c1420006000314004201c2501805c0441c0305100001719041c1450302d0080d059500c406103480c401e6040c11203911112910600340c3d0b085034800d1801c400d00504960380d500c24007480b504a1000800001810400d2006524200c445104250f58 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250582068 1250 250580818 250580821
    0x9060f03021c11100516050105040c060509150a02010b030f06100f0308042105010e011401080624010507050a050106051c05070506032502060603060a0209060f0a0c0503040f0905 78
    0x501e8042d07030700000d80c02002140c0c085180303100c0e42407403a4245406446803c0051034801d2001459060004141e800c460701e0303441e03030b04000c10030441042e0003000b02828182607003801000c800140d190341c0704030040540b044010510f2400c0c00d200b50402007900b880a8242c50011082090468a50604468284038200e40030f01c001040001110348000b2030782c001c1001030400c1c0c1841194003490302807160985000e50240c2c0780c400420300030702c282d46000042c0800080d0000081030000401e03a4164090011900030504000a1080c5103004401c003150100c02c1c58180d030340c40e08c016522801032507000b400b00e100da42c0840e001c2000552014007a0740c4111210306001d004141920700307504003464020210b0304480020020303820000f02441d08080030031030700c007450030b01c28003102c560300c044200c9d02d401039012005114082c02c0502c07920350030440c0202c0561a080303151000c200c55104484001d00400000651281c03028450021382965603480015a81d0f681e03603e038500310390301e00c5a0141c201140c3c5803c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250583318 1250 250582068 250582099
    0xa0305090a030b0f071d031e0309060f041418040f03141b01050610050f031005060a080f060405091b06131205010b01031a0405061816090909020105070212010609060f0302 75
    0x40c806d00d02d4040100101070740926000c4140c0c021900e09099026403205018401c0b05a8468000c0d0503001e4036040d10640742c034500700104004000c40da1131a8051444202ca5080141c0302c0c50406500c55046520714042c9101450112a1501000084a032400c40450340d038028014000000310340d907220038001d004540f01d0704108503a2209600e254004100d040004d2820718024001566000e45405150380d4141c1d61034000c5845030340304503041c0000030184000c00110a1800301525003101307065404004c43d14009200740e41c0c3d440078005881c00120091500381d201d60380d0340100c841001505103102006903071000c0f44048181480004c403410b5080601c2a07906510a125104002d5004140c4c010740d4102003081c0701c002c00020309916003140c0700c4801182904d007416415070180400c09103498000710000801010039072182c1101c1d5440e814200610050b07a4402d051350f18550301102e61042e4101c40c1e4051703034010006a40104d0705181088070000b4006d0000da00241164002ea032815201c550302d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250584568 1250 250583318 250583357
    0xa03050c0a05070b0903040b120423100b040b060c06010305060901090803060d02030f0a080a09050d0f02060f041e0303030f020c0607030b0103061211100503090a0305090a030b0f07 79
    0x860007000140c800d00c8401c02082013a815583c102613941c0a83e0b1070301d07448002e503c94660181c046012542ea40400b800104158110101d40c85d280c00905401c5070201450a01c0d01c1d0101d0604190366240c032100b0100031640d965110440c003010042c030b06a603c040c211072043d15541c2c00d110035a240d000c0c1c0c5000510f40003060088284140d4030921042c510340e2510304000004100343c03c01c0c1c0e003510440880c034080120420150a1541c0501100c640b01c01c650040100100d0803900068012074035640e83c032000802d03141803503402660441c0e0480c1c46070304444510a036070280360701c02030403212002007a0000d42d080d0f03071200c0b040e24044d40d010f01075041c2c04410300c001e0784140c5501344015480080064405031082c0d0101d21206014900890140d0390303044005025003a046042e21800144c03050743c0c4d914503085520740141581400c0c5a41181303445002c59807036507041403010b01400000141c5030300c2e598564440b4405194082c00603100e50a1001c10720240100484414000c500c1c000c01141810200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250585818 1250 250584568 250584577
    0x603030a0503010e070c140c12070b0334091a03160e12070602010213090b0603041b03020604140307170709150f0b0703020106140f040c12020a02030a03050c 69
    0x64a0751450b41c2d00e0308489400b2400d00400c1041000f045056000010340080a0003007403184120061142411410402a10030180038000070180d021030f008105070303c90b103c10750750710148905800e11740c038110340741103484903125462112060211015131a00035400c082c14106442c040031858808403a540c1c20354001e4801a24600042c4000f8801400403070f100d002008039101000d480c0400944660040918044050300f0520250350081002c2914500c01018903004001c800d0003030180140800200d5078510000e08040d0451040121941c00f5006d880380b5007008540c00b601889d0345568440704980c003c3d40d0313000f81900c80e0280ba0707000145034040394105206490320300040c04081c0c2c6003018500c0249110240d4a010307100c0c220000401540c00041c0c00f00a203c0d1295056617401d0914000b402c5680e29040b5036002c41d2080c46da07a032203403100c83c5000d2184e1030507500018468007820060300d25040500c00300e000301d8000907c004125a010000c0c04221314141c0701400903407240e02d84c66419008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250587068 1250 250585818 250585837
    0x30c0f0609121c0903030902090a0e0f012003090c03070306050114030c0a061214010f030201090801020a0504090b010318150c03090b0601050a23180d150b210c0405060303 75
    0x10800c042d401d841415805510018401d08000405080a60110f10802700440304103050a665580c8500345980910035682948030440003044200540251000c8102144a03045c00b900404000a0303041601004071407145a001011241c00b640d4901d4001c0107010300340550244103103101800b01031420300182480051b10000c0980720010f042580481c3e00c140810460803919450741d0078902030900354540039000c0c003030f8512201e4042d800c4d0700015140c020745600ca224107070302c1041049056030f0703c8030603a0f003a5114000d020400c801008012406400c82e194074541d0954036040c0c0c9404c0000c6c1d41c0c904550703110340e03070804d00040c902501c05808844201e1300241c00040c900c0001100744d84103500400d8003000e60700b0300c2201c0c1804e0588105c0e103d005994104a51000083d80e000741201d10400054190001c0340c0c0c6545064090b55220720003001140c09070603036511001c03c03101940e02d0000a444224045d0140345a4141007900a0f40d00c1605d4920715000e54075100100d030060402008407610300d0b2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250588318 1250 250587068 250587097
    0x1418010c0f03150e040b01030210090608060f120303090105040303060602070605040306020d020714100b040501050607020108040627120801050a17010f02030921030108120309030c0f060912 83
    0x80d8881c001d0703010f0800c440720030203000041c0300b0108080c5410b080700c9001e28055041c0390410341c114414005080c000701468802e00207030903020441c640d0f00c074590542c005000c4c0c50240c0c140c84490f0101c2c0e0701600c0500d60140c54007010040001070541580050b00c214004e9a00b03020302aa640c2d000e076180e0405004910000c0d00801050004c42c0341d0303400501d413101540c02c0c01881d202c1b02d03440391010f10398800030b0350076280c21128151109000501038140b0240c0f080350b0800003940b414001a1552090000c003d0510110400240521115501c003e5140b140210300d6503a041d940381045500e0b410011081b035a0307500140300300e1a05031141d1082c0781a07803c05081c9041203400d059201c0038403140d03030390010307081d40d01c44142c1900710400f030001e03502826282005003480c80380740e0611100a056900040742000c0d0610040009603000107100b50740e4440d1264513aa82d40340d641802d400c0d80b003415026016403154802d031101ea100c000450301d12038046d200c01d5402064601074400340c2d03403082e16290101034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250589568 1250 250588318 250588337
    0x1120504051b040e19080f04081005160e04051f0605090108100b071b0f180b04090203030306240a0519080402060a0f0c061a0406050402160b13061418010c 68
    0x2617620400d11484500401c81103082c00141034880b400e540c0f0541005c40703550802c48041d51a080a406101d40002e02020000602c401e907901c002c0c99940d20945040c499525080855400031054446004203401007109903403850f00d40308042c1080e1f01010301c0d9800100f0300400601c07030094804016040e0b40800398490326200c101d84800800100b61020f4910b000032034800000c603144100343c001c0080081040ca246000340c200007041c11160f403070102600941c1485c0e1500d0050b50080104d0f0750107202101c01c0400750072400249a20008032524007070b02400005003418400c1d0f04200038190702c1d01440c00e03030004955070120440c1c2c40d29054800139000b500c1404024030070790061191503510611881e29850f5034543c0c0d25041d0030b0342c0c81c40000c0701d602614003145442c6400c0034015040a01000e41d4250314045181d03425103400103107007001501450901c4c01146e0180444040c895030140c0002e030500c000c6000c400e04501a00054598082c11540b084052071407010601a00500000c161294401c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250590818 1250 250589568 250589593
    0x40b0307031b0b270402030603100e0106050a0b070203010e0d1b03120c171e0c030a0209060c0706030b0a0303080f0a18080d0c08040b1501120504051b040e 68
    0xc0d82e50700012035011054144003041504461010380382400e10500039000820500e24000308207000c030a020790180e4010420010710b80c9000030826021030b512480080c580c80591000d80c0101119003096a02c50401c0c03400180d0981400050100c01d40200c00030440d5140c207c1d00140d440c06100f10341c03004100803040040e80541180d5110760300a01a04040d41079180211512040b82c03010800300c0c02240d204084101c9525103d1010f5510150090380051801c8010344032084500c40189030007044800000011502a201d40550b807400d00d014011513161091810081d80321540e9006150010b440c1a05038146441c10310b0178042103a4164075170b5815030f11b4120b4100006c803c000c089001158036403110b02560354149050074282c601031241c0e41d86841c072060102d01607c156240d100c007000301038010701010414180c121600701c84a40c03000306046000c8401a1508000706040c500c119180a042005100c000315002482007404440c4100a004d4032080208461040c145a03e8590000300840030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250592068 1250 250590818 250590833
    0x12150406020403060c11010c0203090102190f0f2109260703021f0305010e0103020307050d060f0203010e09010b01030903020c04090201020708010e010b210a031b0b0103080405010e040b030703 84
    0x8115000300c1000d840d00c0e0702d0307848040a035002058590000b60b90f03001c01000e901400e02c2070405802d01440a940761015010000b581c440c440312003030400c58550119a402c202440002105143e40310144440c4450030303040c090031040c1e8a40b040424031007582b080404092042200c2019100d2506281800314101c8440180f0a144001807124506c111000880942e0303505810a40032042d4801d08007103044e030041e0003815104181d0190616003403440040c00165030105054080d00d1013078403503140002050802501404d200b400c0d01c10f02510000000ca6401803040245101e005014002d0002e860344c60011000c890350f000c0080e00507000461081c08520b400e40000400c1030052040f10038140d25629805e08455240003084096959a216440a410f0507052500351030a1180013a010100807502181ca401041c0360050401250200083c1004100c0212a0840d604201401c03880e40e1a031800100e90350041c00345501060951612814910f024020745400410240c050310005117507941c0c601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250593318 1250 250592068 250592071
    0x305090d0e1207080d0f11030f1e040602010f06081f0506030a141612050a060203060621040506061c08070302030c060f16080103051506030c030d0c02040b1215 70
    0x1d90207850002d81c0c006405040100d44013810030b0b070000d0100c00301c080101410440e96544030360184881d00c40c0e140c1c400b40d008400c0e00e580302c4030042c0d074680c2c401682d68901036500390100942d80c032402c04100030900b80d07030550086210720a01d070f80810507281c8519641d51b460b200008411345000040d580c8031440c121540003160002c4001c0c0854000dc00f15588499103198101102d440030b80c060340104e84100000d8030301b50700400c0200f4124000709003680780c182d00d030011843e020744010740000100d02d154968004031126501c2d00516403803008020780140c48140c1c0d094406542910403107000c03d0072032030170034020011403071154002d1041102545e00c0390340d99040340f0300030b40550005200d04d48000c0018000e4074400da000005072410344c545070440ea80411181c260410030010301a0051001507000181132100081801480b0310654a590000e880c0c58002c0451542501551800c2c030421a00050b0707030030415200300c4040c445a030050007403003401000e0820700c2060b0ba001c003c0300b100e80314103040340741e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250594568 1250 250593318 250593347
    0x110f0604030212090f1005040503030f070c240302031012061506050a0f080406020f040b04030b071409010e0f030706050c190b06060a031103010b0a0e0f01080606090420040f060305090d 81
    0x2242800e0389da8000a0564000d441600710480340000c41c0b10401c11f441d80114041c0940a428504641c0e0841c2140c0b1100043c9200f5028590b0000200c0d8040ca204c0b81240000c0c007543c1f4a854070b114035458200007900c1100e16841407a4244100858418001c0c400d07204c000055544500300505840d0048681740c0002d00103030b4802d9800c00145d10180d48610061025108040a45954610b14545407549241c01813084c0200084240c0a040d05501d080407104560024a8020000d90b281d000244089229802055040c03045601c0007404542100203444002090001d840303000c4102d8001406030080b41d02c009010f8a02000024514904131000e420810310510f400581c2a005a10b04000c072b90080c0c0200d009040041150803c1640c4010000742d0705405498501d500c022030000603081c860060222881007201050035480c0e9101c40e80b1494400106d00010741807640c6070343d4081501c1e03110740640106849511408600c6a0003409654002d10f45c0720018003400005080c00c581014007040365 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250595818 1250 250594568 250594577
    0xc08130803190e0d2c0f0d060f2a0c0c060f050f07051507212d06140102071512090b0a0c1806120507110f0604030212090f10 55
    0x40c01c0e074440082000100c48000c17529040c50652400704035400b40303030011050f401c00d541521259441c80e2200c0020000c600d400340c80840a00016107081030180400200c04c40c0b0051414071981d08036511000020720a046114084000141c503aa00b00c4d2030800c07085001d41010001201000114800c00100324161040d1900c6800d02246000d041100d5014150903291580036000000000030418401c9402a0380d41c00c02081da00011380307007003060081540d806002183e440f80c00416640e030404028410306507000a400590004801a0009100d81d00036030411211404000e002035000048034026502d2023840c02c00440b00e68a400c0310500340c1c0c008031000d00d0b6199409040002c258181080c0103d0710140701192007071803858000c00c64045490410301d03100000ea01000386d650813540c2c4000c03101003040c000c82c40307a6072480d040c0d40250769410140c07480d1055130740820382e0b0309001c00d109004904c40c0e802d44a1000010280c049280200103140b940300c0c0500c05481503e00d0511400c00001005051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250597068 1250 250595818 250595831
    0x90705030d030f06050a08100c02101805010e060705030f1909030203090102060705210c070b01030803040b070f0f0503060102150901061e1a03280c0813080319 70
    0x4282080c911801c454082600c4025800c2c08107164003905000c5e00081c3d0b2038140803032420307015903516242148040798655941412203407051090201c442c3c1405009010300011040101d041c01d0b914403118191010351030021842100710300494540c0c003074945541c4081c00e64582c811410380c4404090a0015568098406107440100600a94044600039000395407252403210000e4144000100200304100d000c015820303000503c508402d1344120154103842a40c1d82c0c0c03008054403449524409001044110000010400c0b50002184a240320b002940165240d081042d03400103400c1040c900860400b20034007106500c203a014580c0031b038052040395a40303e4800c0840380703400030650315001c19035110681031081801c20500c2c10480500b0004c9484018039188054000341d20000c0b07543e070324920001c0130a2110303508418281080500c003180c48c28044d80e515291f402881c80c5075607203000c030b907002000070b114815003d00845c4d01500306003000d286a46480100d180300764048150b0110940c0c806 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250598318 1250 250597068 250597079
    0x8010e0c0403240c0c0213020f0906040306090201090f1514160b0709080604080901050304050a061a0a05040209030c0402090a08061302150421170d050f0c090609090907 74
    0x80500c3e18611070907003e0007241c00c0c1c0700c4802058411086100c0c0074801c1c040b0364840181c0720100c4d03e000e0058025001030316404071309610100741c0319801096601440c007150210a2010355031045e00310b54400d0300c0700d0f03442565070304640c44441158450f0f48401300d651203004241a000d0a13451140e0701c0001e00384e915000709042c640c2e00380a2000029612603c010003000400d540048090b400340070000010700c841c0c80c0960780d80c816071164101080c100a4048041000c02c03902304054000d065004c8024408110303c2000250400c0d456421903120344d0901c03500240c04d00f4103108035403034031201801030548d2094510501019502c02d01c0711b00c0d0060b042d402e00188040007070000c2c90080d2201010420360070b003540104014204425100e100880c0c04210400c6007060159412441305002026010000400c1c200130080d0a90742e198203035a0040001c00c60b6079045144d00c210310910300080800c0d00c540702e207499882a03004062845410030402c1201c420180b6004e003a07141c1c401120401c4480d00e41d10398 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250599568 1250 250598318 250598333
    0x80c0f01060f12030302131e0e132d08030f0a050c040302060304060c14070c05120721050a060c05070c090b01020d0315050604080d08060906060301090c020709020c070609050d020108010e0c0403 85
    0xe100c02d0010b03001400301441200d0b8020304840c3c115500b1452b142d08182e4603114400a8002281100c162180000a44440e481c0c007802084c40d00d40c03c40f44854807032030a400c0740b5900213021aa4102024606400151000c00c4801a1002c0d41d40241200d421551140e403100020213013a046042405410111200c80c1c280240c02400c61900c82d8400c80b0145160200303004040501c10070119954108410034406182e00541c4407603c4100c501c0c1060313030798400d414181d08112610078041c08180c14140c041d80f0715900f00e8018480507119009003850346075542a09230841d41070940b85401604048081702d84a8401e4002105866013204064084c40d581c030300244c0745034090750040f0040e8005800c0107640580040c81d641e031220040d50000078501d0a0000903590340300501404201540d10441c3d1400c8038030801004018101c0300408541d1030a40b1130119a80d2885031061100060005901107042d08108100383c0880382d068680307030f0587c0d08010914101071001070170b101a80c4001d10000006c038130301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250600818 1250 250599568 250599599
    0x501060602070303090f0e0708040615060c020310110f0703020309040614130501060903080c150f01090c02030c07051c080703091d040f020108090a080c0f01060f1203030213 76
    0x6070001d0010b64594a4080c00d280320580c0404000200e0160803c0010020300303605031301400ca0714041035583d44901d004001401c0101d402c54442110724808500b880e0080c00b90003041e4021400c65100d400403526020603504015580903c1800074003108101181c8000500712a03840303801640c0c1400140e8000c90220ae646a11012444203d9214121542000c1010245c0b00300080800d10070b5604155000c1c000b2042c5110007001c4c10030016030120040014490a03041415400594100e0f003011502040d9822007802a20703003c0340317006402030303a4030b0000084804d07000c1004041d00081e81790408000407400c11f400406001e10445440f07000040d6900020b040103031080d1a12560942000450341d28488030344142040010030307405100116203901070f001c1c2c07074607030900e810000341e9681c02c005402c020403014000c0000d00041040c0d0100303400890a03c01c007011540081202580d541c031410300d800358038851440c00765020040384020a100345c0041643c80c5056507090040d40d070302c6940312002d07401c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250602068 1250 250600818 250600829
    0xf120f15010905011208271c03110102090d0f02030109080406020304180c21110406020a0501050a050403051e0f0412060c020102041d15060c0604060b18040618050106 73
    0x8000010300150845214450141c8805817140d1080d00ca43d5842d06000e00c19809802c50300c1f03c075401c0d40c5034212a19035450303112820107400f010304005003c0060100401d046000c0317022500302c080d40344000c03005200390b544480300206034074000900c41d1507090302801000c41c140c0c6c05540f00d2031100040340c410310040c07008014940c0117699503883e140200d000513468000ca400c0170b60922121141e41548010740442c2c42601040c046850368000b500c220082c8011210b0101390000840c00058168011460680403406207000b4006a80d50140f070404461040f10002d010610600551030b5182415281c10b40d242c1c06003034118038014a01c00f9001d0590820b07840101c40508c07210340e40d0100241d5020711514051a40003c2d410941080e500c142042d105d102c0194003c1e88640c0051010000910000c04d1501c02400a41c2d454464a071220303202c100444043d502d050400c05d0700340300c1e03080000c65080c404000450076501a100c40d0340341ca010302503c464055003440f18030b103050085002880340300001c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250603318 1250 250602068 250602103
    0x1b010c0207080606090408040b0a0e03070b120901020301060206010b070c080a0b041511190c08040f0519060e060c160b04060e09040503070807020105040b1305040e0a020f120f 77
    0x40c0b4140341d85103031210042005001d0308100341480b000813035900c199030a42d110424400e448440c94401101c07298003040820358035100d00200000d018140c0c100401003045421481c1d0090f41c1d4098090382070344020310508005038410f00041142841070005040040e210b40040c1c9880b55507048507500e0300a00c04c2c81545c064040c01c0c284802c20803025204455080360b035801740101100c0e41c58090640c0180803e44070340401c1d000d80b510700f0300d21820b0b00c40201c0c2d520518094541c2c0d200c41254444030b69600810b8080c0f4090740300d4864000c0c25181c0c07801110925030710341c4442c10710b00b0140a07154010910700c0c01c20380701d02c1140c404e2918112401d40040c0096107030041c2c5031890078800a02c0c1d55804484c89020300440810f00c0080350010040744c41e0b00340c105942651311019440102c81c60300ca50383c032422880c83d022030250300641d190301881c0304031a412202031103010340807128152500102c0d0340007580043d0000b40e00c9801c0c106250450024040c04080c4c84070201a0b0100d20309200140c1040300402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250604568 1250 250603318 250603333
    0x30b060103050f0f0f09031e07020a2103030b0f030327150403140319030c020c090c1204060b100309020a06020c010906120906020d02030f18030d021b010c02 69
    0x10359040c42480e82c0911050502205800e22960f008002400a0702034182e60850740c0004007480c00800c22501070074107070444180d04a0703146140d04001d8000802c01c0348208100c142c00210302c8a40e000b08181102070035855228004583d07000e60007440001005a00200c40c17065007405541e051001e420b03d6042d205258403100c403030079091003828100c0c0d00081e2103024440c0040030075440c0001038501340d13139115404000141c2010140d0703255004010205000c24800b580b1b80612681c035401851400d002a022145208541e804220700c22004440414041c0401c3c031080380041d11988505030414011040000e403440001c4c0880c0780d150a0700c1000c800b29494241e40340c11810910541001401c0c1440a40900d43c010000241810140d00c2910200000f000260220700844c2d072020201c1603205104541d100018140003003e0b4000700e400b40c204540340c0f40000e000303508019600401e40e0300900518a03122108290500940100c4510181d001124040c81c08441d0700740720301609030b1a950003d2031f08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250605818 1250 250604568 250604581
    0x2011e050f01080303010b0d0f020c07122d1113050a0b0a05040209090402010f170420010908070902070f0b0a0501030c06020c060d1e1401050102010f06181e06030b 72
    0x20701e10690001ca1154010001000042d00d240c0c161000c00403030160110301c540c0c115418101902455005000d18051190002aa20f10302401001c2c180c1c03061040c064035890440d0002105409081c100303403841c01007480d000005048010049200750b00802c00103240d035441150008079402150500842c3e5540c2d082d014a920b808003403040145000c68040d4503044606000c990b28000c0540002c1c1409684580b8222980c011204417101c5608160076500500c2c05c1c1c20b003080f00382140700d140e81504845485108455108107910800e403012280140412441d00c442d08000354070040e0142c80700c103201001c01d000035442421450080051000105072075040d410b01d07449107181a80000259400706c0c0040700fa54440b001501d40d40303c4415070000b040080e80380031009440c81c400041e030404d80b429041d600681c00c0002e0581c16100c0c207178002c1058070001e0460b10304030342d00b502550340c02455440010300340c20a44c2e00b2918402440242c50301c82e03a07100341854016180b56402c01c940308440e41c2c081020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250607068 1250 250605818 250605841
    0x204051825091d04150216080a030212070305070c030f050d020304060b010207080a030c02060a140706090b0702030702030a3003060303030f0b09060108070311180f0a0e0a020a02011e05 81
    0x82ca5541c0c1e0f0602085820b040c2d0301c641ca076054411028443d1a00407400c40e07840045a080d40c00d0250300201c40340e0340d4008015004000750700509401040350f005101140060748a0310075a84103030361a032561010f10400d6201030303482c03000d941e0006040040822092000b10444c0c006980900c1c4282e4000c994030342401c00190600855410030719166210b40140c0011035802480b4595041d01910800d507504144582140d484405034904030040d40d000940808001851b40a1a015030107104d0300c0c134141c0c4519404070780b68410120081c3d13240c1d1110380c60901040d0150840303c000743e0118124540d000540b01e0411151141c2c10785c41000c41d9443d1000c1050540500620000109075039082080c6081c00c40090002c1401074413071410000348000040f4010f0084d4051017241c440d0700c40658640c409031141d42c50012088000c0c9000768090342d40b00d4281e00b040c01d091004c2e40e4802c280c914003540d40d40b84003402074110403804021503403100c004802c00d42e1840010f034a20a4024800b055600e40401c9014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250608318 1250 250607068 250607099
    0x402040f0b0715020c071a0906070b040605070f0f0302090328050705031204090b0409021504030606092c070306110904180c06030b0a0b13061101020405182509 70
    0x4001340100110542d40340081082410743d805c19291651f08680c0800b640442d0060b04001d94011000280300702c01d0003207889583d84030300c0c07007040c01380519510075104842c9580100100c802042003104a8103c46009801414081d03030054120f408881c0c00050401c062235083c010805008440e0030303054107110091120a01804055000f010011304402e1140b51034441c502c124102c440da6802c03079508139500c80e0840b039943c94006241c480ea00600c842071010546c031500c030481e02c852800a00080c004014000d10011b203584100303010020003c403501084405000910b40e01d036001c1c1d0000840003440c0c91207003600c1c0400c0c0c1c07090103803103101c10010320044564591583c15400c803c24044400122031b41f0516040e1521450085444801840400c2450180780c00654a980c00410340386001d00443e0394540482c0d800da5240d00b101c0b14182201407c0344103074094640c210000203d284918805048182d42000e41c82928041100103000d1b000d440b0f2a417076154100103110031100b04007100c80410b454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250609568 1250 250608318 250608353
    0x307110c0406060c14071d1512100b01090b090d080d02030c0301170627010e1207020f15070b0c0706020a02010615030e030d0506010203251e0b0f04020402040f0b07 72
    0x300812402d00c44aa65180d03122100841a00c1d1408000360310030501100042d408a4050700c0300351400392001800f515002c841324141038161030301d40c00c40311640c8248dd202c421a407032843d15628210340c82060110000c1441c2050328050781c200301c21000040c062005501c1805401c07036407138883d41040408900b850001450348000c0d48058284028590400c8183c80040140130081000140e407400a5000d012035001102c1d0300e004100f0036224282103040240010f500c02c4510019403031b01e050801c101e894080021283e1084140541d10008103a0050280c008032801c5d06242414415070700c800581c1e01010404c40180d44a4000b005808103551204250075280c0c00e041c000c03031502000040d0f803070103095042100c07161910003050b9964020b0040711255440010b42700680c071605080403ca032040d4400444101c03c0380d41c180c20100090b100380706406540300d8540d0b556a02e41c00a0000e4001d006801030f80d0141d800c004c001256078003205050700800140740e00c152103146c0740c103100031403e030181c0c00c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250610818 1250 250609568 250609573
    0xf1a040b0a1107030203030a0b22020408060f07050f0702010912060e072102150403060501030515070f0503010308090a0b04090b09102106020408060a0506030c01020c060307110c0406060c14 83
    0x43e000040d80200590394001c0c413039a000a0b208507038000007041c6503881500300028031519105400b203113015400800c140d4400f03a08030ba5880d02e4402d02c038010764504944c000d00252040c400c80d1001d0380381100a201e1a40149084089a61500312260244081c1c050444006945904006031040c4c103206000042c00f0908004004401000c0d500000070064040203114041c203129164100b0000d00c00d80e00599041042046a980c482c50115034403d13104200c900b000c850f000004110310312503c3c000d840d1001d1540c0d1181580d281d035490300090f0f0410061581c0c044010a008902c039012400680300405141c040070410300012028480c0407a4050b000d85c2e04409291380c21f00800911412040709801d04801110040031b180c28401e00a00694014101d14056402801440d0386a48c100074002c2c2d00881c180c070440110f60f0b00683e078800301c00040319085501880002d140c0ba01500d440c12130280b130482940c0000041f1000541255000d810190204010802c601c06004480c01035001c000c860000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250612068 1250 250610818 250610827
    0x100b0f180a0e10050414070e09070303080604020d0c02010b0a05010504080a2405090106031502070308010e070201020c16030b130f080906040302030f0616090e01030f1a040b0a11 78
    0x903030028500504020501d81c59164040d1484410080b40d0010b811030704003003001d410646011400720310104c1c80304205104020020030300c0d0303030f408064a0040a00c14000e044041c5199030555103d003005100d40d038080d50078045664681c10034025080961216400000c12603610410805084001c1d00140c0c1040000d1109100101000403d1401c4a17007002c0e103503500c401000d106103208040c0016040c1c915007050180304d11f890054005c1d4043e079200f0200d029404417445481e108a00400c06d0207000216040010000003215148082d04400c00c2e1002524080e06045442e2501400c030703002c104200e011100410500501c9440950000d1f9200d07018010780c0c20585a6107803900031038001401c3c042c00000e882c299541c0c3c4404440c0290340c0903041d50030208070400c045454400843d00704000c5190401619842c503c5200008207446000701d58031314690031038584072403a0540342d0040b43c1e194651008030f62640b80791703011148250311841d0800b5851030f100301e6110503520140880d4210b10010710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250613318 1250 250612068 250612099
    0x51306060219051e01091a01090c0e0105030402040903050c0f0601150203070506150103020706110a0233060a0b03090706020f06010b040b0c012d0b03070503070620100b0f 75
    0x81c006140300c51540c0303081883d13241c610700a8014240840010055030001d4024040c0c5280628418121600ca903c10454004400d0050f90585419074249000803410800034005107043d40c09403a00c00c1c00b07032610705c2c100a00b1500c00c03485e0007001000c006284c0d00c1031004000042c5220480311203602140302840c14101c0966500790383c0c03c2d000d40516507411440c500384080d41d00c682e054540d4280c002030709101216804840c12031a0740846100401402520b2520040e42c0d5214500e03007819a00d0002101030840e40802c0c1c031070001c40500403503800452040d0010b44140300b90003550042034800044c0292510341200a843d0203045140d060054000340010008034224005650446130032805036075485a146000500400960003c420144a1005050800502c0c00c002e0200044c1501040090040d2541016138405440c841e107681130341700c40700500c42c80e4810445081c2811522000100c00c403a004845820400f84481000300e142e542c0a14450030f1401050504420800395032100c200790455 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250614568 1250 250613318 250613323
    0x2c091204061101020f0403060b10030b0915040f0501060306150908100c050715052a04050f030f011e05070e0d02011112300c07060b0a05130606021905 66
    0x500c911010b100c159103106405490030b404468008600340226540d464803854100014000282810b000b41c8040c0d101400540c046c1c403640c091091b00900c00c003103580d00c1044844034000141e001641181d00c44c03841c010790304502c1c06450301030b103013503200892a5418541d51100c600103005d051010811682c1081050000c04a02102c425500c03200c041a160907107007003556244900e03100281402c001070f02c0d044158007954465130141d0005002c07018400c04425001d203011986a003850112241003008001c035150003885407144000280030340d491000d12121090848101450b00d0700c1d400c0d4005042c440722519032040341c1e07100c0300c039042c0361501707a04000215805512001c402070502945e5a40304c4028001007040802c10702a21b0061540c170140401c1c01603449800d00c42007284804460740c6401c0c40c0c0200c444e40b41c8901180c10728070b401e010300ca40322000500301b860407040d00030300a640003086a444000006a014038a280081070f09464240028076000421040c9000c24079007003881c00000da000f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250615818 1250 250614568 250614577
    0xf0412030e190608070e030d0f02010b18010e060a03050303070f0f030207050a0f02030325050705030303010e0a0f0f0e01150e060a0302010302030c300705040b1207092c0912 76
    0xd6143c8a401c0b41c1d1411800e5608055030b51b03584d0b07814803401042c40c07206603012081065201d260390090214503039010500c8050064805100c62161850b4014010344010f501040d0340407400518050765143e07251500c90860344150b881e440050098402c1d60103040d080900c54484100b5460218030304001604c03071a440d4014610000c05171002c200d414000c2d59420416030300507602a00d02c07903001040070500c040464a42c80411070303041c01a0040041c6610b80402507030704071140c0c10340311116540d804408000a01c40e41c0d02d07031540b10340d0f900c2e8030100c0540180714081003903602d00c000040c01030620986003002003080c0c0c0001030103c4658100400342d00c6000760201120350a0902503101d4940940403483c5000c0e0f1003504a9400c00011054aa40602045203000301d40e0340303020b4400394442c00d800301e54078070450180c003c50103020400080c48100300c030a00d44e1b0140b11403520907261a250f01c042407d04900f40306c80700740d1012010b914150042c00042054100580d40c00a000e4000e565244007a24040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250617068 1250 250615818 250615829
    0xf060d030c050d110c1801120f060c0806011803021c061d0309010f0314010501050901020109020907180504020928150c0b0c18040f020f0412030e19 65
    0x4018810400c040c0a060784500d0036600c0750a071107110703154060003008824460304555084c82941c81982c01400c01c1d154600050500e060010328a07800c0c117036900032165801030100c4600f0100129980418a28803030204004026a034460580c1002c400040055203242d25170b44240124031740410069495041484034a80d41c00a08850f60102d8108200203003020001504c100302d400c80850700c0e80001000a01c8170030000d8030380c414481d26581007201106c030000a9102070b01264801444036600480191601e07030014030003c2844001c9038085100301c11300341c50000100711000c90941d242c5007004c412030050102650b0440c03d003588400080e01c11400e21584a00e84541e450a142c9042400c9581c20301510415140b1604806a0080100104070070a015602c070380301d003008180301200710811901e25002820006004400c100200030081c48444d415110181d820061204680305900250006050401c0c4c005820101c42c100544840c0110003200c0c410f03203450030105101a5403640b080c00707494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250618318 1250 250617068 250617079
    0xa0b1e01030b0d17030702060709030507030201080a1d01061511030409022d0c070501080712050903090a09020421031704020609041b0908060915090c04060305030a170f06 75
    0x5980200d0307181e4043c1540640000254218107414406020085020b02d51036400c440641e41d0b0000c044520b070010380401013203500180420805580704048158203d00c40a000281c1d51201e901c0010003105440b1031500c499448a208220520100e000e0540072107203401c0803ca4442d182907415140e2182e409464660f40e4045804010b81c80461915080b941ca10a1b6036940484140013000543e080000d5101a5104185010031254810700b1f0032400392000782c80e162044c1c0096039200f0003900300106032140e6440309114820301c664904920100901580c04010395407420050005041c030755517022143d07100644d448110020345c0c0400d1410304e50100b50809007a90302c4070710028045116080050f40d029003049111080d02c135101d01d46801d1001162203c0c0e44240d511130300b040c0c9401d01160440711070b070441c0340c0d5061201a8400085d0348904480d040d035a0560004001608441c03607034100760b032103500c041368040c141a08403d1400020ba00b00c1c0b0f6540062526090008201c800100440e0244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250619568 1250 250618318 250618331
    0x120c150c031c06030807051024150c0b1302011d28050402040f05030f0604023d050301060807020c0a030305070f0c0902030901060b0f0403060e070f0603050a0b1e0103 73
    0xa0149500950185502445c0c02c1d65500c101e0600640d41c0720f00444186990345020704101800d080388505488501909501c02415464200703540c0d40207000b1400c0c14240800c0b500207000081c644401e6609c0b481c107008042c0d1500003c0c0c000101202c0030840b2843c49200c4807001804103613200030b04a10321a00303c1a014200d0b0b00700d402e080c440b82c0507a5200541190010a0205823084d0000b8030710140c5806404981240c034192502c96a144401d03a8081e40169040090500520303901c100da0100c0030404541220035101c04462030300001400c46147c00041000c00140003590f80143ca098020002d03100810103654240f00255101900d84001000d001001508408000ba1090b81c0003030719822400c81142d843d520380c02000a54000c1b160a20594a03080010680c4805542a1046c200d81044000e007401c0c11a6a840020407058518040358843d01100198444000e46414060b00c6140d4020916041c07002c1c0190035071380102e6081748907460b0000071400c41380350280c200f21107003000d190100702c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250620818 1250 250619568 250619617
    0x6030c062b0519050402010c020f04060f0306020318060903031f08030304030e130c120f060b070f0209060d02010f0311040504020a020322030b040f060209120c150c03 73
    0x45030101d407202500005800c44414a11030341e01151180542d041c3c10314154030340c07460300c008a51003240d00034003150103040d10001500b800042d11201001c09000040e040345c541c503603800220603030740c0f044810507000400c104140c017450340240000c1e5034010040c112030030608503040d22400003c11600816103000d2104031030342e00102003c8000c14407581a242e890810341402000c5400f05040203000700c1c0070403080e042003c650320030302c608413217607075034003007800801c0d00e210070140c58554a02d640c11500c5460100b950300c107910080003014030800c10505a06650301c180030444a000305083e100b4034145c2003400140c1d0304082021550702080c54002803c41c103d009090181c051900318a8105101240204060341c001000705a6915608202102000107003c1c01141c80150b0000402c1c028441e00481d0008002e10703c240e8201c4d10036200941002e480d0400f08510780c4003007290b50349560000e03802d00400d05004840602240141503a18a085910107480b03a4034442d0220700800148403c01000c0c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250622068 1250 250620818 250620847
    0x5041e030309020a12030311131a0409061d0901020405010807030e070f08010603050c0301020408030f16060924112a070602011b0509030d080705120106020106150806030c06 76
    0x11a0b0381d0051004000503100ea04013030300790401d680c040300401d00e810700800d2020019004ea5880b83d80f03100320110840c0c180396401c00031800c2c84002190700d0400f84030104902c0807034004c1d0b802809000103613030750040041d0301c48030880ba000380c03403210541d10400041c400da0340e00103050f50340171708241008100f54840031525072412400d60f0100c45001d44020021441403419003043c802c40b0301841c1184c01000502d42010b08074840d521503100c09600c100410000041208082c2900c0062200a02c010b01c005481e48001d41c1e1442c4405c0f1820104200130003206445806086141312050404200701158424190821301c28651400c0c2401c3c0c0c0204049060800314100d002c2c4110603105a420f510765580010f4080d040710308190039428800211802b005100c0e106440c117168006000380320381c4150560a941510020340342d80c0c104041000b84031000c008440c1e40500800440d400054141d2401400c0302038081803584090401940030140070480d90005210b00b00f800c0f00326456545d81628100c00007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250623318 1250 250622068 250622081
    0x30216050a1205210a30050417070302030a0305090309011218150c08071701090c1413030507050d38041209060f021504060b0a080102091305041e0303 66
    0x4100c4d56107182072925120441e4060000841240c4454140c80c0006115581c42100c5a040c40c05200c0308410000181c109500065007150084481401101d0010b0b01c03028650700260087d005a48000707002428560300d8030800394000c2000001d1402c0020480c0000c100c0307005001c80d521002d407a00c05902200002034681072280d5407050061f039400851340021400350158041c28004241843d000490080c0241c902520700380043e070b8100c08586c00c0009410062400c1090103040001440d40d040070500074500404984860b40e018100043c510314020b4a4080d90b6003003a80112200c24039100004c0010107200e1180b0034002e4403020300441c92104072203070000c000085924142c1d10080c80248401d000c2e0b0260040c120340c0d03c40c07a4407620b5a1082d107980011109000041c0d100100c0540001e21000c0d0031500076216000108520700c406000803800d010b9500226003695001482d0f1140380741c002c03450700d583c5a45904c280718074070385511121141c4004142c2d02d50303e050100f82c2e0604040c0320f5804407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250624568 1250 250623318 250623343
    0x8100b0f19050a06020106080a030f0c020d080d0510180b150403300f11100203100807121e0303020706140103030e01021b01050a030e0d0507030216050a1205 69
    0x10850301d084016807036510403a8041c60f1140350104100e0f02c18004c0d8030503615107a00612005000d950700b01c031100020b04941e010804907585100040c6c1d6810907000c0c4141c004d400094841094801507400c41320050b2105070f40381c0e00000100b10a640e99181c14140d0404081c000540140140c0802c01440205800c3e0806480000c5c001c82044010491030548043c44101c2c003448000032172040d14a84840d0041c0f034007040458102000c0e81c2d114040b110707860160303076003581d610304040e5424078140e03081a500d11002000d280014040002c1c04c010410041a4402c4052208030f00354881d1049905000011003540c001940b180041c54080d80484036440d5000a0801c5981c2c002964403c4800080c00118005240d00c44402c18035071002a068034100c0d1543c113003030001400000192103d0340408150750906403104032034100b941c0140103076003840200752a00c680d11091494024240448440185000d0045810902182d00c5114101003551051609107604038554148113283c6000180d46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250625818 1250 250624568 250624579
    0x105010803070326040204050702010207050a061d06010e0106050c07030510060e0a05040b181501030c030308010f0e190e0604030c0b0108010603081c060509090309091008100b0f 78
    0xe4a50000401011007500035503070800c80b8400e40e100d000c541014124206103111451000c20f0140c509948030503040a61400014039010f503642e01c4504040e044042903c51940e1481d4910300c001c51400780c484141030010103000c17150305154104c14088018040c807020081c0103c3c1c50011300c00108600006036800034101d40e06400e1043c0c012010781002d000b10301d40c3c5520400418006d283c1c50042c5070041e940000c40c0da180b6501c41d5590010515a134200522522500000d140b404556200c414003031401400440c260794114200640722020607070011001130b00d41d900c10070a0b4000009900e41109800e2920108200641c1c45100544500d0800500364040c0ca0b090008241e044002c04120601c03c00c1c800f0010387e60f0710b0001d401c81c1c0c010300c070240c070500c000c0004109081400c0a00c071840e01d5903041c00203800b503c4001190356031034100ca01c1a629440000c00c40000e24001915a901030a000d110f040c00030706181d480e6071680c01c1c80c4408140300b0b8a980700b180e030340d0340c1d81e94843c0c0443e04017408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250627068 1250 250625818 250625821
    0x2010b0310050712020a0e040c051c390305040206090604060e0f030d050406140c06070f11062503060801150504140606040b1e07080a26061e030105 65
    0x1000200410f40d4410007080381c900040c3d411444a000351340c1050441d440c0c0078042d52000c02030001a003d007900142c1002010090701128500e4402d1035035070718800c01070018650110f07104240c4290304402c15442c0c1c2c4090034080454620408500e010303810010f00e40420302d0f0302d0381c5c800725085019450156600907004200814851303030203c000b500c400c1d0102e1b940581040618141601ca0403182c4800340002c0d4100b00511150780143e51036032151030000545071078104140b201c1400c00320140d0311030b40000d80c2128140e04295105400c1020b120354600a45114103145000c0d1501d5064490700030100c91034148a28040780c02584114000e04450000b070040111a1083c04501c2c1e01ca400b440c0d201d1864040d80e10340310b803c1e103500903100300b5025000c1481c1c00c0c01e021061585800108803419180c8134100078034042c070000000341c10400e01c00c40760146c85501c1081c0103400001100e0150b46031200c50035100d5a500b041d0081650000c80666040c0d940c0c40803200400b01c001c80c2024440d8241d8200f50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250628318 1250 250627068 250627093
    0xc171903110d080103080a030216050328030b3f0d0207080f0c042a0905010e0301021e0c0a020411070b010605040810020a030204080a1113020a0210090302010b03 71
    0x1481410400760340000e656841030b18032015a00c5200c05c0c000070b088a0300c107000da104941e012354000c1c40c0300803103124841284403007036035414030b0755000c030b82c5030540e900032194800c40030f03240400030b0060240d030341c103003444460703004004626414403c0024043c029451001c8020100309008000129034880402081c0c4480e90007030b030f596800d0032040b00e4005118406000851040220b455107c1c4000e1101600d0a89000010040a042040442c904040c2c92482914000307141d66501841072595858a400c401c0c540000904411042600c440c0032364010032401682c41c0031850108824840c0000407a110383d4200041443c118490307800075003007890480f4900c0e0703626400c0050310181d0b100e101b00d018147c0c0c03143e000300c82c14000c922501050740e1080e1702c500d41540d00d5401608008a19282c01414150342d80001c42c030304000f10005940341047c0400030000c500b0400902c1034203003c0b00b07405502d04098024020740d54006000c10520701c564440f6240e04040c070070340110568210040031640d0504541 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250629568 1250 250628318 250628327
    0x3070f03080a2a260a09020f030d09050f1503070c081603030902090a1401061b0b0109020a02120306060405060d02041a0d060807030b04080309120c0a0309120c171903 73
    0x5940c520f0103d00101c098070502a900346000000c20300c01c2c24068403a03142c1c420301c0400350031138440c101d23031101c842428003206841c1000202d19444c0c80360360700303100d8524050a02005815400841c2d010707010a00351100301e60101021240c1001071803078010300c08070035824809845d000e44d80103480644441c0b11100145645a00050802c50085942030300c940c4030308030480200e50b8840300c51201001d0700300040011901a19601d00c00810080701c0c044210805d590b40307107181e41d098200b0300c030b03050340403031010701c15a81045428003014520405c0ca140d420302e20b000641c603025a00c503003032207010300180d00b050345015901514010300c00502545111410043e0300c01d8039401c148064840b1520742000043e070280d00241c4041100d402c20036021032031703c0f2511004890b82c402042c061070740c4540b11052001c0a003100c0102011840100a01200c1d100791900074010000d5500407421007000c0c0f40c041c404036808000c0c1d002180c002042c000884004021040d042003070b031080c03d8030304020101d406000e05070031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250630818 1250 250629568 250629641
    0x10f060504110313080f090603180c03010608370c06120902060a2a030e0406170709020a020f0a06090c082e0b1c1403070f03080a 57
    0x12281072184100082c1c215919020071034004410510400d09103000c581c002c0020008086000e280e14a042a044080344082d031099035003000e040c141440068a20b8414030914036005011002030000c146070065845ea201c11061a250f41007401c0052440405111006601d10440c0d00c0b907440c211401d2414115a613074220704c00c02022400f02d8000a03006001d911480e182254010041c07400e0414010007115039844508030304855202200504c44082c8042d0b01140b01d092190340d800d140f0300000c1d400d1005031400d1b46c0c00440c00d07034510846101c0002012500780141d8007040300060315a24105012481d209001d8070b036134245d000b40600703401800103e40181e59114040c0e083c542005aa0302000c954450305c107107402e0503807024120312060f00c08880c0c84051b00d40400c40d10100340000000005242c140111f5015031581903100c8401041102007009804019421009035003080c0c0e20b901e03002031100b4a050010104004a000180132006590209038031480701c100d114540121961018042c003007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250632068 1250 250630818 250630829
    0x90816061b050601060c0305041d01090c09030c0b030a090b010b0c070b0301080a320a0506070c0f08030712020406021f05060616050309060a020d0e0306060d0b0a0608010f06 76
    0x501040c207490410324032410301c0030142c1c04801004980e28144e82142c001c140000120200002000300140c074000c0c141e548406d0b24644000d400300340d4500540003003100c1d00501441c007032000480007000072441c80417180d8112004a0800395503551010b5001004004501d001440ca020281c00402c24540e4230f005000304214240072a181d003030f02c2d4601110340380030134407500507990300818124001541049501e80000044000740d40003140741c007000d201c00a05195038400c107a000072000e1046c46010007905030440410700f0030110720701058403121507440c803541002d4200080000801d40783c078450f20414480890840b8210344a46d1902402074481000c4605410b129031080301102e4940345a201d6035000780801003502d4500205000c6e1003802c1c0f0303c617200c00c0c0c90324042070000740d41546500b40107099084640d8050f2041442641024000d0100b90080c84e000f80c1c02101000240d440358143c0c5d4102c55009000b1045a6840c5080d00c4017074491500100c415500b02040c0070bc60300c180b6000300c0103846 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250633318 1250 250632068 250632077
    0x309080601060503101202040b100e1e0d0f110306040804060206250f031e051801050412050724021b0303040c060503130f05071401020c010f0e0109081606 68
    0x2640d030340c412105030100743c90645d0340003241c140403c000c0100d20140d681c014409000800e01c0c3c02124001440b0780c1d10b02407020040761181030711005a25101c0000e000c028950802100d01c5040003021445540704004000e000750780240f0540c040c800780108680c05913600408aa1142c83c082c5040c1c0c1c415045071040002520800020070204e040040e40141c0d202503d400e0155200070848080301c01d00041c080321403d040daa841c1007499503403000030315184940000d20204803400c0404020001603003210312040f850745090240800030f85071a000748800e200724a0000c0c2c8602060415400c81e68081d403248103902003540d0340b150482d035150040d04002098210b030311003045401c48060f4036403000321002402038a44840500c078460044000d1504094a128850106615a0740700c0340302240c03020381660b1a9100030b100f00600c0c800110074141e142c1082c409030401040384000030307281d01803203c020b03404e2211141104d5900c1c7d00c1030048000a00d2141e0842d04030440013400703900030800c40d000750800103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250634568 1250 250633318 250633321
    0x40f030b06090f070509060409150f0501170406110408010c170a0c0c23030f090310060302130b120a03110d090b031501020a021816030b0d020f0d060903090806 70
    0x145020b405251092900701420b100c6980d0340b030012a03544c2c4c08107000c280d2200050001007600100e51054100004070100322202480c20702138031741825a425805181040320780b1100304080ca001140b0650030039441940031400440075040402503024982000c42c0c9503103444030200c0c581d5030001403001d0021324505025503603243c1007420019104800aa11301044100c40814002403500500c80118aa0080840d03043c060b01060710303085610000400c51074071030120710360350549000d0144825801d00c2180400c0090300e1940410b840710a0402294000e0b035545000e6035854a41d19080e451080010b0240e1700001114940130740356402d17100170100b440c0314106005903058020b0207400c0aa0b900c00e40418110b90700d0020342d000c4a125084914118040c21740e07103100503102c8015000444021001076101490300c2000814403400f482201001c041c02c00f0a00250307515803954665030560184c5a8186011101000c104242c081b071a00030a0903240c580007600317040e404006031082d034060b0001d0b52142d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250635818 1250 250634568 250634581
    0x60e0c0307110d050406140c0a120f031404020105070c03150618050402090f0714040605040602010f060501092d08160608040203100504030e04090c0807170d0c08040308040f030b 78
    0x9483e201034400b40440e50801c0240800307030042e05401414084100d800e803500000d20b01550030006407400c11903401c0c100da80d1075890306410603003203030009050f0f1408010b0000d80114002c48140013810103070622600113012400d018500c0b00307580c080e58222140031068a0007200c594001c180c68401c8031110030f00031680264103403030b50003018050b6400034026001074460541d80410f43e0005400902403210791010683d1005604004c0d000400703050b15443e4403039250407006800c0d181d007110300801641c81d041040c40980c0c1c0280601c801d952981c5407408500c00c0015140c0e1001d0401012034600d05504140003841c0c00c800282081071070b00d5024520903040d40c03640161680442507030020741c1a00010515001d40744640c0c07005921900918080c90071444044c00b040c2101c01139141a01e034800411402e00c400f40c000c1216800801204080041c03110b010032181d91140d04043e2400200400303010301d40d05000a540986010b1504860203c0d6200d0b912400410201c4051000f205d0004281000410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250637068 1250 250635818 250635823
    0x6090c0f0108130605130f0b181903050d0e060a09020f03150a090312020c071406071a09010902120c4e0d02010504050f03031018060e0c030711 63
    0x91403604490140f4074019075100805000d005004040040715011200045600c441700022080d02603c1403803e0307810064604019000040e801003003903403181010519155080c003c0421294240c94000d072213118014041002d08500440c2c0720041c8201d10502c0520a0345074010b504292088404026549850050545840c002800410034071b204c0000989140380d01d0704007400951107890145054000390061004030382002010a9142d4031244003030111420214a21080240449589003011040d9540c1d0398400c81c8c280070307103078400070480204484000941140103c290b005100c4055291019400d80d83d4141a4001622500c0c49901c0c840d607150707485c005a502c2d4503c58241d00c411040540c41e442074169840c0850705541c800c0078001d107846c1028001008203810070390000c209401d060924a10b02920858000070541040040c02000199070110b90100d404490a02c50843c4149504000034132540c0d00940e1550301e07840401110444407030003940b24001035201c208070380345100007080c0e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250638318 1250 250637068 250637071
    0x81b0609151006030c0509041d1e100902040b12160902040612021305270c030f040b10030602030a020919030b0c18060a03061d060a140303070506090c0f0108 69
    0x54020000900c14020584250805e44010700c1d1030800620700341d103400100d011540401c1081e00900070503c4c021944e031109110500860001140340600d5055290300c441d2944034044c0c00b40c1d4840e50740c010079011519035401271a900310300140b5000c0d00c1004c0c40001c43c0c84010002c44a00b44100307000d00850074038518420b80d070580d202551006140d0300d0034142000258002400c50784c8204a400f0005019a2801c1c00c00d1280d5009240c000140c10410400003610315024104d0f00761240248100056141240030f010752064100710341d60380d42e4880f5629502c01c0005a0006001507000004100c038210301900182120013098942d0813843c11521401d1300c032003010703010051130b090303040010404e030f130110740b010b843d5000650380880003204d00000021441c0c4d001d000c060010a444810812803d041c0000366006107201d1400c4c0541c91030848001410001d081c050341481b4811803011010a0714200700f81d03041558040c003215403030b0901030050fa540e002d503c4845489042c00920340e40055200740000d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250639568 1250 250638318 250638331
    0xd020d021009051009030f09050612040b1b07050a1101020a030c120302040f1e120b01030206030c0c03031f0911030c07020d0206030c070204050c030103050303060d081b060915 77
    0x2850012001c86600c03016202d00038082d0740500c1108951010310085104a10b241c511940b6050f005d0b500c2a000500010340c01d9221600c81c84040c022000030340301d00302015511032f6219649007841c0c3d84a025038194211780240e10303880e4041c080382c250200a0002103091081c0e01030f511a45c0100040c900490703441c20b203080001c0028400048042c00520010400440780c0c040e03085c00750a107926000e0459203507071140c1c006190b9016140f01e5040da100d02421100c068100c541000e0085030712500c81d211040c10621000740a0000040014600fa0000d0305941e0496101c1d02078035076034100101c0e03013900750f00c1021410300290300940000441040750310904100031510310410b030545e50340600c1c22a0f150803404090340c0003d50300b02c5450069846e600218272402100da041c540350008c9005200c22980001c0c07000e030040c0020401031010a00010a0300e03130060f81160b80e2036040c006454040000e00958085a854034104003180100c6c200216596109100c007504440c0d007410340c0c9045101c07502c2c05a500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 250640818 1250 250639568 250639573
    0x614030d0e03010e0f010f0e011808030601020111071407170a0201081905071716090e130206031303030e07030f02151c0608010c080906011e080106090b01020d020d02 73
    0x480e614140604050702052100a000140d030180e100000c508010b2003084d032800c0c1e039549414510400442c0d109000d070450700000200b29980e0300e0061241081039000c0060202c001c08030000b145a8801d42141e0401d42d900e0002079103480961401a0540300c40f40105800303801800000700d031300e8441c010010384080c050001400034595640054a24030006004141c0010f8600d01c0c2d8078210b542030048038015045980e40941001d90f43d480b0610101c0054960203000e0225414400c1036540400780000781d5140c03198100c05511003021058880f81c2485000350800004410400101e40c1c581090000380c0c001e4405114481814004940300e040900008204030300c02849840541060211030303080d481c210320b069240c522101011040b1809100809000a0310b45000f07014440c0b0038050101c4400e00b60030002858108010380c030740c50f031405006004c0e02044003400b5020b2202e148031914000c0001c80d0003000895140c0004030040c001c3e0340d5800c0c2c007610030040d420f111a84006035400300c1c006150702 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 250642068 1250 250640818 250640833
    0xf1b0a150e060c030114060904141f0605031902070606030305130506070f0f05032712062406041a1210060c030305070c05010509101104080709020a0903050d050d061403 74
    0x450b410380034080142031b0382101f010f01c0101d006840342d1180c940020035208058007a442c04d04120100113a49920a41c0c6d407020845042120b142c02200f500c0e08480302d60480c3d8046601402000f0081c041c082020f4041c5007052800414940c02400421034a01d00400d80314019495505001042c812840005c0804540d02c1c072200215900e0108042614411f4080d00d15007103407034521010b0b151450142640081485902108611300f10f5a03c5090b40e80240c080c01d054500340c0c520b0180410744041c14801c510302040081520390790501160090024101e039008014000241c4450355003105402c204e2007000310012540c002403603034000046682e00d9480001c0c245290b58210080c1c82c001e440c5c0814012283c0300200054000c0c00340c64030440804004004000000d81c04030203039900202c007038400d603c3c20801401411750105140382078426450000d0780d2103071880c00844000215070f0014010b40a0038044400c3c07070741d10070002d01c1400e016a9041c001e00b91074200d1150841d002c5180d1550540c060308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 250643318 1250 250642068 250642079
    0x20a06050c0403170406081501080a1a04060806060418021302091302030a0b1008090a0f020a03061811040203011422020a020327060f1b0a150e060c0301 67
    0x41105600215241c40700d0b04040d583c0e502e41d01000c003014841c101d511800b103024031900c1ea1180c3c0d010f80c42800140603101d00e40038075002824a081c050080800c0350340346d140c140e54880c0c00480c0031600000c0504100491075695103d0b9031164030564144c0d100c3c3d0b0809001d42d010203000c1410143e0316400a0411200030012a8140300960104540a810460b495000920f0840e907101441c0b041445050104080c2d0000007041b440416840c04101031003d480244049550b00103005810140e0248801c0d00264580c000180721450b564002031005040c0004850f0140310a000c0444880c030138800000c054481c9001c2009901090196400b4010004443c541074906000c0d041c8003c007081c094820b0400502d00581c060768004100d0401591000039640307400255603015400c0328000b4501807501b0300074500001c4280c450005558682c000216503c2604c11001034100040008082161f8100380035252003030b408010302d03e07800c0d078040ca002c2040844c001d02040b858030405100070424a580e0820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 250644568 1250 250643318 250643321
    0x91403060c0a0912030e090a05240102030f071a0106030c12050601030b1008070e06091804080c0105010f1a090d03051b01050a0b120706050910030e030a18090c020a06 73
    0x41e4072400400c04290700004500c04c032400134000da01c0c0650b4815040000c2d0006100340000c0180648a4072481c0000704640c841c142c4050f40742ca0360864000030106100800100d00e0342c081c0c0e214040c0c0c18000000c00d481005400b20f45401d140d0365100540f01c1580ea244c1003a07003102c80503030802020030009010646240516440141c1c0824141000224851444003080d603121103111030102140f007850a0007655600482d02191054080741c1240c070301288280418104800d10000c1c2031040103c00c00b20b82003184803010f0b200e101c096840200030320340e0365821400e2500124800c522100032081d0841c1001ea07100011140ca041c00505a1003405406503421102944910181d11144986607920401e00b80f0a0240c0ca014481840011035501520300800030001207190048007158880d5008111880d0403070141e402d45403040340d10840304d000c040703070503800f800c15030758902c03034902000420b003211640124050300d49404c00420307826455160540301e41154040c20144015074020440a000144039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 250645818 1250 250644568 250644577
    0x50d140601090b07120c15290a030c030605070c120801051008010e06091f08100c3011070b04210504050d05030c0d120e0303060a0e06030a021c03091403060c 69
    0x41d010000e02e040987c4e494000c580c00c017012001d80d021005180001a1069a1130015948049a610806030318603a203a40e0300715442d2000414158071940041c00083c05447d5290700c540e0030080c6c60b048500e0003900200300b14802d00134244101c010f241c3c0c02c42000d2052624505a0790b12010003503594490008010840800409000380c265400d00086450710310703180c401c0300401d428001030000491061483c0f080d1013060030301808226a140811220b02d085d94001400c140c051500025804030f140c0d014405803180c082e03541c454250019185040012514030103100382d00172800c542d021741c0c940030600e42c2c0300c20360000302001500910090142d450100c907683c089512800c200ca103007100280c852424517481425500201da4007071000c003440d410500411603481c44e440003451561030308070001003810310a4000c0455a60742800040c8050301e0400181c3c8c03a0a400404505000c01011022000520796800032000220f100200042020b182c140b040c1e0320780002001ba211550768411000c803103820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 250647068 1250 250645818 250645823
    0x230a18110f210c04020316080c0c01050f0708160503150a030c030305030f15030d050c10090b01260604080a0c080f121807050907050d140601090b07120c 67
    0x490040581c5255510026840d036204010003021556220200d5035080000800c5074070b0142e8010010010601008003c92800740e1488c1030901190710f400200b101b0f14000d458000806600e0502400042111402d407944120000e42d103100d5150b0b1010140d507181070741410b14202040080c00810003220076004010040c49021380b01c0320590b0794949801d07004950700d901c2900402c0c000414481c1c6480384203081c50340306130f84440b10700120307100c0d2001c01e55940c2e05c00351500402c2004076180401038824400303e60840102e0300180020b040740e0421a940d40c40a2246200144001e144500d44440340001d9406288500b406808030707696031f840d11882a8010980d110030800202e60440c009030108024204000280c030046468000741c104452014002920b01c0301040d681c0c00000c0c020040c0060f5080c15a182680c200503103854022041d105405007403484860242040e1610f03c54032402e9041c5446032600b669000c2d50300c0d58403910031405100d6880043d210383c6088495002c0390f409600030010301072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 250648318 1250 250647068 250647079
    0x6241d0105010c0528061107050c190605030703020c01020307030606030b0f0102120306030c0604150906080f061003060f1205010b010f090905220305070501060f080a11060d230a1811 80
    0x16581d541e20001c58681f200849a1100301099850510004101180240d10282e83c80030040c000280b00070128030191180c07000300840040043c01d451701c41d40503140f016054070001d54507401d01c084081c000d00414001c8000003442c043c180500c5240c04c0d14100c0c0345400680103084228401c184070019580f00404050b0584954825812141c03501001003000f4007600a0402000300391010050011555a001c00e04020640c2c00340018840802c2186801600444042d000c0340782000341900a00141d03409110b90800c0c1c9080002c000100310315000410f0302c100020408044c00718015640c0c0c1741840c41c0380c1c0004210350b40500c40440554440d54100030b81d406602290940c0201902d0748170341d21402140042d40c04500d41d02000802d000d064040c254200808103000c2c208035125550703c11004001d0000c02e0104400801c94a40c54116018083e6004040c0042d120b82d00c590300c451101d0f040915489452100040e403150a42e2181e90100740a0003c4a0400c41d40751b101c60304040c00d1104c0003903000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 250649568 1250 250648318 250648393
    0x1407060b03030f040f3006090c0803070308100605041809020a0306091406010303050904020a2003121308090103020c100f0b010f1b06241d0105010c05 66
    0x1c0d501003014001c0000ca40f54038965880c00c05142c2d0381071140550003801000110b41884112585480003031012004007601220143c20501f00348010b080d0800d4081d056101009001c15030300002f0006054580c06074850010700e0322100902001040248200c48c0080d100b80b000348a4900384640403c02da0003201d40c046000b003459000226941000ea10444405585002e60030030410041840400000504050001f66140d07880282061140d11091807080758005401d103c01c03401005400d01445e0900d94460740d11102c034000b65504c0d4040b541c40c0c0704020007000080c892086400c6d40d9040c81e40e01c11440ba05003030704600150701a422520810a0390700a059010003500c01503c038056058402000114643d01900000341c40500200d0460041110f141040304180c0c446609108006512400029044813445d800180d4041c074400e1a950000414100113a41283e41000313510281c2204240f0034540d0b0703202c005459203851600300400c039030441002d0308608041802996138840d140c041a0f1040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 250650818 1250 250649568 250649591
    0xf02060609181c0807110606010f2709050609160c0f03050d0905100b030a03080105090402061b250e0a0b01031107080c07060e130f0f05090a0203120a140706 69
    0x1083c0c0104040f8009403c85041113080c903440220306001a88940244c20941010b60000307020300c0c410744c2103400740881c00e00c51141c442885400515800491840d6050a9032241c10400107028203861840c454060390010a07401030092201d20208111754030744a10b14040c0703a51340c0300c2d60040140f0503006e002050044440708405402400070b410b118001a0010511012410084441c40f080035402036100009a900094120131038174151039003140c451b01c1c90313652840000e8180c8034840c0c0119403950031500210720843c0008102c0440049020780e040c0d4003400d15aa000c0307954441c401c041c0d41c84c07507243c00300b03110407184c1d0f0024070701500c107150200300200c800c101880d031035100d140200c40400c0c000951103201c020920104000e025681307011b182007000040022031150025052120443da90041c0320241e08041d03014001d1605083c5041c4450300e4505102501c55405039000d034001e002b044544040c0500c004211100300140b03443e0030701c0682554403400c20a4014520450300d490341d45d42c14208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 250652068 1250 250650818 250650853
    0x1e07030b0f0708090601080a030e030f1204081908070206030402010311040b0403172803090b040f30031503050610050316060903020d111509010f0206060918 69
    0x224150450340e0301260b0528200040450500400c14611034104500620528002003684400e071509441d20440c0010644000b0341000c403a4521555140b03d0143c2d03892200136120302a0003240d00e10010348804000d02842c001d81681d095030b0013818410100a888010f00d41000a50f82250041c5800100d038606010b011043c0c5d8080e070000101108081001c000308016100680070720915080b40c1420a1580b0110354400985800c502c5101500606580c40042c400d5010000c500d03001419070307000b41000d003004c8900c0b0215100546144101c0c028211007100c05854101070004403031501e54420266000c01c13002040c608011041c0380e13a0782040040851030800c4041c0c0604528542c1441e05450070040510302076113200c0341c3d141c0c004c0c1c011040140a80080c02c0c1821241c0540d00d41480d503546241c805401c040c442501c507031210b0a8000340c0c48130b4241c4005881c00303401c01e0701d911640e075a420005990b00c42d400c9402940c80341d040740001e045c0400346034108075880210003c80318500144000c500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 250653318 1250 250652068 250652071
    0x1021e03070507140a0909050a02040c14030406060501030c0206040c0302090a110c0f01200711060d020a02010b0102010b040905031902010b0603010311090a05010b121f081f06081e07030b 82
    0x181005101d514624585001c42c517400040c2000d01080200c662140e44464481d035075804c0191040d070780c50724804610341c069801d5001508180d10030329601d162920700780e0020f01013401540e0020340303000ca0000d4400d00010340140134680240d903005200e4915820840c04103001050b4500c501d45880620b5040c0c9841d2025041c00030024000c0d0a4251a00b14407900311259480d440e11103412801c109514a800c5a003103e19140e0410700b00b0185500d0100864146c0c40340c141c074180c80360b01c001503c540d0194194403841078280309034001d10055071030604000c1601e89064024002c0c1e001004118a9920762040512900300a4000864008411000900c0c2c0341c1090380300b5a086151201c044003a45010701c001a03002c4110401044154180b6807070300c0c081d0141500041c184d8100c1804162140d6025084c40140342c1c0b100323486001552030300f0209444403806540042c0803202c43c3c0303185500149600440007515880402022280c1074480750007105901940098918050740c070021020031101810035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 250654568 1250 250653318 250653329
    0xc211a0a0b0706050606090d0602071703010621020315010c0f140319030c05091c060e030405031002090108190b0d0602070201080a06061e0311130611010b01021e03070507 75
    0x642c41e82c09a0038070405840009000d03034070841040003001c03a10f944508045002c99000600180c40b65103501d0442228500d007039007210001004000042c0d810781c03041c01c1c0910704202c02c241995410640c08104242e000587d03000507900d000b014042036552250031082c42440c002e01140c14200c0c0e9030b4032002d403108039100c51000c00350030001d0810b01110140c424400b4611240c5001c0013045040b0400030003e0103203010261081e00045204602c410400d007406082c540c00c50805c21074151000c0d0321170394a80c49841000c1c001c0c024903030a183c0c011451300c241c485040042e11851020f9039844060841070500300301907021241d80701c2100400e03846000b032000340030740310381c00c010f0760360755203000251078000c3c000c00784940340d404d180e410320140f58480d90f071030100380207003c60b000b00181d819400d41c050820180001d000341e1001ca8105a6968601031040440f04140c171a10500041c11850b2800d0702d034110354140c00740c1d00104543c06c01140c1c100c64692251075600580c1d00345496941d4003030134000340764001d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 250655818 1250 250654568 250654589
    0x12021c09031d09060d03021510150207050901060e0a031509110f0a0605030a0e030c07261f0e0a03020105012c060609040204030203070605040303030c211a0a 69
    0x25001003503008011920112800700d200c08a085090002030f0700040f0082040d8000d1340c001c401001014001c00c08549000c1e00000035418600d4680305802d00f051843c8100c4001c86c644400c1c0080c0c1b20700104070300e4103450003d40a208140c2c2032040a89400720662002c0e81c100413619030000100b5401c10740109414500b00340810b4080103400c02c00090940460308520405035120b00c4c00903a1f8955514030201c2d521800e0880c0c89075680c040301001005822a140c8007030100181c3d406000c02c02051040c01c1e01d60306448a40c001001e070860030711009008241d039907190700410303a40c1c22543d048101010f040c0038090002c200a600b00c10441d040190350401200542e4456005011818504500c030340100304100074110041d00c50340300b0104480001d400790380504000100d000d007035107a9070100c9003d160041c0865044981d504e50040507a4000e20090b0700180c80c0ac8800301d0007034411540000344080340c584007080c1d441640000ea004201c0710500180d00c00182554018584500c40000c00800d8034240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 250657068 1250 250655818 250655831
    0x1a0f182e0801060f0512030a0c1b141e0612100b04090c0f021b0f1804031d0108040f24051305070b0309070e090102040504090b0403030b0405010608060112021c 70
    0x42c104c01141c1c0105200351b440b81905c00c4c007940000155160103d0610342400b00d030066080c84442d07020401c441d0f00e034443d420b200110b11541d441d42c2a810f0352005803040c5034841c20064204c000d000b050140240e001c08100140c26442100b1144150449007034034900c00380954490801c0001d0384107601801405480c0c42c585000e0b0754100c2d44d0840148070b5400980b401c407040114a00f007980380b000e0700a10442410326811010b8a401c14160024407984494903c24101818058100c400d80880728000c83c007429016482c0794483d107001d82c0100d502150491443c3e1250355001c800e6900e1440380700490003c00c0000021003c0b500907140102c411010450070240305080a9043c01520b400c0100c11850800a101e5410340000c0e109c0100d444e042c60942c49915810303550341c0a440382d82d028591190400d07009070180302042d480c280c042c40c0b181d10300304684108001440b05841091088001062111000910303d50082141c0380b03514840c030000624158116084100003c00d03050384118059440300d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 250658318 1250 250657068 250657079
    0x712030b030f120a030e07030f0c14030d0e010c0615061101020418380901080d0e09150301110909091207030c020409061a0f182e080106 60
    0x11035908580401c0e800b034940c1c0844010707225900c5400c10101944034000189100d8124880c1d4001d488241c2510b0540d03400c20f60300c1c10505440001c43d80251341d17440002100240e181001900900c0d0088040c0241000c082804400d803000d82d040010b0f83d060104454107080050300500c6103a6100d00c42ca2450300442c1e0034080001c1602031981604074282c0e1041200b0320008000c1c010030f2103010b45812020680f100d440c1d4944014400792080c000045202600d840c4014442040c4105514000d90b0349800d9a0ba80310700707042d600c015089090010481990721540181416820140e12080703046c204041a01c0800219007142d02e00c004840300c910020400003203e2508284480c1c2040c503c20007014a500c602d072050816118602d001010300aa4000d28400c540b116003102000079000203040184058850403050002c55440c00a440b41c0d0390070003003c90914085800040300c480c0740440014541c0d401074282840941c00307c040d15200030f42c21801070407902200850f0050300b84500041202840c08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 250659568 1250 250658318 250658321
    0x309050409051006210605090c030615040c140306012d120b0307030201021c0903200f0307080a020111030405060313050706080f0a02071a150109052e0306080102071203 74
    0x250860000350000d46084170180804c0306003e4800c40d0007050005058942d0301c030346c0d86130814403100d690700b6000d00303410821101d004060103201e00340103507014802010480d078201c0b024002d04514005030001800440c240354414203900200e1400090180c103602c16000b100040c07003400421013800590402040b41e80c000c4a800f88100030b23071040c0c00803c10542103a002135142c540e1034000c1e010203881d80032220452449882007100841d0000d0042c034480b20042c01400702c00e0085010203014242c584611801c5040004580b0100c96802d03002d4040400251f004488241a5803c010003600c01404042020343d6200c00031805034003206403c5490078194a0f0007824011158000d1080c030200381c0400510711034a0301183d40c404140400181c3c1e0780f0300d500d400340b0300820200001085000c0c0400300036804803d401c0702600620240c0765400385c00d98035410800f400405443d4407202090f180029605034032420040c2403c07d00070700b00414200d407580b40c40303422604507003820307503c0c16014a4010b4255403d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 250660818 1250 250659568 250659581
    0x7050c04060b1b011113031103060108120a09050a0608010e011a0403020108040201030905010e0609100501050a050f0d0501050a091103010207201c050102041a07050c04020703090504090510 83
    0x280c4003030180398940001d010403802420160740054419001c0744894000c00e500c140032116441e00c17007a89a4501d50b54000d04641e1074002100c20721000f199180140c68000780c50360480c1d800b01c000b0310b08185591000700644d0018040e01e4180504641c0c0800c40d9a00c1c5040d00b409089980d407100740643c9070140c2202c840c41e060307116030303070500c2040c0c140f03401c0c4082d80b41100d0980c0c0c0c0a08083ca4a91582d2004034000e00010384050429440c040d8804481240800c2d0b00b402480b1800483d0301c1c10707a4001036941258400e101c1e1540c0068800001c2109051120130190780039030040001c07004050649400d400e55004a410801c015590402002048085945409540700a400842c14800705949040c0030000318a0320700079846036800450340e103544200c40c00c440c2c4070100001e8085e0005510303102e401317504a4011000c0141d401c04400d4410404a0260b4401a8101008100911044091000075485444254104071500310041495121030043e02d0030705102c0d1005025036003c0c800b41d4003c5646 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 250662068 1250 250660818 250660843
    0x2001050709060c120e121b0f0307060e10090f090b2e030f0e010606020c03190f080705010b06040b1c020f070605060f040509070e0912030109020d0b060d020705 70
    0x840381c2401000c204d994840c110200141d082042801703500900003003042086030fa8000c00d610034281402c80098604520500004003541d10203201e00d00d0704201510344160b0300407c80003404c2043d85118910344040b400700c014041e4280343d206070740c0710620900403003a2600302855284c0c403404000308908241c4441c0700861000500c3c0c0715042840c1440c02d00c07880913041400c0c1011703100c421020340c0207a9540711206041190000b004860f07034039107001e501c2d5031040018501c00d0044890460702d0721b00103152030800307651000326018004150390302d1481304c1d00050f03004d4a45650751403c90300f007911348030300920191102c980d42039268006800c040021130602034030194080d006018100040c2c9020701614411680030701e002c241540c6000200741c4403081c0d081c0d210b92040c1044180040c0303070800316205080d5100340700e40b04d005584481c07a03190703034001580401403000c40410040280421036030180c2540f2302c0003440407503000300b103000148003a008480000070143d40042c80208105082044060420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 250663318 1250 250662068 250662077
    0x140907060906090e060904031404120b0a05040b0f04050708070311040e0f06060409050c060d050405060a0c0203190c05060c0a030b0d05120c070b070812010608101401200105070906 79
    0x1d0414030b6070030792000045d00c0c5d00d01845642011030b0400d03010b1054101c400c0310070f4142e1612035960707004601424421840c16515100207001003035a400303940c0141403040c1d81000c802406038840328001c0f001c0600007481501c00340a50034010520700010700004008600135882810100d40c0d241c2008115030345007045184903400240d81a02400b0040340c1c255000c1c10890f070015035034081d07013001424107035400040c030b03031240c0001a06d0110030025800280601e0041c401c81e4400e0b55210490401c072642e42202c000541d2040c80065034034154580010000080380c5868480180d003075403124940001035034010216200403804c41d0007260315201e44015114100c88440c074402d510b40312a9100c00f624240c0790120000003500d1025003200b081307034400600c071030301166541c2c038040e082105d0b88ea00892255074921780350400029000b481000d0582c0101740c000b8a94249500c4c000d0040d1686801142c0b950501205200c400c40c6c108018011052403001c1c0c00c00404d6600d401a40140401c9241e000740c000e01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 250664568 1250 250663318 250663337
    0x219030506031e0a0b010909030f0912171c05040506090c0114031f0914240904020112110d05010602030301080d050c0106050406090e1006081002030a140907060906 72
    0x9a800240c84084495680b02d0754003544107083d10141851a1280e015006203000c10000030809403d60080c0c4040b0700942e1044c42e441000c2408880c40d42d1070b449008078048804c2a49004901e4108a800c05601c1d504102458002071721010240880110728220101c1d075a141004207000741800490b40c4070703030340001a005150800c0d00203040005241510b100d070303c02c080001018500481d400380c01121401d070b0340c9e050b10b03907442d140d09010340074200041c060b10500300e001c100d00b511054000d44000750f1811004d0403a0006606110001d50f000384103a0401c2031941e078a0540010a1107001030600918418594030404040c0320300035a9010703030124085601c1000108245031001c661a1007281c054a401a80d070503400e4501d50142449803c00341c0d00515044000425004541c0101c0c0c100c00c40d0016230722070489400170202154502d01c01c510198004607960300d9840007560045070700c040d02440c00605401e29541200006404a6040d44243d011607800c4c00b400d42c01c424003400410180c075214442 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 250665818 1250 250664568 250664581
    0x714090a08010f0f060b041802071a0a0e060c030103060213050a1409010503030403171305130914060103020a090f02070803010806010e090307230327040e07030b040215190302190305 80
    0x114030135071242005212a041e00807903901c088c0e404a800c15504440e038600e18207481428a1007061050300c26000307407440d0007220207a140021541c54450a0509001815603207035484d48806544140f450000145140c90085403540d14040d070740001e0041d110666801c0040e0000348180d04006801151103548244410070000302800e0f034040c41a102d0216098548a0309098401442c204d9000380d48c0c406403034084001241e4050b8030003000c2c240030b44820030003500c0e013070481030309e402c400e00001c0d4111140c00300c180440b6031107810441c3c07500c1413207800614045154903401469042a0003011664000000402c420b0304003840c07140d000300c920409980b606102d580d0f2032000035404c03003486240321031003004030070140014800d0300c500ba00305601442450744440c6854070038294000e03000f44102c6ca0846125a000b100042c4101503d0340000843e4a40d1220703000c10103040148100c180104200300071600480148242d40c54008256440250302c4030049011804d002d104044043c003098a41000c003c2d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 250667068 1250 250665818 250665839
    0xf070b0f0f09060c0f030904060e100905090c0301021908060a2103110307060b2b080f1926090c0405040201050d09110901090e03030714090a08010f0f06 67
    0x115076a0814403607540305603100109103140116060800d050040079020001c0c000088000c01e04160101c5007045400d86a241d0565100019604030345942081171060080e0800351f031040d038108400030b00301c80c281d03140c0c40c000a0070382c1e02c00c010400d0b03000d4403d20140710490300442425040030080b40c042044605213940100c0c0d00d6441c02e141000c0017011800803003850300850243c0c100307011000541c0d86c1c40050782020000b4103a80d1070010300500d403843c8072030102030b0741c40c06103840b4080c03600b08240c00c06150384441003a42c000050000342580100055603050400d501c3e03035070384000581c4500d8003041c00070b00880c00258100c1e01d071101003d074000c10000c26a00114204002640894000407a62030318001241d160054412680c0c20714036000d1014107000c80d01c060804041d004940c038400b660780702c1d9401019980365030703181c11749a88148085241c80340101e600107089030320224060304150141c80042c100500c40c0d031200c2203d03551190003110740c20090160116581c2d40c560180115842c0058004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 250668318 1250 250667068 250667077
    0xe010608070c081917180c0603220f03030b01030b15030703150803071112030702091302040501030804181a060702010306030602030c030915071704140f0f070b0f 71
    0x10100b1160840c05020080c1080035a00303c00b500031031906001d1021400a044036000d034103500340c0d16480e400000c264114500d911241000280081c3c48060b40031400c1c4003042e04060224844030b5080354200750308900d0035480c5000c440c060200c0300080c4803103080140854142c14410f40c10103040807a0310030715494001043e484d200d081c08a095032559510000ca00034603011030034000542c0c0000001a000301c0010243c5500f5009201c09090030309a0402c10021390f1402c03030818950b40051003030302c000d481d221002d154030508029969003000740c90350000b0100c4509070811144950041030500044a410614802c0307009801c80400c070100901a280d41c1c0c000c5040c3d0307258865180025a01c045912030740181c0010f640c031940070340d2a41400a03600f50707079030021103180420344100c03030742007800c50889001c10340502d919856620307a1030008480000300c908003c0003664a0303071051302101200d5204000c030040c10691755004d1b204441c241d41981d418840594441d004401d018000074041348001402c98 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 250669568 1250 250668318 250668331
    0x905150705030909160f02070e0a0e030f0d0f0c0f0c110d05030f180a21060b0d060501030302061f052e02030d1413031805040e03040306060e010608 65
    0x21a2a064a440e0191030343c42101036490b080880c00003889201d400c040c490350841c407815284c900b2426040c00c812641c40e400d0b8443c030311034040058082120386415900180c54124140103403860102410141101c0707500080d086050350351783c0ca0311410380e06164442c1c10300d0b440080c5000c05c3d90782094030009002d000500e001426502030010810440e0340c03409101811194050b0941c0d40392504422508003541044403c204001c1110381d8010040c036144500c242911070342e001e4020250840c034031600d02a0030202c03044803000c0d40c0c0c80707020501d55909444c550900d48900d07800315041d811403600904203200030703001c4081014000505811440c0b0034090030706850054404c1d40c14010002468542e446910015401111101c0ea1000003c5d9000c802050b62030754410742072200891140c03141804900c0ac440040064258105400010b0700c0f4a2422003030310000f4400d001000e0301c4500083c11200700030900086503000103010010040c00f800359030014541d800404c040b0350301d4007601601c0d19200a208 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 250670818 1250 250669568 250669609
    0x9090609180d050304060b01090303020703061503020405131103300927071e031d1603031b0308010b0d02040308030a0e0f0106060e0103090f060c020a020108070905 72
    0x2409690030020304903841c40694225864890031580c06821030b8010389090b5402420010012425402a0342400c216941580100b10441c556100d04005000c1008bd89010801a00000001d80d40c1c9003c0c450045081d5284070482d40140d1500400ca8007030343c04843d0103a041130381503121009940080162078000702d082000c0c0646200001c4e641d5100b49170310164400d03c0028200e5a000b01c1d100950a00c0c0022010b025042e11034010586405881ca151120044040d03840000000d1090f0020724007005884240c0ca1402050b000050606d4000c1045031b10305c222201d03080041c1070348483c810041841440102d110050651001428940c05024a000d0068002103401da280c0e82581120300460f00400415181d050030301841d0051f00300d032038200e1600e214030006403442d601d040c403e500032101785e6244e0450f00107001005401400900c3d07025200f88055203807030f00100c6d01501070b515031056030740e007d8604242d140c80050014034024140e4400c100700b441d414440f64580d03d84030a04611035071003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 250672068 1250 250670818 250670821
    0x4090513022110091115070b071b050a1202160f0b070219030c060f030c02060604050a0914030a090f1a07060f0c090806010b0c0714030123091209090609 67
    0x8286291054800f42c1025803490a40031030148914072540d02a101070850340303c01d0662280c0304403030860040340f10180c01894008042032845008108000c500f040302c008440c0c0700c143d95118142231011502060f542811010401c03422268103012a5800c12281c81c10038081030b05060100300301481a029020900e14009503020640d079421482020081380c0f0380d8403484594681c60300c2e40c0b01a400f44503404c00b08100881407450907000b409800c8107001c0340d40c020000e40e81d91a0405c8051704010b0442c0402965034174000c000302c1d600c1400b00e0141c000a9004507034540344820001e059800745d40c0281004803140c98103000d041840c040032180106410102500d441c1942400e6009001e29110601d503545802c040b8840c045d00000c444085555182c1522a140e036100c80d0082036109090f805509a0002802407002040d0401c0f03103074000314080d000051409008164101842292070401c84441c100820010900410090340b500f42c02400b6000b410906d42502149c0120030290000e441a4481c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 250673318 1250 250672068 250672129
    0x70b0c1005040218180705040e10050c0d11091908031c110d0b120f0a08030c040803040f031b03030507030503040614070e0a0510020c0d0303020c120409051302 70
    0x701c4c4400f8912032a2401c41c200c0c1080521850f407120401c01c1c00b078040c020700d000080c0341e141030f2055100c00c1c40c2044c00707000d03004807000c1c05500408008100d141051424054000d40d040c40e0300c1480a400441c680c5540c2c4d9540c17a030108120501400456106401254414040301c0c4000c41503d501e0345180021802c0f050b002110003003c2c18041c6212584800003040c000540780440d040800004426600242c0e902306181d04592100c540055143c1141d00c500c5400300000c6120f4020365208200498035130401e6240d0034840e0856201d1f074440c07070102560303090034070501030362034584c1504405851000ca0345c1c0f0302d50740c1e001c2c00600403c0801350600c0310100004060003100c2d003042100017110a8200c0d05403600c907501402002400681902900c0c11000101e01d40c1800790020703048580d540c0080c4842c503240d10403c03030514540801202015020303c00400704180411458241441c00c02c035554495003060f4401080303940040c14120300094000010000d038480a40c0000b01d10644c0b40042d05103103941 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 250674568 1250 250673318 250673329
    0x503090708010c09060315050604050f010e130e0f1515180928020303090907020f060c0927160c0c030602031005011416030e03030318070b0c10050402 66
    0x7548000d010354200091101000c1e40700d850301099805940702000091581c5041440d038a20320300410f6000345c420082444103181254000c060f401d030514280c0307104000d02003c5822030501410082c01523407a80c107a9421704000340f01b010702d80d02448000f480c4080d98901e032030244000180090802d085001103200207038844402e400440d204d440000c101d2820080c00d01a506d00d1610302413400100c161440c019a04003440103e031403540c00600443c01c03d8601010420300c00d0000e0501c41c19880759080e00c89244005112241c031500f81c11001946501100050001e02d041d000803c107450110040b103241100d003280c001c00c1e0414169a0022040e5200c00f0003a40d9001c01c4c800098080d0200c004000b0800c0200d40056218005800170080b9071941e55006641e81503420b80400110801407080fa10714a4001c8800c950a6010b403070b100b5034503502d120101c1c0c150380c0144da84034140350040000f850809030400507070004200403038100d40f8012411a0403921f6244030300f00d1000054881010505543d6403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 250675818 1250 250674568 250674583
    0x302030f0609060a0c0c02090f072a06050c040f0902040602161d04022101051501030605030a110a030803040506090c30070b21070305040b16140d0204090b190303050309 74
    0x28008c10715034100088508010b00007100d0400008603c03081d00207419405144c600c43c0c0c1d4101c1c45844810a9181e603c1b8030250000601d0340704115414000002d00d12411061540200b00b0740c05c00580e9241496070003400d06000741504000a0000c040c00c1007860180d0080300c03e20714001c500c40030191610710004001e100a011010220040e155189050700419480103004aa034942c9840e9980101c00c01034058401c14843d895041d0411100034010a200ca400c90381a2030000300040000c03034499a48a006030802d44090311503501a07000c20055001c20494001540c2c000c46011000070208164441040365500202070851501c2120b4500e0800406c00700d400b038244100e805843e00d19a140d203501c010080840450300303042c44400700328540d000344162801a50440450301c40303070340c40d440884500a80c844a1000300203a91078a1a081005000640304001e003000002d82d4440c640707000c0380f065a801d0613823188201c1c06000701e0741a801c04e524041c012a64142001d68590740c510100b2402c1044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 250677068 1250 250675818 250675823
    0x150614220f0623042c010605060703030c030b0a050303031506040e01080d0206150319020117190c080c0a080628090f0b010207030204020c12070605010302030f0609060a0c0c 76
    0x107140c00400c0d01c041001180740e802031031142c01003110460398100f001750f61503008008900300301120703c0d9400c21071707034a07042c0d0400d00d0304000032403c250b0302c4010881e154800801600000d980d05204040079034503008423243d0441c221240b030780440c18880025103d10000c0c081d91100d03001c102c907059454407844180c40040c0841c28151000750b030350351611919000c00b0300c860320040c09040700150601c1458030162026103005001001d410030b400041c82c000b0702c988034061f8140a034901c0041e49030116801071030b104246d603047d28101c076001880284143c90028100c801031101213820030031480c10340000e49852110314a440c60321510b0310008601142e040c5528240601c020360b822496041e1200d80040031681c144d40c00b001142c40304240340040f1481c003444180160401c80c3c1c10405458143c01a01440d0650002d80744640d032005801400c6604c0b5071012a0b138513446000400a610307040c031208141000c118040d045a1034607409031901c1e00300062494200a41d201e903000c00c40b0313104411a003441c95 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 250678318 1250 250677068 250677071
    0x6041e020304140d1b0f03030e0f0c0a080102161b0b040801021210180c0504080d180801060f0e0403050706050705070516051518030109150614220f 65
    0x2040d0800c88000403401d0b60700c40b03c0b4400d207840404014821142c0708525005054464083c8000f42c2d02d440903907245d00d030103070101a00e03030341000b025243c2031100c2c00303020703018400415420145500303000030001726a21040351039105002c0c02056040d19001c120907a5406043c00000c00341c100320980140c20340c1e401180248a0105021070a0b81055000f0f00c43d07000007505480c07840d40d51171801145505a401200d009004502114138080c08a4004401d40140c600344241040d0f2240303009440c1511401c0300000003401606402c02228030032043c03401410204000340107050811440440181691003000116507a030000a001e01d4403a4082d02c08a5910500030b00090908680c02406500321358020b552030300624100c220070512000a00d41280d6002d040344c1c4034038404040400d510b800051002c58aa034420b070199465950a01c1101d80051240d0050003421b55050220802c940045c1c03c00d089101c0d01d1201071000e0b5482050210600e05940c0d61005d00140c20442c402c0a46032403019094080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 250679568 1250 250678318 250678321
    0x40305030403061103010f0b340303050a05070c17040f060c0209060a0602060c090a1706180d020c0609030a020a030c1802120f0606070b010914090c010806041e0203 72
    0x4080400180300b01ca005a20501940da000d5980d03d07464802807003425490981c0490401ca4054400050810b1003941071816414030300141d1040054250310340005003403140040034608064161044035044924210308108a2928200181030b240e840407024006000d00c001803005003604408850240c02c00c1c11000c104280d40d840050100381c20749504074401c0c14180300041721030030012200310484200e0b600811064440f088440b0140d4825084540c2003800700c4d00100303c1010a15000100b40301c800300406031345c41d00c00703400e004c403095841d040701254008500380c03645680d0000301c0602c80711045400350b40d00c85508000924201000d00001d4000d0000200001440000318140003180c040c459002070b0406200c00c804200e10405110f40501e500101c0811038000602d05403507032064025021501d00400d5890381c0441c0c5000340e06c1841c00507142e00f8102411308a0700480364208400c00c00405511811a0000e8140d090003054580a996510b00e5071007079081c0203203a200a071514100c02c43d5603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 250680818 1250 250679568 250679573
    0x2010c08070c090506040b1206010b0c0111031306051e04320106030302060901061a0a0201090b2406030108031e16030804050111030402030303040303051902040e0403090e070f0302030a0e030403 85
    0x1401c0205d81e0700f440341c2d00d0000340110906103aa4145180f030895030203086980c0c00c191031043c841d0030802c07010340c05d0b40d640c3d281c030304024000c04000e600a5900e1001d082800001d481d043d001d96100a00f010b800f60021192075606043e1300098942090340303c0c0c9604803584520f0700c190040c4084895904203252620310000c40403c0c10340c8802c007030ba4000d03801d03a1640d0361030b441080e003038400c0d03031145003100102c0c60701c403480112000d40a04180c00c084d00c00820a4140d90300c2c0d054540006035422540078207003410081d0f41c212280200103805100f07403401030030b40d0700d01455141c032401090000010000340f2041113007519030440c2280c051551b000100d021054050070000d0200404980403901981781c00e01007c44040058162842941d00400441c5140d669982c2180034000103042c80070f200a427400c4030303007502805001800140220240c0f815181c9898100249040c2540e0312281540c00c0a1040c0303d1030a5000c01442441c0007103080c0507a4903200e101c03081c00105144c09c042d0b43e4500010030041b08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 250682068 1250 250680818 250680821
    0x41a0301050f04020c0a240903111005010510051e0f04080c010323040201030b090a020a03050a060b0403080a0c08070602030f130b13020a08030301080d0f0201020c07210203010c08010501030f0504020d02010c08070c09 95
    0x151450801c0445039031a00d030354040d2f011603800380119907125039031039001d4078041d106100400e49038110b411441010440f0380c1807500503400141400382075900c085002d04c0102c20422103500d030b051091130280300390050030304030009468001c101e031040005240005410759000360825101c0031006010040b4a00c0d007602020000d4000102c940300090030800400e10801141c001d0030292000c240e105403500345140d60f0030300e043d070080d025881408024585440407420140c06031401e82e0254801603501c1c0707440c09201c000604024600d0700044031405114003c200032000f041d03440f4010b0342c1c2c03140c0c1192840c000a52124615440151148400000842c15040c00700d80102c0403e5141c507030940c81d07030303540340e00364241d00803a12080300c0384c2e104410801880085100c2614403107011300c000043c5600b03d401103401d5544807520700340800c422800400c0156410b01c14a015202032180c10081820103900040010035050800fa04101044246205000d0b03000308551400d980300c00380301e5136560781c1c010341c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 250683318 1250 250682068 250682087
    0xf100f0906030b030d051c0e070f08241308070510110301061e0509030a0f260d0911090901051504050103030206070311041a0301050f04020c0a240903 66
    0xc00c0540001401e078000d0288032000c42009003d0700082842d0f46044074203410241612507000c0c0d040d2503845100a0358807032101c001c400c1c41d026003c0300e8101068845140c0f040e0b032140da00e6078007208900e12400d5101147c2c2001034000759610840b1b481e4552038503c905024000a401c1c1d4600154031001c00c40000f4040d0204c8192840610081103a00c60b400c646000910a581c0032980b60350524818141d030200700300418055042c6982410b0101010a00e0300281c407604031001c440192081e01840307a40c0d103040d02e4565401c030310017884c80044101c20805000707008045d030b1507a0310354426030108030488032981111500641b0b2004681343c4140c109001c0c0405550440710003a2074640907500e41050b0081c681039030f030190003c0046840e00c0074210000d1141200c001300c0d00340188408110081c48143c4031402e8070a10012681340c0d410b0200700140c030450305c03545620030f6104100c0c24400b582c0c040742001d0b038503800c40d561484a4580000d056445030b071403151800b06901c3c003407010040541041444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 250684568 1250 250683318 250683347
    0x30313080106080601030209070c1e05011e020a020a02060c01020d0e03070b06030c0a05100903291003050a1707080406050417070e16111c11011103070e0f10 69
    0x388a000c1c0c1c3c0e41c843c079483c2d076030038000030313401c104c4410018000c4c6004d002040b40340b40c45a50714544082c0d151800c2d901c3d010740c00408949503511007a03000d01250080c0460038158031309a83c00c40c030b0507900304006035403200341c0c11009001d15408108402c0d520380a506441c1d8042054409004a1b14182c407410b4407984091011901104510301040351400e00040c0e6070403100000c0c028440c83c500700002c10022030080c403034030420061a01c40110026404040b0b0300000b002201030002040340604c59040300110050000d10505191082040403450005402c000140c01501c29491a071105111044e5849040e001401091000400155569201004000711119403000c43e80b10364414410f1629054240302e501c0c3e1041c4e41c140828600e0316050303503110700740400e0300b00103002c2c40883d20713421308080614580015010581c0031249a5039008041c1e42c4c8070300d4a14000300030b03445c503014200340c10780000f0b04040d042000402d10101075441e00710905101d50002048c00f0b070b840d070310b6190003007034010400080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 250685818 1250 250684568 250684571
    0x40b0901020f0106270e0a060b18240a0f03030207050907050903070501050d020d1b1704030f0c03031d0105060103232d090c0a0b0f0d0e0106050303130801 68
    0x1260041d4506100706002e454132081ca0031101790102c0128801141c4070700305014070a58030f0b8021000745808111001c2c07054462070000c14505d0f0800c0400419048000382040e8541404080244070440b8804504000c1c40034003017011002c4481020560503081c41d004100070705980c41e0044281a000129001102c0d8101c4824032199100c7c002121240074510a0940541c4880f606115542c00343c000707412520305030940140cd000301201500245c6000c11200480d075001400811805507100d40c1404100300042e00b44040c500745541e0007800b003007144a400f801c012801d0f031258200342c42500060000e4010a08108415680c17a050a00030502550a1800310345801249145180c401c90007076204c1d142e0500c0340c0c106944814284d09590440f06c035523105004400c000e26a4620303910b81440c010080709000340f010711200c5c0d082c0300c038240b12074010314200003044c480e140c0401499030440340c0b00661040089910300d001050075002d0142034000503814000850300d1207503500c001c5410021a03e070ba500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 250687068 1250 250685818 250685833
    0x3080c0a120c020f1210021201080706020f1005042f21120306120607050301030303050f0114101112070501110c0312130c170d0f050405010315050402040b090102 71
    0x909407100050242c000750000820408600f1924103c1c204c8503400724880162661840400306800c2280c0c058030107851040340190040c48000420404180031f0203d6000520301c1900c0e0040e01d581e03550160440d0100207460704009000c100c1c0041680080072286050b40069000b0b2007a81c07140c00c4145826503001d26882960440c003030300d21690407006030303441802900054503c2c025203603031580000c080c00d4114441c0d0b0417a201c500001c203d01d41c4070705d00940e1015260f5046d0703d001170590f40c1c0a0034070007860607140018851a00100d03c0d0511518044030502100801c0d200c0907030360b06c05a104000410f010b005107221000100c04020f0130700f41d108000070481801d1400c00e0768014003603160703204103560040c404012001812800c2c0d981162500741012459400380d81c0c2c0203174070002034018551141d810144288100402c200c11030f181d03245401c10003a020403e5000611a0049115417810507848140d05018040f120050300040c01c4080c00a55407640c8680b942d40c07050703000182090051080c1003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 250688318 1250 250687068 250687103
    0x6030705031e1b0d06080307050304030c090219200a050601151e031508010e0d0e09191112101514030601050d0f0203070c0c060e09190603080c0a 64
    0x40c4920403d0821011010358842ca201e000c41500410070f0a8000c03a074800010030040c0b41040a401001d20034001107950380d08500d01510103890300d91108070500d0040c05801c944d103d001c40d070065aa00700b0b1600c80300c91b081d40c17064284a628410080b070f0107401054000c1c010300c140820098181c50946001c18002e041300d040440e00b02c91220703a002290140c421600400c075110780c00415610103a0702d405540661120740395421603521020b8038501d41c4c405e030781c0c0b01030280c2c12030214002000c08541c004144c1ca840080640708680b480b403205011691000c070301e01d11944420039205480042c03400d00009190081d041101421540a081030b401130600042108900c1003512960b0400840007081c215251040150364035046205020712040d140c07141c5901d06071803407010314442c0c0030603910111807420600308119851040d400c40420000c1e0303441407240940700d50749601c0d0807903030b80b0380d03a81954803007515810000c0005400003041444c000501520003c800a469407566000740b80c035020542d140b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 250689568 1250 250688318 250688371
    0x61b06050a0b01110307020d06050c04050a08060f01060509010c2a09140a05162d050d0b0901060c030c0f0f050303072606010c03090f061106010801090f020d030c020603070503 77
    0x55800230b500c038010015910000311150800ba4216080d441c420b4205600c910008940244c0354015035501c0d40b282003081415043c600d51a4010a0700c0e0500518000c0c499000030b190302d20313801f0040c0180254008007403d506804c05070039a0904a51050303c40c9a4542c00d1a902410b11042c451145951400120b01c0c0d030f40c401e00c030b980c0c001c02000b0740304040c45240380e00075268550398083c8580044000808805030020b50f41c0019100740707080d80c5682d660720240000364221500c1d40c1ea0f8602500c84140103000154001040d104690381500b044110031140340380c42100151450802080c030030660000504000c00000510701900098485080b440181640b000718501001180c41030020f040c000301c0c44ca54005c80601074114080e203411001203803640314841c840100380d480741c8000f03148041d10107205075041c400d607030141078204000d1111100fa61262900030348a0100a4400e4050300d0b2176508140c0140c070a96221076001e0039298480c80c0820000d04690402c07030b84400e40440c0c1c204c5056108a15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 250690818 1250 250689568 250689577
    0xf0405041d061303110303010906151103030a09110307060f110c1507030201020903060c0a03060608060a03170c0706030b090108062502070302060d020a0e0307030c061b06050a0b011103 81
    0x20704000c000d40e0f0780d00c204406201110072003d40a000c0ca4903984809032000744000e601801613000c1c040b4109180c40a08944800c0030b5030b941081001302c00c00c80d84140030210032603801c514040c1012030511842e040200b0f282581c0280750760b0600c10074000040103600941e0380d00c007403106034944451b501703100c40000d600d5141d0300d465640e21011207001ca2035040d06c0d41004e002d03414080d1000500f49081c030300200c0c0c9840800d0b1490181500007080d0400865803500801021302403031310f4000c15504081c40032036005511030000078408454003140c19907030110792040c0d5a8201d240c0c0200e92404d03603a0704019004140e050300762406007540710f0000c508150000703401805020130780c3d504507002213003440c1c00824954006a5400314044c2400c008050b0f0f5850b07010301400c0082c500c0c0160f4580202c0300243c080e0241089a03806500514010000315400166050454040742000d106c111000403140c14400c071489002001c0c036260030b05210b4400010703885000000c0d1b0a0325030140c81a40d01c3e00d007642d640603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 250692068 1250 250690818 250690871
    0x20409051803071110030f0504050703020f0607110907030e12071b05030a02010c0816050309120c010c080a02010609020d0e150105060702041d030a08090d09030f080c070504020f040504 81
    0x103070100e0700139142011098a401c1c440c461800141b8403040f854880c09460059a081d55560b00c035000500951402c200d86404000c82201c4261030000307580e403000c0301c0d070001d0070105202e003030001c0014000f80e0184d004451100d0442064420801980141d0384254100001c1a5119801d00111002141c5441081c109a4800500421910100742e00442c3d0100d00c01c04100e4203807006108020740c100c503802011590034410b80c0599213500c000428081100c1031044c046045c0e031f10140c80340c0002d0360050400900c40b81c01110b0550f8407a15240141d0240088ae80700c4032035140700041e91605103601d5404181c003c107203482070355900284140c01d0311182d1820f0091507848402013003401d00624207075011034000015640700c41c5c224060f61103030600395000a6003d02c04180050304004075a1400d0282361940c201d1400c002e404281191034001c00e1007407003c0c0007070503200002680241d041007000b014004003002030081d90b490b52541a070301510b41151203054000e0782880600c3c054000616041903c0c3d0a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 250693318 1250 250692068 250692083
    0xb010f06020304060e37090f0b22180c051e010207151b0f0c0e040f0311010e07080106180506060a03180b04050d080705120f06031002040905180307 65
    0xa42c80010801c40b21aa1011241d9440680c44c183c2401b07502414112030401c5005c0114846501c0d1110315015141404482c03800b25142040c011303a03035641e02104881c0c003d0310705000900510103407220340c000e10784000c10070002106030303102e07604001303800b100302d4180d410507a440f0b12107450b94900780760380115042c42680540c10882003848000510201c400300064149010b240700d50703211100c8800034880e00010f84814545501603410300100204120003400d411403144e500e460140c0f504038030010854401420886031070911646500700f500410902c1410400761a1070310340d60304d1994000d000e5845030703448400e42e4000c40c0700c60911900c1110b00c50030002e8025072a10480310070450041c291150002d02c2c01a0081c4071102061000040350311480c440ca00030a00b068814030090903804004107a0300401508100795060030b005503980b0b50300300c4450001121661a084002801c0c801c2c0003032182802e1380701003400540d40403036403c1140106800c1080b00c00b1100100b040c036480344a849000317003421 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 250694568 1250 250693318 250693337
    0x1203011503090b1b07060f09031707140d1d0604030207150206010b0d0e030a1205150d0b06060c0a0f0b060a0f06050c0c100302090411090d020108060f0a030b010f0602030406 76
    0x1240b800c0304503030700d90300891a168a800850f40e2210115000c0f0309287c641030f40d81c1d8580400b01500000044070055040440c401c482c41c06140c0208a004a021034610142d0040345004070030881c1e4004200c9400000780310341704040c000e00095074070401110240c00511600400059910b1070603140501c8002603405041c16a003440d040b108154840b1198150040c1d9800f10394460b0b15041c0041c1c51492000d13544d54500400361000c1c00709031540500190315601c10306052406070303038075000c041003915800707080c0c9c1c060769981d1000100680190302c1002181c0c040c0c2c0c075807001044555005d400c00035201e079812185948440c418880945414003880032002c00c2c5c020140012801400a481d05010b04c00c01c03550000480400b042ea00c03180c079500440442c1e004150440c0b546000c0c00392852205180001e141043c10003000103904c00c80d42d1502070b0602282402150040d1104c84d001c090070304d0060118410160b49140281190000b442044520403d00e040480c0880c40402150300700d030000c0d41c54840e107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 250695818 1250 250694568 250694581
    0x31207030c1701051e0f0306040305030a0e070501080a0f0603060507030b03070b09060f07062c011a0f04020a020a080712080901020c03030105040b011806030e0d020c0a0e040201111203011503090b 86
    0xc080c40080c22175001841c1b10f0004e409640800510384124420f83d82c3d5601c030308040440740191481c0d014494650741000780d0234001e50342c3c0a203525502c0160b000c0c02082800b01c10184100a250076040a0425410300082286150f0150007200800c0d000750212011580d844054102600030ba610060388008104495030050314208094002d05000b15030000b101145a007141d00300100150f40705d00d441d600040794401c410300138440d20004040c0120100c41c081c10f041c002540c143d0220025074030440d0301050300c0607414420011080690782c0050885d035070f44100c0c1040d04401a442003001c001a000600084903078a0600a86458829020041d42540d0038001044050a982c3e8036480c1045803403030540c007100b4a0506031000400050320009140d42c0c40400850800c151044420309650200c401c0311441d0300d807881e0402c1114151010841d00743c9443c80101e07487e42c0e60648000c01845400c9400840b010800006e40c100c40d05186c9000040014120913010380340c00207400780200d980031000885e1b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 250697068 1250 250695818 250695859
    0xf111c080603030d020a0206040606050108040507051908070b0909070c080d05060f040c17012705270607090905090316020f03070f0f0f0b1803031207030c170105 71
    0x400200040a0f2400e08000034201da00320b801800401005a208405100901500303100b0803009e82400c0c600103c0c02c1ca8a629000e46c3c071913640c40f42034010040c1d001200001e03010800b54101800c05a41a60000c03a80d400300c400c0f070383e08101c4084d2b11a4514101164215019480780383c08180d00800c00e90601c0c5642444030002c01d8020045038104009078140003850b5510300c00c030f920529241e10b91060242100c2410301c52204141c10400d0350700c6004c541880b4100c0340d18100180d0940c40072000c50255078010001c1141058103035040d0401ca148004001c4030140401c0c8e07a8802c816aa0320842c103075940b076510740309481c01503032040c050707402c100501c000310070f0440e143e5030b00e1500280200e4290520ba4000c03915041c4240d0281c0010654024113020a1b230141c0034100051400c091100328880c105450b042c00751280082440701c0c000800380100a64901707100f503401c1d20307080c0d440c900030a04c0d01c010058040e051801f00200010a41d11002001c40f203160101070684401a10003845001c10f1200240e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 250698318 1250 250697068 250697071
    0x90201050d020d020d050c09030307150b0d0c0e100f0b030a060f0801090c080109050d0804110901061d100f050904020d06081507050406020a1e0b01060f111c08 70
    0xa040090800c00400514020300061080040c0044010390390040c0e2a480822074001401e0601d00200800840c01e613654000107440909030091a07201c3c000304100b17841401024141c0c41c0307603002803a006492040c041b030f102e40d6400700c40f80c1503c280125580d50a811950b41c0310350085101c42c400745030342440361014040c041c59000310100340004805444100c2c100724544654080c0d551691180c4135107040184000c6c0c90b03c0207108c103034005d1040031511760700d80380c07a01121006c0400b00030001c00000e00f4480d0541e05074000c010050295401940c648000901c0c0b074905e4182c04014030b14000e034440741d5080c10307040c0c0449110340b42d60b000300b0b0b201240c9040764103602c07a440080e4800e07000e0109241d4410207100e400b00078818040141030b10807800d00c0703184881c1c1009000b0003d020050000b0019580c000c2880b1501644c0701c545d40300c25070028201e0440b601d0804031301905590200d400401c47e42e40000da02007010311b0031380b80e405400c003103100521381d20307044111600a54100c465031001094003030a00305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 250699568 1250 250698318 250698323
    0x6010902070813032f1c021f020a020f10021c12021c060608090c102007060206010b0705190201020a0203030304080a08062d0a15090305010e060601080a09 68
    0x20707031801d00036242507403c03c180d54000741c6045041d0075503c00c80c144a800c50308800c101e68140f0350f001420080000e042c60615504a0031a001500707801c804564424014004100d0718441c24258800144402580d507814808101e001d8094103020a04038907004500d0b1851401d0359004100d5040d030140805018810700000b4028421144000f001c100960700141014404d580d94481d006002030203000c00fa994158002001d0060142c2800540e44000c0350b486145102034450444000708244211101f81d052a80c004590440e40f15210807214040341030b00c1120225402c0307c1c030f140d807036a10000a51049000c005c0c03541c1d0207a000c10600c100c11001020f41140140107554120b15642c0201381164000c40d07048860f0103000034204501d40d0003042c1071350009019589845040111403e185806103615414590140d50f0492040f09a4640418101a00301d0000c80103c200072203c0c00742076101280802c8549509008001250314030004810f8071031a0140e4801071641c0b41e1050751001025820b005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 250700818 1250 250699568 250699583
    0x40501140904140c0310020c010f060b0703050715060e04030905040e03070b0c120108100f021905031315020405031b03070e0a060305010606080106110c03060105060d02070f050105270601090207 85
    0x544c110b65014007007051040a2488090f95034521400031901b183c180c5901507100c0d519004050201d8250700c02941c40310359050600c0d69840c0001c0c1001e08030701c0c0e0552442a405410502d02048160412390524021807003030311000021611f4008000907601995030764445948140900c40c0030640503018940c101466209003803600704c1c000700500e141e042c00d800c0701501703a100095072102c2440ca8440e184a0007040c00b070450401d081d28409450002c4000003010401501201165150302807600e03802940741c3c01008020703140e810514000294225206840c82402580390368250318450462445d01040000c016004190500c900c5040b0201c000d00b02c0038846954100210000302c09200b010060072054403500c442d50b1403c0d200402054811070062102d8008605403038081d140081d0250640b80d00300e91090b00e0b0000c04507040001d008000e0080d0408232101920402d100c0198081e0b40a107410302c480f404001d40000003000d0314036607810035040e41d90083c00100064a03081c1c2c05824001d03c01c489 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 250702068 1250 250700818 250700833
    0x1080a050c27100503010f0605070302061801020912010506040b181b1201030303140a200a0509060304060501050901120b0a090c05040c09050918030714010e030a05070204050114090414 81
    0x4140e4195020f1a54000320740000010310030800d02180074401400d180c508203180450a81e4000d44442c0098600110000090904082084290180e44c0c1c90000940f01d64880d90100d6012806445c080c0d4040380214a4044414070900f0301000c03848a8060a110f1002d4588403503d50507030840034903490a85903a000d101c0c451040402c004200c0c021030096402227150043c24000b1442002e01403d00300c0107510f003820010b80c0510550b882102e194100c07641c135403500c1da401002d90f070512aa0141643c418800400c100030070410350310030f906844081d0b0b440002c0780c2e02e442203000e00c2044090058541084000001c00c00d021a030403507000240b2808100c2c4400d0b5503800403038251292003451101041d01744605002e2401d25841c0e541d4403090b900010041001422076094691080d15030140c451061550018042d207000d410400700303143c2d01402c880c0d1f0b901c0e9458004190b504101c3c42244148c0c20180000340000d008107040303e10704001800210781c0c0e04c40d640c5055801c4440101ea1026018548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 250703318 1250 250702068 250702147
    0x10e0613030506150d0201030b01050d0903110106150c0809041b0201020901021203102105070b040303030c0c120305040f020a08030c01050f0c0910050c0102031501080a050c 76
    0x1000d0204084818500d103111800d52405a003803400081041481403e00c100204a135500c10301281804c41d0203080010b494140300004944510450025041d102e0a15482d8803c06070701c841c1442100c05180001c1111130384813480d101d41004d442000400113198815000c0c046600040244543c14000f0400141c28215607220794904407400b0030707140580d50200f1140d050703503010f00584070740c902a50760941c5140b40c490070200d1078003040d0181008001d4002c0c070060008080400011000750058100d0b4a450340d1901403103065071090004400082c10203500f0080c0c54059941a08401d5110420503003681507500114000d0070020702c1a00c40301e5007542068096101e02d10640098050003000d55502d0400442e09400c2d0ba20203808140c4040840b0100004d0101030400c0d9404540111991181d405402d8811038041c0607084090000394400000d02c46000c0c055020010360441c2038840d1409036556000e13070011240c0c2107510480d0300e441000400744007040150710340b03211076100782e01030700030500203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 250704568 1250 250703318 250703329
    0x122107020c03011a040c08040b070507030201020d0905071701021908040305090d0323042301020a051603060509030a0801050f03030f030c1201080a050c191508011502010e030711010e 80
    0x10311301c2c5090790300a80500c10300c3c10f080c0a0030110008906103001d02d400e042e55001a15140203005808114002c0380346d01c1014400e40413a41e814015100c1032244012609145490721550b10801d42004080310701c1c882c10090600070b4400107000007486488840c840841500c4802c0010030032005c00000308000c0c1c805640e580d4030381e40c0803402560b803c8082c40c071042408241030f1040d11402d5010b45d00b800200404a00c6042080703e40a0702c0b05880c4010489900507072500e81c0b40c0c2d00080c00f50107106640392482481e20390500c22640030302002e100c1380d101ea10020b46c8038401d4540080c0081c0c1e8440c0103200a00341841903a103c800041c0071203241405071641c5800ba45c2040d503182e100c02c07400144120955092109144c098000d80000d003079100625590103903514581082c0c24016410035014480381079042403d24020315080f0074004400340e203202c00405d203000034096040c2e504125900d900d58240305224000a9a07681c0008500d001c406407981010b54034100302031410020140203c09103510380 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 250705818 1250 250704568 250704581
    0x160309020a030b040c06180f051c0203070b030415021809100b0a0305091b090a0902060f0a020c1008160305090c100c060b040c08130c03120c05122107020c0301 70
    0x200a41c860711410228010487c1c841e00c07078841c01003100004184910030751101848200c401c00c0710310041c1c10018142115000110202c003950501481400245001d80003000314072652069400742108c40f118072201c001c034007400f85c1709160a450310b545c04a49040000784550810030540c110142980e5603001c02d0856070000d400c00c0c0c0000c2e1078900340300c2550340c10005032803034030138143c030340d00180e411000890400c203002401d14800c1c0361229402400c2d0340703034841110400c80d031204010396100c00b03907040a07590342c60012200d8050300304038240420310352049070b2480c0218030380180481030f034003692022005800007502d640900c0c0281e50300021755603101c10240501400b00c4c0c0307506407411014103020f42220408000103000c0c0d811319603400c0e18968415009a8880705811380e03051950003600b40303050201c07905c0e04018030f010143c43e03000e0240d0350840c1500844900c11070031030354001c04846890f0b42a004041c0003080988005100c074050f62609503110b5800b40c0d00b4411183c280d0000400a0b00352404c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 250707068 1250 250705818 250705823
    0xb040e1e01170601150206060907030207081224030c0d03110d09060f140f1b01050403030209040b12191b0f1a090310050a020417060a060608160309020a030b04 70
    0x42d01111600e11440600186004051001603a00b4007408110007031340b0750074010b103281c0c450304c8443c0000704042d00950580710300035002582c80391140100a45225403020030b0743c0c0c44104028441d400580200112085811082c000c0c006c7e00038070042d0414000d110305500800c406005181454902d5424200407a510845003a690b103030b40b00f032030480003818070940e80942d0300400c04001c0740200c9050b0304004441040342c01090b60f80e510710b0480340000e414030480e4040c204550810042c00141a415005054082400c50f010812000e0301804c00403881e4800c92a000941c012250317140360b180c502d107110038900e03019240503c5000c0601845507405030054109078521250308400f44a540c028103003082c074042c1042134644c0b502d814240042c2e034400c10200380d07104c050789030000a1200d0b116601910024903f150b0710320322180d410710207251035070030889006a03040d11740040000c55902c50a0010b000e1b01110620081048900d0300072030103085003030ac090745c10001c010000000a00100e203001e210b82d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 250708318 1250 250707068 250707089
    0x20a090518180304060906080c0f1b0c0a0515160f0b090c040605010507020909010e0307030201061518150c0b0405060411090105180a0f090305120c040b040e1e01 71
    0x10340b40761400700703030b24100700d40d1241070703009000901000f03402c80e0008054600e51b0409a0702a59032481145a611480c181d0010000340840c900c00b00d2000c1c007040d02007990b96081501c458503101d00c00d10400340e500e031044945c0000081598248220440c00502401203103d0b46040204420b40b10f0345240a41d4440444444042004000e580d41c41405184058001220140b0017180b8060008145010701540684076025200210f00c102c0002d611094040d60118142d0b510b5940d03509020340280101d00c6640c0a20a00c0015035041511900110f0810000002c0c1c107070701d69003003840f400b0240005013520010f0000030702030030300462800391185200318880c82c0140b05a04e0310b481d2a07000315104002c0035004517100801800b40f9a0b5041c11100d0020001c81d1100d4a561100c28040203000380311410800d49180c0b00c84030082c9540013004003400340c0d65600441070b0b03884a0409100921a510498045000500c01408084110085681c2090703001c5842c0270104142c0e100e2400445081c2c0c08010082e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 250709568 1250 250708318 250708321
    0x409110d06050607080d0e0c0a15080c04060206041707060501240305041509020411030a02071202070f030803040f0209012403050c0a0309212d020c04020a090518 71
    0x300080c05024054401036807814102989035640c3c41450040040d61158a03480308045220030200300140c1404c0c034002012140e00c545d5545142c094403410602010001d1003a01c000394101c0d0602080324101d03190f550041010f40c0c0d0300e844200c0404101002800040f2040010740041007090203070a010f07011610b00e5810740401e0b007002c0d0006543c04159541414180b204003c00300d125150700f00407401001001080b001301a10000d001803030451603065085a01000f40a0300142c150f01403d8120710a03101c10944601070a4207a030360f01c2c120311440107811441242400020080400f4540252040c00c41544401517540000c003007490903000062038814070803840d110b003c0a041c3c811012440c50400b00140d040144d1134500b42c0c03055150f010306141d01c40d00c000041040e20301506da82a10601c100b0059008244c400504805c00030409920800c4450780000100c0720b050020307403541d08241c0041000e040e1940a010203034121740010024071000400024007038030703000c00c00c2003c81301c1114401904d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 250710818 1250 250709568 250709587
    0x61608120a1803020604170c0a0602120105090906040305070305040509190b0a030c090c0e15041a030c19120e0102070b0f0c071104021309050403020705190911040911 73
    0x201d46458941c22140c05103600ba803008250003141103500a07170009115808507150400d00e581d944901c5004040a2040381007880c01c2c861030341c0c080c0907402c4e01340d0481202da0741c3e10010080d0a980c02d0341c00c683c0e00e812003000300c3c002902844c010201540b1130300b41242059540d600080c0311070402c0360300b004a9440d07801c601814492500c110410044121126080743c0e056417504141c140703240c00751080c102c2e5a0f4a80a2100380549101c3c8c201740001030808603540d0f408a940e0340560410b10410400c0c0c1c0850316200020f200003010740f440b44600508103400c1411094401844c00400c4112405010102c0c2c401038070038001d80140054014010005070b618901880d20303a0000784c00504040c0c0c4103030728a01b404920340202c0304a924158000d000c0340000388000001a00034800d186040081c1b10040704000707134036001500702d148203500035029240c074a2794071000e001e801c001c2c070682c0b1184811b4080050100303020581c001483c101950400d42e0405407280110422102c0d801500c2e4240d4002181d0f8011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 250712068 1250 250710818 250710821
    0x507351906170c1c05030301060c060c03020301030201140d0e0d0c0c05030705150a050d06090603050c0915010309051c03141305070905061201060e0115050301050f061608120a 77
    0xa1882120b0381c0700c07a50110600c951140c0980490510500340318100400b0350402c0c0754079038055600074040e41c0d6603503920034002e000040c40e0324007110010b04280d42c49080798024820340e4100c0c3e4040e1208207019524418003441540449031903075603296a0840780b5800305041003164000708240d03d803a14100294107081482d503081e680018400e51103076030140803940300c0c0820340448c104200c500d9071325514913480039a0580500501e81c2400e40c0703001c100103001d1384123400103021240100e003a518003050318030501c284280c1c11601020050500707600c0c43c0c1d0a5100b41d10005145000ba4141d501c00e40907004000c00900c91009a0000661500307031034503441e40100c1d00241c0184100b0a00410b41443e036a441d900c400007446604001d40e40d40c00003443c04e8480c620032950300c01c20034000300826600c5603003040c3c052074203024003010010041c0d0218180c90251007280d05980c00281004a40002d0200300070740c680c44010400c0b880b0902d04482c90000e00c1c240040c00050a51405400c074030303c2c11341d40860 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 250713318 1250 250712068 250712081
    0x9090a151710060b040603110c01020711010e0f090f0702010f090c0504140405100c0504031b03051002090d062c070302030c01140d09020102070513090b0a05073519 72
    0xc8501d00e0030f03508000045074542180c08507030391400d010400e0902c09160581500900003011413550000400c9001c021501c44408041c00b000d894a210b414120020710010b40341080e0615081510100450030340c00184480e80c0c3d1040c0b8510004c299850082c80e4075058521203e0121000d840000050100e0310300340c0128042d000000900402034035141e1a015510742529620b954510341e41c14050414030f108130102c6018540040d40640b040d11131044030082c400b124072064400c1d005041540303071400054000c440440c4001030584c1d600c0d04094848000401e01000d403681e0754840361030f40c1300400d80110240008552000058500c062950050504000b69150300d9410883c020500300b42340b11200741600d6003c5140d080c0050710341c0c01440141d15180158102c00c0d4402d50384c0c1d0160300547c02c80d4014450451007481c121039587c82d0300c51548281c41d02500d0440c046044411a49400c8050009004d0071070107181b24030766008044103c0940d0f2040654910b006d245444522407024000c900480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 250714568 1250 250713318 250713343
    0x709060f05040f0e0a08090f060a050307020c03030c0d03021c05010803130909031b0f0b0907240915120f050609070903120c1505070804050d1409090a1517 68
    0x181311903618040c12907141c0c00c2d0100020810303039001c02ca074207082c2c96148403204000400390119641d070486000c0980745d60001c848510051080040f88545400e0100c01e503441d0364103030801440e409074103c9007a00650001c103040500d41c608402c030500d81400b103001d098001c0c01900c0c06142d071250400d260309501c00341c54000070320a074109541c2c0400a980407002d00c00c3c14140039182d009031100b500e000200f0018130900580004042810f01810310300c041151821250619181c1c0c400da17105403d801900044102e4150200d95074050402010206040198048100d85401c1c100591640708850850f6900e44012040a644404005050400300e0403a60400704505000c1d40072071440d540e07260703a552042c00500402c40104a06400c121121000c1c41c1c005505100a022902e000c2c000140050001c8805580b030340710703104c042080240580380c80e0284c0c40f0745ca4480340c40c02e1010814450003400190268000e90354030080e601358105644409000f42030305c03191503410b000c4d46244052a150415141 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 250715818 1250 250714568 250714571
    0x30609011509020306120d030606030605030613060b01090803040b0301061d0f060903101802210c0411071b1701061409060103090c030c0e0109060e0402040e0709060f05040f 76
    0x10165070145103400d403003141c0c04000d02694a075134120200b0715420008031522070f144240175140e84000d40540000050f00c140703640c10043d09945004056590805446112961214114500106003d504582c007105018180340c10442e2b5a0390182d859940b25600c071104100d00071005110223030344001c8114404013007034500401c0402d60780c00100405001007441f44107107000200f030042914180105c070f42c640f011070741c1046581600c0b02c0d08035602242c580b00328031074114429100c2d42c081801007100e04003030b0301130000c0200f005820107000040c034030398040344540301052003a00c000840c280b035403c0d2440c4170000200b400d5403071703d18a40d5034500250a40441641407850502c1346241c84508c2040d080e004a4101c8204c0c0c4609005034000e040b40030026040340c00c1c402e004810700c01120510780c100e4aca108010398a580c2d941d00d0000440c0c140c1d000b940d008282c03000200d005032901c1d41003680441c0c260000d458001e540c40051101b1075280358001034600d81418400c22292a05114090308a2011b840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 250717068 1250 250715818 250715831
    0xe16090e01060e041e1410080a03170702150106050901030b0301111204020a030b1015031404023d09150e0d080702030105040f0209070201060b0a050c0f06041103060901 74
    0x601203900583c0c1d100d002d20303a10403c0340171070490001500001e0f880c40500300300d0840340c0d840030300c400b90b403c030760b9100b00c4002c0c0c5400241c03028001807407822150b00f556481e0030044c0303c4010449240b50251001045124030801c0e2200581c20560080c007c2045441c2c082c0e0740ca15480014064a00d0b01e4441403180e49007207642d0b0400014002110000400341d0b81542c3c41f6038403407000030325181403034001801c00d50340f200802c6030b6800100084400d541820040150221144004605848400024102d092404030106006061220112804028009589040b0151a801852114031800c00d00081c02003a820b000e5400d0380044440015108141442d0312828000c1001b906d64600d040d01e00b030080d24a1071810042c41641c400365141a42d00400a0041e0b04081c24151455a81407800740e10510100000c0780701a0700503c100e40c01c0ba4200b00080303081044840c010703141e981201d03940c0203d03030084215002e030b00c117028001d4a114501c10283c1c1214140b0b040c00307061410700014200d0000b60724050703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 250718318 1250 250717068 250717079
    0x20405090a3903080307080a11070b0a020909040b10080307110105030c1e0301061209020f06030c040f0803030a0606170105060706390e1503100e16090e01 68
    0x14061400c0810304442d400e0b045400240c981c0c0e01c162003030503030102030080d900c0c04810001c001c40110700034002651907003a1611000e000600300c858200035041c0580c82003000d64000b441c070011a9130300c058400710040c181407420010a10311a01124101e41c840004070070000b100a00004060240403000006d5040402e5545da5105080b0f031900418140140800000c0b1151110011a41244c00c109107460300302030b10301c4141d42150000e000c0c0f100411200030500d181d003001c6e807082009203074000b0039540e8405080014000301d580080d002d0110000c040001041d083c00c1541d03403000802d000c400450340c13490302c0030004045540581110080003081000202041d03001c0c80d423141580e80131103880390703140418941107008102041a071100c2c048404d05001103090902c0044000b01ca28040350f01500c130146400712014185030614990000c090803080c02c401e000c0101840d40b10850780403001d20561181806012030740112400022080d103c00d0640c840d6074412909402001810040710b581d50612 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250719424 1106 250718318 250718333
    0x7030e03011d100903090b07030804020f04020a020706050a26060f03060106020a06051909080c1504021f02100203070e0301061d0c0a110d050403020405090a 69
    0x1200c5051500d00a01412100100c82c41c0039084000650030000c00404105400f43e0400007900d0011071154440001008080d000383c840714110f00d094410420303841c01714841d00740a1030040c081440300c10340000704101601d1003810100d071944902001110032420f144a440312040c80c00041c440d449041d00590f0380983c0c0c00b510600000f807292001d0607903d41080c0b16000051f400003070300303102244440d84407070380081d02c1c00300c5481781301203804c1c4030350039944400320580300390200254035041030004111050702085505046000d916282e000030340444150302081640c00280d201003401588240b01d0300e80d00c01d8602070211344905025000500d01005040c3c014042d620300240400c0d0310b1611a40c951600d4008030a14a0503622071030481101d4014550000078801156100029510705001d03c6187e08202c3d0b0f01c158440d8954010003054840140031b80340d444d005500c414000c030f04203 = true := by decide +kernel

theorem cover : BRFrame.Cov 250539568 250719424 := by
  have h0 := BRFrame.cov_init 250539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250539568 ≤ n) (h2 : n < 250719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
