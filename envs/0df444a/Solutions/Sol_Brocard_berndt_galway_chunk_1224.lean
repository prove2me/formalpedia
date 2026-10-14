-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:51:14.202894+00:00
-- url     : https://prove2.me/submissions/4ccf1106-976b-4102-a215-bcc949ebedd5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219964028 ≤ n < 220143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219965278 1250 219964028 219964039
    0xf050f061c05120c010b040c0c0b01060801050d060f140703061502030304020303031605040b0712030c1d06032706041106130501031a1008250207050907170c0703030f0b 74
    0x15620f60300c458140c0061440b03051a6482d00d012103603648403809030004111150701d4049207644103280034502000160031580c00c0085c07003070041146a44d050018070101c0d40100000440c02012890b80c001340210100524101c2051428401d0b01ca91580c040b000315140c0c0540c0c40a108031481040303072a03110a540295040d03000b800842d500c201005107004080001703040035464240d0340c50740f01c0c1860304194026030b91031300304503020b800c203641502a6920102c401d260880300300c00304200c0d100d121010645114020702020001404000e199000000f11a00c00034040307001c864a188140d40c1c13102d0803501210115a00c40502e10642488420781e605040041280c12806040500440051109411080585400096004250312000c0354403600c103481e50b0b0799561328581100c41d02c0d0f80c000c4000002140180040075030803016800300d40181038900c1100c076414a0f4030345820459400320b803180c1c4e400040e06480240020203001c0c0c00201125446a10140300107240c1c01181c03000ca4009413130654206 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219966528 1250 219965278 219965293
    0x40213060311090601021e07080705060307020d0311040f03080d0e0f031204080f0d0203150f01090614070c080303090c180112021302031005030c040902010f11010f050f061c05 77
    0x1443e103004076036848801131040f2011181c42071a0744064800c29850540303140c209400a010400061007201c000c1d1038159152072660401f110000c0d52605c5840070f400c101580c4070003421103003500704100ca00802008519070140c64403800c00e444154040302c000d2909a2400003500b40c104404a104160300c2d074504086c0d821321404080b02c2c2844180140b00301c6d80c504c41040480c9444c000507014000c0b00d90020310041c1c0380d19010304030f004c0b62003420b00d03094860003200740c11420320380c0d10030000801c0d149545000341700c1d04461002c4030740d81d0042600c01481d030b00f000000441c00d130400001651242d403110041741c0c01c6010350014052034418060701110089800360051117000c540d1148a90b04130302c09483c0c0c6414118120f03084049030420b95501500d070294600800c120700d8200300b15203200108a038100b00c0c5804030750000c4c14010b02ca001c030200344072905444a183c09001c0d4428140d01034030f00f009101c01d04c2d00d010882d100b0001104c0d01413103509200000c038403d80d140381d100d0380540e44c0b120041001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219967778 1250 219966528 219966563
    0x20906090a060b07080306100905030d030b010909090813090501080307082a01050105030d02010510060e1203070c0e130c09050901180506040b07050a090605210f0402130603 76
    0x49200400182500b0380b142c00c00503000c100d5200405005005404c01602d90a29004005101c9000b416600401020070428042650045180040e00440d410000390042e00c0d240141c5211a02e5406401042d16208c10b010510034903600512000c4805002d104800380c482c581e910450354203000c2d5021590051107104001021103000303103110016404898410f14801415a120480480b600d12007039444500401c401d04041000e4000082a80002c1c801480c01e000443c240700c43c64810403041003000354014005860f8550415003400f5406d05403a0703510791781d05000d41500070610604505100060001b801e041411128101383c236485030340310345c400345006a144080c000140c034858665580d00c252105410030000003401c5640310f540a408103141c14244045510f10007480202407040c01c200c80070007a030b40182c0000580c0c4550805a032510604114602031461360701c02900341400c0c2c0f0040c00300448103040124072862003199550001c500c0310104034282e4031944002040002c501884403403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219969028 1250 219967778 219967789
    0xc0806041718010f2f100207021f181502060705090904020907050f0c0a050c01030c09060807030603060e03090a0f060e0103020714031204030f030b011b050c04020c07170a020906 78
    0xc0f04800d4580741c860b00403464a02d84220b05c2910049441681c0481140d02e00702c0d040c0140700007151048805c6003080600e070040741c28805190540c05100d9842450f8101a501911058031030049040744402516202d1148054072450241600094801d0382c0c0000d41613031041046404080014050708070700e031155400c0c025481009007041701805001c3c01212807075591400070701015000d80004003410881401c20500301803445091904150a0103501e103e400e40003c00381c0200c0302d032440c0400c180d0343c0301c0708118014200c1c0c0d0001402d030360030003020015600002014102c1074000322030400a00f5a1100c1c03000340c0001074825840410422006000a58000c0e8017034200c29005914401510040d03103011030455100c03a40d9000e00e112900705100c145031b841184050f050070791781402c1200100460000e0042444001110001c0b5a064207a004028040c04211040705001c0e000755190504104d0b200e0b112851805605510001d034410035242c1100007805420103034000d00300740390a848200c14000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219970278 1250 219969028 219969047
    0x703140c0109080c010b040b040b0603010e070212181009080c04150f08150a060f0308181801053c0303160b15010309050d0e0d0c080604171801 63
    0x84035540e00c0072401d0209030f51000400002d1210400014401c0c50b0f403042100315102102c94600992404d00f00503da44c489070100e9041d217443c0c0c8623810b10b603501c4a4080346006800d80005400340d40c0491084505100800c0440415070701719855000358a1040c000c0340c2040b5244500b4400c0c0e03005510002c003500b082e6010621006c210070740ca05119460704911b102d0a4420307405000c2d5944000ca0045006000030090342d0404d1b40450240100c03403901e0100354070304815000151070450006000c1021110b211141810000040d2006144068840d804280c0030380c02d1160b0360003141c00302088002c01d4001000c451040c00400c40000e1952403004900c1c5c00c03900194811030f0548810409580068110150303600014070030340d07000c013452800b0101c480c5d6101c1d04100407810300d42032403200d200003900481d03c0400b1840524000441d8a03254001400241d06590050b2500d540c0765004035186801003051841070707000300c4904003106040b2800b14010b118118544c1c1005103410040c10303141d0310801004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219971528 1250 219970278 219970297
    0x608040506041743081e093312010317040f09202502030c0a03060509010501051203030a020f040f0909030201050105010801050105040512070e070503040b060303070314 74
    0x60704107001140b54510192402680f0513240d4094900b202410440302424200741180356003041241c4001d5a84140758000c10030601819150200458007103001e04041e1625040018004003a0032140388013404011060a40c4000d80c00f0380c400c00e52107100000c0101e42c41d18031641e40079010b036071964441c20515908024031107038800040100288903d88202400040e207444000011191040f0044100001142420080920080c02048030501008101d80459001121030f010a0003451001134200015a100c5940c4007200d40c10100c2485850b510003131140050800030400c03a600e0300c082044c14141502c0c088104c0d0b108000290000f102ea070090203107103d202a40750300340fa440d174240200c1e10003541c0181014654410040c010f056090090380c2c014182800d05405d203504000c0000d24030311842c0250340c0152105100c000c2600c50070010840200b44e81580c2c03a905003828031008110760310688042d01c0d00c04120011810514021040b200f1003907040d211800c045820240c0800d0715002914003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219972778 1250 219971528 219971573
    0x120a02091302180108060615040e040201030e030309030904060905220606091404060f15090b011205040b010f0e0106050d090f0c0303020d020f010501082104030602070c050109060804050604 83
    0x80720041e01c581c6048800b10158108507035856040c004100e250402c01071209120380d80800e8559810355029040b10160307042c98020348019900d07400160301910321302c0c6540320988400401c200482d44048041d2000e04400c981c00d10040760340380030b01d500307541c4144c0d010103d0185c440c41e000c2400d0810045000454030600e0f01144081d600c006410440b902000040d2440005108110400c1824444d0024402400c43c04001081182c04c60309030401440c060100010741d50355403941240c4c05450740d45402e494052081c40149001e00d402009400284102c030140700f003003034001c115031910308000c1d8141d03812940d45a0070301c581200003002800d00202c0a980c5104100b5120000c01c0c856030004020318080d400074008030118000082c5041d01c0d104e4640c6007649004018003540102240d942107501a120740b044c20f10218161150191181d0f071b200074039052001074280e082010071900e0404079202621104584c0d40e0301ca500350b580071400c40f8020702c1c44d005040050b0020b0178448080401c20083e50f213 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219974028 1250 219972778 219972811
    0x9060d05180d020a0212150403050a050f0d020a11061909080c0d02010e06060301090b060405040c18090605070804230c1201050a05010605070201120c0c0f20120a0209 73
    0x101d440c105488040c030100140c0203002e050041d8204200c0440e00c11503180c00038551401c000e030000c4800d02014100a00f007000008502408a101d88107030740d00340d249140c403903603280310f2902400029848402003202080d0741c403818142c5000c000c14964803400607015851010340074962550001c00f0486011100c91106200520b8001c9081112180304080c0f07400005500f0316015a0900c0d14100070485e502c030ba0705010300c25001542c4100440c2d0002e00a0790b01041c0b40d2120b103065080c0410f80c2d0803210b000707040210045001a1039030000000b0074050042080300341c40b031000840e0300103012240078004070155000d0001c0188200c80400702c020b022001d440c011040030000940c102030f102c802403001c5e03458806122001754144039081c0101720303900300b09190900c25400a4015140084c101c0010b9903100380c01c2c482e5074004c005407102d16a1004ca008045c1e02c4610b840c0092540c10703075028100140c241c1c455492801c244044810060146e001040100d06503400c00c071813494020f00d940c00c0341201e01b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219975278 1250 219974028 219974071
    0x61d0301060b0d050420011d0607021005121501083d0311040204050f06030406090507180c080c040b16020910030b0f060d0605040813090b03070b09060d05 68
    0x50002c083c95800d000c0f4060420b410039080c20204100c000007054001d200c1c3c01304070f0780c0140924940c0c9005640c0785400b18441030000f0a04d004103031001c0d4002c0c514104042140d6844401030103c020303500d034584030f6602d440510010b1100c6002e403030f82c0442d4090002c5031007008410006000c00303800102021020080c0711518402207102c0c41460901501c3c201d00f03000304184400d841c14601e4050310110f05041c41e00c00003030100340c074070701e00035000e804008042002d2100399003141d00c240b600701013199034450b540c15208139034454055140c00d400f07103440e9034111058403a400f014000d1228200050500c2d04040005034581c0c080c06446107000c420340d40c6400180c0328003a03c1440354441d51044d9070320515500b4075418240c0d0046c0f41d00c100404030010840c059450001d0b901845811100004140c2e486160900f4280b04201d0741d209980102480050004615044481811411b40584104070307950901604580254001076a00c081c043c0400700384040329500607070744000d6105141c050740c0e240d603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219976528 1250 219975278 219975299
    0x41112010606030e070e090c090405190506100e06030601090518070f06110601120b1005042901110601030803100302181b030621030d060f1d01061d030106 68
    0x39400440404d444140c0c05075040020302c44d00d8024039040392480440d250580159480326020031056200b00340c0c00c00482e09001c400c004005000341008582c4040f01c41508000783d4840b0111f0f0100801054240f02040111260300028010300340600200916424200701c00302a150060602181c5210542020b10140c0700b001042d009104085006507011300f000401446191180f24505c2594041801001003104442107810019041050010203886102e1074000c0c420950b031010358001d040250480b001d00d099140d03c0740b00d6600c40700113035440c45164015034940d8a2030301031185030f400c80c0f40100003244248004543c00f0142c0100c5114090b2a40d001600b0034800802c6005196000000c01801650b541c000c0d41000892041c11411762501a0010f01996101c0013041d600c011080f18000c680841001611050800840e040c084140c40310003464510002d803040030842a281503148412440c0403074494140c90140d51906420040c404140708032907102c8000031740540d0707248000111001c54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219977778 1250 219976528 219976541
    0x2304020c030a12020c1e010c05030c480606030c010e011b08030711070b1e360906060304081b071536050409060b0a060503010305060903090904111201 66
    0x280c4007600e0018441034a080e08498413075400c481440005c0040c40b0040c2008070933596103110280c0d80000a8140c2c804004003400711500240850321040702e00c00c40301c0008021941900810b40c12980b583d500d01b82019611b05003903404070301280801d408000c955200c1c141010701015035112b6650340c142070f692400080e6108882c00d40000b060310010401505050010300c00900d0310709200d41c2441d000c00490141078440c000c40840344080000ca580605c86400701d1448000c0080385100490350030b8038810400840060368042c41001000b0010740c0f07a241600a0324003807508990b045040c03035020344c4e100640b004550005006403103840c4000030307800c8004130140c2e8200c082d07985102140341180070403c031007080100380c40501031034566020709040340d022007c01251021030b000710b4500d620742041001480c48518498004950100104d54560010011412284502d044134a13a5450800c80d6480b1300890084d5580401940003203004214000124102648000c10540303002c80080030b402c0c21500d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219979028 1250 219977778 219977803
    0x90b010305031306030c02030306010f030e16060f0302180f120d02030a140702010c12050c0a0506100b030c0301090518030313140f1903030e072304020c030a12020c 72
    0x100040302c0d021a03e000b05660003c1075142003d104031070305a00c010b51607000041025040007505d160705100e81d40700c1e4103d440e2540049042d15590110405940e4090155000e84c0010644911040b0803a80c030034801c503505803440c0c1404828441d200010090200e0150310b40310b80c8920764241e400c0d4a0032060210a6484030f80740c0083d82e0324218070001410b0b9990b0a41c000c0080c1209014140160740c0002c040c101d502d0f03210070182c05200b40c80d40151428040e03000080312070f11803120740d042002000104e0302d018250f14039203450980e540b0781d050b4100d440308071044036800300244010003540f815600241d400c6420740c45d0a00c0100c441c008424910b800850f14001c90540e200c000030144056145681005a031340c2d0007400001d03880e00c981503500c685260242035540e07841e0b040841414030030703400321455602d04416134407100e41d200608800c40c85902c8209202c200071100500c000d14180c800c481d0300140c0003000e1800c080503140151611030010b1f101240540d0204a070791989003081c40261140e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219980278 1250 219979028 219979033
    0x22030b070e090705040509040327030503070c05030706200a0611090a060302180108060a0906030b09070b071a070908030c0d0e06070b010510090f180b0102120406030906090b010305 79
    0x1001208101e00084050300d043c040c000d0401c41808141c9514100c0c580c4507405086c403443c080c11503420020206200202d40303000020b0724a001c810080017000600f46a8000c003001082c0c1d42d00d840415482c0d0910b40721340004600522014a06017046c00301000f1004c02103420368003005469158801640c40300b54251041582c00949023a0901d071500c03801c0702400e0249802c5040140c44400700b07403402c0c044104c150601c040200042e5007a5900b060900203041185400e002d160340d00c0ca05001141c105880c441014010502c0224031100d0003400d81d4030451b00404802050109048042d6a10001600b881300300010003d000ca0032050400080100c00302c03480050211ba258660010035270500502c1181c402e010820606010a081100306411741d10704641510401d11b0010007a10344081c13a0748410808164005c00088150f402da440c041c0c5940311480611450300360300300480c1c03106c908401143c0701350000e110030700115100354003d80ca0140303c0c1c54009410f803090740340c0700603441003603104a4055 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219981528 1250 219980278 219980297
    0x30a0903030e0a02010e040902060904020f0405030d02060c07031413060206010f050915010302090118230d03120b01120204030c0314120f1309090b090f0309010522030b07 75
    0x15505100310360039012204040c141da503943c0d41c0000d0940d111003881c0e0b440799032035039103038019952904101e90151f280101b0441d940c5080341d0848809400a201c2d0a03c41e001c1c4c0b8000c4004140041005803260041d050054548902c40d5420b841100d4115078207003078070302c05105104007500c0e007041d9540a01000c1c1c000381201c3d8035001a0060b050800d42055024109641c240b0000c10310603406000070003c242005a00c2d004002c0c0102d501904103400080845007a01c400100030750744c00e1098034010314aa0030710b058500303144107101da207800c10403004000518942d4145410f04c05540044008031052500610045501c0101c0099800c6900300303450310100004200300300840c40001400d8540c0c40380151840c4510300c01c0e90892409081c010604c2140c0c0015000b04811445c80385c180901044c1600300100d104c0d0341070240c107260040740d490441c1e1140d203401e0350303ca8070004265640c4582c1691001e1616140800a40751404404508045102034810100c001150070b1381161003040e039652030600e039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219982778 1250 219981528 219981533
    0x9080a0b040606121106181e0f0105090d110a080f0105011502010b0901090b040209060301090c020d0806030703141002030c1c09020a06051303080313020406050414071d06030a09 78
    0x2201d149031300c140d40112034500004006010400c1e00c0f00d001c64101c0e0203e442e0001c810400c450908961201ea0344420150000c4503d04807040301c1020380703001549d00f00b481201d020010354140c860142e10f5940107040849000018220080141f0002c030301034a0040500d07a00c559040c40d22001d44c0030312400d651100b00500582891921480d081d18141c0b0082c00001070aa000c40c900c0030040c000d0340c020b40c1d192000c040d0b450315250121030700c1c6d10025140c16603039a501d0344e803200100a91191000140038403408030805922484ca0b00d4050780004000e05151841c60392018140c0c0603821140303206000d075000b0943d12000d988055840703a411510525514620340d14240c0d82207541035555000640b0740010080035864201c000c1042e5061800d1031691246c5442d040610081c0d564001000c4141c0002000310b011199550382c00107a109036020703c0055211400c00c0255070050030445906200e480c0042e1045103c0c00c41260300044e16001d00c000b200340440410442d500440d0704420680d12848030108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219984028 1250 219982778 219982781
    0x7090e030c0f16031e0213020306040b0a03150c180314070603141b070b01090b040f02040326040f0311120d020601230604091b0f02031909080a0b0406 66
    0x9600700040043c100202c00504881980703019800f0103041d07003001e00da41100070981507000c1410150002d002c0109422a03400c490040c1d0f03c01c8030207500480c1000f940750110305202c1c0da4003060720752054075410138a003201001d0004200d2603078640e04000c188030f44598004030301c040480103503016010107400e00c1c161080700b500e4044140d01c45810140341c441c603840c6900204004980181084921904500160308071100a0282e00c3c030142c0014903140002903544259804031038407d030192028801da02c2245800800c0303009610015010841c1c0c5840b00b005aa08140c0300e18901d0080c0240c503041030b40303d80d00101f80400b540c200b1a1030842c600306400c4c00c1c3ca0f146084640d9072030170380e0081424009261003b9150300040c4100480d80d100030760580051000740496007485240a03041984440d034038048580034060380e10b4201070f12940c62140700c0580d4411600c00c042c20b11550000d40c84c0102c210110380e825019030150f0010440482c401103035162040c0260801e03103004a00d640b41b00e0519050910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219985278 1250 219984028 219984043
    0x2009010f020d090e0606040302091e0105100e0402160c17061005010e21340305280b0a091b1406251a0a0501061704030207090e030c 58
    0x55510400b20072602c280d11244690542d030266078119801e440f00000f24900d80510703080207611030700c101c0802c120101d1814103218a412207a200031003a90380c035401c2c40a0502d216441000240112011604905042d0001d01c0c965032002c00f02c010141d82c58461800751002500501060301e5504c3c440215502d041000d181c00540c1081c00349402803030301c7c001801c1c0741440e101c0b0b01c1c051030b50805403645503c0d0800e10800c420700d1050568121500725030f42851203004d913031003100010008a85500035540c0051000f016607034000d00601c444100c5040c07208100c114111401ca84c2020521010b000500b0380d60a180a40544003022803031a6040c94507030fa00b19540d03440c039440040b4114040003144110101504130701c0d000d4910300d903030b0b2107407596400d240079003001d482c4084400c81c1101c4003000024540709880c03407a8103d41804517201e0080040945400380f00f110700249400c03820901e02c140c0c081640303400c40d2085c0100c58400d0b81d1806003806455541c492800c094101080c0030240020a100c2c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219986528 1250 219985278 219985307
    0x1612050c0103050f13060b030304060903050709050106021e0319090302090f0c03060f030a0203061006090e060604030303021803070e18070803070609050a08120a06091802090a200901 80
    0x603c114a807441c50f9100e1a800240554000da0b0710100e000280b00407079120390782107038001d41600c1e07032b441c0c64000207030600c41c071407004031600d1250410000d514510f612403503040c2c1d0b8055020b080d181d00c0240801022044188042038039000801090300401c2105400e2131401010b901e03100c40036451401006280c0c5801420900d6206038075040020051509084a9002d003040f1040900f62a425001c42e15240c0304d0f860094042c4501010302071610b40c02001141200c445a4407042a1919064000c071101030545074581c11200038481880020f00a402034044d15105801c03540c5940909c00000e4540699a4400c0c88100d4100062020f01080c4c0803da00c501c3d00b66000030015189402d141720784e2031251001c06885155200022800c019051042a90302d64101d4038194440841d8030446a04620a94100c0c03601c81c50700100042c0008c241c054241c61b0110031940f142010302d07940910002c003800522139400a940c03446509840b0501d0110100645800c280480d02e500541001414250251190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219987778 1250 219986528 219986531
    0xa06050303120a050c040504060306060905100e0f060d1a07020705030a03051c021303060b210d0c0c05030109080d0f06030b011701060b21011a04060509031612050c0103 74
    0xc8070307902c50341d0603102034009400d1000015076558440307900c5554019500101e40c4203081080000c140141604a00141e40111404000b1078403038075440030304108544150341c070800883c4005104800611042d5a01c0340303000e40a0210718520b44d85d00e908130794110030f040404825150911096650404c0070401800d23099000303105000098030090994068072300a030800035159440f816019002d80c055900013056505c080c2200c0c0e440b85054000703805505c0b9124001e40e54881100309902d1000e50080030305042901424059a100500b2101d100c041c1d00203541018070b02e0f60000d0b01e45c4007440b40c001d49a0080d626540c80b40d001001c0c07842500d1440340d454501c1810003106001150b0904a0f690440f0415001c9081420070311107404c1c09808590301070050820080b40c0c40b00550043c4c188401e01401100c081280b030780c0c0b1220301c005c801d1103210a00c05101ea0911050003d24042c0d002480c01c808010100d07080c58441440300448903030990401c41e1140000e90024042040800c10010046401d080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219989028 1250 219987778 219987787
    0x204111b070f08030f090301060e1303080a0204050a060302030402180711011109090c0a17010909060e0715030b120d09030b0c09100309080d0608030a0e09040b0115020f0304060201050a06050303 85
    0x41c2d2030382c074000c176107440b0321141c0002401540f0355001d6204200400440e40c00c00100d1410b40c1d1000d00e4110030040507408112840e0001e54030a56078804c031015100028581031009052a40440003500300a1049801905070000354550700c500743c0a29100e07c0165403500c1d0414145000709080d228050211654000c0a005c50012a900d00412980c4445200800c5031070301c0d403030001225083d030f110000808410205001140445954009031081401444148403110316041110358803041841750343d10100c00b0189081d0650301c207802c1201140d00090204820740c59070310320b280c00c0c1100701a01d07002142c11604100b04008113200000c0e4454031403c1c0381c03800d11802d000802d00000011000c80200342d84c0342d06540401c041881501c40090343c1d60010400144c42d5001740344d6907071168488001040518440d4907007807400d0040544a594402c90b0000709910301040350008600889803401540a65000142140d00c1007000e0001840c155002041a06040704010b00b210f9854202c0781c00384d0804c11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219990278 1250 219989028 219989039
    0x110601031703090709020d0f060503060f24090a0b0f010c1208181b01020c0301090206070206030403090302120c011701050603161218050c0901210204111b070f 70
    0x403440c166071003003080110754a544048841d0300b0820030b034016103030641c030104d074803507291500ba400014554501c80e01004001d44480800d5a0ba1008a5003003126035440c1002a5045040c44101180301121074100a104040f042c006815080c0880e201907040b40d0f1840d1043c0d0070319110046860001c07080c2042041814991540c9940701554001041400369040108400f0304c205000d56801642c01d009541c1d6004240007d200031500b01025240140f1a2800e25141480d061003615086a030003001d00e458840c4680c24400c040c0c00090041d401d1040c2040b00001680740c4c0c0300d084c3c0f42060000094064209058005884003503849003140e01c0303070103c00050000d522407504980c4c00206000c44601d040445441c1105c7c00100302283d00e180c541071400d5030800340350070441140614892015680320a000909201c084102441a90030300c2d91100342c10f05050384003001076540d540c000f41c07002c25006450000383c0b0281d1b024540503a4032500e5203c91408000051106401500801d0940200a86031a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219991528 1250 219990278 219990293
    0x110402070305181c0b060d120e041b020c041a210609030703140304170a0207060305091b01050c01020708031608060111030406110c030106290a0503010b0a110109050105010611060103 80
    0x2400103290080c4c04010601a5031402d401c442c119a0008d0000c61241c4207140043c441a499000140a00d00703041c0d4141006204584189513158a40e00a080100c1d0500401c801b600c001d5140f0341c0c013000034000d00340060701e611003041c0084d50501d410340000d804000305185420b40051100f50b054206202100029911105050740c40d009003100a44a40301c82c2000441001c20200c40c0c010721100103052190309402040c2503003122002e4604203c540c0c0c03081000d0741c40318611202001000d2407400070080030340c0180003804210030803c000500305481691085800c0d8416a250000010070707502d20183c0550018000703034410404e00c1c0522022041050180e500e005c0c0e1701400040c800e0350240303c0b03054281048900d03000f800017030007070140d83c0d43c410b01c152400d8448078419446042081c9180f040490020071109085810707074400d40395a01c0c018180140d504101c0501c410441c0c1c041c1c8041000000f4043c02d04098021000020305515000019020580030302c031707134407207038000100400105041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219992778 1250 219991528 219991579
    0x305090a150f0f29060a030518010207050c0f0613090b0d02090a06050102060f07090303120e03070b1906081002030601051306081b03010312030911040207030518 71
    0x4295011541c001c0741c0601074034120b00814041d600d0001c007141c81044039000400103001c00c03c1c5400380e00d912a0301da1410307144500c0d00c00741c0000c01000304105003446540690707400840c10403400030640300304140c103007660701c0f0010544850b8840d0860008500c1c1000c0168010301088400b0b03407900d0361003051140e80744c5c0302d0b1013146a4240c0e290082c00045d150360a44910b03c0354001c04003035a500d080c50121004140c0c81c01402d00520440c00020900403460313803828020b5055032510040140b45560403200402580c1150001b0b98450426100d0a1760801c09094a1403040031483c000e0314141e181c3c01402604102240d440d142000c0782080924008620303030002000210001d80d40c1d65400005a40a10410207000c4801e950341100042560b409907915008043c012225504104080800e0f107085c04280806420820040030108043d0b01a40c4400c240c10f03c10518282080c5a000005007241c00c602c4c0f041d4040b03100000e2101c80c0701035010984050000440b40700003201420845d120a4840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219994028 1250 219992778 219992783
    0xe01140d020111030403030305010905010f080303040f0606031a0f0603031c02130e0112030e0d2d12020304170304030b061311040b09041508250b0408010606020d0305090a 75
    0x20303860412015644160f0480e0b400d45100302c101c0380d0320341d603c0c82d00400402d801d124a01c01980f5040010030914480c44044c001ca400280040d804c44c0c071151a0b11150348140e44003104c1d0b00c1da0f01c0c040000020302201d0104101c40c00030b180032030303280b07006e128800c0396440060245101c1c0d0400c11400c0901070f114204140b03d2031740e0060041e111301880d4030a0052580750b4225580d85a0300700000151210401d108101451281e92031210303100103e414440d0301d000c42c2d034000741690b141d01480100b0912208001901c3c200790040d1240c03ca0325034945c0f546a0006601000050f040020140103030207041111042c005401c0d0300440c82c0c0f61841c0c440c903801281c0900154421000904103008044c52a08180c0b04680010039956986995140d07030000b41c2d102d41050341c06141826007807006a40c4640003001119803043c090900103500308000c00ca08104600b00c83c018415460001ca0301d429508050700182100000000780740f414650081e1910191180c0c85041508280800c000b440c0007103120740c0c1155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219995278 1250 219994028 219994039
    0x1602190302061801020c03030a0b01020712080403080901121509110f0d0e0a06060909031209150509100603120206060a1a0306011e0c031b02030c0609031e0a0b010e0114 74
    0x103040040079000e441b0f4149202c54a01c0084244a0551600e60285800c0d0070700740c00711441a07a66400d0030281581580010b00641414801000402c1d4030b5001004c800005141c0412000701080072003085400840810041a0303102400f0300600c030962180c0c0050180150a80d0b0800090240fa2859031003110782489000f91554503c0750f000d41e041110811b2550b2059081c001c0d03a45035800600200300b154010340018080d5000380e5010000303441a10113242d0459942000c060070f015948020b4500601018010f12400d00001030b03041449c440d8501662049a02c00480f00c15010000d10740440680014828103201030700700492032480311807450f1801c28510b207603102e0b9603160060b15841041c5c0b040341e5014040840c1c88140603803005241d0f031003074800d8507107540751410b802c0481c11042d00000000c0d0154000c2914803c00d00e00100a8650f19800030201c0d00f40d40ba9404401d003507403003005954181d40c2c0c4141d1500f000c01c40c61a44003405400942800002907141a40c074413140c112a04019010310b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219996528 1250 219995278 219995311
    0xf08060c0d0b030d020303090106050a05100c0519050106090506060f030708060307030602030411010201062702030c040803040f090c0c0b0103240513060b0d050a031404080105160219030206 83
    0xc400764102581c50480181511211940c08401035126030040359040340c203501c0c114000c6014503115408005507400500420140c0c50040b0081d20307042c075082000d551034810b103020509041042007003281c07031510620000c1040c500e0182e040f400c1c1d41d4042c021038410b280a100d140400140d074420f59600450b6860002905d840d440c01180c140712050b04064400d44c000420401406882c20941c1c04542d001e078020403107180d0381e1403001400d4811800782c09414110209034064400242c000d960007444c0d00d00850f1078141d481101e1440c5910a5120a95404003d00104845040703841403000d012110b083c01e0105440340c2d600c0449103d01400010464804520541181e101c10380d0466154565050300b0480350802e80201d04601031090782c2100c5039410f0464180c041c4c2030001c0d805800a5002c001012030ba8a10756042d1041c5207100424600600d00f8000065165424080d41d4002c50031490381244141c0c0c5c2000003801c1025005251402c5148549580002540001d42c11381c0841d0440040204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219997778 1250 219996528 219996547
    0xb150f0403080a0306030506070e030304151110061d040f0f0501090b0103050c0a0b0408060115110d0815040e100216062a08070203090103020a050c01050a0f060f08060c 74
    0x502807500098804640410f001584a0301540440152030281e822a11591380b0458200c410702d8404035000e8140d0410b0000b0015030062100a00034000d050a2008440300b07102d0b455840c1c4090b1440412043e511140c040000c034420780c0c01780b40c22188602c0f0800551a041d01c1e4604669820100101045442c49441051020a500c81d03001560f0004524603156075a003031107a628a240000240304003107103100014003070401b80845d002c0300c904c1c0380a412240e01c0c20fa00444007420005d2414180041e0310400041540300340303d92540c400990710b80c2030b20340c104440407150303000030b4080c900e00446ca4150400d94082d0b001812850500044034056601c03c91450000c02498450310f00801603410619032002c81081c560f408541c0104030181c0d0103883c40e445004640c82981680d114016030004c0022500d954802d030020142c41c007440c1851858170f100000c00b5805c540c42101c1c0c015490f95103000410541005005440081c5a4012060340c4d89041c0300e00c0c15280c2c4000f4010b400304120001d500c044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219999028 1250 219997778 219997807
    0x20c06090109120507150507030210050c090603090105010608060a0302061210080111090301050a09120c0813060206071107060914030109020604080a05190c06030e1c05070c05040b15 80
    0x1a28650501c0300e1801c0380703494055503c441600414000540c0720700d506246c0d500c0303141601c80c031a07090741c01401d4081c50002104020003003d4240811003408001440054075124010340c0141910000007030190b141480c020b0046070041c010621803885600200090f81c1c2c0d0100359000000c2c1400c40c123107107444200a00d4140e10391507108940359400d1003030226010041c18040c040f09402503000f4800c0d9a9100c0a0f02d08490b103192004045441c141c10482609208001c080c1074140703d1088103141c446400c42440c2c10801c01d610000050f8400750400040c83da1100606a000e0140310007060210305000020301041d0b114000c0041001c00c00c0036045865030f01750007000c04d80b034015103090740c2c468442c00044d4450090100c191090f01c2101c8924901e409492140700300d5942022601c01c1e901e040071011000ba101000454081d44030342e23070003684604002200c0c0405040d45480d40c581d640c2143c50038038900706495022601c210b1601100c011191250980d01000c1d51000d40190380c1c40101150102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220000278 1250 219999028 219999047
    0x11160501050d0c021e03120105040b030303220b132f150f0703030b090c0301150309020402090301050106050415080903040909020612010603200c0a0212071a0315060703020c060901 79
    0x2e507600d94881d21018501804001005c181f00e0507075026075141e0302d1b4428041075130103501070315825a20800011340e200c0c1c04070f603141c00d00f582c106035016004400e50312010343c02d0a056464543e01e21203107d1072803c110400142490508801a200070701c00d942c074030606000500704000c01d01401c80010034544200c8640c0c11110904003e002003600d600d201d09008004116100176a4007806440010030390080402064034100c0b40100411054441000c40c00ca0281c082c200e000c07038000b5000d001012035a80d0038054203020340034035540c00d9100e074545000d50a81d035423481700c071105208414040c4142e0000c08402c0750141c1f07810010100b0f0b0480750f840810500e210300300e010300c280f80200d4000f09040b0b80c9070f040044e10900c20580991807480c40069030006214103c4103548650040001c000141004420340100c019140265004660b03114158019001d1303035407241510071000010801440003955500682101c141c1c0c0706410300040d60740c060740e211520a502c1e0300c1f81c14040384d0901503071720403404c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220001528 1250 220000278 220000303
    0x201081b030c090108070c0f030e1302030f04060c030207030c0f080c1b040c0f0f08061306090f0c0306122d05030703020705010f05090402161211160501050d0c02 71
    0x99803490600da00b44007030707048010440d0003d100d003000b02e02401d01ca5000041400e40000b4a401c084485950a4404a416400340c6410a12421840c0c07036506540c4041c5100340c8400364000d4140ca01864004110344c02e0345007010515106101c0c107004203031301c440c000d5007103588014032107040755040c10701c1c1e1040c2c0501c0a03506450703c5058039001175644801491134a00741e0a0b101440702d03000c20542610010846441c550002c1e03918903081c5030701c80c420285a5081003021b061070284074440721504095400b0354020080054540c210211720054610030b0903114500d038070b400c00905050610400484200c218040c04e24600c1100c160710300078448101c05440c5a41c02245404100c5628185861b500f000e8000c0d0054001c00c0b030b0008403035004500303c058800066958a00c0c08032144108802500329100c1d60925034094003c650002d504488080c0d80c03010075844815100c140c081e502454541c04c00c14170018880e011000b00100e90f00f01c81503c056041007000441d02d8440c24804910b0100d80c0f080341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220002778 1250 220001528 220001581
    0x60516050601030f050606010504140906040b040f0207020111070501090b0304060213030b0f092805070801020d0204050a0605070b270703060c0e06040308040509090312010e270703020108 82
    0x2006044c9200d0b2044510030020707954590b940400541c0c0d1409584114102c1ba452006600e00301c0c60a003502c02c0c0d000340300a00000e0000020070211303080300c601005240810b0340c00200300c0f09560708851160745002c0704100501030a410040000c00300f006074850315129280101c0400c0402c1069015182c00340c110780c0c04d0b60345d11a50784c2001c031510707801038400b80664070700d140104000d900045000034900c0d01c2c03850290b4000ea10b90228641005240905840500907048045980007080c0010703e0140b61414015890f6401c1c001007042e0204250320501c18043c3c200b1030500040d900ba2900c03548008140052250080c00e5440c420450b0800207050f9524058854040100a250745c420805100710340d13140403615602e034045c00128411808003803c032940c2848100800d00e81100010360040301401540c3c105400e091180c01400340c283c01104045c2d0446c0100700782c844840302c0b890503014580900c003c580320840c40254a0394071038000a4108812600011001c89060100c4c034204165142d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220004028 1250 220002778 220002781
    0x20307090921050307200615030709021201050a2403020702041b111e15040c180f150b09150c030d020706050105010f050a030b0409080c010f060b130605160506 70
    0xb0020300303e40c02242c070440414803005a41841400a102d10085035201000500550300c41d103080302030340c003c01402241d0512a411002c5401e206a00240400c4002e401010f105075061a0400901d0a0140c22100803421100500f07440101e08000c64800c01d00c082c100180d40d2030b52800460060410b407440e512a46002c0c2d1030000505501ca005000400600350035603c00035021610a45014085020b0030010b500100c00c2303296290819030484c0d0001e1280e00c000e0b04856448050001854240e802103403003940d50508085c2544507801400104000c02c0c03000300f8a40d0400c5e404800d1805149034560040000c07001d0046071a42da40c089400726505901142c3d00c4403211a4010b004c1c3d070007000212407980c02d00c400000c165015051030304d4a61095160a0308000c9440c40803001400030001c103580c050344030f050b00c0700404d40c42401040c07403120180000c5440355000b0741d580140c0b802c5500c5194110000c100b401d052198500355001039031103c1c5080341e540d143c400c44980d9040b0301ca20f000b4000b40602030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220005278 1250 220004028 220004093
    0x3030f03130204060b0a02031c060312090305060708060105040311041401170111190f02011401180c08010f0510030f02041e0608060603270a11011b0203070909 70
    0x50207181594400c6030144501034460050703030390300d014001c800005a4014000244820641200242e41c0c5007030203000030360703c2e43c1e9407503641450003100e8100c001700d000c5400500a014040c8007080d400300031801c01038003900b4040e000a15520540c800a840030b10040c200e150705540303c2c0c015800c08200240030b41e0103941c46000f803415240d14103052245130761170300c244c6000034142c21003518944041016012624642031206441c1030307000d603014104555031030880e03c010b032805032040c81c068042c41005e408881c1ca042e01600c12161501510401d1042582c01013040c0000c0039040408d84074152280c0c1424111200300b61f02a0615a03e0000c02070b0010801007010f0504100c104802281071034400c103420341d05e04042d83c14800070f07101950030a50410008090074103007007803d40f40c1419211460144a02d10a8a0f4206145494110307401500306a07a44000d69100f14041c400282d0b182d41104001003c3d0b00080d5500c08500c9020400343d100d50340d98043c8480d54458202e106508042c041544d22880e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220006528 1250 220005278 220005301
    0x90f060102150a0c030b04150302120a0f03051b0619020c030f0f0a08010b0301141e060a08011a09061213080a030b04180b18030c0d09051f020d0c0203030f03 69
    0x30450400007a00e05646c1002c0d034905405040d0040c0040d40361450101d0850302444940f0091561100c07080c03081c880c0040c0084e20200800790511301a40d03415441d60768441c11040d10081c002c032443c001d6800102800005248034042c1000e4075141c0340c0050360760407440e6085045026034240c0c2407000301c012842c00e01030143d03800108048071180c1e8a442161381c03640c00c0440180000e00800e0000c42c2800d10b03118683c140541100360700482c100750300f1a40252200041e0890303000352828400500501d004200d00050408800b0011071800205820000e00d20b01140c00d502074003c2c0074100651540108000c0b94594174200183d6400040b900d40d180e41d620b201801400c540300c000c6010700c1c40e001c0f031040f01d000300d00910ad07c001e90050505c000c071b480703c152a49800b050758901c07c0250008104000104104101050200071251140c040861426080100c51041444a4001e4000d40c1440d02c9807035074045030012140800b8100ba201080704d90021910f14040e05c0c1c000741000e00000284103080040c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220007778 1250 220006528 220006541
    0x2030301080d0314160c0804060c0b01060806010c06150b1204030909020f0d09020102010605060d06180b090402190302040515030f010b1c032109020102061005090f060102150a 77
    0x1801100c000b00d5050000f00c088501601c030700d4250007214408101e110701000301ca4400e0701c14518040080d01456110050603601c03036445103001c6420f01d07458030b0422200300c00080c0107000d20f003003891081c85c18000103411000302c284001d045540d070301064010500510001c8028244003c4030b00d84079400b200e5002101c59090b01c0039000304000400000b03809802e8003c4640440e0046030a03030400011001080c040c0c0100081203065540f07a000120b410740302c51015011454950304003083c2d407880d00980403000440b0241ea80041030621309042c0c4940c9a405050350041c0e41500c00f00780114001401d00000501500025070041c105814051480e083c540710b00c451140440c01c1e03a0324190040c1042e4201d0340a0604942c12290111a040c0c603034507503500080215011341020000c413008540c800100e0420944140419a41d070f441107015540d040000b55800361078040000c01a40c1008000b030303030f070b110001c0a641c03641214200044e0541d200780300b40e07449044240c800c8680303400c141c18004080c0c0f00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220009028 1250 220007778 220007789
    0xa050a080705100c09050121090309060f170408130b0a08150d0308010303030b010c020a09020c0705011701090504020d060930080c070302011116060b04090818040609090302030301 79
    0x34441c207400c04003140c1d20511000711800d07100e09610f10311b4080151006030481e080c14074a030301c1014500000c0d940714055007041c103200355118a842c60903c1c001801012015208000f0080b544003170010107000c180060342c1058000b460242c032440440d042c400c0f40009908403c1041c60003040500d0030a400418141c050006000003800d210500020b020100c2c02408015000889500c010800b20303010b0791107040b42690600d020024045150041183c51205034004840c4660000f00c206155805101d88406090700340f0f400d041c02e00d49900300c621040c1040c058040c00c0382e0344001060031551000b50141c0710304d91002083c002d42801d810b1440203040000c0f50359002c146c0c9002003100c8403080d401701ca040c400e10b90b00d8203205611341c10703404501c5410005045040d590780d642100c0300700c0342220180c201030b4201800c40403003148914159050f58081c006140c040d0342041c00080000c0d00d100e0076603000d44c20201000300c400582c900002c000d4400d80e480004c40f14900307041c503c18950302100540c180c0c0d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220010278 1250 220009028 220009033
    0x2a071104020c1009050706050a0507030309020a0f06090e0702010504230c0423060405060a09090515090616180509070311040b042c06060304030302041505030403030e0109030504170a050a080705 85
    0x80d1f64100c184e50901c668050280083c00c08c200400010740658403245a0b03600103802c0440b00e51311100c103da010348442d007042c000b01d541e00108000d80710041101d150320400a2000744142d003001e540d2140c13902050180614281c02e4421076400483c81080f0000203c0401041030203503007080c541c0350302e078100c42514040383c2034103403000501141418064640265005800004075905e0903245200801701c2220071141400341890014106d41d51002d070034000c4c8524000f402d503d00700740b86007003140d012040c03200003440950941e510000d989541e045045a00c29075400400e0340d20b0603022401007040801640910401207030114500d07141001502c16100c0302c007240d58000030176600098541c94000030781c5621100721000241d0508048028640091089c100542415240d01c0c10701200f034030320f45020340010004810801403582c9030141c0d484a0326030380000c00444041d62001040741c41a4020710766900d002e651040c0f03940e9000c21030640e00e190004182c4185440504d440c50484d0301010040d102032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220011528 1250 220010278 220010293
    0x618060609071e090521070f15030e0c040c05030115050705030a30140f16050c070503010f020d1b020712020d05152a071104020c100905 60
    0x90a050040c81c2c060341c0507840f111010696030101071080e1140380100c00802c5030310310000480761166107038600b800070340601d030200c003181c140441440c160707150b40140352000003407008011803005400013012140d01e5241c00301d828072000c4506850024101800740c2c005123802003600348503500502a60580d81514032040700391341d00d0320302281d49001d5004054070039001003000c0c0300c5080c040d410030030028180c080c004040441c810341100ca10004944010b1703d40c1e849091400d038080c844d400180d070190034003001c007109040a11070107402001500b9072a0600800281300e8114407820061000284001002805040c4c0c036420071302c001c0c3d00054841c403401400e01100c8d401200383d0100308a0201043c1d4000c00005180040d1862101207041c401d90708855040c0c1c0070343c0414402e0220042c804100351000b542c40c00d128002039528200b4658030785d07d090452813603000e5900d00d032084035000b50b0800b0a083e20030806500082c0244500303c0021030702c1c859042d020a0f051266004482154052020340d003d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220012778 1250 220011528 220011541
    0x30f0304060c2324090304080304150e0a080102031e0c0a0804020f0402070305040f050f01142d0304020906011b03080606041511010c030203040b0c03130203030a17090a0b040201050a030e061806 85
    0x207e0195004203080ca4000f8031050240310150b48070f005103480913141044080c18414007241d059516600300300d9a694001041040d42c0480b800c4c0c2181c0c2c0700c4141140c140c0c40c605484c5204040c013440d600781042081c02d1010a0030f540d45c04480302d9032044018021941c0c5c5c00742e450080c00c2a8454864401a560181000a128584034901101e200070603180d807400d61500354280e0b8155404100301c0341d45801000c0540310700000208600e10388104544c18181d40c1e00306401000300b04a4010b081a0412107400108920064811016108140d160a241500e0340f144400901c840c0140e8100c1c0668540d040700914503542e001910300e14808005c80200602d1000c0c8a086050f07210442d40035109110b85004a00705541c480010341d404035280c0c034503542000041d40003e0450f4468441e64000403004a40034046e110089800c3c0d0700446000010056120569542802584020000790500c1800300d8141d15090003901311828800120050311428031709843c444070018030f164107601d410312130b5030002000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220014028 1250 220012778 220012783
    0x1b0e100305070611031e040302191a070302010e0303040302010b150f160602070606140118030213090816030c0b01080d091401020c0303031005030f0304060c232409 72
    0x180d81c0c008014020041c00c0c4801514441444030b0318468601c02080400311303440b412481c00b10540a00310340036544601c2d500400ca48075072202c1500c8018480081704119942d0810400c10340d070707200b1809840d19600c450409900414041940300701500000042200301a41035100f2001c0301003c403180b10007601c404681c1241c0d4001d031400e10ec07904004016400c00483c91841c190740031442620007518100c0c0f03a41e25407094624580c490708190001c0c00b1813480c0c0d51703045110900c1204000069440d01407442d0000781024240c98106c0807010f0b902d90054090198440413184440c140744000c8040810602d8003c050710b050a006a5981e440b0500100d18101c01041441c3d0383c001c0c5039604003000d410301c20b50602400461700164194850060403038456101440510b12580c2070704822003c05150809042c03d0a40d440c401040582007000203101842e007020084000940000090308003451412561a4980419041c620580b00300c05030001c0d4412340c0c01c0007050500700e940c0540c1480e2100c01072282d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220015278 1250 220014028 220014061
    0x1050a2007020d140a03030b03060618010312231e04030308061513230a08100504050109020405010803090a060206060d03030f020906190f0903020a0e131b0e 69
    0x1100d0910810038900036240040700c2440300c0e03010b1107100c9003482424000515008000c079040340447c2c1c444500400030311301404819405a0165080b800401a04803006507481c0e0500000340701c01c074000903001c1c40790b21900403501005a0321441c03000380345c8840b1078460b21b6007248058030f104c4142c0424003022140000140d030704581d8541c42e0102561903400070040444115548518880000e000501e1810f00d09500c0c04018501201407481d059520140c00221041075003d0342c0c091050b90348204180e0400203942c02c003043d040c3ca40041c068071645440343c0076005050b0065441030500c0c0002c542c1000200042009170030445035111103d9075000700b640c8035a01210030685c4000280348640c00309009404c02d8102c070410030750041c503102c20b040008a10307400c0100211905031504040142450f0004c44081403043c180c1020003166203503500050701c1c02000d0141d002e0304030880e0007240280070000500742c111603010860140d8081c0c401a0410310b82160b104150b08540c1100220304014008040c01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220016528 1250 220015278 220015331
    0x10e030304170906040b03130507092004080c100912060c1704021c05011b09030201080c040810020a030f0c03020c1902031203060d08040605120a0510090509071701050a 74
    0x110b00b45407410500710301b1a08002c01c820308049180004400040c1d0034002c4a01800c0581380001d600b0b42058a1901c444401c80c0c4100031041b4100002e0016502c009960101031600700c0e200041d04000710b8044690146a80c040640d004c4202c04403006c000c103035001794242c02c440b9502c0f840081c40048180b011500240c0d00a034000908248051072200c00d10600041e4501800020400c00c05c5102ca2441200407000c1e00d030006000540d05004543c1c0c403d0840d504483e2800c4121701381802c2a42454a4805801a6009032580002c6040c022402508082569510208100240841810050041c3d03002c079460305150f000f504510440301c461440d40308038094000c6c0007071000d00c0440300c28540740d0784040c1c281580300c011411000700003180e54000b07201501c1d9940d80c250f00c0f1003041080345c0640d00050000184942418101b007500d01201102904944000703102040d0713501d8006a007410060550005010346150104040080f9415085a406484200c404100c16007404100c0000482d090f0000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220017778 1250 220016528 220016539
    0x120f0a0c021504060c03020903031303050f070311010c02300c0a0605030406051e19050a0905030910030204080a030c02150301060c060b01030b060d050901050603060601022d010e0303041709 83
    0xb03d0046521076202c81443d20799414010320b0981c103040000d180d9080b50400807040d112115050040042c00e215010401c04520000c018040c1181d961260302506404250704000782c0102c07070700540d0f60b0503560010f5041001d802d600054501300d42042504140340010809100e020701c1034084c0d081403500c040840300381d50384a50641d01c5030760f078002c00b40c40702030a0414088408082050303079001e071560701806419403000d0821156100a134100c10b456000f4014113166107003502605c04580003008880c49030790100c413524000d000c0501c0076002801380d03030000e9584d44655580e00c010107402a890420990089440c0d501c07450800d03401005034032090240030001120700300410f0010328560480500b42d0030504002c1414010040410740f103801078000e036a0040e0b21f65040c8001c528080c815a900000309402510251500c8070000c1c3d80d9036181c1c006d007c14000025a1034010710851003078400c044110b1341c024440c0e0f00088400a5403508141c600381c400c0c0313004003204081032300900304407950034102425 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220019028 1250 220017778 220017781
    0x10b0c03041406040801050106082a04060c330e0309010915050405030d030b040c080720010b0307030c0e0a02180108040206070b0108030d06090e1b06120f0a0c0215 72
    0x8401c1800c80124003110380100d002e01c004940b005e02801028040c2040b035a40c1051460000400b204000c460100340d0154200010015480a404421502603030744c0e606011103040b1951500f41791104205d10007a07160341c411841ca07040040c21201449030041d0741c03c8180a0560b980310140e0300c034401c7c1e0b480c1c2ca01098441c40100070f0303640c90441e6080314510500308241030607074071400700b800c0a00c03540b68030700002c0e0741e56a107801e1480d051181600540b03061a01c50140d1420820240c500c0d10341040c01101207061185980c4c031f0030b500f5000780098190103001e6034045a41c134a84241032011500407610380d81c40b00400034a42c800e0368800c1c1c4440210140340000d110300e221300155200303400908140d0700701204000caa030200d01d1b2905d03a00d00034820180119a1681d5442940088603601d41080172030a0904408003130103000002e0160612001581d01801180400c001988a1103011040c900040c42e403010022042c1314001e00c3c521030a084402404000443c20f012030700c600c0d000e03803403310b80d455240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220020278 1250 220019028 220019039
    0x60a020a020f0f0c1c080d090c1d01030206030603030d090f0c0503060c030f0c090d1406070e0a09270b0403030c110d030b01020708011503051b060316052a06010b0c0304 74
    0x182c0280c1105e03240c1c4407400c4440000d4032881841c2d400711100b0f10343c1c1910341c0b0400c002c21007140c0006000742410341c2040451140741000c03584260040c40047e00c074400110110360580e4082c011900f1516005204018042c0740e031410301c44401501c0f10a80d02d500d500c41d0001000d0a02003159880348000c94986460750b42c5003a5406031049029058040e440003c0c450707801291101d07000c01e031030b07140580d80a04a017100480e03043e242400c000c0c0340034108880701c05c540b40c16480f688500d400307444116101044030840810030000ca90303d420f10303441240300903070044e2050000e142d004034002c074000d0f03400740641242000161640c2d1b403900744440c0c2540c070806506a821b8400d90248051000503c1550003160b5180b09290a540d07043c041580c80651619081040010412994060114000494404001440010311a400000d2110303012518902c03030b1203142445001280d151040c010000740c95981c0907450001040c03009880905540301b503900100d1200c01113070035039081d01c428500071440d2a0419 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220021528 1250 220020278 220020289
    0x4052d01092004150203130b0310061e0c061107230304031e0c050a060306081b010c0b0c0708120a05090a0209070c05030408010908030f070e240c060a020a020f0f0c 72
    0x6032031300c0118002403028200e000d080514240091107246416516810042d0381003047c000540e00190034400300543c1c000a0404018010008002c107040a802e100c0c4281492005481c00010700c40c203110000a41004020b0040c0400c41ca202a408070084031115064005649128034000600b503114410001ea00c115501152100c01902c00c8002040c07040c1e0340c034041101d06582d50441c0000c01e07216a8140070380c140030080401e000c0c40c14500301c050150034900107000c07001c00c5a005403c903031400c070005000b80c0d10b8204440b034144d443b5120b1640c405035800b040194903816a03020603111704100c0466000b5200080540c0c1481d0000c5c1070142d20b8a50810076603015540304030488050205102c005403103d02071003100390b91030003410081d6403407504078001c0740d000e00010002418806620014001c036195034201704483e10010340d07410340745204102c1d104211b0140d000c5014440c810001001400c50b1180c0150a0340340f007075001c540e0303000c07d05200d064440010917030440d840d502042c1c07551401d2425 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220022778 1250 220021528 220021559
    0x611070314010b131a0d1a07090e15040c0e01080f090f01050a0c0207080d210b060c0f010f060e2a03010e01060e15030604052d01092004 60
    0x85000083d92005250200e0f1100d42818510840c0c0790351008103241024000c0c19074000e64104841c02510f8000590b00c0c002400d0880700340c4c1c103440c0350160000d0b40703090041c0c01a03030180c10700161b03014041c50940c4d914401c1d4050f442401c1d01603802c14007409420760007030041044010050319108110f503220300300170801d4071009199201c3e030320034a00c81513007148080c40380a0103607030b2414020403020700d0301c00e019280c543c10740e001180950010a8031a031180d446000c1c07940c40101c200c05c00a0868844c142c0e100607259401140d640143d000890881101002400320030b03461282d4000d20007c20850082d80c110f800034440c1d51500210343c0700144400f41e00700150b000001c1c0358490410802d000c031a00c003100d1b0304260005d070081ba0400c0d005114081d002107080c0100e100450f8914800c00c0c100f40d61852600028001138082ea031102c0c08111100314646803c0b08880317924407c0b0091048003024028400001e1040e4254149000e038081c1d80b550500c0640070703000c42c80e041058070746130ad44810400076150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220024028 1250 220022778 220022813
    0x20c010c08130e060a0e04050a060c030b180703050a060f0308030903040f150306150f08060f03060a060e090c03030a2a0f060b04140606160804060503090706110703 72
    0x80220314500c4500ea000d880c007030f107949600400c03545000780502459000c160050b411840144007040001072000401502c01a030000c40030a01c0800305000303502404204000310f42c0154181200c851002c1158045072141c01640d0b01070100b0345820511804a80d014018000040c3d52054180040340119001315088003c40b003c41c0d150990f03e054880c40004150442c860902882400f2110396600d8066600945400c00b410f02448200c604003a000f4481030240405001c0e01100240703081d075422002848400000d002d0301c145250681c1c00b1030082860f8020041590b00c01c1011400c50000000d5107a0303030b410060011803400100320015100f41704104036038458500c14481d65181708007500c0d904c1485500c82d80c45000c10481c170f851300c1002d54003072400d01030045182103109810030f0070643c00307190099000d0310203d5940d0f140b031541001e40646d024018180200005000444950200007144255110002d98010903158001100e82d0450b043c079418481e4401030050010030062900d40a1450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220025278 1250 220024028 220024043
    0x402010f110c0a0b210c03040f051507030204090e0610031115070b010e07080603071701020c032a070e0c0313050d09030606080c010210050a062d0e07020c010c 70
    0x907030400041d29010090300301c107074500f4000c21a0b4440300e00c17140c45619880708002c0600c42030324080c0359441881c04002d2029241611000c0100c0c140305043c815101000e40c1c0c00315808181c41d001001902030760041c40341d10308117031402d151544070140c0400d42a004a100c400310010703861a50311184d21403040e400300c5030342c441c0c0726001c2032116058110041080510805401c6900d46c9080b03200502510000d1410701842407110420005640204114040c0c2c1c904410305040c1c101007112041c02400343d00e009420901c00054201d0740389281e0180d901c0c9841d00d0318039400540340c1da2a103079134484120340b003540b07284056a00440d2490701407001859011580e00070754847c00d0110384505103003c0c5400002000f007180c20300c051052040c14082d81002c0d01004000f03142050341000003e64035019030500c85a2143c1e40e40c04a00c07900e0550704240001c0c800024480b22035003d800c0305000540b03619146004202c41e2050001c1c90300d142170301c1c581c8141129000b030003a40c10400011340e1511301120741150401d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220026528 1250 220025278 220025293
    0xa05061b0f0a030309051009031209050c0d110a0506070201020a24090317070905060a0c060b060a0203030f07170105091f06030903020c030f070b070501020405090c070303050a050402010f11 83
    0x161070401c01d400d500703406560045081e40d41410007a0038600d40025070540341e81003d2445c4040b0f9001440c244d04e070030195000050028072800c156060130b03030748101e540d409442e10150b8028001801213a401e524000c46500c0380065403081003100c14071801c00001d000d0b0304010b01d400c0c00310398260005440c2d044008001200c03610030702407035411100410703802c03008210245409511002d0a401c2e8651140c41410704020340c0e810309000404030f00480c8001c00401014030000803c10945400441100d90040d060a4443c2ca8003e000382d129081203608440030114840096003261040038285c1e6034220003c4502c08503400e00040c8410040300400c10443c18241510403d01c03a050040000000c05a56500041c1c1100328036009081407c03216043d84a548a420791800c071040c089540310407541034800e060f540303034028500b19019010b070340d0206602c902c0000c1080103440480d0010024544251b500300303c69510114802c04a40d41030320040e0000c0c007081031012406004a899006e0300d4100c03001c40d0300c0b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220027778 1250 220026528 220026553
    0x4050f010c120506030f1f020c070b07051b09180f16050312070809010e12070e04140a0b01062a0807020102150f150612100807050a05061b 61
    0x29a070124040800040e0702c0c06010803809814460b49130003132021409010144002e00e00d0a0765240100025200340c00440200043c87c0050f40c102d401030300e146c2d81920000c550f00c12032011036402c110350a581c00c8c061941e040f59060034005000344189402082c3c1c1d03081e503d641c180071031115090805080c3c0f610403850180c0700d00c0310030000f11803544081d040700c02e80541008103150030f004201c550340059840500c881c400007220380040e110301d070307a081c40d00c120200c5480000842191142c0c801c0c000c0360080000115020003050403951080b030040a0460350b00b050070b5001a42d880c40490042c02104502e801444400e124040035a04124481c581c10b01032465951505100e40050340c04a403030f410002003040031941c05004c42100060000c218203000c1c81e00001c00b030300d0762030003c05441c1485465560b200d0183d030b558055a0400d001c041c0707180042d00d8156240e03003200f003d6009145862090f00400a12840c040203401c050781c0026290030306088024468070761608110609507414042e14006508 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220029028 1250 220027778 220027781
    0x3040317030c0f13050406050301020c150705071524060f030b0406050402280203040303080f040515090a050c03071a030a18030c1a1b0a17130c050613050904050f01 72
    0x4c3c201d4010300c0040e140e4640410071084031881e6000c40e010341d0042c8401c0d1070104000c9180490113140c0e180040d296603880c1c0040318684a252070003011481c030016a000c4013101680400e180b080304008501c0c620810000c110307a100c400748102000a401d4490380d01c4094400d170000001060081c02c08940c5a840702c001500b40c0c1c11604c185440140e5015511000d80c0f90984200304100171130020b5490302c0c0c00e58500400050000301080030510060b8045000c111082042565640c86a8103d098906280304c119840d550007050503580707846002c0c985c840501c0d022400c0e0040365112400103955100c144124501c6070001004e2441e02c5170b552000c401200440844010718070304c41d40d40c22030310b1801c41c0348c80b070120034130741e40c2e41d202c5400700e1030801076007269468208480c0b045c401368182e201c01220303900715020f244092038051203040755810700c625581140c0c1100305030b600c10250400000d441d0f60510903540111401c0c0024160140c008101c1801c16100b0160810301038400e0f070740340f0500c02c000c950 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220030278 1250 220029028 220029037
    0xf0a271205190c05150d090609120305090303010936021e010c080f09030f0c2b0f0c09050705030f13150f0b0a0305010207060b0303040317030c0f 64
    0x494240c4014920401030240030603005444004440305103180c8a8460034a940c80902070107000d1101e414850084154081c150703140d115224400303000e10307819458000c01504e50040120351440c001c0c90110340d181d019024603480341003044011810340e071a050408010b0040300680c01d110740f4842c0250305103860018050111144100383c3c130001c6084a205010388000c500b00302640203016070345142103503a44204840c11071500403075030b2034072800318448500e100e1251464482e4148a25a0301521040c4082400143c603c0100c038031002641042c0001280c10812034070396031550804100d41000210001540c031032050081e003401903041c0c1c40c0d60b0301d401140d07000d0b6819804103101000700000c0d00a603130070860b0b00c00a8000344040d642d0b0103998080c200b4101031009400703141c560600e0b010b0400c0c1a0b10154a040700202402050382d501c0c10700034001e5001c4402070303940d54142241c0d40c030181030020449003144d601003116204003003a10790354400c503080039201603c66801000a03050318001d450141c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220031528 1250 220030278 220030289
    0x10501020321150a0914061002060a05060609190306051302030703120504150503060406060516020409060b0a03033c030e0c06180109050a0b090402072102061503030f0a27 75
    0x14089483c1c8400c40b100e040700071f00d02c61103544140054403100d54040b4003580c00084000020405454210000705580100290b40d5000003d00b4040c2d050131514140d50f81c02c485c0201d10400454681c03c260b140944c4024802075010b900a040c1003000510304180705142d101c41c1e20300241880d8841341120110244081e05400082020041c0245440c0030301c10703400200118102140740131014207074500402010340002c2d12690352961240288401900840f800c204018411400d6079200d10707000d8859950341d80b00c00d0b40842a200700c01e000c0c40b040c2c49025490000107503200e4440110000850251140700000c40090040500304002900d40d8000380a0090340100e000311407a954000061144005500c040e200c0d6a8880007003010645807011102041d40907100980d55500b10b040044031100500003840135000c280010401180e0702050701c0b40200d20945642d4a400800e800301a9030740540941d03014440810001c090740340380508240700440e0700f403601000e240e03046444c1c80d007502211f47c2d001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220032778 1250 220031528 220031531
    0xd021008150105040311060c0f030313031704020603040f05010f1407120c08061915050309150c030609040501090b0408130501050412020d030203070807050114010501020321150a09 79
    0x1031010014101c140070341005001e191050400740703152500703072544141070440350281100007142c0224070740501c64801840000d2003143d41d2410101c041d071a20b001140c005500140111a207110b00c0702200400501868000703000390309607141c54803280d4244248c0001113540350760f41c2c136501303000384101e000f034083c103160511a0380420718205001500c01016110320720006071803d0900c800491308034154a40001d070950745460006408003040c003400c00070b034220481500108440503061607201c001103118440b00410703511040111402000d1801003501c0407404103805000040c2d150a00e01136081c0d005018030000708034549240c46102c04080140c1c0c05031000b080c001a44180760094a000c140181030a1074601c1c503003407030b01003c0c0710081941e44c4001e100b07482100a900904d807007081510201340c0c000040d035540303000030f2505030700801c10240f4107880c40380408000220703980040305543d00c2511040121000c004440c01c070f2264a00018000585a001d89540480076125440004054000b00c4d80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220034028 1250 220032778 220032781
    0x12050703031404020a030311100609090c0609030c05060313080a020c030606010e0a0302090901020f0d020c280210050412051005090304060903080a03060902070602090f04060815060d021008 83
    0x4008003520b80351034408280b4a941018000140c032a1007544044035010f103408050601245101403d10034405000054141420004503e0104a5202e604224401e180305050039964110a41d00d00a01d03100150041a642c9801c0085003060380007941d02220694040104100c10303516009190004041d0000503840043d82c0c007060305080040d55007040e42400d103140152800c0c00001d000480c2808000d000e03941c82401b0034400794007501a15440c0c25076420640c2c40300310105015000b0f402441d007002d550f12420202401200745c07490a04503200e0b41c2c20052810a4064080c0480100640300e001e040150420000a8400003d03000c2c0020501c41e801901f44c144004035104181c5202034103d81c40d60f04204400c10030b00d5088140ca4080380d42c0001e0741a00c90014040581c01449c9950000c03022500025081c8208009a03000344040c15013180e601c614024118103000031219240105421030303100002904040c402490a0b9501110040c00300c40c0d20295580855500c004451410004c10035500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220035278 1250 220034028 220034033
    0x30501050307120318080706021011030601081f0302031002071511071b05030601120302010e0a021e03010f06080a0512070209040609020d0614090c030f0c1903120507 73
    0x405005180850060501c00d043c510024189021a80c00030180304e864502e03505c05080b00c0d81ca0f60000e058500c00c0d601300755030317808000e902d42a014265100f214a40410a0421488001500e0044030b041c1d4401d211999001e1201c5455584445201c4080c28040703000401030741d0800c141c03600c56803070020158648610749488162140ad02c22203400c400c0c04c0c6070210b45031034000800da0f11501d8200e09050981424000304180d0b44510f03402461b014001c060010035030b50305c80d070740c0d20080718403a03802003011008890300140c1303806014900940c400c104281a00780594030903d88603000c0c200900008c0d2108040c820345048070f0669001c3c0405402c211620001e00400348503070301d0081c0044100701d2414031302c0d90001d0a446d00090008002c0342e41ea0010005644465030b0350302c0001e5021004200001c0c65148e9400c1950b011038446102c0e12400c80c0d0b4041504020507948080380d5003400a106040d00382d820010b1309140c82203011b001c401d40c06030000200d07400146030084030705c0300d4603200e9a80c3c2007070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220036528 1250 220035278 220035281
    0xa0903021f0e060a2003010305151f141e0a2907110102010b010516120504030b0f06090903041208180613150e10030e1c091502070f0e090c100c0303 65
    0x101702548802400100080f0f8000700364496242c6451324007113195903c050040c2c46e102201d0002c0c0c0ca5241c54040041045107c0700310780b40000008848a5080104a000400400c0421401d0315003100b01d20b0405c201c1d0200301460540d64155007645070f4429030002000380300c290802032080c1c1300800d040800c0980c6503028412040200030030310744245810102c001450b40743c1402c490062814011519070035046225000b0b4a0185901c0409240e8505100d0908036074540c040d16900d102c1e00314400031404582c0b0000480e4202c440218000c0d07114003007911880c0064200108200141c686085501c04558a100c000c140e08042c114684000c181040d5004060f41c41c840d0317141050009030503c605c250fa03118460301703010b5807075880d0100e1013061051103141417541c1e05100040090700d000708403081c0c582000c0c010044d15504070f4003141c604602e49080b40c4c0c8034024820060040c510034014405514240341041e4050035400480f41802980340120715000006041c0c00e0014402085040403d5810f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220037778 1250 220036528 220036571
    0x307020a08070f030305160b010b0c0d1b0305091504180605030a0807020f0102071a0408060a05070903030f021c0e040c0e01120b04090c090c080a0903021f0e060a 71
    0x18286242060f0300d1512400712808060180710004c118603ca0512000300c10b80b4003503000c8a10410340d41c2d111a1414a6009800303405881d00610001c0404c06100b9103020344130b210050400d14610049440c00d640d190300280d645908941c0c0582074581105145006100401c0e11644d00c98000500000c1d140481e051a007206209401c0494404081482882030310309060b0103e034880d550000510060386004803640c40510002c174102242d0070a10301803000f41040350945002d548055884d80d0380f0a0444078200d81500c08600c04c41d00900101c0c0c030030100080e0403030581c0121110141901c401640c1d04042d4244100011010342e8051030b1030805016810b030305c003458200744280c102c0e440d00280c5400407054100d40201c0e50f422000c0d51640c0d07940c0102917041d0300040301c0c82903141c589181a01800b1a809100c001c21b05060200d10760a025102d01d205050b0144c1c068502c1d669003810704400f03041d580c00010003c54942000403c01390050000900131190640f001403010103541c0a500542e50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220039028 1250 220037778 220037789
    0xb0609010e040b010b0d0b0916020d02010203061503060307081b0103060602160b0c0718050915040c060c1106030f100605071502030c07050a03050d0f05060d02090c1b0307020a 77
    0x6260003800300003052900a503045d030b02e21086403615486141c1020700100340146510740d02045c1d440603c12310284052a02040c070b402030342680c885c1c8201f0a402d0742070b0301c401d0b5081500f014036075030359034011108640519000103000f01a0f0380001e50f10001c807071901c4401042001c02c4912865034a0f4103603014807440000384401e0018000e0a01d07a003c0700b801500c02c900c01c044840d00002080001400c0030701451002e8540e5101c03650070600052103440041c40c0848410300385106d180a441500c0c401400004d1050f40d00101e080754031350038003408540706140c0600c00c0740e42194980c040b41441c2c0da0b10b006540711b40c1050031034130b03c545802404820340c6035130b5520000900c8010080701c00851808840d085007842c41c101e0160f903a132204082c6074080c0c0305200780a015400381d5040e101c20142e102c7c000300040051114240b1100c009211503100302c40c0c050300c103240e005695803a48001401c1882080da4810b440041075400d003240140e00d441039018204655000d90400950601180b41558a0502a00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220040278 1250 220039028 220039049
    0x807020d12030609060f12140705060f03090106120c0915090207051c1103121306230c090d03031a030106091d0a05071e0f1203020c0306191a0402070b060901 69
    0x14036010320403102c3e147d1518007810804200d81c440d007960504008180082c01c0140070582d6481400b00f0000e0542c00070740c1c00c01015400c04200141854146900300011a000f551480a81c4d140141c04c00061100303040c9100e0700041904005100c8600344050f04005011720060441d4626000c2400da0010300316004e8030902c01140f07440c001c03000002080e02c05100b00d0940c9001d4980701c1c1079415145140081d0010419410564640c4850700d214102c82c40c079104103c1c04445584032001d40342154085c1c09000c942200c1228a00404288290010100f8600381c0280000504220000c03078207495294101148250b01d8149071203005800041d00e0002c006800302800d60000f9955030141c13281070720b1107003940042d00751000900c0c0e0004016044010052055400d00d80c035580d04190100c844422030135409402922a402a2800d000c5200c5228640615003011035190780e0f0703104401030000e00c45036134404001c0c45494605840b10310041c045207008900500451401904004685805801910515 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220041528 1250 220040278 220040309
    0x30b090a09151505060c0a051c0f2c06093304080c010e1309030c020a0501260709090f14090a030e010518181605040b03040807020d1203060906 63
    0x241c845282c10341513807000c486099403090030a8030949001c40202c40a1700900400840c002110202c0102c0b040c1e00c105a15002d0061564207002c1e6100d001943c0c00c072914200e80402c0c1900a1000143d4585144009004608154031840401c2e20b0010003a0551805409807420301d03214003018003800018411250b02c680303064117008525482d8100c40411034103208011081c003c45030349410402911804030002080344c59200e080080c00c90341f8032075082c0e0280c9016040401c165200e000c0c1c1051a0007410400c0340200340c004010046c484000701550100240000e0204060415000710150321503005408104409a2501d0000030003002d0034204107030344004203c400081c3c00c000628050f201c2400c10584803441d45102c0a15000c10310302c1a5480031425494282644c4590b1003103000d91449107100034201800b6009890038400c0d800342d503106a03408d100280018a940f0002d0011034405000340b456440700784d9441140030074040313814010a817070f84014010901d2034458a0020020003601d038075070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220042778 1250 220041528 220041551
    0xc0b090a0b01080f1903030618060302150c0c010c0206130602011d03130e1302060304060c080703020c0a08070204150609090c0302030105010e090414033f010e0403030b090a0915 78
    0xc62131158455960503482d1800700d41850f01030742c090401800031240c410a540c034101d04d027200620300d0f03000891146c0075080e4030b003411145e2130090751400c1c069100140142991080156600d0900b070070205c4c0d1041080150501d10243c1c2c020600041c03200740c00101d01ca41000e50300d21041c459881c0c02e455030390b1003400f01c0031031001c41044004c01c840516058005a8555892018002c60341e210b010390810000400d002c00c1029580c880038014815030303500102c94585802c110207a210380145603000d03074040b94425009c59102f10042c4161407004000041a0048120881c55400640e12441c04520408010003074500d1500600380c1c00f11003031504603d15810600081d00040820143c01c1c059000f4000040400c07914004103002c0800ca07608494648000c01c0300001554140d00140140910514040c08104415580c00d82101d00f0707075100b2050741c2c0c2080b00b104c55a20000740190701b00354941c0d1160b406622400d0b0814002d650410300410069001d040c50194458010000210f040c54500b0a104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220044028 1250 220042778 220042783
    0x1806030705030f070c0609030e0301050a060807050f010e030a060c02070f03260702090a020301090605030304050901090c0909051603050906070c020f04140a0504120804050c0609010c0b090a0b01080f 87
    0x1445040400303c48410b4580d40304c111034040a00c01e0060000c5e2804c03158505043d041007540c441000c0c110000c2c001a03480d2880318052382c146210720801030b0300000b4144564a061320080c108408103140003c110039989002038a085c0d051b000a94020383e84590b140b224a80c14000302ccc020300004c038080540c4510b1950f45841c84c084050982d40c2826440703004220542c0c9240c2100d0410350001c00314511814984041ca009500a1144201c0140360001c00a943c0c1008026a0104c44005001074016840c1c120f04401812a48000404100415102180b044a244541400383e2482e01c41043c181001c27884c041e045031400b41000302660301480402c0402c07a84401030107501c0303034103559050485461401180c0608540302c0003002c2d040c4001c1c2002044d0190307500c400d10a500640301015904107104040d220041d095401502c036400c071100c400354905005000b8090401c040c9003042d51401c19880d00000e448056134055069001182010103002e401038186024014078005861074000b0b0074400356 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220045278 1250 220044028 220044031
    0x1f060804030f0e011e0305010611010606080c1b0304030b0f06040207121128050d03020c030403061a0604090e0724180e040302030c1b060301050405040609080f180603070503 76
    0x10b04000350f141c01c0c15507036481003001e04400aa11088101c44075034054015010305400d01804000460f1011140e10031201401a101241e1642c0c842c255551100c007040740455000c0c0300c4551b016504511001800642000204000d41c002c0304030071118200b2400b06090741c2000b4007001d10982c0140500c1e004601c008904119148003810318041641d8414402d6045c62030908030000c6a40070150701400580f2002000030a9070310420503100090a01d000903002c90050100075010b96105000a000041050744550310820310b14010b8500d00001d00000391035a0300940117020f10384c0d140e40000c1c806000801c1007038051300c15403480c14a00c0300402c2002c10356008507131100d410071018a4103081058403406444000c0d002c1407480342114545410060b65035803101111409521440380748024002c004441c000c1a144000c11051130740c0d103882c04110107002c01400c113643c80c640e038940c18000945144001c2903140c03580c8688540340e80d40440042c2c078403034100008074026801007080000310341c0d000003100d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220046528 1250 220045278 220045307
    0xb07140306040c11010c020f0705030d2a060c0e01110601141309020d0309050a0929180726090303042a0308041a0c100209010e04051f06080403 63
    0x180c0400290011103007860f01400c1e004885d441c042c3c03102c46885c1d01082400500c0d044004880426075503806040e0380d05100c00010700012004040051180390a10454100d481c4860707001d1605222078848004544140240c0d0002c43c8178070b40c0103c601e5070044118064000e0b00009400c5c01d601d4860700c0e11070159035850322440360807003500c080c1d40004107a000781080b58000c0d00000b6214582c1c0340203031000729039016151007500c000c880010840014007540321508402210001c0c04010103100703414540040744034690211668044002d10b10b0301d02201482400300342c0d2214041aa0200d0707040550203011300c541d51404a440420410000010440341c000fa03012811301c200407201031419a030824000341c100c0456402002c00002e028580c0054001d6400380c9412480d8041d1440003079415106800710b064550300030102c6c07408920701590107000c1580d018100018000c0c108c40029003240c0c4100d414000c0861850b1104400a0302120500046e01c91410205a5420035441c050700510980100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220047778 1250 220046528 220046531
    0x15080a0902030703020603071107031a0c0a020a030e04140a06090f0605012007030b01030501050402030601090603030c02040903050d020f1b0102070c1e231206070507112107030b0714030604 83
    0x4109002d202716400e040e5414100c00740d80e001c94507880d01c2003046250305c505581690200700460b1031f43c6400000c5800c00d4600e07400038022403c0039541610140c0348800040c2c2d101d1b554183c9a049100c0e510495441541031580000d05181048070010031206001c80c10040c5902e80b0009207c1c80c5d130818842ca80441d42980705010603800703415410728042094000074145003503400000108001500514081d600c200c007a03400580e2500a0f0a08a804d9481302400180740c003115600981083d5100c0c04c00d035030007480c041d850070100b000b40b5816a0301c008141c17101c402d80000c1c0c07050040d01d6071564080380f41e0310034000c1d8036154980d1900900740790346006288800b0b64031150383c0c060302c0d0b19040050090104044000c2c030107121480e00d40f903100c00c1c200000d00601c03080400100b0024040b41b201e11500883e200c2e0350501c1d550f500c0e140b921600c0340d45035640040b1503c41c80c0b840c524041803461880c00556001f08901410b41c0b0380f02940803005041c42c0103001c5c6002850022070300c4001940d0340108107540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220049028 1250 220047778 220047781
    0x7020409111302130b2206050414031b01030e01090c080d081e0402012a150b01020604030f18030b0a0606020d050a050d18020405040501060609140901060f05070c15080a0902030703020603 82
    0x40a14407240410b02c0318100a01001b0026081e43c1190140c4215041004051512409442890303240d881c410f1101040e1500ca8030320303a16960003580010309516010f00006540700d205d544010364455190840540c90303018140c14a05240c2c007210490b80f00170041d00800c01c410145010000c622000b900003418020f0035246040311011910a15000c40200c14560300d0f40082c90610141a5030312104502c00070b030900401c0d40c425400024014000ca3381079480a1100c91658001c42d103213405801c814110007284800000424801c04089004801031034002941e103207000300107803402c1d083c66a124107003c07060240b0010580c00c841619184000201c0100b403100e64030180c0381403c64080350082d4004d20340b00034402403017030550041c070030744038103840d000034052715104103075505803421103900e602c8442c020050102ea031280d42410309241841c145a42415030960300c520440800b50010601c040c59034040c0c0c0040c3e6070128810750040c110a40400a400c0190086501c1d0419404068000c510000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220050278 1250 220049028 220049047
    0x90904020d05210901090504091211010f050c0a030507140715020d020307090611030f030606070305070803070c02010818060f06060c070f0302090a0b0907080403020307020409111302130b 82
    0x1162094140300c28092010140403140c2400c2281c100605a50000d140746c2c801107014102485203111161b0003801030900b1503030407c0d007102c241c2d1281070800751035500c85090a80f0764046001e1140117110440309962190340c403480003130031502c0c01040c0c00d04006040d6a4020032040b000e0486880c15041640c1c8051041c408071804e01030f1180c402141c0d42c1c54400820404400d510914150541c1d45c69900d410302d081c00035140556074018450740303000c018020004201a890400011320b003647c46401e0503402c0c0081a2598811354104541e84000f05088411000c119030f8485400b56006101003480400340d0041c02d121a910f0070010801c4016a07032401c00b0a207655103a806880d000904901118991522061007518855844c40102d0081c0020408200c160426010300d502c2442e000d0700302e40403a56410000c68045402410039825400100010809a180d0b40160105113000b0074004292401c2c0c80284040c8940d051802040d003441400400d107224030015150044881d40c0800c282c9a01019 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220051528 1250 220050278 220050283
    0xf06060801092f0a120e071e03020a06090e0105041e0b04151503050a0216020d030909050f040212010c020729030103051606020d051204060b1806040c05090904020d05 73
    0x82440006688000844001981c5002407940229070756505406015031017811040d01d114403c038821580005101784507440340000001c00004142da0380c100c100c2d54980220b42c500446404c41b100184080c0741c10300149200d02d25603401410140d408102e60031003c001c07411018412010300410944a5170000710035900c43d08161006c3d403055100f01105a640c03000c1c031003640702c1420084c01281c2003400041c5460707254420360307880603001c0c0f20744a10620164204003c01c204a1001c40900000c00da000c80c1c0f001c128030170640710f07201c2c44000017402d0810380104003101181030b040d802c4503810018026030056010030940300700c0d00892001c40d00801103104440c982e4030440b6550020203004000042440000100c9001186202310280911a190740040780c5945038583d104001c5141005980c9a60498642260303000c0d0085800056003202d00b000105040407412144800307802c000180a51860544610075903141c4a0800e54504640d42c00422911000284080c1c40b90a40d4000340341800001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220052778 1250 220051528 220051571
    0x6010c0803060f09160e011e0c1401020d1d030a1d01170903030103030905030613080a03060306020a080610050c07050d0302150702070e0615090405040203010f060311040f0606080109 80
    0x4189010603c0c00714a17000d00d01e03002c9811071000482d030156090095000d4900d4801e031080c1030b0001005459050390503900c50749001c00440d0ba60010140c41c6404c03040038400342640c0c400714500450000360201c01404507131090b005001035a00100b003c205920340008881400012800284260040700c130016940a03030b510210407486040d0030704204e5554008402141070728403030340340c10303e0b1a0b031600700b403559502040300c030b44500d04005005100481d0014018008400c50391030003050654881c3e030780d0000d98020f2030a61010076281c4007805014038107019141c421102a01d48241007000e14400c060343c074403107481028007a0116092030010b06200707022490b401d11800400444070f04000800941d50010b40c03140e0641c10742c2c49404518030b45400c120035845807040710710941c01c103800d0008203c02080c01500803a032640d0380f00c12054004109000d020000c0d0701800f018008400d54005103c2650070880b4040400da28128003441050b800200c0c00381510032504000500f4100881c0f00c10702c2460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220054028 1250 220052778 220052809
    0x1806050c1f06080d0e041d03120916030f03030c03020a02030a110a08040e0a0b0609130b0f04050a06080105010f03080a0f090308032d2505070b0901050610020606010c080306 76
    0x104da90701c010054028521214014080d1401c100300c89024681c1c0d2841104062280c1c5035810400c0141c040040105115400410441c00c0d40c20105900113140715000042e070044034200021942c21062641600c554508103003c1d0400b5450301c004920029224451041080284403e402905c900c07014104115180c5035442607445907a10b440700e440c4c2c001f01008031403500b0312030b0810301104050300304401075501b9200f0180441d8495200c0c0750040c00034007000b000403038000440703060002e0f2a503034038001c15008104c0c00000180403402c1c126041c3c2942d00503005190710480c0c155040001540000445042e03814a03d840c072011201080c00719042062940060710004000c8240042210f1400c4c0312100341c06580800d901165070140c01d0543e8400031074142031052a00203200011006007054a2800135031441c010b458074415640b00580003606844a1a040e99114100001070070704a00740c18111115000034106407800500003020406d035114010000d02021010a03107545605845106464 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220055278 1250 220054028 220054033
    0x60a021e0c0f060a020406050904020c24010f14100503130c030303141e012702130f0f08030f070317040b04060609090f0f0c030507061806050c1f0608 66
    0x901c844070702555030b581d2000700301c0c8a0061002003101c0c50031900c211000c641c96515001e007005c0142003040000d42010f21003a520380140d02c80f01c2400342d0880203080c05121616a001d0300d55040102d202c50b017804581140303071903150b2810002c81c0c40d500c404000b80c040714a03240180da2075842c59981d0120b402e11420080040000240110800d0f402d9045440c07152102c000041203640c0b000c0c5100d4100805680081c3c81c0001440140316410142c25100400702c110000411080c40314126501282d12503050503d0000c8840c1052012010f0200c42030300030300f07024440086450801d500c880c2c991094440a0820400014800c13003094001d010004110848000707403c00c0e0310745820503e22290040320304481d100e01e40000880d400b1903038408d200b055078000b03100140d40c61960380ca21803081030f04a03041e2401e4407000000400203c0400501c0007404541e03840c046450f1084000c1d00700f00070715411400c1031040070b003d00c49403080c0000d0f06030424000100214412034004107c1c40c000c027240d4200a6031030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220056528 1250 220055278 220055287
    0xc020d05060106020607080411011107050612010801061502100c0e0603090c0a0501050c0d0e12010e0a05060a0902010c120908100c11030a0804080c2b120509060a021e 73
    0x88081880c40c103c401540a44040381c0e603076001210b00a2080320300400c41004590399002551050400c80c0287d03910004507954940c581d80024007541000b4607001d070040c0d041005104040c000c4c001d5030024041100140d241411000c00603490300d10149546024030313610b0b00d0380300b180ba03c6651400c0703080c1c2001d002142d4034200050714a03255160380c9600c13801150020000034072035100758101c2d6845000407000d040c51290034441101c030491110b0010740d0145000810200e01c200070710079010051030890041000c600c0610341a810504010240700c00c9034a804c00c0c810250b60440d0764415180c0d488034002100c01810700081c1e6030101d064101840310311966082911741e0050b9400f01303d1441c207a40350448505c212100542d541e10403a0203082c0050305040100300011041070192964554035403e0f5400489551580c0341814a400007180322841108000c00c04950031a429450700e1140c00c000b40050b141c40084159906400380c00490042d90011f0400720403002c1481002c1000008060302e07645 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220057778 1250 220056528 220056533
    0x1005120a020415091a0f1327050402060904050a0e0105010e060f03012c07030611040f0b030907030314090d0503030414073210030906050c0a0512070c020d 68
    0x940041c001c3d00c007821100b54498206074040d20448048420200208000c040400b15504c5d281d004407000c143c000c8400d0004200c1c0030514002500500012940c600401c0544046104c50229100c0c41000f4a0300e03180c11b100c00341c0c403101c0841c0d126003030541e0003040a40f221020340f80103201200c1e0f1140907510303200c008589c1c3c0003c0f1503007500443c41194000400b102040403d4222a80e800c0510070710321000207108012080034407071009041700304042ea181d45589490307403026103410340d00089000354009004e100905502511601810510204506600d003013500f141c0d56100c1400054248501c1c0d1040541070b110f80421103c08440141021f80301100500c0d191350399800c00c5c0e4040702d0302026140b4141003104002458411070b81ca44540d550010000b100c2d2103041c03a28030308010f441c00e0722540040b03a603864001d01080385080c0390f90300080d052400e00b440340440d1000307003881c00ea2120400001c008640d1100a8403003006203080c4c0200d0540b5602c0f01950401c1003110700075007003020143d07400c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220059028 1250 220057778 220057781
    0x807260a0e0d2d02120313050f150304060e06011a0703360503060a09200301060320031506010509010e060d050c03100e0714070501110301081b0406050d021005120a 72
    0x115500c05d8900c004405488400c4035241c2c058070301e10b50b4000e40034020030011454141b18443d40d43c00302421034a0070ba4805400080f00340c0c01100d080e04c02c507440f00b0071425440340400c1403a0050544d05601d65080c0441c3d140120f0170b2180c140701500300f01c5445541c1858500246114000c22401a841d0300070482441c03c180a070f544900c0380910038001d0400240140c502c90207000c0a041e800080a40c81c4000001c61181011a5103000c5806641c0e07440d002c000501d9054000444100900300f80151503000c030201442c21825070040c071460803822007132241c02e9030803c003a508600c42c2424030202822136000400c079580a040c42e0805d1550410040c80140d403802c200460003a4540c03c00540390544800c940240001d0a0340d4041c0080c052030820620308a9820160010a10034400811400312003540c00c80650802c0e082510590805200029840104e4480003c1000152824010103103018005404001400350180c020802032242c0402640b00720111407001d00812610040390800a81400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220060278 1250 220059028 220059113
    0x1506060f1804020414040609051b070f120c0b060409031b03050c0601030812090109031e27050a080705030604080915070b04110d2d0807260a0e0d 64
    0x10f0042c7e00c0c1c0903010813406618050584030320001500d001d046140340b008a00c0780c0d03200c080c041e07800340c07a80c1012400041c284400149050155912501071045a0034038110b1014041c0900d48620300c0c140c080c0002070b4000005d8481101c0680c00842c100050341030580c2e1a20504447c80c884c2c0c00b07090008400c000b81000900903c41c80c85640451650b03d8120507801c0b2140030340081e01051240720012150310b480c0d404580d240080707282c280351014500f40c030010703190700100c910000441d01880c10300040c20a05000c200a003620b00080c80b000e42b8240c0400d0f211140600042c001c181c1c005855407542d10b602c43d0005007410047c00312680c81d0540c1c180707a400d101c000d9800311101c0031410741c964460304e4035030348010040c0e40180640ba4104036440000610100700c01903e03e20070b80001d41e03040854a541c025020b10740c081c0c003050b66100c900009000c009401003454000f5600140300c01038059038004103418010401b80c48a4181c5281410030016000d5440e10f10740c0c8e803d0034a0821000d5100714800c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220061528 1250 220060278 220060319
    0x70e0a050f0105011d09060a0801050a0603021009051c05070308030f0105270f09122b0501030507230604120b060108011404110903060412021506060f18040204 70
    0x1c0140d88580044580c80b4030080b001c01c0c400765030052000c16203040c00409401010050044601d541d032038051a080d90340441c0c401c1200c9a80c5d078810015810144041c48100590f4500303403c60500f4003000540c030360002d481000400c440072003000c00308501040603102968114a45c00d0311b0307142801c5205410342090081c1401484d010110a4510b0040c21807024101100114800c030f5903292203840b034400d0b10050800034036101e0340c400100c401402d6001002c0c00900005100503554415030b41070b41d264500d4a00410441c0340c40010000b0803404a0402d0648800b00841b10f0400d60007145d441180c1801a1915400000007400082010307252900065061040f0200040d9030b4809006540b140002d22a950032443d914401d40c10030300d01580304220f040a60b0080a00b0030350b202c1c000c2031400c0c0c0c0c104c8049405035a540524a00e05804022000030400919801105031806101180460003802e816140c4040007007040e8a059400c060b4200601101400454a840d0780c1d00c2c20804800030680d51 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220062778 1250 220061528 220061551
    0xf020c1c0906080c0703180f051e030706080901090204060608040308160e010e010c08072a0302010c0809030c03104104080f040902040501030f09051c02070e0a05 71
    0x5a1481500800c0d480e422952103483e2404556070b03d00e0480e00d41c0d484041c0c100c04001d0f5800c110100c01480100c81e001400380c2ca14219649803d05d000d2190b00c1c607500750150010700c02d05403a65029030300007035000c0c145c0d100c1d4504604951115032441c2d026041c0c180c4020b62050a10743c0c049801503226154500c524081e82d9002110f4442c0450700c001601010342c0d04000401407441050554000c11344102e030001c0600d06036207200c1580e100c10380513800c8401d045038040c1d0310030718101e011034005880c243c0c0a0002242102a10b16644c0040d000001c99040104510000b182c1103030b03517a03024002158542c02c003400350b814107090410460010510801c94400007580342c40c90205454000003142440030b5044284406000120318a0b050448001c1046034502d00420000000c1400e440180008100b144c40250300ca604100000d8103131200342c841801484e18200c1d0358000720fa13000409030328149400354041d22074000c2040803420300c81b05030404401075190106010070b8000d103912203031140d85894803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220064028 1250 220062778 220062823
    0x40f0312140d09061d0a08091206010b0a031506271502101d071e0503031b06060607080d0507050f0a0206010504060e010302151c0c0f030609050c0703120f020c 70
    0x2030041c210710540000500d46e5001c9400c400c0020311030b80041c641000014425041c0c0c12040c03040c00e14040c826000a031000f00701141d800c00c41a094000d460b181094030a038004843d06098004080c0c0ca502c080e9403040841400311004c9101c0712240d6000030340252000c810400d2142e500183d0758401d4108820306442c0707064030048146c0d6068415211800c0701c0b0000c0c015252a02801d42c000040206620a03000d104d10000030303e41e5010001000710301d0320400c2c40390f1484030500c551401c0c000d0040c8114000c0d9403c01900000511781c808807495900344c07030b00019145d00ca0800855032401510301d0010010400a4812101c540014900c1d048034170444d4244802a25814001d030078540c207100c002d403c14800c00300041c0001c11030000e0410080d04185000203085150358070416901c0300d03280c60001c208000d88045585505000764005000c3e162010310a03810850417450481c4140440a81000f0105d100c1098a08154110807034202c540e0505544500b81c01c80c4003510382c0440100744001010854 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220065278 1250 220064028 220064051
    0xa090212010807060e0d0c2d0f0e01180e10090507090b010e06030718030308091c0e060d06032a0608040803012607060809070803040f0312140d0906 65
    0x1034550140c03041c5540f4071105d21248030621280001000080701c281c1042500070030104210070b003140c2c00c00c190050200140005241c610003212031a040150040300141050000c0002c0d030080504484040503a076400142d840c40041c0240840c5080c0021030107101e851b050303050340d40c2d00a0b1480f10701841c00c1d0740085540b11016811510310400180c00b00342084001b090a2422102540d805030702070800009050004014402c60350342500210007184555041c007a04032002c00620321649501c800c2c01d41c2000c1c001e4000340081702c000c60728034441c5200280b0b0188045054002a00440d4004020800460401c61181444c0110314035400c040075840d800141a5110f071390806c3c05103401c5281c00c2d20316402c0c40c9244407200c07070304100d400c0c010800080703103d0f415030100403e60040034180c1d2846050704100c01010305008540d8040c2e24a6801030000b44410140240e0680c1240d6004a903041e1600640409482c0e510540c0c001c420f1158011902255500c540e070050031200384901f05c04c12060b2845c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220066528 1250 220065278 220065283
    0x20303130b1e070b0c1303050d081617061509030708070303020610030b0406020708250302120a12050601020a05070803041d15010c0305130303020106081621030903020a0902120108 79
    0xc400140c01130790500d021540401c00d16005242440d613003018208010b8582d1940b624000e0000b03080d00019a80030204012038a120030114603098040c0b9201c07904405042042c0301211000d403810344510044082d102c40c1e5034500c001c5645e030384409000d540782140d640d00c4680d1610340d40d11064003d4058440069200c2864841080540f03a01041e8030546d503c8548944000390048002104c213403908102c21132544459a008250394101d4411a000410b001c0c41c0003400c1c00741e426035a0b0075900b414001300d04155002492680c1c1d00070a2500011b40303585500040b03240822590001e44036001f046408030304440040010010350f00780300c45502050740360400000c18050121501c0c140d9215502003203c140d803081104200f45802458250305103484261410002040b90b0b06c100d0240c0c0d55068100070440050001c1210201d103501c04c20340c0300f07107414401c1c010031801240070702266000c03415201c00c040c020884d0380d02440c0c01a15005031940c0f1480248025800090840000c041d404000282941c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220067778 1250 220066528 220066537
    0x311070915080607050909040f06020d090b060a17100506031518250e06010c230606030a0201020a0f03090f260a0309090902040b04090602120c0a020c010c020303130b1e 74
    0x11700356087c1a640c60b00c5214a02219400c2103640ea030b003c11603451f900c0001c1c000c04603403d010314109812414211304001d140d0349c00d5403001c45040c4c60024041045800800ca01c0302102c9140c20109070350795117500081c10403d90542c5c2121200c0084240103214010a150340c00300c8040c042284d80100c6211790141e0480843c0c038565060315510a4144604501d425034690001d406041a1001c0049a55220440c10300410700141200815000d10b610308001c0200071341102c000e030301802c00d11095800003500c4030f048030300141003044210081c00402d4403904440c0c008100c21940100d580361582c024140802c4000007542100d107d0240100c003500010440720249507040d21450601407421002c013000d0003051000388d0f8055511805803000e503c0e203018049881d032140f500140d07a8041e4019440040902a042e0781c5852024803052451640024029400030303070908200682c0c41d03007840080c0c51446240c038086503500180d0000980303842c1e880064138481e1f02a003888111b143e138450109219008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220069028 1250 220067778 220067797
    0x120c050a0f060209030a1b060810140109090f09061a091909020a0b130e0405060604110706090b0601090801020f030a0203130503270904050a031107091508060705 71
    0x214080000a001c10700d0340180d881c850003016003400d224200103410416803200036900c45100a01e0803040240342c10000000d0311007802d101589081603a03841003146c40da0b0090050707010b844684e0100582c0100c8540e0000e0002c8a424010020f050740f1000242961010460b500d904284410070400c1c80d24020312250349015000008690794401001c1042d001e03030041c0704845030f41d19105000760301da00640c0000782280c2e009172613070788400321031000b5444243d50120f03480400a80c20303c400207001003040740e00300b4401c480100c0c4c00a094100b00c1c2c2288200c1c28000c00c810300d852006410403c4004104d03229207402d8840262440da52401c072400c1c0c1c40750320740d0f4810a100400015840c070b002039000d103801264800c84031807400c1c03d80e55000d03e1a840000300d41040c0d0f5540313580c181540714001525500100a56a41070582000c0d962503956440c204001022b0041c06814822084400c004030001080c42220a020356104003011448440035405224503e00903040010304060040c01191070421 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220070278 1250 220069028 220069033
    0xc0d1103040b151909020304110d020a0b030a1515030b0103020a0903020108130501151e120609110603010f050405090312010b03131203020405010f080103020102100902030c0d050307120c05 83
    0x3c0d100c0d48040714904082c01e40703551000c6030030f80d201010440301d00b498010f44400600180d40342043c2c240301116a8080c0c2da80340c070507158400e6030001070f21b81d020344104864108940544940340c0001c114043c000000c0361251900c102e130380c000786da0000c01015455084c403070b4508102d00c0b0f0b100302c0110264441c102688010134070a13034040005501ca042000c0c0d010203003d06d0102c405103030b40c3c1c0e81b90a42d580c01000c4042c01e46050310602c12036805070304014881c0300029079150183d140c16000070350004e90078006032602c0d680e03c2c04a4140000320b40448d11114008083c0d80e074035a12501200000d1800307000e4240103a141900040a902002089806880f89000c031510580c4c03a02002401d0b65000802101c5024429000c43c800204058180001c2e038106031400343e01c85042000041010314007030481c0e030800406030010400350342c002c00d00c240c052444000100741c031a9140003092824106455183c0c000c10160840701c240080070001e0400c0321700c285001174100704c2481c0b0484115001c05801380103034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220071528 1250 220070278 220070281
    0xd061208090f04270201030212100602070f0e01090b030f1006060306090e030723030301060c120f080c090f03150a05090a05030a081003020910030203073005010b090c0d1103040b 78
    0x180841320f690f0301020710502d000346c41e0004808094402c2082610100c90b8622161406e000c49a0113000c0c000181c29000c2c2381000080c03808a500c1003558040c82407040d80c82d5035481c102d285480c1840242101031024040b02d20a00c007001000000740311501c110400a0310f041004141d92140303001da00d800058140046090441584510f60000c558542184410640c1d11490003904020701c0914020555074880201000290070180b4014410301c98040c1004102c90792103000d2600b000000e0741040a034029941c84801c05804100c801030b1000c1c3d1650700d842800041042000e1908003e803180c919001c0034841506c4000d50240c0d10103001d0f038000c210780c0003880b410380d003035114008060f880041c40c540e040302c0070f540e9004500501e03c1034507903074002141c9840520650030100300240082800324007003007845044e25100c0a030230401c2c0460000b2505c240811100f880070940140e05480c000500c940900d08000c500d50b60306501810354004040c0c185030043d441c2da0020b00642c1c0c8555000303c04501d0703070b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220072778 1250 220071528 220071581
    0x1090b030c07021201050405010b04090203030a0e0111010204090204080706020f190f14030309011116020603060a03061b02240f09070b0301120c05030604170d061208090f04 76
    0x240c10050a416000c4014002ca20260b90f510701001022000c0000009550030035081550942e4488040507004608040100005890010855501c4400c5181014603404020012110782c003e00034a9000740d80082404102d25002d82d000340201c03101344088845107940c40d40266200e149000400c941d0317420404a45180030300300051110500c0c441c00750f00230542d9441c0d0f00d40c5400c1660954032a80c80c1e02c003104001004100b48590143d00340580e13280382c20029103089010660116001c028007503000807010841310707254460301c0380c05154400b0b0103110b0341c40048005151664124200401445500740c2403c0c0300390342d00782c1002100e01c0c503210440c0c0d0f699184494254034901400303d010b184030715840000c1c0340980c84060350182108049543c2807102e02d0a00f4121884507412482c4250082028400005d2610112245945420398415219101d841b10039000317040c1130b84041d0000441000040804c1112401040340c210101d42c02e0075001282c0701408115002c1d0104050b101c504000700141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220074028 1250 220072778 220072799
    0x406080f0c042315040303080601090e13050a0c0603050f0f1b071112010b040b0a08070312180e04030f080f06011202040b0d0f0608030f1c090f0c030b0108010b0109 72
    0x410303d41c00010030000b01d8030800852480b040084d1441c42078031000c9424800c05510400d11600800d007440d000e0080c5003030075200c0a0010001d003250900e402d01415410400c031051100643c0590002040030030240d60342c8015020780001c4603074065054100d0700180b032a5507031a080741d01540010005074103041e000c070202c8145030703c03e800640703405556010301c854540c0c80c2c051130030543c04400e0003c200205500240010341d0020900360340b08400c41c03401400340550006201c802c0300d422146801d245c1c0013000703040c1c0f04c80072118400d00f5001a8288003144c1165120300883c0600e10a9031050034588d60300d8412903c0385016116481c2d40052400440e40e198464000000c2c0e01040c103c0041c40d161340d9002d04030b0039902c070205052035107071507400c4000c1c80012031040030018182c0b40b016618000d12207003080c0c010302c1240e4403010440103414403051990300030b40c4465030455002542c0c0c1401c0e5224207000120341064403044502c2651400081400001801041d1603140e06848441c4600e08040213030030f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220075278 1250 220074028 220074059
    0x130f0206070501020c0c0f1002030d0911090f07021504030206040201121d0a060c080115110a1e05010b0307050a060c05030c07060c0b07020a020f090a0605150406080f0c04 75
    0xe0344414107000d5500850b00a04c01020789003041c1004244000750b038020f100c100700c101c0f1242e611031101c1440c0c3c0f0b00e14a03000710844020444035180083c40010910789142070400e070621142c0c0080d0100100301c40d11490f000c9480c0600c845800700c4610000f1784c00c0c00080e900c02114001c00580161b4003003030040d405001905401810440c0c0800e0900c0e4044000d00041c8000500300d20b41c2d4052004401070000500c2464459041c615080c015903040028050307810740b0901c01c42040150319140540340070824040f84018035840603091202c000c001449144a42c082c80080d54036500c0c100b0b9400c081e14000030014116413010f0524110507180a20640b08956017040c1610240010484010b1740981441000b018006c2501c4144020003541045041400028540800d552103001c00c100580d4030a5251001040304654a8140345c1d14074200c6006007203503a018680005220f03c40030355041141002d0000e41c1d0b41640e0700890303590b51840082c901d01c0e0030382c4c03d110303d900100300c2408101610350307040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220076528 1250 220075278 220075283
    0x90a09020c25050a031113020c2b08012702030a230709151b030f0206150105071401090609080c010e1207060b191503060909050d080901091a01051008130f 68
    0x1c7c044500500851059a02c001010309990f0400070200c0074070300d07403c0129440742007140010b96101d0095100900010810b0145210001e203103c550740418005a440c0c400038803100c23900b55203900f1703c8600c135000783c8612110400c1100305588100020050940388522610a640d03c0c2c5101c180f03092000e10410080ba51540100800280740079406006410b000c6d80c028030a940d00c05804045203c0241401801741050401c800385500310116a82e004007640d900903000011880122071815582d80104584c200c002e22907030408130013009202c10704001c3c20a400c5c20500a0101d1142d46243c1925403400e0040b9050502d0240040808201c05c0d40c007616002138007501c480005094030400040c012595400081841c0400c100b02c08604d03414080d500003014016030600c03c05080c0d60390702c1d46400511a48a0400c519240000e40700d03030007500326902040c0c10211480075a407102e000040c0c114402d014150150900250089480d03101d01e40c0356204004402e050343c080d5000f555000505920003406 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220077778 1250 220076528 220076539
    0x9061d0a0507110102070b040611030108152815142103070206190915200709020a0507060501051005070f050304090c030e0f0c031002090a09020c25050a0311 69
    0x100444980920051211b18010140542d89242078078028040c3c410a01c0008104041800100b00c4001c00060b20b503104607c0b200d41e21255914190b02204211546d41842e80002e07041980713880d007660a600c07106201748804d022280e290345030488602d00070182c0700c0e0150000c03200c602641621640c08003e0f41a4082c07001035900e05681c0d900000d02d135030000064081a8040002c1080340c60f41c01c40d5280c0c00801140104001400340410090160205030f100d0510203560f1010003115800140700c04000b6041c491001c544031000000d000340340390803443d400c80701c0d5881c0000104061501c1d4009a00d0608160b451500d0318010b0756807801c003114860812203440c80140400300e1211418020003020051560780010215040e0314183e1520041c0d0000700c030039400800700e4540c80e49000c602071740d491902d02c00143c2e681cad5000300031a08904c0503901841183e4800305500d0b039a504003140a80080c0085021411640a021a92030050b8518803540c0d83c481c0b0a0482000002d100340214900108000d19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220079028 1250 220077778 220077797
    0x40e0309030a0c090f0c08070318020306161706150705070f2d05091f1205060702160b0a030902130f020415053103050f0709061d0a0507 60
    0x10918003282d148003255a2461018244a414018420310081c01400c1c0e00610103800c0c03008024001c02d9000d007104c1c1c01c0613181c003d840341c00212032458a40c04d65015040300c1da24030b803d03e06d005003510441800400034000c100f0300011110b102032418000c0400820356041c101e1005901318095006441c200d82a0081646c005440030a4001200042030040d00e081c1d03910311903001810907180701e0081c1401103000c004082c4459154260120342c0a43c81c05458081c0070701d15080f0800400c01903100520b949416a8514100003000c0307820350003008260200c0d00e4882c04400302021010250240a0802c4024003c00c0e035158881c0d04610318072800070b444007000b0705c0e2014503201920420b040510030b10390005810050003603c2645225800c40303a00c0e080b82031407003408004600c000c03c0d0803280300b03022625800c0c0100011004404004542c080110b500000c403816003580c0310945032050ba10054a0314000003800b0310108604800201c080c21001540d5441d5119440144009420241000070070207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220080278 1250 220079028 220079047
    0x10110405090601051c050c07121b030e220b0f010f020312180105150a06030c081303030605031615050a211803082a040b0304021c030804141b040e03 65
    0x41558051f196a403104c65442c6414103080c01d56820040c0460304009a28036240c410648100000000d15070518010b00860500b200080d94050b40310f0004640c4444002610040719030360313001120106040e04c2250440b40c090006603415200d00b480c6c00d000da041041609216404164140d5004000030001050f029501c1a12421030710100c402c132805028041702c2619503c1c00340c50060007420f65240038440310108a000410108000d0500302c08401c20100d4602054020303081807015120290484100c2d0301d605004520100ca54480e07144c541d0950742107010303640c0c03040080b1800321001d502c6045a00a0300041801d04113019010045d0041e6140503044481d000c42000c2501c280c025940c40700b480c02c1200b044a055030511210003a02d0026814002080d070211042e50121101d541e4007a03280c0d5100d0000c10611160910003907160714840704002c0400d9000840d81e801640910004040740304001000d035543d42c8283c01d00f01808041112040491070309402241014151000f62420a0641c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220081528 1250 220080278 220080281
    0x305040317070e0102060903090303071401020d150906090b0d080306010e0a0801090c0e090a0f061e0203010806091209150415020d08090a030503010e04081b10110405090601051c 78
    0x10b4429100040103001c0141066038100000c03a0082d0310b100203103150180900002e680c91241300402020030344c0020a40110843c00e42c19165802d0a03104103000c414840c60350354998034003d01402081d643b0b40140410101214441c07480f8001029008907100100d98440c1682d94000600c8141000864502c01015445241e414001442c09900108901f2502e1400760b85850312078100b007090200b41c004003c8218070000794110080d0b045404a40d114000d428284054052044d219401030710002e1440c040c4a202c1c2c0c0118125030800043d6005c54407241c202586541c9400c0300015004400c0c00944000c1c074007481c0c400141100c0a0310145055603800304c810350f02e500440036501580202002c0c40c1410b0f04150034652108066014001c10b510540d406012408180228011f0300040c000090401c490710046032000d14a41822031610790400b20150b559105c0d074141610040e040020443d48948450192400d90701c0090401e00ca9076165401100c01d50040311904c008400d0801106a0b5602d06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220082778 1250 220081528 220081531
    0x9060608060901141012080c0601140411072004091401021207050a05031b070503283018060b010f050f0313020f0402040f14030c100305040317 63
    0xc00034020500d000c0510500311102c0072a007140030007100c02001301c60010755940c0400e42d580081c00088098076810325100381d00170740500c5181c0388101d8001090007030014804150302031044074140488400009100598021030b00020600b004802c0c030321501002c0c00c1d4107138846035005400092400340c542c0340c44840e2032007c00d000d4010b0354006038103d10340d06200f0900340d01403114103026142907845000142075200c000d240702c3d02403007091070400e210700c00d0104603403040c5d80001c202c90720340c203110882c2200d02203215034000301150a105500012030140002c0c0c08848080030462540104640b0405006000701550001d4607645486403031092550303032144030400b401043c0016803091860000341c40100c400c8242400c1c0f140504c000c2e0101d00ca000101e9034002041c1034501125900e0f403000c0303000e401d40301c0c10550703105001090100c0c580c00710000142c01c44105240381c3c2c1c42e0340300b0403042c03541701d0b1560507845410202540e0044105070280d080280c001e8070a00e4404e14003c1e01100c00d41044a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220084028 1250 220082778 220082789
    0x30a060b031504051902190305030a02060105101706060d110a0801050306040c12030c020901170105010902090a0b07150c0e031b030613151404140d0905090a090606 72
    0x1a00d92503945182000c00c0b207003500300303150b00c0c0010b60b07820541c84665581c42c40c000c904462010340d410744821500c408002d68000040e5046a000458403882c1154a07900010010001403050200000352441e0120104d016407030180c58606440d80c003402c1e00040107130010b00300c9810590402c91124042c901c0c0c8654103661101103c020f4554007980ca0082080006034041032007580000240310214452280c840100c0780050380c00101e61180d45420b80c0e1101d10520080d60044c0320000010741401140490039003603110305c00030032042c0e89948503542280500c210503900612003190500c40c8140710001000b91500580c0f0800901c403010100d001612a140e8048002400100c1c5186090a00300011100c00604081100c5403c61500c04240c2e1a800103083d000f002850b003d41c0020b0003000061004944090f040c1032148a02c41c00700030502580548003112544564041d10141050224451012584a07070319529505d192104000305d900380909103d828a0340c0f008036a0001d6200d1280e00e00600303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220085278 1250 220084028 220084031
    0xb0a0c0302040b03130317061c0f020d0b070e0d05030307080601020a0615141c08090f060316020d0207140f0f0306090d0311070804051002031b0601181118030c030a06 73
    0x5c4517480c0c020050f0150068074160138000c2001d108965640307407411001313a00700b01c034103203a03900407070a0450200440c080080d411180130b0b02e50109010010103a6842044a501d41c45a540340c0c080901c5140a1005000340c425002440800c100358411030105401140500c103ea9044410307031100d0b001c80311405441841d285015004000c441e400020840e0b007003608960300e0000c0f04298000701515800080010612800020b8560080da00c210030419003006c05071440fa00e070300e000b10b4010402c0790312104444c0944600405072005500c0010031390305881c00d520300f80c0401c1c020301c0c0602ca240d000340500d035903204000c5404c817440c40d241003105070b200b850480024140040f004001800325112000e4103498010308001c3e00c0041600391007160b04131042074988106030200260202d0550050182003a1003e08016402040c2c05e000035447d4165104000100c4002d00c111000300c0488003c910f001c200480c1c280881d00d008440319400420100c005400d0b2403142010100282c145030b1618030403900c89 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220086528 1250 220085278 220085311
    0x17030406050105060702031510270e010219031e23060130110301081b06480102041e05030304031401020c0a0b0402031006030b0a0c0302040b03 63
    0x6001d009035801450b060740d0061a054541e00400e407240e00118141074194070100101c3d0b042290102c00c0380c01440c0c0d10390803108215028034039400059101003070510860401041000d000300c18400c880014210707041c0190101c9140f14150050310070755030b001e00643c50300c001550202a1174050715101c03502006020040d03031102e848540c1c4101001c3c21280c1009030500840055200d1008000114003440c1440c56400c0341444081000d030042d13001c0810400c00c040000218203100049000414006000e2403540308081070900010f40103c120702184440120342948050b00408120607443e440d144045510000011508107108024052800c180c3e47c00501000034000301030781407020b007000841042499140c0310020f0b540380501d02016000c491f01c00140901464258104d840d110100c4041c0d0304581520b00b050060709101711401c0c6c5c000d0113146006209050a44a0b8500707a9500c50302540c4c9039210010301e03c00500c140c84d80107040c55420400486c00c0d80b490009944155032a5409e81400b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220087778 1250 220086528 220086533
    0x190207141504051e0304030215031902090a0501140d09200312040b030601051603020604020108150306070e0f181006110304090c030f1a03060907050f09070309170304 73
    0x204500350740c9001d00415a10140320000e1008184d440028083c0084540181c1114808600350712640d84000c4d0312107080003c04000f201003070082c501c2034040c00184150700b81014402c0b0140c2c49039404070740d805079001c0384c00d200640c09950b08c40380100101651504003070496002d2400c6500e204410303640700c0321740366815901c1c281258041c0014002600541450041d00400c50030500460054020944011001403d01c4e48140c0584084c0c2e162081c900110b11500c1c140a51141c8080d513017640041c5047c0005040c100503107036800c10311100900245090350b02c0a008640c00500301c0200740c0d000d0b481e072507031340100c0d551207103444212080d1000003d050304114040070f0300c030041c41c1d20200500030000500d1440c81004015542140d030003403400f0a0b01144640103d00400200e0b010142207881c0c029018060103c1144590303030184103808030380084d02c0300c44145a03070fa20103121b60340d030141403503244441038245800e2003500415035090124121460740c1d9a078402c84500717200c9580002010003000306 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220089028 1250 220087778 220087783
    0xc07030b07021207020f12070303090801060f120b150a090b09060306040506130201180e040309061805060705100216060c0e1003050411040c0201061a160b19020714 72
    0x8100c59140000c1c0b030b0f20340c6240c458000780d024400000c0c1c401c01c0a00009a1540c031414011084001494107865407980c8a141c0540301c0718240c0266181c562a007103011401034110503005003540c045264603002120340390317103103641c502d0000c0c40d10f1006034030414010044d844510814028240c030010100e4690282d43c240914510010020f500c070760b10900a0101145021401982010b12140500010308060006982e10f800440314030513540c41c101400a50003441005141c0103070704ca03a0b1451040c076550602116400c021162000c41c00010180400c00d600c3c03e800208000c0b0302c1007098402c2100c0c038409907030498011103021080c01080e000c2080400032184075120181c049400c0095102540e507010558400c1c0040c0c0c02001c0c15a108007050074042c0192070700251510041091000412a9070001d000e00500d20440e4407202d15281c01d2070011085400303030b90000c000d600c00d13079040103140e841d041c030403800143c083c140000b001c00f000340524601d40003c0048070700071074810f240911849011032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220090278 1250 220089028 220089031
    0x50f031504110d1a09040311010e060103030e0f01020f120714010222150801061407060504081b0303132d0803010e091c030c030b0303040f1403060705090108040f06020c07030b 77
    0xe404c14414103888944e6595250b20a41160b0035107001d0150402d0903015600500061020001506c51180004105540548040c20300d00c0b080c0c03031210040000d04016603444121003007002c4150800741211100049902c050f181080c09110b075203880d140b14500c61400c981c0701039011201440c281071a0440d0049101c4540b0080c0040f452032056541c4c8450001d0450006000316402c0000301842d80400c00b01000556021981020003000141814645100564407440c4e203400c0340e05448041c800040c10202c2076030f210300707150032010f101080300c0c2c0c1d2000e1402061031b0501c4410034201141c150000300d413408a803501c51145410305d07070b2035050040b051310301c0b2401000450f4951209003841e21035507410144811014407418003149040c4800425000b5110020070307190140f00c04a800a080041c50650740c00302c4070440041c49880302500f0500d078a0340c4048039043d000c5002040b4500d010351281e0302d810b41c042e019034021505100256661420f81c0d00500f9510754592140c0c03010b0060001120905 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220091528 1250 220090278 220090301
    0x151d1e040f0501140d030804020d06020f0a0903021507030c0b100806090303010302011805010f030e0c0411030402040f090b07140f0a1106070306180f0e0105040c0312050703050f031504110d 83
    0x200324845c5165001002100d00400007402640e0801601d010015a901074420f500140e0381d19030b8031001d40304802440400d8510041c2d00c50402512000d87c0c0c0340c0c0e030f03104031070000e81c143d03496405c0c0500e581c030340c0515000054445d00c0400e20400c0000382c40c070b01c180301d898084e00203000519642d514500006101c051210702580c18640500d1040211b0707070b00110900c0d000001410041001d007148408241440010440c09420a041880c900b25019500004603c120710889003040410011001041101d55881c4000c000d80c1c403074030108580710f000c1d8121815044007410024901303044041074007442c0c2c104a801d4000704910411990340344a090090320303403103c80c43c03904214492070501c00e0940001880242c015090355070402d2030300e64000e03801019111141b14001c0c800b134205440c0416588036540310690728901c1d4100800350321031148048840b002d41560f01e103420045940811849039002510ac11005480b144040f03055440d9409100021580000b0460320392504035009419512048100d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220092778 1250 220091528 220091539
    0x100e1b03032110030203010507021e0102040806270a03050403060c020c060d11070b04300c080d09051005090c01030501120813170601151d1e040f050114 67
    0x1c5950428010741d01ca14601c0c0b224a03490119251050f25404000081e000070703400d035080108105600340c0008440032900c110f1007400341d115544d01102c5080703005038000c0d07500e1600a00042a85001c1da100c1410000900601d0301c0c01070150403c01524180c1d1318001140490000b00d82002808642d1113035618020150002c1c180040c10000040d1252065564041000780d9512284c5402c0302c5984c00c1d100d289034060350030780c1c950405040800004400d540c0201884c81548018400548005c0800001d00740c2602d0b4007501d64401c0da180c40b2107802c41d0a121880356a85e01120340419010845d115206034000400602c80c10466076140c14440e00600560605040c00d00412556110a124000481c4c009400d0307030322480c000b41c00c4d49d8022034a0b4000181c000c450390748003140080118000d8104d41c03a4410b030541e5240003070b40503180308280c5103101c0f9240c12200581c8030301342801d0644125841301400f0710030240c42c2100011f0111404841c1c0c100c0300f03643d03803030040c0100100e1a298501c8076208550703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220094028 1250 220092778 220092787
    0x6090c03040506040b0c1c0b0a080f030a1209060f0b040c020d050405042c01060603060e010e0a0905100216050c03060103080304030e030304050a031a010f0b070311100e1b0303 77
    0x21903e50b62840544020083d2a00f6000200c10540c0c80003900c1034811f480c4807a0340c540344407500c4007014040240c5000d1084c01c0d484400104240c000458a600d100840003031401c02007401c03001c1d0340b4901c14141240a5a85946c5071b280000d0f101d202e5440c04050600e4006000c520381e03400e000440f40c4002c03190041d507002c0d011035807240390883c06440880e041120082040010030b2204201c450b10f200800203002c00d0070410194070300c010341080055900a40d010002140c0c0c4c2d40c10280003402c28400d0403001c03010341e800b054054100e50050b140150140d4100c0b9550004600620200c0e8403403150500209035200300304040040c00d022803d8010800c500501e041d50554403030980c2c40c400034000805200401940e0030040d20b040c000d403402080000c0960b03541c5507032070400c111f02c003901c3e6054a81200c094000814502080c1440c04295a518560349080c51841e075415508508038014840641c440d004840d42864624002c0e02c0701a9802d901812500f62050440310b4520101075071984290018070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220095278 1250 220094028 220094033
    0x2040b0a1d01020a06090203160308041a031302010c020f061b0c0d0506072a140d0309080a0e03030906041d0a0b01080a0c050d05090c0f0d0804050103151203030506090c0304 76
    0x40c01c0c4860355080000006d001c02c051000a18040021004c85140380040c04000203228803007011303004032660210801c040c1d4445002c41d4071f81d88821a1038001d20219000b015000d54802d0016590040c17018010000709841000050780301d0700718002c3c8054402481c94040050b010a02101030b802206580c14604003640350390300e5441b001c008149108005540402c000c0d09402d4400300b21403c43c0d0010300b05150b03041800c104841120a00c148000c0c0e00c19041d6284169100348101d2549035040200c40c2e00704840414200c820003200110540d2520042c400c0300f0003692220010001403d075180c80070802690440720046003c0000e081d11012460036600320f8559801149a80d40660402d50001c4c1001101c007042c0c1e9a80a00c1d8007900c0b02500d03000c1008400e4400280120044030304032140c47e1a880300008003c00b6410a040041c03941c2001c0c8810402d03035009411000100b000b04006001c860340300d0000c01c090005841003034001a8440080c040e4a0078014a00750304100481e200c507185207403a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220096528 1250 220095278 220095283
    0x6010507300c020a05010302070f060c021506030c0a090c051c0e07080613080d091407030201090b090604090c0903051507080c2a0118060e060109060617060f0402040b0a1d0102 77
    0xa2041d11b061580000c2c0d03d0081155004520040e036900510401c6442603980c6c0080d41d40f4881c8008102c81201007001c5409440c0c0003400d02d41c0e44000400c03200a9906040303240c005020310008a200340542408203000043d80c0300c10100320350007180000102c42502480d1103241c01e916503c06421600800c06200c40f01444d28a141c64054200f113213155030b2000c42000900401050358003400c0054203d110801200011842c101104e000740da41041c1e15896200038201c0d485070060301c1d64040d40401040060b4002c41e08490071403645410690a0241d8a403100c078140b9203103080c0d28011121450400508681110099800070460b404d064145040e2040385281028204030030f901010310f840c03085105001c00d40200804c48009074406101c11780905d03044001d4103041e507100d44a03015980c0080340c0040e5a22030f04044135000e548031400103100090f0045080006814582c000c90301000d40000354580d4001000105201c90006a030b036180b8000c001e2140c02c28516010b1901800030490071140ea00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220097778 1250 220096528 220096549
    0x231e030a060b0d080d14010927050c030f030a09060206010f0303080a06050406090c02150405191a0f0106030f090b19090b01030c03050607050306150306010507300c02 73
    0x82480001c40d1004a800100c1003d5601401089208001019801000160460410004c182c501e41a403641c0342d103a41020740e10303400305108041207062280f801d04215200c200a00c40d00580c10350b81d8012071030000c64100188407154001d1a0b20002c4c85642c4a9400f04091005040307a1000d060594103013115489015410320000d402c016880c0e0208a481800740d01a10050200502c10030941c2d541d46045800341c440343c2250805070080c0100c4143c5005800600703841558406d01803c050840d101541c5401c0f4410a01920390320010082901c0c1d1090703201d815070140e420f280d88200550314080e8000c080c1d0f0000070442c60014140103200c400110310b11034032600b1900740c5403814841600160b050b0024001c400340a09441c0e1010000024021802151801d80c4c0c003c07801e0711b0985da5400000d840c00e103c2554629002a42840f000d20182107400245030000700c1450120702d8107030345440c1c22031501c1d145260301c05140d0b40304a40d0941022030b0211100c09015500f403444625070244c001903806c40c0c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220099028 1250 220097778 220097783
    0x60b0d0c050d0e01061508060a030f08070818120c01080403080a15090209040b150f03180a0308070e031b0f04200901120b060307030b0307231e030a 65
    0xc45840420344140228191038101550791030400c40c06090b0600103010304054072482e41c561030782c480b5544640d40f00d44501c6100b0038029004c15440d6181d90394581044c4403422064031060303410701c441000106041d0040010359450102d1811094003003007040801007880d05000f103194072584a82d81c42c0d07600800981c0d44540c150070f18403403d9844519041c060010b4104c0a4804460442d010441812030341c094007172910b040d80c04210b00802c400a00234250500c00010007100401d0260307001c50700c40769000b15403001092800054035101e4003c041e1401ca045901140440d1117101000700c1c143d8060300342010f804045000301740991524035a054041e040740200c1380560341d05560600e0548940d001594a14000040e185a45500140e010425044450250700090300c245020351030703010601030501c9407200207100713078a1500c03981d00690040c048401656014001c01a0004409450181c00720745003100c402e28541a885560801c00e8880c40c1004445601146008140190f1070004191740d00c80d6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220100278 1250 220099028 220099031
    0xc070b07110a02043c0f0606091401092106050f06060a0315030f14010605010e13020d1d0d1202030f010b07080f0313020102010b09040816110405070503070909060b0d 73
    0x42c188185e880310444074511910300f110007031204c403030b00f51003c03001d514034a4088080218a4407000d114041c4d510520440300003420407a404d02c180070580c400c154034014141040d0ad0019903803c1000b841098010302c0803910480800b0f50b070240115070280350360046d13003640b5071803692600c1400070743c0c036000350600c040415607218101d102070801c4030007010146801510304825181d0758a00415240001c0e9450140c070350070710038006029409030588030916080148480310a50522041000a40168a450381695214100340c1d00400c42c16030404820b5103040050503c01c1e14041014021403c00c52140390342c5c0b481001000490340e040c00b03186040d80c00c200e81e900c0c1d552245061501d001e0251513544e800d489400014084154005070180d0072440c0f00ba0024081510f01108014820004607005405814100082c0500c09450b110b0f00d800b240c4107910081c03880880c0c41c04102190740c1143c840c00410b10010501000640103c5a2001000380a10600040341400f200303132080d0240d202003100c400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 220101528 1250 220100278 220100291
    0xb09161d01120f110c0609160302130209040920041406030d03050402010c14010c0f180501180f030b0402091006050403020603070e030f0a06150608012108030c070b07110a0204 77
    0x3222500300390b41c513642003c105525a19002c1441c0e840e0901070f03e000c1103610550003814403408481103241b0480e0b4000b441006000c20205080000e540800b081e958042e039200c002000080e64405004070b4461048062882451340c4403d00085500307180c0904030407203e020404c012a50001042c003078095607440c0c0032403513454620059400e0070b0005002441901d042910000c910015440140c0c000040c0d80c440032487d40d654825181c03e0b0301c2103180c0b1200c4520b0130092107994010744620b040e5601c800c02c20900d0556440140b06c400e142500201c4120110314284019072506001c5603070422102c00180b0500ca162000142440c030035403000a014040c084002941c0c24014940480300c00d0700501a2640d18206424440c0c035108030304e20869143d460401c8074400e0b440c0300e580c80800c2d1007031500c410149034240714101c42c44011441e100851441ca00c2460300000c3e00303480180d40121011154030380c49074058038100c0d00c54400104454108030b000442e03030710440d0000036040b02140d010f54001809 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 220102778 1250 220101528 220101551
    0x3021305060702011715040f0b030a020907050405030f0f16150e0402090d0b06040f0515060c0a082d070309090b03070312020c01080f0103030903020909010b09161d0112 74
    0x31000c13104900b050b490025801c0001c0c0321b82a40907241800c82c210360802c4601c141c201c400c001c5aa01b010429050f6000007983c0c070040c205540190b0300700b1024100181401d40e118000392410b002201c22000c40c0d040707000e814642074410091044000380480d1054100d9003000d41100308200c8914404041080b00301130340f03055487da9412642120b0000e80300010f00101803e103151000c209440c002d00851900880b0180c032861442898040c110000e8024079480300c1c942000390780d800c01035451740540104030a40d40000c00d403400610310140d105d0820f4000020950714500f1491901900c1154000c0810030100000da11032210420b07220b1a2000040508042000c28035112031508002c0045861100c0f6204c43d5030001021842100300b42c0e9240804d503140701102100100038440100071403c032030b00600041ca0010440c6900c00c0c592400011244400000109902400d5500c012001049005030701c0007a0304c80909048080403500c0e04090801110009207850007217001c10039103e595800484c3d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 220104028 1250 220102778 220102787
    0x203071703010803270301090309050f0a0311060a11031801090e040c17030910050d06170601060c050307050109030f090b0c0607050c0c1518100c08090a180501060201050105010302130506070201 85
    0x19181006d002040841c0342032401511001660007014811500d1082c1c0d03114074075042c45010240c0f07070710442e01d20700310550300180246038201183d91014001400e120703450f5203000300041d000750050900f905018400320000500810b4540d007005803202040c0c400c00000c40c01e0a9800801c0b00c11000081e2085034042c01000d0442c02000751203a40031030b00d000c1d80e800325075200d8082c203a0320110351820008079030385803c0d10b0a84030251041c6a9543c020000400c05140206c229007401e900480c140c82c50000140ea1725403c580f900748003200490507010b80b01c0601c81d170000841c005000200d40310791030015513024003590342d00d00610300c0040140009000060f601d00b4080e120010341d0140c20f940c81141c94228441480c0c00505040a0064546e0043e510b0380c68030440d1060f81a60980310040d107840251103136400c660205100c241c000e80703e0040052130b00c011b4121718260300d001d50800602541020300c024259041030744214105401030020003100a00300d021401142c5c4200c800e0341d40d650389407005a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 220105278 1250 220104028 220104097
    0xa0c0f021237020705010905010306120b0c040b040602031801111902030f0d031b180e06060f0712170c220b070f031b030905130603060c0203071703010803 68
    0x49480c0c1102c46000b54603500003c444c0180c0740240ca4101003a511000110100d85640c401c00f82e00d0601c18038018045102c0e11070003500901110032082c50141c0340c402d10a01c80e0b106500c0300c00148d10016a01d00180d61443d07000d440c5e4102407912001c1c1a4601030095500c100d172101d10440d41c401c4101d420119541080015456020401a00c4030b50360210b00140007410240401c0069201000540c10728500c00c43c00031705070100f00294603040e103007008250040368100500c00c5411100c10008001c5c5010007002a246442c8580c1c2e040c82c40042e010802002c0e000a003404d0f240c0400808148140030080005840403200f2046481c0d1145188c410110100d4209901000c54110f00042100a100d030032a69080250300946a5400401c0d040d0052424000c0f198800790018248407014480792070000c2d0f5440360304402000214cc4140c0b01c0d00d480f000c40f040d01c0c1d80400503a10000e800030401a60343c41c842004010482c20314255850003240c0c1340c8a2003140070080807458611000b01010341e5140350b44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 220106528 1250 220105278 220105357
    0x1002030c04140111070f1404020f04060f020102090a1401170c0d09060f05011409010b0301210807050709021809060d0201110a05030a0203040315020c1203070c0b0a0c0f0212 76
    0x4407400e542d0340c90720801b60600340c060b910b005070240e02001080d0400340200c0b000c4070003110b69a480e10b031418004450000343e120200007155020440741c14240c2d20058242e005d400d03c541d01d0307260842074100140075145041c1c003240d8070108101c1040350705402c44041e40c0c031514081d04041344120042c9000c1000b024a111070600c802d1038503001103001d6071b149100c404004425207894000c0e0343c860200400034082403180010b9034111b894010003110000b0342208400b48920102c42c204010382e070311a424051150030481c00c071980440c0d00c007070061001d00c0a0400900c1601c0c420031900341480818188900c02501a041c001417803540101c2c014100080502140c106060f40d844d045e000c00c00a481c1d61140c841a1a0f54065008100c0c2106042c802c503100c8510343e00007007003401412503000d0440d0700000c0c480b00506c4036240b80701c0702082c40f1500080c8a106400c50016070380440180282841e8070001480c411580400350382203903100b580b4100d416070b5100407603650b0310305058600a0303c80c41605014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 220107778 1250 220106528 220106533
    0x90b0604080106030804060f0c1e06021b060a0f061206050c130e0601080a050106020a0f23010e0106080703030c11131409010b0102030c0d03020d0209040c09081002030c04140111 78
    0x31701c080301c800f40c01942c84aa0307401d210042180c0d0200c48828041102418030314540004006030507041000e04040c52044a0242c14200c055403c040e00c0c20205001040980094040060740c50b070740d10400e40105c01112003001803d041140c49a0a0a0440401010300b90381d01d0104401c00076600a4542c200c107841003064129854400a4004000584190303000c00d02c103101081150200d0b0041c28160391440c2d006140c040c01031340310740c01c64892680f000d40c0c900c0b0700101c0340104804801c0d1025001800b000011500303c0000c100c107030840d00d6680c414552a04041c40910000380d1181c4140401384c0c006801c0ea200c0c51010000405003845102e030511203030700d0520080400b41107001254414510343c4000c01400711442d0041e030b107a100d0580e0420b4603412101850400034040c1d800351035800001c5c4001402d000705000030030102c0b403818a04802083c0d403101c00b0440d8080410002c10100f191800945c11400e00202d1080c081c0164083e581c82078a11078007201c80e07a44a08007840403900c2e060304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 220109028 1250 220107778 220107791
    0x1e0c1504030c061d030706170a14010803070510060609031712070915020f0607050d0b0909061f120803060103090f06020a0908060903120405120309011e0b0901090b06040801 76
    0xa012031015002d60130302d180e4021007081262a01090403c200c8201e0f40700c102c4902d48010380c814106000410002c1c0940d5640341d0032403010000310015010345a818000c550340c007160300f0800d140017000100c11514604100301071010503400866181144d5201e91100d2402c008240f05110324011340721803100705840e0000300f11056510075160011a0401034000c40c078003695040890b29201a504444250340c0808003140c1168442e07801007544c401e03071003000038a40007a0700000d007492800b910500d84030b1b8898402d00c80b00001591007806891141c0c01107442007460201603d2405d000c0742c4002c2c00741040072001a100f81d02a41008400c182d0011720005045001e00d0244000d41184206100141213000d0100e5200710010b40980645458001035007400c41c202c00e8807000703407030013001182c01e4090550075010094510700a54003c00c0c0780360020420f008520213000c01031201034620703010300703042200401190301c4003c500c0e4151050f80c0d20100d0204d5443c0041265489140d2011800350710700003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 220110278 1250 220109028 220109039
    0x32d0501081605151c050a1a0103183e090f04030e010c14030d06031104091a0915040510050601080f0a0f020f0706021e0403080406030e010912030b031e0c1504030c 72
    0x900407168230841d11308081061085e80011802c40b594030f541500400c05213508070300400e210301105c0c441540141c80c3c07207026403d002c20360010042c1c0e404001c3d2260041c002141031510740940103540c450000010039100e49820344005160502e1001024144002c0b0744034042480502d80c030200c3c501d61010704a80d585c460941506c0c00070b01d0b0a00c410781c0c001e0b914404a400b00d241c54003954400d680c103c422100c4080d42090707000e2140d40090001c0304680314401c4c001010326140322000f88554090742c0a0a9562024440c071010b03110700030b01c4581040300180c100b0810601402034a5001400c0800024400c8401c941308002403240060311b0020703d001089030010481d00c1d400405500522030500c00f150b03500c05024098902aa0100616182040c04180300d95482136200521140064002140202054660752000c01030701c00f0900004e5101c1c01c01d41c440d8101080024907207007101c1080d01107201401506512003000c107551500c02e015450a80c070840e000e0200780c50146070469071980b000c5a651 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 220111528 1250 220110278 220110281
    0xe0f01171e06161b111c080301150201020415031d1c0905040203010602031e040e0a0b09090a2111160f0906030b0106032d0501081605151c050a 63
    0x2c40d03244045580c1c40042070701184c440c203040100261000403242c00341001c1c0e81d40c044505842040b09401140c19601c58040082d030002c1c4d924028001c401f255170300d5040c50440d040c031000003003503030040d03a004001c10812042c000d00000800f001a00e030004d00145510031210010ba000c1d656141a403140007907400c1c054000c0d0042d6108112070380c80700700c20140c0d00e0040c881079000c00d20811016030400c0c4543d00c03039a01d0340d0000c00072105040318080c1c0381680328060f1902450b01911f91514065460416072031609012001c15008a4214001c01708002c0310f554110444090003001d00c0d0a00018184420450007800d00142c5000c1c60404d40c0c549450030010110082014490018000100440080d41c00c249116841c19030740c00c1a01c070f100316070804c10306902030032001c00030b800c1d02c5001c201c0c0c00c6406003614201400f00d1104540104243d4984280380e49446107100c00840c0c84480720404100590344c100882291000d0390100d07545030a281c002454080910a4010464600782030401184142d60b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 220112778 1250 220111528 220111531
    0x3111c0305090c09010803090103020f0c100b15030f04020f030a14100b06040f06031815060303020705041e090f05030a1809110901030b030708010c02160e0f01171e06 73
    0x69508407440d0711405404c00820a0080c03180200303d4000300159111540301790002c21b4002c100b202d500c0d29050090305200d151005180082c95182d42d80c00b01c4107214601644840c00cac03a090517401c107080d4242500e40700307892701d40540000d200c5e4148800c0c5524a84080c01824040340d0060ba400046400d1500c0c0183c84040d031800e0803911920301403074001c4070703d0042c0c1943c00b40c2d209442c0200c1d40c603007404000e400070208504c00c0f00d03003140e502480c000003a080b200320182120304840c0202d0340d030340b86240c0a880c01e4174540181c0d2141d4141040784014040d00341200c1d108141a880102d10f1480604040041d80781300303d0041c019000002d810003015400c003074060419410140c8009100350384040b41d5003141d05400b8000c0b42840100f021000943c880d40000c1e01552004054400e901c4d03860603151b007120044102c04000d07801c04a0083e0318404141d0440e8010207441035000c0c41c61800c0c0100703440c0f22505008402c003010038803040c3c51844404000c00303440d02d42008040340c0c0d043c0d10003000540c1c440c030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 220114028 1250 220112778 220112791
    0x806040c02010e0d050909060303040b0f0d0b0604030f0c08010605010c0609020f1f0f02010510030638030708010603020303040501050d060e0a0902041a100507080d061710020301030b010303111c0305 87
    0x7c09004508942000801c460403075031004210303418000c1d6010ba000301c84d44461003851600d9150100d09100c1d94842c1c000344011071082d002600c541c0ea4a2034805480d40182d80b0814481e49800002c1202e80d0b000b540c149441644082c001136024110310008a2208115102c1600a640c1a1400c40d420590081000a0180c41d8640c0c4941c0202c03844102d0030307154100d52005540c096013030200001134164000b804600346c0002d00d4042040382d9011001d0080055858540303403505035820700258181403203240064540c1400900440741140c010903641c1c0b149118150400c94001603840c000245940b103000030300b004850040b5a400c1014060340902101803080c0e108500d0f2441030785500c3c41106107501c00e41c00240c402040301c003103c1d0b4160390b130b074202d42c0f02a0744143c420000c1d600e0800c0301e4400c40c005030540f0306d0030100702d000003000c82d858170910074100d8a4031441080140b01241c281d0742998110782d8503290665a10089603402402d1140313000c080110b1019811071041c1d0030303406030411842190b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 220115278 1250 220114028 220114039
    0x1020c060a1508120f0a12050901020904061d0c09010908070605030a06090203040b06100309050f06040311030703051207030902031006060e1014220e04150b010806040c02010e0d0509 80
    0xd03203800c040d40d02c075110400c4d035100307410081022444041c0c1407030143c483e000050422045c41d00d01e041c00142031703410840d00030314242d5001600d1840781c500b901c01c9401410314403540b614202425110b40000702006040402014004254003105030300c10300f0707800c01600f1940186c90f403541d0303100f0000d042900309640250880d4101040451403481510a4030700c5907410640c00c0500e03840b00341c14000d44c0e01120a80b4001c00d07845441e0480482c1d030810030f02d0301000c445001444c00740703403d040003030008003121195051504208071400100303522805550380b890809400c6012915454401d8000f4580003038025014081d4500b442c0c20f880440e840a0200c925941361198000a00300410030040d070300c096080003107030720b014861100c0c0345907101030010301011075003c44c00e042d03e40c1c88000588420b0b030701c40d511540106007080100010348a10500c020000c2105000800104d00080c04c8081c0062000f400b079591a002024082e100750444c000c011240c4056681041c02d5080c0103080d503010115140c01117 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 220116528 1250 220115278 220115321
    0xa020607141c0e0904030302211005011103031503100e030a020c1009030807150905030403031b0b0c0904060b0a0203091801080303060d080705011103090d030e1e01020c060a 76
    0x40b8806440415100140e583c1c0c254403020700c104003c40410060302c190101079083c0425007006010003000100442d1800781760f202880d129605c0d8506201c907401403810410107481c140e4481302c0000c190b9800c280c03a030080681143d20702c000300b864222038a0800311354904180810461080c080300404100c941d503404d44203445102d406004091022543d6480007881d1810100b000ca00503401a10001c0e00c00e04098140c0c3c3d20003941401034660420003034035036800c0000c08000301600304040183e601500344c0ca4448018154503508100500100b54032a410070000c0d20318910f44d10b540c804c101400710000265215114a10000d540c3d8100d07900c6e00b40030780284210125243c0700a5100b03812a048000214030b180d840e8018482c903220581800c0740c1c0c641c020311540700083d80030301940340075502c84880c0380e481c1e00e000c60800d41b41c800002c0060040c18545146501c013200040307010074204010000f2039414030b0050044500a110740c241c030000c1800f9060901c48102e41c0c43d000b000c5580300301400740250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 220117778 1250 220116528 220116553
    0x1c0f08030c07050c0102060106050a030e030d0c020c0112140601050304030216090b030708032802120c06040b160c060213050d080901030c020d09030f030e100909050c04061706030a02060714 83
    0x1121f07401c0c0200408910144590b030b00a41c440c0d00701ca20b0041c0d0010559007486965540c03801039411203010a0050f801c091510301c1e055034044410b5820181d072010070f004030a00e01c00f2070001400041d0105040041c0000003c0506008102c0201c45540d041e004942041d0344168810040c401155074511078004c84034002170000e400400d46a101c2c0b8414501c20148003140890000100c451a0314004e60103080980244000d401000e0030200345100f0180c40d10f80b906180c0001000001012b8880400c3d0b2000000308a640c804103002030075a001ca00140d680c0041000d11758440207540c441e43d4089501c8610700c0400680074050a03c440e0283c805122000c4c0186040ea00e40007001c00702800110000700406c003250790030082c07007142c3c1d00074208003090085a001140c03480b00720382441c4000c600815420000484648140340e0b02640c25003400d0f08180c18018001c2c500541411442504001c00c0c2c04141a41c1d000d01107845240c3e4010005551881580f40c019071032140768080103035034011802103204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 220119028 1250 220117778 220117783
    0x103020a120809040902030c060a0e04110f160201110d030b0310050103330f050709060f05040605031e010e0f0a0902181008011104050a080a021c0f08030c07050c0102 73
    0x81d680c0d2000500b8204803503c2d062000503c0000c0060381e161160320383d5850141c0703c10004112030380341c80c0d4071659100440d80600060b290071142004a0220130042d80042c0b8882c2d100383d409440302088101391150300d0307000407110030001060b0000e84e0b01036241c0c08101d04d5050b50050b49806001d6040d6401da075540346200d001c0382c00921000d80003580b24862200c3e5065140c503002c0c21081c09840b800c1c0031403200300701d000440b944140280d080cad41d40c0b0018840b0310760f04100c88c48014092890154003d80303190708010828019403007a1800d03c440800400c4100ca0716081604050045040d40101581e4490962050080540c0d04602082500000c074240010310300422000c42e8002d040c0b008250003850342200c0d4503034000d14610320007024500200d034040003802040b107100e6521300469201c509200c02c011904405074820395042d07002c41c0340315005843d003694144031a03406180000e43e60095040807103080384465801001d80800200b003000340d1041c200642002d0b4004c0044948d01c0807400010b99 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 220120278 1250 220119028 220119059
    0x80a090b040b071e110108090109080301060c0317100b0c0c0d05030a1407120809030d0603120f020c0a0b0c0a0c0306051504020c0604020603130803040614131203090f020d06050103020a 81
    0x40c90800c0f14282a07145d54040c46a01382c1100b05c050000400d84540d88400308680c00a8001d034000800320000e88040c940d10800e0100f242d03030b40961400031030416009050700150030703200301c0200280101c0c1c1c0c44002001803003640100da401510b02e8268601528056071a640090a1200422000c00c0182c000480940954ac65164000422694040001410303145c0c03e10040425446100400480b828008140106030043d031266501aa6050311248064440c804a0700766500b1948000c1403c800b070340e620401c0e8800c44502c0040b859a840340c7e89030b86403d14030a200c5c06000c080c19a04000200314155100a06c51060401d8043d0911103034401c01040e480381442c501440c5d4803803004a000742c0381c4240195003248501240441c039103015510b9501540085809440080e940c8661800710490900303025480001c86140c086d0b61a0320f591100d1113606088404003c01d40e485045104102c103850780d080c0100d8005003486c54410710342c41e10802410090000702d000b4002100000f0308201d40400c0f01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 220121528 1250 220120278 220120283
    0xb01150809070f05130902060a030905010c0513030f140f070312031811060d0e0a050114010f060c050316050f0d0503060105090609040b04020a0801090c09060c080a090b040b071e 78
    0x100740d1545404c04202500400003000c0c11415540c1c150000181d031000c0045c0000420354034017007102900750500c0e6085440c0081000b003408030800c1011903600c185034429041c0c81e4000c1c1c035000c1520303042c14604040c000c1e00012000340d2140c0404451040000940102180e05c03800d415400c0000c2c5075801ca090380d1000e107110380d4101503044080700040402c100c0042ca0305029000d18100b020510701a41607400d2210340690b290041c17000901401420b001d03200300401071444c5030850394500010030030329210901c1104100000342c4140010000c0034001c80d039480c0c4c480100c0c0c0c1c00580700343c1442c988030100c00d642a070785880740e03110740b05101e809030050f2486450141c64032420000150188109031340190075959025665884101c640ea40304d2018000c00c3d03100d1342d81c0d101d41750704016503070302100c403500c0c260070070701411140800409920041d081c6113250701081c41e0ba01c0d4803c0c2e91013980c1d141c415400050103101c0100f004220b42803000050594140a200e1503100400078490b5001d0308044132401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 220122778 1250 220121528 220121549
    0x1e010501020a0b070c0311031606140606120c27010f090b040b0d090b070503041a0c07060f1407020d09060c051036030f03020a0e010e06070b0115080907 67
    0x1c0000d0300880c5c0c034059040c007a0804400541c80c4042c040d04541c0400240b403e0420150445010f02100d4842e10807000800881c074025400c0c07846c0051441e0092607811a0340e0790040d00024403040070351040d601b003445c0d0320360715104841d00e1220f00c5100f04004c3e82c000f40000c4882c503c0340c6140d0b1040c1441002c40744c08203480c07454207040c416182015448110a07000c041d803122179500001354130f803031014403540c002d40c3c0c2c094680c20300e03150140b450790030070400c42a600c04807070612402d10008000c0b51030a913449180021398102c0320107c2c90140241c40311a4103d041e14804104c520b940106150340205000d541340c0740c0250712480c00b541c1150001d10054030715400780c02403200955581e400150000c41135808000b010708512640000e01080c41d07104ca0401222400748010560805c00722134441c2e42c5810254100114000001c00602040c02002c0c1001141c06440700b003600c1e0001100c045580020380003c40703685503c1291918040c0c0b018860000e0301880c009184500701107108029503240c1c451 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 220124028 1250 220122778 220122781
    0xf1505060f0913290906011e03030f080a0e0604112713060209061306020c0103140f0711191209030c0b0c03040504060806070909110f0c03121e010501020a0b 69
    0xf2001c003d0000f4080c4982902e890001030058002c82d013002c9485203200c10f0007031541c1d604006040a88401103a001c0043c0d40c2c4040d000d100098000e241041c0c402c200c5d24002c6055a201d91010010f000c2196200c1141d004032814402848a15281411070220903103042c00b40d800000710308040200350110300414180007901207003903101b540e200b041405014080150500026000280007680801014a89000451010020340c0e40502c42140c0d01542420100116803041c1c800c0a400d14000b41404030b01590707000064405401486c4404071100c5801c111102400e00c03220200c1c0c00010010240c0f480e070300e90303103002e4001440342c0c2488064982c080351a0001d01d2410780500c00c0c3e508194411402e5000c10722011070251903501c119401880120014542c6090400c800b6185071a5a0480c3e60340d90f00341070780c44400000542c2200c0d4240d5488104940d03c0e94005855415406900d401410b05403d0f4410702c500740f80349180c0750b51000b142c650f01c110075903624401a60f03120781142009212a28175030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 220125278 1250 220124028 220124033
    0x1002031b031c020d1401080616020114070c020a0902040f031725030c0215190806030705010f03020d0612050f0f21070b04060f06080f06010306090f1505060f0913 71
    0x402502c800d40c04c180300800c40640c160340c2182010400d8000e41d503240e200508200311074015084885c81c0310030341e000030020700d0744803400e00381d0701d48000381030009000c40040600119143c0003000c1c0700800305640d0441d156078494a0f41c1410100e24481501c06c9202180410144182e1804840c89140503c500040b1f1002080c41840782440401081d81405141d0030100003585450011622850b440090030760303122502400d400c1704d00700d0a0701d40c208100b4400100075050b1000a0403409903182400c060b801a0b1841e90218003901c11400c01441085c1030150000d01501e001200219643c41042610b080c0f00307814044660b913002405400b4031315446180b80c401c6164894046a01c9604440751991500780315840e6045010b900743c4003202c50550340d94620419405900c1a0005440050058280c0c0801c461102c0c1d0340d204103002c05804a9510030a4000300004c0380800140c948d400601c9242c5140207046440042100300c4100e07000303a82d140600d030103510300100100c0c4242c001506090303005c12281c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 220126528 1250 220125278 220125281
    0x1020c0618030f033402070501110102250209070518100302090325060203070804140a050d1101021b0607121b0b01180203040b0a0c020703021002031b031c 68
    0xc1c054029540410804003040c0395100c3c00940c8503854503410488040843c2c11402055010540b102046a10b41c21216003920b80c04100c0008540c800d10785595141410482c090081c461144031440b40d0040d0151080044407c1d88400d444038001c80c0e501c81d4607540c2800940315071055000f4406c064000a03485402441c00030440b0001600e02e1800500b441100c4022078a03207005241030100c10007040d0151800c1000b45d800341005000c05101560900401313503542d4803d80540d026002102025442071300c00398583e03801d40002004014910707100d0300d001e42800b080110102642034010700a06600804a40f14405040740030325000c0c0900d440c080e6a81ca030940701e480b80d405c004c0200070a07512000e2420074445501c03150603000f6240004994035001c0f12141c80d4110b000e1030f2100758018000c00c404500c842e02d5003a48100290317804074181280242c200d0070300d03109030402584024440b601e5024503500001a1220010038150415200d5a18500640e0390103402d0071001d03011040c80d958500d00307006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 220127778 1250 220126528 220126561
    0x360606031f0b16060c090b0f0705010b0307030b220c090b010c0204020f090102010b100c0b070504030501110a081e27060109020c06160206010308160b0c09100201020c06 74
    0x102080e54040750b45540250b0b005901100645400c0240140c004003070080c0c81c403c150211500c1d0610301c201c42d1411000240c94000c443d640c8030003040c082942d0003481000c1d0807c0d40c2002d00181030701d01c542d4582c5010701d81007505035014907003081c0c2d6810842000c04410346107500c0359042070030f4405441c94080c2e100080d05c0b13164880d5042011a20800d00140c1b10750024210750180502010748860280000a0850b00003c40b40c81c49185448154036082da0401c90425046400c00000e00361a80c40d0300054826200e980e0001307055629110300c6407038403901c60016080841c00ca580f9080705d511110000880f8012429000255220140110701003003003004607000c1580150480d03c0821000144140c10321409903c403241054000849501d524030034009070394858124240f40071181d01c401c00c02580c98005010003084450300240c0180c80001500601141a40c000c80030303000b625014a0260442d0400d0541c28090702c801601a08240c2c0180281c601c4d04580c140103064550380e550090f105040c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 220129028 1250 220127778 220127821
    0x6040504031e110d05031e060105071a0a0b010203090310020901031d06070305070908030904050402060c0109030f110318100309020604090b0a051c06050601090536060603 75
    0x20314482040c002200c00c0c12089914240d0b85a03544103e0807100858185102404440c00300a81041080305403200c2d000b01c44850309203640940701942d07400c03005950610405501500c0e5605082c442c20510130406400380c85186070a5051000903421070059035680500b080040d80764206e01e8a415010032564054a9000300514010400ca00d0400441808121032100d05085c4e400034410040615094003400303411225a19250020340e01e4880d49030788a01521400724404e94a84012405640e1203d090f03032003000c2803074004c02200b0f07031a180160217081d500c0900703000314141c1003601c4d030008008800c0d203040c10070421141829032480c10411100000041d144800d140e40e034645600580c43e03170000340001c0d00381c1032400251030b81c88004105013100350b6030140384500882e11034110000000e0381c3c1d964030180d0141d804949a115080142c402c005260480b03600b0600b02d4011583c050714121607800744003019101e420901042c5000ca01041c1401c40310300740c10030307070801c0801e0001c950341c030702ca605055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 220130278 1250 220129028 220129037
    0xb0703050a150623090a06030c03020706020c030307021507020703110303040e040c1a04030f02090a1d0309010305150f010c0507030519060e070f05060702130204120c0611060604050403 81
    0x7034403507840d0319004210341043c030000e40310340b03003000d682c503a18002c10701c0340c0c6180c2480e43d00b0504a030b400a41c51a041e80502c6041580307400c0480003140c0250140c5d59015802082503481d9403114032fa45940b50405c0b01c4240041c0701b10700d46006c19000307901009004043c0d0b503024081a600f180c41d207900e1550740c0d0180c10f8040c481003000040440313841f080d05004900c0b442000c1c91035450030000c0980310070078038140748010600b00820400580c01d000d00b42130469066814070142d03624804c208004007600b00030301c200c5402d401c02d00d200d180c2010005102e03802090f01d040149848d540000c2c1c0200b0740e111a4180c100003c5880c0d0034403503000d00780c02c6982c40c4c03082c0101c89010351603640d005c1c1003041c42019442100c00280340a8100120b501641124618101c01013a805207011480c58480c0e445100ea80c2c042c0300c0c00903460003591550a400d41c00403500c3d900543d0f60341d07030b80c8051001400c2c15001c00c0d242c0500101e0046040b9125000b9000100124001460541c032854108070003802d000d8400c07030511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 220131528 1250 220130278 220130291
    0x30c030605060d09020a05031605010f1716020a1a010f060804080d0b03160602010b011e0f030e01020d0203040c1409070509040b060405030f0d090b0418020702010c020904080301081002070b0703050a 87
    0x948d400c2050700a0301c2448400d003591139280c000058407108041c0684800e0214140a1000c81d40900b800d655111070200090b20082145010503820010700440280c249442601c1e554804a81201d030181203581705024100d100c2c3d0f031450b0480e41030700181c400524518040005005005c503d40002000c40402030950702c03103142c0d100340d640b8160160f038001e80c00b40c0d444d501c00394032a40e002070004000c0400300342269104801c1d050003c040c49003e08009003455030300c0000510b400d01c01d506981042882000855072414182884a441d60036841100550380c40758110491364148240c1d028080c0c03a8a4035a01d0616168004000203403441c0700c00c45da002002030000203035030756080040d008080b010354042c00c010b0b61100d000a10211058002c400c0801c82000200310601c16a04440310443c4002001a00e5500510049851140a59011b075000841c40107210034840e20400860403100400116501761480c044060142c0c0103104025008448010004000b68005c0c0c1005510075000100003401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 220132778 1250 220131528 220131539
    0x6010c0f0b0c130305010608070e0601020d0f02032a0c1f0305070318080a1106010f06050702130e0d09090b06071506091a0102060a060f03080d0f020f0a030c030605060d09020a 77
    0xc3d8200e94000e07030380d0740c2d1280001c0003112070a0081c40701a06a0140607203a178a00900041c1d035039640d264010040041907807840c0b049510900030b448040c480880074182960b40451117000319118410441d2050161814400051a04525003906c0400641d03001c181c2440180040e0020113001b401ca0042c10b85400342010641c00c95441c03003901e030744500030700380e181e0703481d5400140079404c14002d003916940702d44014000c603040101104101c40d054903009075101d59510101e02c00402c0a1400504581031001001c2d44001c0400c021507080d205903202030b200740e5200d0149050b40c440303c9a05400c40810843d4a0100d02c0d203001a000500c85002f0214640340d1740c001c8801284d80354400d2101c40b0707860400031003045d0b034148603d6070071010302107061148604110040011140c03a2000402030100044d200c040c0414940000d00395020941086444060200071040c4581c001442da00c002407500c040403d016010b4803a102c203030342d009000c02d0304002100a00384018098990305a9006000020002c0c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 220134028 1250 220132778 220132807
    0x11e0e07052107080601140d090203012408060a09080a080703020c0604030302031e060319031107030803012d03020103110405060f1207111c0c080d0c0806010c0f0b0c 73
    0x800800b0610020b849180100c0002d00f407440141a950410005031441c2e41d26000c00010b50702d460350b003050001390b594280c3c800a401406002c01030101180300c203103840709800e9030303000c201c00310380741c090942c1c045039100c0d4030142c200c84040e040100740c0101805000c0101c1e11801c0c02c9940800e95090044c5804501c5180c1740c500305080318103e0009800004210310000d0740300b00290310700d5a42d001c40c60142850300020303403a0308070a84006046100e0125010038584526540384120500005071079101c0e40b00d040401d544e920902401743c4910a44075106422600300c01d074240086220242e5665243c01d6500440180074001051320005000b44004a8250b88500040044c035905000c0603984026a003600e00c0030f90401040901804100c0b007105402100c00718800da00c441c00c00b59130b0743e00d901c6500707820358403081d1880d40505503a50200f1610f20a00d1242d202a85440041d100e050301551035400440306158411401070290240907004000561f0b9080b42a0b00114016070141c1040f0741c0030139495 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 220135278 1250 220134028 220134067
    0x714040806190f020c03030f15090103030206010503060c0307020a110303040b040b07060606030b01051c020d02040305030702091005150d1103090a0314071131020909011e0e0705 78
    0x201c1c2c0c20620008400424410841c15a810820945c1848555010300d41c59000c003c05003491120b0000004a000410303031300b03182040c0c100600d801959616030070001d58820782401350a01074812203010407401c010305d0050743d101e0300341640102040002581d403100e11001650455030540700901000c152903647c130000d4000b0308200f04c92030b03031109903505041c03080e13580c20750102d018140340c13440441305660b01000b20b0700d2924100700204020044c2403002002442282403503400188041004020000c0200061585a008850420144e200e040c4014000101c41c89019804185515003290041000003d01000c1c3e800d0480001c1d11801411047c251f0f6008031401a002d030080020041096088040001c81c1c01020000034107008465480c4800b041001c04054444e03202c0407901003102542d1406545614000b0250082210800c140d050107074005120461040034490700225078108004a0313000d0200c202c0424004c510700d0310300844000e06c809000c0c10f0400004000f440710301016000d260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 220136528 1250 220135278 220135291
    0xd12170a092a1e1d01170d020705010c06020405030105040506100614090d060e0a0b01050f040b03060402012d02071802030402030c10030915060611150714040806 71
    0x86a408450b10305000d03545440320a56002455501110050403045002003007520340c050608800740b505107211140c403069540c010701040c03800d4a0810f101c3d40020364220f048803040c1da09010600248400d0b03070f84910307020280e100142e0217400200129031140c0c0140010f0703409268010714041c1c07100042030035507801721000e4a40707030f1200c0300303210100041100d40001070540b403030404044a4140302800640c411318031468030940c18081d080c800c2c03001030b5210782030004c01e0808480a04226244c4441ca848092241c244904280c40c240200d0381410b004004044100901030907c5594a90054407a10300c012544580310281d401507410f41c0244d1500355160002c96002010000c0c80c0200d6000f41c038604568480a260040c03040c000181ca000505e1403010f0401c507850401c92842c19011130041c401010003901d000c440d02d1003080300c1104d9900150940f880c0d80ea8151500c0c02603804240d5424a020344130800c040d100b800201101e100b4201200d03406120030440b4640b6590700070b0185012015100e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 220137778 1250 220136528 220136531
    0x2010509130612050c010804051506210607030c0c0b0609040501021306081f08062a040b130f180902060706090602090321070b06032d010f0b0d12170a 66
    0x50106002e0100841706400409203400f019618060351030a4645010601100c001000040030905550360b48682c1040302940c0203410f000307038000b1000640e60b0101a04d0007008030780303440c00021045201e000c44907801504103d100000751250b0b01407140303540000b0700075180c555080c008020000358004020700200b01d580e850b0541e0781030406904c50b2407400d102510301d02d800d40d50400c000190700031464551214401d01d040020216848948018420400203980d2041000030089109074034800030301100e8204268200d070b44e07038540310740b03040144440c00b60840d84904521142450507041d00000076082c805000141440d00303507030f50101a96405d040460b6040d4000c10300c015142010098003c0c070440c025807a95030b01da050054107003d482941c001901c00041140014001d40701007000b900303401400e4050000b52071040c510100440e071020115016942050003104c0d0448540c05646209a4014452080d502503030b520001500a50104102400b4601044107000e12120703507094810900d07041c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 220139028 1250 220137778 220137809
    0x3040804060e091302040e010609063201023a03060305060f06090a150f030f0c06020102090112090219090b0406060503040b0a0905031303030314061c020105091306 72
    0x8003620a542c18601d981c041c41080c0b0030080c03a800c01503514440c894042d640041c90081030303c4017901600103030b00140665420007000040745042540c40c02c1000d5520f070020703a4601e000b9610000200c48008030303a07005900170b00c000960180e000c04e44111000840e020304110100268a007100610f080344084042642c41108006000b01403108941c42420b0034141402c40c03500780d00140720240013030801c5585680d00c1c1d03103001807440382007030bc0c1e00a004500e11242c13130a40e8902e851404039004c800c08a40342042d00d100041d0140c014025a0f1711014140c5645c60300640114180e4020b02d8606800d036031001070b40d20111814202e11149601600003060017045400388001440700741c4005512007410084c0400410010072a0314816035002241081e001c030f204652810007600d1070090207200176420940072000010076415520492548508120a401d1a580d41d03007017018001080300d00c10000050361101c8001584114010103143c64010546a8800d003031034010300440b13035940c0001c15481107402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 220140278 1250 220139028 220139039
    0x10c120305011d0402010207060806030a0c0803090111150c0d0f0f09050106051020250801060506031311060408010911040605040207050a030e010323040308010902040b0a0804050307050303040804 86
    0x100d1000205070f80e6a0340f081c0b801d0a50000355144007a125440400100d840821800e50b0180711000c0d6481d000402c82401a031124400340d01c0fa8880200700d0302041c0048130b4481414400b0503068201e44581a00406c07603512240a560142c1c884902107003025500c0c4120a44802a0f01c90001d0845030030f80c002800300140c1c608142150901e801c411300c1403582098901142c0d5000d00001000e100400106a1840091a0a9142c407205120390000484201343e01d1100450016000c401c440c03401c002485040d56500500805210035501124241080c107000e40103c1e154100c0307000355000240000745007a40d108000c6003100e0031810125580200c0342d61145880c03034640144030150100310780c11407804032695a01c43c0d40d42c491103c0107040c803600b103140e03a2540c0c0c0282d00154100d103041c0101140c5d070017104030301103240c0c2c012202140494000c00010604c00818420f440c2564521099103150008440041c1c0707503000000c0040312284020403605001031b0040c80913602440c861215192200e0400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 220141528 1250 220140278 220140299
    0x618050c01080109020f0405010309112d1509010e0f03100204060e090c1b1906060e090109030801050f030a050d02060612010c0905090604090204060806060f01030204030c060e010c12030501 83
    0x41e800b405004d801403000c2d0a000b80410304480c11a00c09090011710440e8516020042001810880d64400c141a81001e0300d201d0000e6400c01d125110b001000720002d4200030051504003107884181c00150900c20362030194000c420604002000403c240e079081d1140000901d0441e82e580d20b101d05a1300824208a15608000b0082c01410103c440c10005c2c9068402002c16002d85980c000c840384180e0009010030781e0074014100416a088000c0709800b00d0b42c113005e40986010b10514000b080b92b440001c40311a0103200301108168165503003000d5910702810011420700081985034540218210f07003001407002c000e0700ca101c401e90380103000300e4039200c4200613040014110242259051003102c44a450f444088001078230000c8400380d030151141c0012a0040c104018000d401614013840803440082c0010210301c02e500450f4500141045e0300011802c5e406036102c01407500321484004e00c01a402203004038031039a410716101540d8420707138541c0707407801d03c42400c15008683e49000522150564 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 220142778 1250 220141528 220141531
    0x60f020106080a0f02150d02030403090f0905040b010315020d0203150f06041503022a011e0218040203040201020a0206160209010f080c090402060418150503070e0f040618050c0108 79
    0x40041c10848856803281100340c0d11340c0c403000b4824462a01c0d0701d0b642c0d00507002694096000d0110440d12032800f8600074280725020301803440068404040050010b60900465210f90381c4100c0d40c0351140d195030b0b24442400e10300c42002c40703050340a0180c10001402c03071001d14031910603030144c1d0804110707480030302042680c0080031500480c0100000d2040c01896042c681000e051460016507070700300150460400060306050030509032324032074800c3c0c1e40c082c150012144050703010b801903012910541c000d01240f04800000441030f801c0320380380003207142c65805903601c01d006005580100803940d000415503800001204070440100c5044c50035070805106103409880f010444079207031410324413110350340e003074014050f80b20b07010318400101151501d01c1590014030f520002c1c499403811408200c805407200c12400340100d80107100c000f401e0320300018072030212003022140082c551a991400c12691100906c00e845040d25185068101807109016151482c007900103080c01207280320004110000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 220143884 1106 220142778 220142789
    0x80303160311070b2e03030c02031618050c030c090f0a09020c01020c0c030106241103030c071a0601080c0702150c0304210302030409110c010501060f020106 69
    0x4c0704c04100d00410340d154144007010081955100e403944100c81c649266210001d0030404a4021030f0215505ca002030300360344100c030503034001c0180313601181d000c26641c450103010000b9207441e61040e19000300c0c1da02c0325a495030520b4404c82e8410302951000398452010180c04c20001e0340c0782d21600004080b151815900c0780c0303241c400c15000350081d800e0680d82d8000e10600092714a418807641c030989231405036042d41c2140621001a00c0d008555108051201c0c4044a103104002000a14071600c10f090040383d42c2c100c149440300341616108201b9181e42d42003028885260707001102c140d400b0078942e1750940c492910380001088070507040265040c444001071700181c0c5084c01300007082520140c0200342411260007880348a1907444000280050700240030510004035180c0212205000201c1c558ac140054040d040382142c00c20303444a030101d105040c203880550380a001c1d6200406 = true := by decide +kernel

theorem cover : BRFrame.Cov 219964028 220143884 := by
  have h0 := BRFrame.cov_init 219964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219964028 ≤ n) (h2 : n < 220143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
