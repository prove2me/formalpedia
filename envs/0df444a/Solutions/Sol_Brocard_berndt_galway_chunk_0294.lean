-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:01:55.66899+00:00
-- url     : https://prove2.me/submissions/34e24913-02f2-4508-9d5f-828784e5dc14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 52697845 ≤ n < 52877701 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 52699095 1250 52697845 52697863
    0xa020f0316090204080d0c1208060607021e032808180307060507060509011404080c120301090603140c090402060315131407080108120f0c07080313080c090c0304020103020d0e 77
    0x5080e50400035030343c28180c3c4c40c41f004580003000420780c50120300c1e81c140201945034016402904881c02d02d021035001c11403000221030303146103100500c85e00901e11300d0200a05c2404280e100140c82c06461a6842c807443c4500c0c1070b100401421002c6169000b0000c11107402000d0341c0001d080750501d5545680162040e4000382081c0c81c000e0501000820b00f050500420480c00307a5030706280300c5941c4585401c000c58002c41e5030305103140241032001d41503002d0240694042c000e5182c000402ea4610300e0074010401032488034440365080601440210340d282d001007a4056019640503659070b0712200414109440b003450954004c0741005002074540130740d070002030034a0a8100c8988103484810040c1e94001c0c0034070408110f036000107240c0f8403680448006d0025881d20400c1ca03420245124075013400c011640d0800c020035400480c1c0141c040c0c881d000303148018001c640c0680b41805080010600d0700070000d04002c000c04c000400318046911907030440708820603820080090390015900c40f600d50142d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 52700345 1250 52699095 52699109
    0x902070512030103080a08060402070209040b01081011120712020301120c05030c130b01090504060806040314030c0d1508061302030115240c14060703050106030606020a020f0316090204 81
    0xd210440c809020781c1c1c201d034180c940210b001420000006021a41100000c086030b40042d020b00c800001621001e1065004601c2612800720795030620401510302802c0000074421242803000201c0b071060300d6812141c030340e202030326114078950740e844050740d1108480d044840140d10000c000225540c00707054410030a0b208507480c240c4203a84d50101607443c00d5140415030722181c250310000304200c440e8041980035506061146c0540d941d04002421900590712003906900028200000c01d984a251a2011040500c0d0039045041c002c5481c01c4a0143c55030743c40c802075442c50081c42e80756041c3d1030703940141802c40c1125581e180000c040400046640303030880c007039802c150b500e8103000201b8a8000c1030f40c043d0850b0002008600840200f0014941c0b1140184011404c0300d00115092003514144103c08074018845030070711003c0201261816401102003614042081c0700003580403c4181c24545c0454283c075500648030000703402d103403404224130b010000e8014000b84c0041a038000c1c000f15a01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 52701595 1250 52700345 52700353
    0x10509010f03050606010309060b100903020333070c06020c010207020a092f09030708031c05010f03030804060f0c17011202010c12022103010e1e150301020904020409020705 76
    0x80c0d000d204402807881c1c00000c015070846800a00c895100303611403404c05000d83c001181314140903003c11440003041200900060700010b0602c1542402c01075102c0e040048640302c60b2003801d02da501d190048403d60300b034450340400c9011551a500c41d503110741819403c9402155100a0049564000e44c8400d900b24007840c07410354009080062803103201034003004406911410700300180c05660b46549288e110b901240140202d0070281c504112500251010070010356a400f60f04804031141c030b4060314480e81c02c80c02d00c001445805005d05001c0102d0f6403504140314540c60303a15222014180c41c005000c05240f030051410700060b4040c1240d201e006a11520720196621a500c80c0e0340480c00b00b001a000c1800305280c00300041340c1c00c1d8544030100082c030680d66070140e4411001c1e511078507948841000308000c0014000c05141c0318046e50040c0b00b8040c2c05030101d100c003010320848100140340700300340c81c1d0402d80025180c40c00e4048441c8114000d10455945403540082d0b0300941017140b06464500c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 52702845 1250 52701595 52701599
    0x415050f070f1707030c210203180703020f0103090203032101050112180834140c100f02150406050f0601050a09090207020f09040f05010b01020a0809090402011e0801050901 76
    0x2000d18451003c8180182c410f0f40d40303035100c0506038080e00102c06503c0130400850075201e0041040401c86992a403445c101603074a0606581c00240c0c007264454940558000c02d40410040c0d4072800f0384c4222a01c00e00700406c4001c4240002801e60240bc01103145441c6070502e02500000760081a42c160740003603d405410131007901c041c000701c4135500c410100d4507440d0501c3d0400705401c070000d8a50907054890b0060303034921840c6040400d000d8050b10082e58001c07040d2800c00c1042d110610003040709103000805100e56070304006050941d0000510040c4803040c20b00000462003801400400c244042500703400d0b00f0309207400c0c0d00034a001c49004001c2078206c0c012035010340c0b1900c01c2322220603990381d031403c40a04050313038800258080d0004036031150441300030325140e0315001983c1d4405c600a686180f4284881d050040c2914004035001e811500140020380028203901d0560301c0301e00d820341e030340040c1c0c1d600c81c401a10f18280d00011b80e0900820300003102d6241d80d010020720706907002690000d1944c1d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 52704095 1250 52702845 52702847
    0x702060916081902030109080408010510050609010c141e100c020708030304080c1e100b01050406050f0702060f070506070201150b030a0c0909020a1112041a030415050f070f 76
    0x21401030100c6070700300e40f0446502e10011108800418001000001c440c4d20030750350030100380c2c0254058407540e519081085200c4405450081c01400c1c1074035030038a4604d041c8002400b5142aa000801c0c80741032980c0820344030400c10161310054911440140782204650032907030b40c1c4080105203154141800c050607016440415027008a0300844021800c58546503195006908a2642d50019109840d6142d011103450110719106070f2a42015000c0c030384034180200e003a141d140d8011414000104000c001c1254030208461440030070b1080503403102001e1000946034882d0700c45101002e080810440309000c00170600c240641020780082180c1840b0405001400ba00e40c492000d41c00414000545142030542104070405a1031901c4500e8540740d051010803038010404000024200005068000c0001c00100301c2c0d241040c03a049007094504820001c0c0407034440003100c1401c00100214040044000e04141c406007540014411460015a040717240041200c0740f02c0010803140e25003540d0303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 52705345 1250 52704095 52704133
    0x190506130b0d0209150f090108070320030a0c0905030601120f08031503060a0912080a0e0d050a0e031c050a0513030f1505090601030b130f050601090501050a0f03021306030501020307020609 83
    0x858601c05011f410828601d0065401c00e000400c0340707040c140c580d21040c070080400620308405054201c80c3d141c50781000c80300744040340d824403441c0050190f031034824812503030001003981c11a021400300000851141ca00351a0700c0d11a4017005207105400b00502180700541480a400ca81054084401c0c6994600014040c3c0c1c030507220207040e44110944070100e40b07100d099180e5011900d05004034140050a201919115121411070005440416030210b10b0360700400000c442d0f0790440c01400c100f401c0315041d110f80803d10b440e0105111001503001900c600600545802c2d211043d140340c4015074a003005000054443e03400c4070407000c59141d5100da05c005d0f02c2000e000300302010041c940c03030f0b0035561b0301e001400d000707401116852110010342001071045802208030500c950301a0195515114101c802d03520103030070075031040204400a103d8044d1925420003202c1d01111820342c0c5084550028006204540020703202d03500010800600030b400140c0203000390148411038403c60030340300080c209 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 52706595 1250 52705345 52705357
    0x70c05011805120a0503040201050f16050a030e100e0d06060e09070312031e0506030f0f010209090c0403120e010c02130e060f16030b03030f03090703030e190506130b0d020915 77
    0x20170307000e0001c00c016520031800b9054506401d940c030b919000e980d0380564108120144102c032141d00c82d091b08401c2590180400c02c0d5080d040c1c0391065501a02d050207081c0502c0300c0e184600070300c044509038080c45602d420140c014170200d002c040c9a0304140d400715846900d00e0200740c07022042034084645c43d40c4070744900368055444120700c041039003441d84024040e00c000340000340e05114500500e24041c60a21483e640702140c48001a0303103900c603000f4032800540c010488100618103210400104565040c100d181002a281001d42900d0900040c3d52280b2000400b94101c1c81112210f00c811603d9400850b030500e0140840e0190f80d98031802c602c040c00121400d03442010342032045103119001c3d4110383e1507000000d003524140503a036040000740f500121900d11850380300300360820078150171050b08a140c010a89005182540e42005c141d8152014407445000344000540e0084100026042030050020540000d66554120050301d001c0d40091200602c5080501d000d51880708001044a81d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 52707845 1250 52706595 52706597
    0x5071401140901090b041e090605030a0b0a090506070c0b0a0606140c0312040809011101020a0503060f0f10020c01020d020708070e0c040b0a0903060c0302120f070c05011805120a 78
    0xc07040001081c061440d00420010381c180480340f2404940da00038034024001620b00301c080310300070078441418040300c0b283d185d00c00c07005145861810301ca07940700820074580f190b1300f00310074100a0300e464140d500103041003940540b10f8003404050200d2aa8000415480c56001e0301c80380102d80c03144103820040707480501c500030103ea1000444040e0551003006401d0a1402d1403d070b074100780079450b0310340c0c0031807003220101c1d00740710002303a501c62540e04030b4510340360741c11108001c40c201440f40710040c18920002d400c8070b105148400c64410719543e41024020340b0480602a4500c0f0f20841030040c0d034405d68942c0301c60150094000c0780c4801440054032008603174a55005265482c5031488040c070003074000c3c090700d5500784104404075290351580010010b0030503a9585600091960030044200d034204840c540416004012901088403401ea403a500844400024603540c0c4070400143e40d403500d50207000b1710750750030581801684c41440c0a0400c585006106540000200d10804003031341c0301c4c955030070b8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 52709095 1250 52707845 52707857
    0x80d080a0b03151803030a0906180f0b0402060c0d030905010507020a1a130c140306010e0f0f0711070905010e010f08030d0b010c021804030e0f0a030816020d03090305071401 76
    0x1072441d1220f0304009801c40900755050b00c45802a00c4007a0071a80200d0b403000c0d0075502d48004000300a003a2003005440354030030208030700a440550700d8403c4d40a0611000d000b406003200403c040d545e8650417580c1c4140c04c28100ca0a400c00188090003805d82c94000340d605529210010b15214004100350f46d0040d8013503055540700782c02254008400001500d80d034089078001d130320400090042c10b002006800384160300720452010008041c5440c005800000d0201001c200348403c08035540f41e541d404c0713540030400c014299525482102c010494107102d02881c4031310705000444140a9000505031500600c07803944903a2100c468005003074051040c401aa802000945c0440b0002c0d0f010f0742e070601c014500500c10300c1d0306030001040c00780001c1c200c40c143c48600f0180020180c010b00c10042d07490381038464160040c03401d00007850000640c030016180400020740c0e0705c8030300010240140541ea00600801c0030f400306003401400c0c01018081103d40d07200311003001c03c035442070f406126030034001650ae00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 52710345 1250 52709095 52709113
    0x2030c090105180d0302060a0501080111180102010908030a06090501120309061808010507030e011b0504150c020d0b0415020702030601270c03020903010b0a0b070f080f04080d080a0b03 81
    0x115070340c0d8000781110249083c0402c22408a03500c028088542601a40c010038950500d030003407004170344041e4003841d00d45c0e252620001901d4080303c2030703075009000007041c40481080c07000142c5c058848500020010400082000007481903a44202c1c182c400021080000d0380c0c80ea1031004050b500c0c0d82010700464524501001038600c514504050440d030201401c080f26926400a400d40704140c1c1c0900100351502900300d1099000d11442d6284241380880084a00a000340a881c51080303002c0c080c0102e102c080071b0320005000b0524610b40a501404580c1d11701e5460512228074007040e03a046a481000315003100040e0b407070b07000340d4031703642c0e0018060403440e4038080d1030302540010340780c01501c2d0704c0d80018884403013180c034882e02580456503240943d55803c1034040600b145c0810005500c070b040354030000c0c081c1a08610aa41800790700000d03041c0302c0e03080350500c0ca1076409054000c81c0440b1001402080001000c40c420810841c0354840e800151284070510b41500c3c44241504d8140c1e10600103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 52711595 1250 52710345 52710347
    0x102090a031b0b1602040b181504090503120708181b011115091c021b010509030303150112050903030403080402011101091a011403030d0f0f09030e030705030102030c0901 75
    0x10116560b41800305250240e9030b035001080c40358004601c0b04218034210450135040d03080900800d004e509045800508045852035884910100030302640300170300204414002d55200c03039001c0c000c7e00d07030407104032611034004030240c0920080c220b45100001301d0304804603019a62444825203810301c1e5001404a05184c2c08842141c0070404001d20704000803030400e541e0140c2d00f407110455124107202e0b9024145454030103145444012441448070386a0031603a0542950b010a10f09641c0a41484d4030054415020049549001d50300180e64103020000c00d01500c2000213000300141074007a200d03003002c40314043e0310504454045500ca90250070800004001920456006500c54030504106a12500808d2418211031032060115206000c48035041e98040420007101e00502603141000123612140f0003098480c007035000e60700c1b00325481c0e1100036110001130304001d200c940c2e1840304101183c00e42c20000c0c005004401c105000b070003800340c00b040504041c02124030508207510780c03601d007030440c2c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 52712845 1250 52711595 52711613
    0xa0f0608070207030b0a1407020c031b03070306110307020706020106060f050a031113090b030a030906121e0c11070608060d02030a050106030501021908010e01050105030403020309030d0f0e030102090a03 89
    0xc107003002c40c0600740000c800507100510003401032070b0b009400100303064003103034018101c0300260891084d0350003501e140380d8980d0300003502005a0218a00074000e0071400d40400e292800a402c010841030034003040d82c90004400025500c121100c2d03080301c3c0802d40e1540e00b41d0032541c25008101c0050145040210301c9400780c40200b00142551400003100c015485040113140c10074849440880c0d012042040000d81502441a10704800c030090701c0d2515495401030083c40980c805c00052000a082c8140c001100f98028050403407080c4002c0e150250a0f0184401082d0500312200824181201000301800003e83c82094078029103d50380c41e0b071240c20400030380e4021114101e80c5485800c00c0768001071020302462000b1803040c000503880b44c00310902d81105402c0c018030b0070100001500100408181c4a40341030440c0d4003800c000755241ca8a080403425403107006651a0548944200e03c0c01d1182d00010034400380d103565940400001264040500746e100d18051185d0007814400e0503c04a100c1d10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 52714095 1250 52712845 52712851
    0x70605060d050f0102090f01181203021504031e03021e0306030a080409090309080615061308010c18060e01050304170c10050a0501050406080d0c06060f0305030c0c0a0f0608 76
    0x10702201c1049219601c6516140d180c1500200c0359401040948a9080007400c9103905a82420f0041200e101000d980c13182c0142071164940d000980c0380340740c0c20f1500174000c802e40540b0484528482d890a820084c001c035160560764061000c030b981d00194114400e02c20354080c00c202c0e2102e07100000c80901d108919030030182245501d809081c0174000003c80050080c03000f8910700f100410b4001d131604014000034402d038460040340c0c20800421852a031000c40003036000c2000c4440e1900c0c1c1ea00004c0b10140450250002000c56291413806c50034981c0144145140c00361980800c000b203619a842240d1101004200c0d034089001440480c0025034040001100c41c108040814281215500030525100400d90480e040c99a07600c140700d204010741c018940900390546061103242e2620131b056540381241d00360601004440d8100104200d4150080d40003070090034030088145460741062520380e40514481e01003442480a405058240760078600304031542d140004540620302081500c5440000f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 52715345 1250 52714095 52714099
    0x60609040c0f030c080c010f0203040306020d020d06030501021801030204050312030603120313030e010206011d1005040f0e010b0904020102070b07240c02060901110301050d0c0503060c120c0a0507060506 89
    0x35000c251003807000c4840b00214010030000001e50700d03008455040520180001c1d0412075506400310401f50008200c40c2105e9102c07a0050380d4030542d000c030b030000f4010300b4410b6100c1418401c0020034444150040d1111800403a180c54100720b03024015401c0303116520405030580c00070030b0307002250700180b0301640c0d01140240a4890810300c1c00c1c50007000340d1040369090003c240001000c824507a00c068046e20100c4280010000341d4180072125190108200c6c4c0c00c1001ca01c200c00007a026148a003200c8020000070703006100419100444902a11040321800d8841d882c00c025032111f45801c00819002e90340603000340c500320707081c4000c0c18a9540a880d0584004020b40c41450b04683c0402c6c0c108070444840d0710001d0103030f051480090401c54003501514945c0c1c1088513030f08004403035104990440e07408032282000c8800610740b06980f06115070100c0c0e814007503801008094143c0c840103010103a120400d00d001903480070000a0640039400b401c41c001031040c0305440c001013030b40d40802c0d040840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 52716595 1250 52715345 52715363
    0x801030b13020303090909010615030606091203030e070603061d041a0709150e01080703020c0c060a030e03030408130f03050a120e090406090309052b030c02061917040506060904 78
    0x80c10081448058180c47d0030303031140c0d50b034101003220717015070814640c00390040e203414010b8030f103089001020340f140c0340100b01c503071701028007000101030007540b1846003034000c202078810042d83c2d1400a00201b81510660601d00004042881d02400b83c0c1c03c0280300e580c0c00107800a50921180401010020040c80c034414040001e070040b82541c05080803903d074004aa5902c146c001982d00014428840940100d0505005010406140e000840c0108141c0010303144591284040310044019089107031403501540000410f000500c021400207210440d030380b041c41e00c840c6990b0803011561031075510024021b90003c0100e000060740d07606840904904c02e1411031111a0580005003401d00c050350200d0301aa641c400001c109034111001e8001031104981d1307002011140e40b55020304500014124405220070750f003010130140282101752403541c0103130016440c0c0304459808400310440c0302d8988003040600b100420803103409070041e845203a124000d00020744440742030050940001d001102c000e20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 52717845 1250 52716595 52716607
    0x614040b031e010308030402010212160b0403090f0906050a050108010506030106080a0f0e0f010e0c10080a0e12071104180204090f0206030903040e010506030103050a0b070c06020d0207120801030b13020303 90
    0x1c9202c41c0601960180308099a40d0a00f440064500001161141c0324850b040c0000800300111100d09160203400031400320488d525850304031f55419154011500f81403882c4004031304204503034800000e483d420b44000c0a080c4d16a001501d42e040f0074400c1c0c6901c0b010810052120910840000b0340004030b40b00085883c40a000b00002030700c4030300d0340000803034bc8081d00301010304209015408048000c0c5001c0c00080c91385101080b0009810b14050f0140f10540003c9143d204c41036024118644801059800c082644003140c060340d8420720083e80c0c40848012403801a180c01e1007010000784a41c2841700f03a00a5641c00c1c40081e000780380c400d403440b03485000b2034800750b16034400540c410f450480155645034181103205129060680006004040510040c4005100092503119954018100c20407540c0d0f40c0400b1180d403001500e00421050010070780a84030071060300a8010391707101c0c0040d614a0810f1500c100c4000d042480007401244404000c50340064010a40300e1100e400035050307d01e020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 52719095 1250 52717845 52717891
    0x2010228030e06070c1203182c041101030b0a05040c0f0f0504050607110f090a06090f0207050c04200409060608010e0702070e06040605060705060603070b0a080a2706060509010614040b03 82
    0x41c0e903000e5003500350319502507000c601c044927180701219020300081e50241000c1c0c581c42d2109448030720003414540c0d15003001e0480c2e980c08190314000d210007030007402001407247c4001c002d2004005400049001090410000c40c0544251029140060000da05124840c0c5074071101011b103d280c240c1203607143c071400d102034442d02c0ca01440303400303040404928145011182e408a40f8121854081a0f1041c01f801c80080c40100d00c403490800112004203c1d00002c09107204010000c0304849440b00c0c0006d400540609990449006c56a0301c0d00c84090030782e40c90f58401c0c4400300c00c1780c4190050300446c0040c0160b0002d601500d40008000d0000074603140c44501040d0f0035881640c096a00c0e07802441003044918080245074040d08000c00750b0381c1001150140a40b81c03084c0070f080240160b0311141d815581c6100d03088141c0800e011030340440007101e468200200141b0490140700e000315050b0002049036406081d44850414400003030034941403401340c1c80120744d0005800c2d40100101e41d00c00b50095 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52720345 1250 52719095 52719137
    0xf13020604091802030d0507080f03100506030405011b030605060703080c040b07060f06120f170702090c090301060803030603030a030f0608031b0105060f0a090902010228030e06070c1203 82
    0x4880d8551454640c0710f56004041ca01019001c402c01000010481e1400180300305061701c04a101c0048203e4481e143d40d446007250440035000036401480100c108002e0106c15004004e4108064042d8070003400c100c442141550700700e02600d80c0042c1d08020080029104403103459008500e141ca0a0810b51146000c5c04264000d03001543c005441c0d42d02d00304508813520403803004081d4166510b4080340d907683c80d0b015001c520940a400c5410f01e0514000c090501c82c200c0700e200d0360003408204140350400e0b00c06071036085010003a010750721300100810000e0002084a0181c44002c0081d81400c03283c44003180a042c50781d42a20309071b0340340c50000400c10000c0000d0a012062103840044256640b0b01180c2181e600030070f800d2241d943e04256034440c0d00c41c07035007250175150118001300d10148a40010313450203d07041120481000140e82c40c0030b1004400300c1c82c02070180b1039501c5040c62072000b401c0218a000c2d10102074000c0100321020415500d4440303c1044c110b210307040c00c10081040c4981b4504e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52721595 1250 52720345 52720361
    0xb0a0f0c02030a170f01051201091203090b0907030857030f040b0708070f0c06030b01030e03120405120f03160f0e04020d060e09010606020607080f1302060409 70
    0x150b44003003600001603800030b2032244041020a01d03022076142219000d01e40034010301c140c501900140000003502d5000b03400480801d42c10014172581e25a10b50002001004101001c1c0c40103c903100124624000124000d401c82c0c1d00016401e0800021503040605052001500300031141c0e042d0b022000a00d10000c85120396080b140312641040c40500000c0c101c078100c2c43c004059400c200f10040c40000b804082c1d6068030301d024103141d143d40b8035140c15045e5224807900504034485110101e810081c0c922a088250350090303a0a00603100d0080040d0b065551a0300e03c0f2200b50410311103880307100c15136004958050302610495000580010400941c0e45c13104000102d1000c00204000720041030341d80004000c18945400400480710800082210800d00c1c415071140b600000d842c1d40c00010380d0050b0700548801c1c1c00041c01400c0c42003402c1c0c0203001034494500940500e4000881041c00f9803482403042c0c007200d121240075500c1c0c890145105900443c100e030b000006000c00310355424a40f24002c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52722845 1250 52721595 52721597
    0x220b161e0203011b08011d0a1104090e070302040f0903050702060f040e0c03010501020c0d020d03120b210d2303061512060a0801061d09030702090f0a060b0909040b0a0f0c 75
    0xa21a49200200300001c160071151200b801f602a0103601c1e0a01062194031140108000a40d01c9000c898000148610792210351814108103081e601c2c601c010440030112032080310200408503004184400307030740410f003000d40400c1052001102500b80000280004d24031101407034036090300c40d03011943d40311054480d551100301c00b00051107556010408180600780440e0408085d4840303500143c0d0015001d0b100504100d01c600300790301501c0c041d0700301061444000f8042104440d0701401000031400341440c550040c4107407aa8141d283c0e010311038894010702c2c500040707040304902e03d034070340d48a910180030550043c107000020507401f40400007824200715280c2c6a4001800c00700f0030050640500c0d00600c0c1143d06d0701d44c5c20480a05c01c1c100c1009907444500721000c565440010b86030441c050014040d4206181b0010840401c0040310143d106400d002810028503403900c0c9144410300a0906c203940060604001c20040b0f01030103c600d90101c65441c010680100ca11515801e64040b222814 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52724095 1250 52722845 52722881
    0x904060b120129070f021f0f0305010b0c0d080411040609022701020304060c020d080a03050702061b120c2a010e01021303080304021302220b161e020301 67
    0x10021851030038a440c82d0114240f401c5540f062604900390091244080081c040c0000300307510421500d0752800d4050340303181c202800a04211102000c0c00440f1a0f21540000034038020000c540a203040c01590a900d41400007807285d2200302c14182d46c000000345c000d0300c40415a10421540365114003e000141102820250304c0761107400750940300101c2d0300c08000501800c0065460541da00205039412254580307000400682180007051030130743d05460207000100c0c00610001d0751034040e000300b405641264215082e80d0740c0c2ca40d00412004c0c4038842403c108c81c00700b0210784c030010365003030740c80d00f098070020034624100d105c051035030403400c200d184420071001c4001542c0d0b1418082c03061000c040208002035190402d1140401038440880c0001859120088003241c10340d00c804050b2019045061421503442407000da03000d4800f1440640403000038207445006c07e4481603841a50466400303e94200c407149810368070510f01544092282d00300b500229520805660240600480300d8040d418039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52725345 1250 52724095 52724099
    0x804030f140d1e050703080a05191104060f0c0b01350105040b0601050405060f22060e030c0d0302100903031808070b09060903070f0501140408090a060305010b04050103020904060b1201 81
    0x1490f83d5034444a1100c05100090090301e01280e04922041e41c070554000c070001d542d80d952000b031440140f0b01728001d18401e140c10a1080f803501c42034010400d0390342130b8484524403182c03910100d41c001a640001003010f08035100400001540e01500c180c00032040140e0181d805070040104042141d440c00c1e8030580c0e44a80601040c498034a8580790170034420f02c1c001c1c0c603150801d0003003003081c8100c101d03005000300001160307950002c01c56a0f01ea0140c081c40c10b50700741c946d602c5000030107070300310800554807078000d4200c1480c3e00d01d01074141404050b8143c025003410442002004003d1895030415801e01d034442604407211842510584010361141e000143c585503d03003003401c2c0f11480140710f1802e95000c4000d1085104000080e140c82507400b490b480c07681d000340d02d031330b03409480042c1c1c0c06030196510070180802c000014000d80405841170f00d6904030566101c90803003d4601c2071084215040d0204801d0200d9442500100b1080202071300c081042a5a414143e00039400003980340d008039580001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52726595 1250 52725345 52725377
    0x1201c0f0314060102071a13080a060e061303030519020a090608011d040b070908070905010e13020108060f06040f08010b01090f05010e010e0d050601090203060307050d0804030f140d 80
    0xb07449120501a4000c0e0001c0c074042c40080c1d5514181e00400c1440480c1d5090390006010180c00c880480e40818981260265181c20725561400002e008403816406c0c00f205071f6111400040071441601a800015251050794400350000c11014180460030301c0031052071103002045000030100402180d680003862817414000070040503061300700f0100c40043c80d900a21007400010070070303001900804521703459282c07041c042d00c4804195001011900a0410008100c802984068100e40710040d003044655500d41c181c501c45420903c000740400e480d07002003034179800e019803142c0411031b010300b100e45015207600e0200c00c0d14803142c1c0118541d82d11501a8509568441a0080200421504510000e00348400038002980e2103ca4504104a424403040c081c1c2c0c411201d00315894100d0140c818558440701c203038010398011945540a03100c0c00fa000079a43c01d1488001c0c0d54140c110030b030181450708603074480c090034112900680d000d00c5c021908000084050100e110501e1598994288035510988 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52727845 1250 52726595 52726601
    0x5040b01060f0c05070b0a0203070c0b040f05090f01150c06050a050603071a09060306061204051501080d0203070b040606030c150816020d0c02150a080604060806010501201c0f03 78
    0xa0b42c2020460030b10403440010b040025031030300b41d0b40540305083c0c8414810030124514050f81740040e012210301e101c00550503074180010000d03242881c10aa600c1525201130141d0300b00d0544110713100014a80040000f280c05800b01400045589090303080200b03107440740e0050b1042076400702c511560b1101403061914007001050014000d00d81900c42110310240004241d001e0400200e026400000020311150b03590021510304452103d03001100741818180103540c0c031191200c1c818402102c5002240c120000182580100c0d0300380e0046103402c040b41d40b6107041c0d010250089a40c6a1554800b00006140c00c114101514440c1c00c0c0d000710b2400920f0050107540051700c0300180340860610710341d102e40e002c14451509043e40c28030341404507292000c902d02d08082505402c04200205a03150346951100000e40504030444060141603110603949440740020700c00c6a0100e41109500b10042d610080319071445030000c0305070f1b82d030043c0b41507a401f000d8101c43c0241000407098404041016007500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52729095 1250 52727845 52727867
    0x15040b0912010e15040807170c0607031503080706060302030f030d05130f020d0f0803070e030106050303031e04060f0501090209100306030302121c0e0703050d0f050316021005040b0106 81
    0x40028003943c20151540c940f161405510064003109100000d401e206440003124038155010b049400c08071440840d981c40d9402c03880004595024241c00300d00168428011601360b41c1c491000c51204030329598444035150700c6010b003200d809881c0c0600002507075060042502100b2100040c541c0c5003c040d8040f0304079030004002d102001000040000441c01a1038a4a129903050b211180342040c04c2c00c001002c2800f100c0004c02e00c0e031000003044940ea0303210fa066911408241c00a100300340d2500c04140c4c8a00044541c41084050600701e44000c01c03201d045030790000d002d651b000480310b0b482c52520050310400d81222810036000222180c40b4201340014110580140ca000c100150456134029120325a180541055000c08102c40001c9140e40701d004a0412840308200704880c184c88001d501c40c850741c80309841d14015030085859950160b24802039500136655a00d00d15070320f0514480705c00c3e403000e10385821803103100301c0c9550000217480792502641c000c030603007040ea603d0108000d00c580040c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52730345 1250 52729095 52729129
    0x2060114010e040212310b060f030604060b0307060804050c2101060b090906060702180901020918040614070504030204090309030204090609120f080c0903150a06031209080c0103050615040b09 84
    0x6450100700214414103500306d41c5a01c0381283c4030302c0e01d0b290002208643d890230f41c2a410f0040d501800200000d40c0c0c00109400402e42c151260f041e44c900080d600c45a04650241454006041c103894914110000380700d101404d150f40941c0d04000e0701c3c59800c461a0ba00038402510000801d42c07680c0c84c0c8003810300c0d03000c9022580149408600d41c0403c0784912500e290010124001c00403441144081d01958100c0101038022080800755951814203e801600c00352500e601d00700f040e0170800e550b0a0fa084c4030311640d4946034640b620355800c0c0f01c020000c1c0e110540401903003080101c0140c0c0c580c06800780944c042c040100c0c240c1201c0c205203001600343c0c41c82c6800d000740003641031103064000301c105901030380c0ea04842d0b4540740d00700080307424889030700b050440301d80c488810440d0800c002e501c02000e490140701c0c40780c010907140c501990145079500a4103400c1c0c3c440c1044640c191310940120b94421405032180c90380008850124200d81c100e5040349006600106207041c1c3c9007041907400b5405120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52731595 1250 52730345 52730401
    0x40e04080a2339010b09060603071e0507060203010b07050705010806010912050307020607030f02060f04020a03060c030b031c030e06060616081c050919020102060114010e040212 78
    0x301000c0c2e40c581d00c2010040700508501c4000701d4100e00c00004072044440c801d6503c1002d4882100090380248580160a48501008001f003006821300d0410b0744e00c120910385480d100c010f04410f002200d106041040400c0090400c58000083c0681c00654001c281c3c0015a985942030741c0b5003e428003005410407410410343e80c080000b4aeaa0090302101100c1d00800030710f508a01f02e04115055201e2050040d400100001d840e80070180c0c04403819180604990950f020b50710754040d01d0000d800d055602a40c4429403010910106866501c20301400b0502c1c200020500314000110b401d000d1004010510540c150410002d196014080e09602140001c080c240743d20380341002074044d001d45440c00a01c00750a00c004401c00c03450300300b00c1d074600c03c8010700314402d006a855500b010f00000c68040001c2e000d41381a10845102c420980c030740035a4141c000c2c1c1b00c241e00b4000220110960110150b04022541c0c200340c409458038401011200c0513100d1030f40e80ca21303004540d0768101c00d04096107043d41c18 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52732845 1250 52731595 52731647
    0xf070c03060905211e040b0a0203040f0905130b0901020d0501080f120c1207080d0504210c02010c0b060102010603080705061608010819020604031b1401050918070203040e04080a 78
    0x41601151540865004900d1140c00305c10a444402d0107281c00c6030b0300003400011014442d90700000a0b03c1228400709101500b030762241030007011350b441600d01f00080343e1210034a0000501d080481035024a543c000141003010247e0440c040e508203a00c0a05a42c022120f0b50100c001300313005590704401042c0400d4a00160044c0c2d00d6075807449440c140840060101d0b01c3c404100c000c2c0c04039181c030302c3d0846c014070660800d42859203a07516080034030240081d0400d4a070b2541c030300510f03140c4c0466405031078040c29101e0720b03201c0c0c1a51400061885045540e0744202200040d8007202a21010313000d4001051585004800c80f20840d40001ca881c06018108004104105001802e8001da8001d80c1d600a4082000c1c4046035031400f568000401c03e0303507180480c948440c0e102d240c51048070942184480644501c200559003403241e807406a8020555298845000101020180d0030104500c1100d2400742d40350700c2001d1041007542d088032041d00c0000c480840c65440038044c41d40051f00400550104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52734095 1250 52732845 52732903
    0xc0203070e0406151509050f01021509070f0303050c0606090112080a0e0402030c0901020c04050c04030b060d050a05031201060915030c0c060608010c0314040b07050f070c03060905 79
    0x4031081c4503001005500000240411800380c0001c8001c1e8042480c03001480d84651000b060300c80540b001c14000340c00d100c40080c052900101c508840c00c41078015058050580307912a5a0f000c0040500c1410310540b070340080c0103a06040000011800b0b80c1d1825217884181600c1814144090302243c4a21043d42c01072045452240100040f0340c3d0003c06160ba41004080c03d90b080c0d2807121010b684544040100100c10151400a0105100c240e0981d42c1080a0030200011102c0c1070b41c2d10040500c0a0005000080811250581040008000183d007902c240c0c0c1d9245080e06071a411a07842d000070600f10203110406004901608a50501c141c403942440b48401e456807041d55042c04040d11400b8001d0040d0142180100064005c0720030702006444813001d41c0a030107040070b09400079141c00041c28442c028100702e0390155502020031001501c038914122000c0d045410740c07185801040100034001020051a00d004501c03541c4c0110f0f0300b0b5004c2c10001e0510300c05076000d40311140035102c092140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52735345 1250 52734095 52734103
    0x21e030408160501091e0201030e12030a09060216060b0909070806070302090d0203101a01020313030308060a1e03110d02090711030d05010906171f0c050f07030f0f0c0203 75
    0x10840040680040780b8203051850242294035809001c10300d511944108049401e440d0b000428001c0c3c8040c00140c501647c025036500824841070f001e00414004181c040441c0d0b0040545103020701005406e0014540282d2440c45207410308403003650717680941500300e081c00c803540ca92001d9214003402c207681c40d2421044c4c44000003814101019400101616140e488010303e5102c0d5030094100c82081d01c03d452003000811a0681c20700b07070000200344a6045600c00400c651213000801c101980ca54656601030700c0c030600151002d540013250b0100400c1d20815180102424511100307400012880c500700f10245500e40360020740078811900b120805a12060b11a58001e01140780c21480403000c01e40301801c50041e0f04408400509000000603a02942d0704000140c84180f0a008009814400c03000c2e5504211840c0026031506845c80c550020f00e181d2081286070054100780c0d140c0030304407099002c5a405090100d02080814900a42807a03010301e02111400841c10854002100d6800003656 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52736595 1250 52735345 52735357
    0x30a080d0b041d0a050c0d0309170102040e0c04030b0106030c050922090b1f050d03050a09050d03030e060f0603150a090c0e04030e03150109090201030e10021e030408 73
    0x203150344804241c4215100e0368004a08000310221001c04058449000f0b40c54200d590b0050301c0c58459034011031250702e400016520310355419200d00741503502c0c0000d414480605c82c80302d4034a556081c031000800030601d4052512942580f59034a94680c00c0d850222a0750f40c042e0042010075103014901c0c1c2d4000e810104039031640703804440f0445a0360034003240b00403410100f45450046424a8584010030402d034400e0f42c0030301540001d001458404810f41c610744041ca10509500141900042011078000e03c010103000c1c1c1c40d0324120104544840100d10080b034800c50840009030b54101c1106070381014011b083d08202030410a00d00c60600f00c0000c0c3c0c0c0c0c2c01640030321b41c00d070a103040e01141c0010343c02d5100440690b480528040243e50310402d44012003070849040d13003ca402c002c0e490609140c0480c0d140361700c142303501c1c00703c00f240d08019041c4014841124103c0c140360f0b1356500b01806020800c0000d00d01d40540c400580e5600d40d0a00b040100b50047d500560303018418424840080ca250302a144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52737845 1250 52736595 52736617
    0x50111090108012d09090b0a02090108040201050c07050907090608060118060e040f090c0305060c0702030a0b18120d0b030a08030a150f120b13050c010e0a030b0a1a030a08 75
    0x111111039015807104100f801c0746150702040644d6000103101e089038200c0ea542c1030181400d40e1040ea207881005050788550ba9403140020700c4500010300540c0034030302500070703c401a0100c803107c40c0c80e0300220302460750a58a510200d401e40300104200c9030b01c221210f07444a0280307800340e070f006c50f4071030035400500d0140106801d015941c02010308588130355106c010f800100b8036048c4a0600c0d00e081c0481c009845000c250f94502800b4001000601914101c0300b441d64054000e01c009107164031480d002a9026103880c11145032070020b176110140030040074a02c10f880300045981d910504c0368200c112010004958000e0f00821101004204880b095a920101155001c22180e00c40720022940c0b60040e0003562400d0035076407000c42c20055401124420b03901c11a00c28039281c843e0f0301d01c004c44103006a17000307043d42c4c403004900d100c075441a0503545282c0000347c01300040580740d58400080003021610310418599503101d10713042c603905000645090409801070000e1181355201c6800e00c4c030540c00020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52739095 1250 52737845 52737869
    0x108010b0a0509030a110319030801091808130608060a08060c030709050303070507090b0a140f0f04020c01051e0c041a090603070806010908010e07030b041104060f0305011109010801 80
    0x80d0410740600100c4003440f00003800d4030740c3e550461a04194850f4a07180359406807007541c0415042c1c520030302e00c10b00110307003549036100c2582c6452002c002030201d12000aa40d840300a103100c00040c0303140301070848a4a016a4801d0f0340f0b0818800619480c40100750703501c60401401c081000709004102640c00003150041c90707540c1d40c0e40c1c01007500d41181c25030016405100000c0c90b1802d1103c0440d2180c1900e0741e440c401e0010f610041d0400c540c014490045028901800c0d2403041d50340352224400b80203181c0079105102c00031001002404a801200300142035946500400c140010140404100140f0901c0c890f6614286411904142c2c0142c4c001d81c40700c4103124614448100091056690b6081c00400c820381d00e10f0314840050108a041c2c59044c0821110348001c22000018000c0410140c1003030020400c40745140c0341c007a100400030300f00380d81c8850442c02400c000c1d1030300d020300000703400c0c8030008110180c0f441c0303801400c5032050800f51040890502814065030b034424602c504441d000d03202d103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52740345 1250 52739095 52739107
    0xc110132060a0510021b04020403030f0e040f0608010b030f0a030c030807090f030602040e090c06090105160804030609051c090501050306041b081909020603270106080c040606020c0108010b 83
    0x200c0c0b82c0c1d40003500310b96880b00c6992140c0403150b034000768020501c010350154950040951082c002030b40905c1c040200483c02c0d841040c4440d40c8104481290030b0703002417000c03507100c2d04810400125501500702ca002da944a20080c0b0302ca0070100044040d0760401130082c0411030f036a440092100b0007000c0000c040180741c1d00030415940c4941c54031805810885401c0c0c001e00d5a0349040030003540180300d001034843c1c00c000040c803108804035050f0201200030703000d20b280000c83c1d401164690320490020044081074450704d0042800440544044c0d8407444002400b1006418528504644244045d40c000d868508c1505102e60124000e4100e80c82800c10740c0d22a102d140000d8040c007005400808000000392240001591107032103180217003116012400d0040400f2000e1007503800440c07001e5040341d000c2002c101d40d2207145003c5880d40c14022034240402c10141e030300c01d082d200760754003101c581e60000b08000c1c83c0c3d240a03c100002040c0300d00090601d0181c41d0000380842005101f410341d503440203d12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52741595 1250 52740345 52740349
    0x9040804140604030b0702010212090624061c06030c05060f0a0e1201050a06050a050d05070b0d0b0901030602070c170a030807050c12030103051605011209020102010f0c11013206 78
    0x5982c003130b60307004960162919080500a00079080754003030200c00c4003c000410034421000c0344a40c000d10b401d210140200c1d8074183c1d13004c1000c0502030300a1300848108034802c00c0030b542c100c0030502004250320200e030079441c50800721031450f129003100d442410704000d6185506051011691000c040381400c500d8a058070300040c101300c1105280c69015424003041004074140baa000e60243d42e0202c1e040078180b41c81e10305010082050002c010700941c000c00301442510000b4001e80444241900c0c0450780043d090003041c580b01081e441140c0c5141c011403100100700c446914500603055501c2004000d180c1c2c02e900680d80c1822540c0030701031001501c00f04002520a40854000200b0718040f504102c41c55592912981c3c007d2005481e580241d568a4085101e07603001c0f041190070503522a62401e6403107081758003c15a004c022410741d9640c143c01d10304000c240c0a1000d11a8503038598040c030b103c0884206080d50a00340f20010ba54070b502c07c40240e01003140300c0d8400c40c03e140e0400300c0365503941c07000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52742845 1250 52741595 52741597
    0x10c15090209011205010c02010507020307060b0d020301020a081902090f041a06190809011a10030e070e010302011b021c080405060c0f071205070e070e130b01020705090408041406 79
    0x1030194109005000203d002840007038806034140c4160003c018141303201004074220703501520b80c0c80050700100180c201007049900603150b1014000e01c1c420640c40940e0010307007240d0002400a02280c07041e010480d08041c0c0e030851900d15004800c0640ca059100800100342917004464148201e0345c4840426135268102c200c1300f500600134091642c1d138031412441c3c3c01040b45a07940038000400c054006071582c0018020400c0303441121040080d40f080c00400c11200c081040130200807d41c0e81d04140303038140c0040185030005c0850b10050f024550441c0001040405800c2404128104000d81d000058031104589103119810010311404611185051041841254001ca9014402184d03256440c0004600c91800e80d46610403a1480c0e603980b110718501d06158030002c0c1141c0c21166040041c4003c1c80411a4000d540d4a428042e420702c520014600001030704050701c5490740c40310901403d50301000f03160040c0c42c041382c900600d494940d80340e0105200c0c070300a5507000d2000032010403c40e1901c1d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52744095 1250 52742845 52742861
    0x1111204022425020d0606090c18050609030a0507031208060303030906060402090402120a05010f080708120d06030605070e19050901140301200d0f0501030f140c030a0308010e01080309010c15 84
    0x10420120303002d0307604041b006030130140948034007140f030603441130021400707040041d019410540b040c8005515103410041ca0303401c814401501400b90b230000b01c00003141880024041c0d0b01c66541d007044035a02c6d40300103041c000c0041905000782c1c420800d00c04400303800514180d200c5400c880250340c8008030b0b4003180c0a0b0080d01502c1440310918014407038081d00603000681078880039140003001d00c0ea644142c80c3e40b455184500482504241c4a400c1e619620760014421500c2213000803494176034a5a8030340449004a0700303440014480c6007204828605005160704041c01a51150340b61810300c00020f080d01010310600c604107207a081e00e265070b91402c0d082039011084080aa16100507100c407050031607409164243ca20a1820304101014200751003641c0c141d0760001031980c0c0207090b0b5501c00300504070141c1070100b00c2c481c0704212a955502000700c00c0e4041c0c442e9640c0e502c00d500d00041c429103000181c21626083c2c00501c500c6003a66400b0302036141c12500521601e00d01184010b910004140403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52745345 1250 52744095 52744099
    0x30315030705120106080d0c0b04030806180703024305150f070e0303160303150503030301060c14010603050c090406060902070c030506070804030914030111120402242502 75
    0x161030074a075a071806521172000c441101e000c0c0c0c3c03000240741600b01c42d203c0400e140140101410008a40483e1084030030590100c000340105c05c80d04200c480d5a210407100311a414001380e00001c0309140000841c44c0d44240600d441c41c0e04416209940031402107010501c05140d01c4144214806c0c180300c010451402c5110741007502d5900b42c00c2184600310440b0044626a0200e07220ba4182500d50900200300c8901401001c1c000310101000e9804802a11081220103c004140ca00102c1d007a9000d100850080a00b03488000c118005442c0c00c00c81c09495030a107e00da0f900d071401c01c0010a402040e803004808040700d040800340d8a6242040c000c005c00d40198004030301c085046010040e01851520640780908100d645903550103070100d9800c00111802030024403150b00801070b9071003108101c04d04800040c00402c0040c4400b5405115411006080c441c001c186800e06c0150309040350b02174201c1e4940648010103d02d41c55071801d00d032140e6200e41e5a80081c5481003181d401c40030024101c09540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52746595 1250 52745345 52745359
    0xa050a0e0907091d04050618010b0909160e0c03060603070c0506090d1205161416110f1e010c0f050f01090303060906120609020103090b0a0c021002070203030315030705 74
    0x2c034410007070084409000d00110340320940c0a00d8109082d48001c1d6110303075400001001c1aa442c0000200101e0680d480c9143c0d41d134940c41c0500c89a502d03041c0b0346200c0c00c3d00b078005054841ca50b440d0150810416071040116001c0c40b418800002c5288088940c4207100355280384e503d4a540d1004c4401e00d401a0303020345513028410900100d00c2d07000c03400c040f0179001d030f40d0781e101003103a04502d442c21500c09a650080000900c1c0d400340505005194600d1a0200400342d18140380d840d03628080003444400f001c8400512412140400780703000103140302007580070b496000c0402001c90304024898800490503042c0b08103c0940010800d489250800c0c140d840f100342c81c00310060041040c0a4141032600310082401c101c40414039101911070b42e0100d43e1001314190300c8900340e4413420024081150280e0415032902030010106210340c00140c0602c1d40c0510000e003501001c80000d0500402c0001c00003004d00400400002d41d400005690700540161502c41000d13120400081c40c144007035100ca030704405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52747845 1250 52746595 52746601
    0xc08030a0203040506060a05091303050c01060e01090e0d090605031312050c1e0304061214040309170c1e0102250501020f15010e0703090602040314150603030a050a0e09 74
    0x1140c1d401030340c00303588190101c640c2a215881004680003040c058583c0046440d00002c0264070403510040c000d60080c241030746003822600b030240c00d4444580000c002040000010400c0210780d1240080301003c9101800c0c01180c2d80b0402002d03000c40e84180c004110000c000704080388010402c507082c6c1d80e485400c801d4030311900140989542c10070b00040da030b9409442c6201080c4004e800341c00c02d203030111201940c030386410300c00240d03801d86000e0254580c2c00d0380d500683d4040c4c407a01d040c02c0e0042d4060745a815580e46066801c81c1c2e4010382a84c4000c05030032802050354a51103078096250300300d90740c6058408504000c0c00403403500f60100041c0180c1413400103000d10307210800c080e100c00d0322400c0e400e0307580c403640580113580da84840706028004a201c0b200108030310035680c0c41a0750080ea8070318011841c141f42c1d4803a030069801c5608181d4102050a0b4503046c204410000302d812600211280030303040c80e0100020352a400303508055018008000740300e00c545441a4602d510010b80102003103920f003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52749095 1250 52747845 52747861
    0x117030d060e0a0506040501050f0d110d050a02031605030a02040b060702131a18070503100f090c0f030c020c1e04051005030d080c070204112701020c0d0c090c0c0803 73
    0x10042d03c402c4210ba191802040403402c0c107014060580b440036024103a0030171607c003440f14180380742070f0640384040d07400ea4008480c0d450498151754540a00d00411103801c89004040c10710201c060000803400080301c2c02c01854602140c51099a030301110000342025108001c102ea503c00c2960081d0300644040c080c0380c00b00400d07400091090361044150f85078406070400d0003051180c41e0111031042c00360500060100f44244011030340070142500402060390b449800740c6041a064000620b12500e0784411400e266100c0000f019150140c034051100d0001d98001a48480b2803105e07543c001c000646c4031200b90003020141c0620704e02c02410070020751800d8080401450101e0184a109000301c019045009100e09a41405010305400441c5000c02c65400c000040c80c5029074082112818000b0110182c09001204204440005030f00e0711039561100082c184241046042c1c8251400c155a10216a0f088411800e44103054800120b00700302540035183d520324004024008040001048245 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52750345 1250 52749095 52749119
    0x40b0a090f090209090103061d060901020306130501030b0610030608030f0903010b0301020a050313020d02040905060406240603020c0a020303040b040612090f06021605010e0a0b0108060c030117030d06 88
    0x9a040c625581d501a890300082801e070300c07880d400580d00880c1400103001150f056444103160003109a1180000c2e081164140c0c00e01d902140d14018a940c04002c008d070074104441c0001500d14a074504100c20f42c1950f54640c0c0c041c1d005403495000300042d00380c03030300201d00985c80301001d426101c00b02c1c1d844031081030400c00b50382e122060490080d400d00110140c02c1c1814000c1d41c0108580c0d0300c45034103555a425100072000009002030360700a444100d03000150701d4a220740f410391030099010300110700c0c090511005490700040810450f9020040041043c075035644031900380c031502e03d009a9185011120980790242c070140117903041c00000340c0001c8100c0b0180091040391a507888141d018051000f020f41107488401c0054417040b0100c0e042c0c03000442d194020003016000000d0a802507545440701400c5a1039030240c1c01e8140c0c070100e10030b014043d03007680c19401040f406c1c00a01851038001b85507807a6000620651a0924441d040041c040b0b00c2441a150345c0f050a440c200443c1703035160074413549 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52751595 1250 52750345 52750349
    0x40302160803090103150602060712090204050f0103020f090601050d090302120a08090d020303010602070504110706060305100b06160b1902030a0c0f05071214070804120b06030f06011406040b0a09 86
    0x406d10b400c81400c51000e62400803001c43d9010340207400345a0750420181c0d00c0313000040c0445c1d1140d560354071100050741c2e9841a5070003500742c54040304a41d030440c0705000c40c0560a41040d0310820700f4070208506603905c202100c15003240481c01040b0360b80c852405074076017000750001c110070010201c0c15030f0103a44d00c5080700d880361192000b1112001d0310242d090380c41e48800e001d50300c0160000310081c0410300b23182d04189040101502c1c0149800256125a0102d490f0340d001152030350000c040c81845159140103501d44110101e4159290a03142c808280800111402c001d06100c01940001c0d40210b07420000f080c02c14000c6000d650703901e000c5000c1002480f00e00103030008900c1500d01030300018403620655208603442980c0d092680c540b00e0050b05c0114004840c482000c104124040c0040ca0110180005244200d103400121560f843d000044884c0200304501a0b84440200c18104070f00045050441e1000e03a40f10000709105400300301c00f44180d40001c1242032000030702401e55580040314a00b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52752845 1250 52751595 52751597
    0x80904050618160509060a030e0106080d080f04050c0d03090503162d050d050703050d03051003030f0203130e060f0303130e090102091807170705120403021608030901 73
    0x6946660800c80400b2260a11141508021000a6024400620a50441d4603505011381403518600000b6110f034030800840000a448452820108400340210b001814903031024210081c0407410040441c180205108480e0818001040c00d000342401040040c00001c4e00f0800c5280803820050328400ca1441660700078400d07048001100b410703084e0a44166421040980c0c8161139003040e2895030541512641c4481d01711860000e540c2c0d603442c1140d00300900c12405072609a00d03506000c1e06004490b94135030141410f08040128200c410303003915060700c0d814246126040c04240317040386180981040c409998201180100d50707102c0510780c061240804807103100341c00c5002014562a4040c8c0b020b01044281c0d1000240f00d08071100d22a45da03c0381000b4001824844084006031405e050005400702c43c18600c804c1c080403e601460300038054180007411461070a01d048003d09600c20380010303002c542c4641010508142c428818130590464506007068501c1e1074482582d01c2e68061003a80b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52754095 1250 52752845 52752851
    0x501090f0507060e0f09090f03030901090b060d0203070605030c091e041b0f110a06061401090b04060c0b0406090c170f0115050d051e0303070306050402120a180b04080904 75
    0x3070f03c61103810500000701010700400d080c1c01001d01848a1281b000d48a1002c600500750751440551041014500c6140c100c00007090800290610544002c030141c40d071401802c0038400c003c00f50718002100803ca51140c54002d0380d030385da9500440458012a4119a0700441c80510040c261a81980a440c0307131504580c100f0a80100d02c40f03518801103480300f0000441c40b2805c0c0300198070f01800440300f03030b01c0c00e24040d240c1c5100c075566520100c510a421a4022a1440104103000d503485207450300501000c030000c83c6041c0c18010003900381c45035100d0043c0319500000001e0200a00c503040411000c3c0d010b0f8040b07c40907115015199102e621000d00d6450344107007402d036041c00005000d86107200d9024000302c00c0907420002804118031100200b0344180c031400100130481c84604944001c0340308020043c540700e04000300d0090a42d101c80d4000d074804d0780180031069134052008180b1360404c3d0318650000c0c0401e00600b0640c080384404c040038002d0000c1c00c04110921070840001c00c4141c004407010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52755345 1250 52754095 52754099
    0x71b0b13030b0109020901140a0201020c1c0212041215020d150602011a090612120d150b0a170601090519030b0c0a091406120405030702090703181106070501090f0507 73
    0x82c400c900486c0c1c9454001003410100c42d421610040003000390010070710000d4a4807131902d40092a00c1d201200e10071030804101e02c08115503505005032641c1c59a05100d0074078180c03401e00201d201a034212001340690703215800c1000180c0e0b5a904035624880c1d02c14082c0400c6900c040c1c40c00e611100d511408001d5400d2031143c65496800000b444200e000081c51400103407901d60610000000178180b0703072402e02c9914590035071f6840d47c0c0c010f84005075160002283d516003034080e4810001c0180c0c4402d5000c4403e02101100c907400281004001c4a00c1400300d020380e0700d910040710505201d03806240c20261200c0b00c40b08a010040c111010b5a0244081401e261100c21a4200314400c0700221400200c0700d8200388040c0319000307946050660300030704036420418020301c1010b000360300b0348088509a000040100442c1400d0209950041c024102040302030740d81861042500e802c031100400c0310000e43c4400c0d10301d607154400d40388d000790440003c0000c254949420762010780c1c2010141e441d8400c00c900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52756595 1250 52755345 52755359
    0x20f0c0909031e04051207150507030801140307030602030106050c06090705012a0602030a0504030206070c050706180902040f0314030406090905060414090d0f1103071b0b13030b01 79
    0x411801007551030015880c2801c0c16441905480c0c800701c50b203d29480801001840383c0d9000308110444038150080c006881ca03046840c0c049450156032101401802d10491011941000b4428115003050081c030341c03162521400603050801d0764000604003803011001103001c0e54004003401208045100303e0305c1c2c94680c41c0080d0b96800c29485040d0000d001c00c1030441614070100c2c8120403030041c001001c2e07040f580507624078023a070f0021145504855a118200070a0690402040d6041030b2903061600f84079038561038860325005140103110038880510400184a04404c0098000301301031003045444a80300ca0902514030820b00c811b45034201c4005901000520101c100d900b05c0d0220346890300120315018681c4081c0c00d004049070f901ca59161801044501e0402d0003500c1503030000042d000154641d2006850003442e1070041040145500031411003000000c01c59440e950000c01420726045210410302100c0601e40140c0f041c075001107210402c0080028440040e24840e0b6000d408581c5c030303000c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52757845 1250 52756595 52756609
    0x6050a0503030f0f16030201150501030911040203190501080a02190b03060904110337020d0b06040e0f0c01120c02030d110c03070b01140105030103021807031407020f0c 74
    0x40c5645600100162800c07460000020840a0903032026a800c04c8070659000741003018090342680540d44403800061038185c4c00c002500580000d090820040d04c1644960b5407440c04000214042c690010100b107a0040f0920041c0207a00244414001c968440090720f07115041c180c000c0f402204422203414407000600160310070b44544203a400c3c01c0d65100000c1081000f0040c2040c0c4404a424001c2012610107004891540c04600c1c05031000440044641110a14080141440000c194034000050740c40a400944158200d41a81d06a40315800002d00070102000501c0051050019a504c0f840c0082010000d80d40240c80b614910008551080c050720540070b08940141c204100d1080340c404036a00c480d5010030040703c01400d001c505070b00e031840c5a100c60820303240303001200d0040101c0b102c80070b14051082828a0800e065514540c08110150215001300c50024400c20000d02c02e40d10a900c100602075040a0018050912000180d00c1b44d4400c450080b49004468611241c1e040031700c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52759095 1250 52757845 52757849
    0x20a12020112090f0609061a061c0902041812020c03070e0403051b0615030705030c0f060c0c040c0c0203060f0c030c0a090e0103061407090f0b1615020301060306050a 73
    0xc2c4070414803020200c2e4100051203d610126102c80c10181c007031300852044e00c11060fa10384190400148503c000030036a200f40c008185080c0304010803c5904501c49040d4043d5640c001a9400480e03003200d40d01c0000c000e400821481c650032114a006030007448010880704110000d15000d40e590400d25000b89038a45100d401940c400d00011404240001d10540c000d001c000d00e91800c034a181c040c009000f90900380b0030350f8000c0d8010756a4204007003914050044034000c10080b070041c105100542e021031602c80d080b8440e24403580c008596006402e005014041c01550003d004102c55082420050421551044160b00910070704000a060240100d28580140150001030307045549003152001c2d903620900800741040040c03000011000400d0010318080c501c902004034010000302083e0080180041444040014041003007042401d080240c00a5401d080c8000d41e441c80100580e803101c1b070103140006c010341d08041c81d2444801450340618140da40d1594140801c41d0f8450800c20550558 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52760345 1250 52759095 52759097
    0x3040506071101150e1e0115030e0a05010e070e060f0a05040e030408011d011b0c0204110405030316050f0304050616030314040303150501030c0f0c031b050a020a120201 74
    0x2038000700d4900c0740a5194010b01c1d01c4100700200c4c0790001c1501134607015029510440104800e0000c6c03140035699201b44004c0b00520316035442403903140c13002801d0750f001400d0107441450f980395143c50005605004039450281c03c80c00a12030544600398441c0d41c1c08291003085510340140f80880c10b240360095481e060500c0003420102c0007404c100c2004002d00320100410318600c01080000b40040e420b00074240c5003000c0c1001c80d19081c001d60065400d40e001d180d600540d045048018040854100325510512601a60000790444610010840c41e100780d42055515100c0840d2001d1b42c40c11945c140b450713592080050703c1082c11240c147c41e070307640107074040e0940c00f4100f0f1041c0c01c5510b05400c06043e003d800307480c012945074000002e00c0c171203060540d004c0c0c001039120f4004000350f11190045400a000c20b2808005090904034024081140d580718a42003061100c245000e15100d200146c51600190414014030300745403130403960fa404810300c01c07402400c41c0300c1c0024090140d812440d00c42ca0301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52761595 1250 52760345 52760353
    0xa020703050a03050a0605150c06070306260a0611090102070504060513050402030c0a03050a060c09061b06110406020f060a02180904240c0305161d0103021e031b030405 74
    0x54250660181c813009180652844c3c1e686000281c075541c8984d944101c24150110740c0d42d65000300c3da01800c01c0c800420142c01e050610b81c00b00014200180101c00c00d000050100041240140d00c0300d0400103a01c40c081d24050425140c00d0548602c00001c00d8407513001d03022038034107594aa0500c020744800d40718030b99010179a4110200803016981000790312500c0201581e0107103e440b00000d00301d104503003080d902036200c00100000c01c5800d2040e404892240e0802110251410ba4001e040485040c3e55002020880d400030b030030440160042c07080050b0008240e0f88550701d65000075990132591707051100c54410f0b8004142100f600d4403c403440b00304580b50740c001c04081d4000b4883c40d0307580a4412241c40d216100b500368620031110400000000c800d10228001d0100d42c40101a0340d800380900080741842d03c244e00b403080e0002c8828501f4003458640160718040310006800070300821002403e40881510b4070405817041500862040849525400f0725032103c010540c1c2c41e010407100100302d544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52762845 1250 52761595 52761607
    0x70f0e09010501230102070806010e040b01080105060607080c03070c0312032a051b010507030501050a140310050a090c080304030b0c031303050d0b06070506090106060c030e0411091e0102060a02070305 88
    0xc4c1c80c0014102061040c011036107400d030f0b00e401c0c50385494001da10000040d401002403004220348802010f00510030340c0e00a104604025000403545e00c00d216004042140015000410210078410742e49a150401200f07060507a4900313114141c90005010703c0002494210642070249682c5a2098981b060081c0401c48254600c42aa4107078012005002c1d10000c1c03400b9100318600074020548905515980810385515140c10300c41c0c80d0038140c00c8882843d103400e0740d100483c3c40028207180380200554000ca125290700310204020a004100030f02049111400401c5d5400008000d2045038401d914428240d03441020000003400705a8040c402c1300d501c200c684012074801e40282a0750032860000180c1d405400000850650100c002224207801c101704122000d8800e204401c000e00f21410700c07640c0e00c034642e80c00134039035500c6002e05031280d940c0c0d40304507009400ea03805a4100342d4000d00041c980300c0161240e0202a0700c04001240184180d10015050310254000e644803580d050b01c400341806d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52764095 1250 52762845 52762889
    0x1d0307030515100b03070309030e04090b1b0c010204081b011704030507080904020301030f15020a090902070f02091f0b0a0c0605060d080f0d050604061a1b070f0e09010501 75
    0x46020345500390f079094441001c141242902c4c000c50003075500e40c60004180c08186406085004000b040303900c1140780c001ca0300c0204080b215425405450665a0b07000c2d000040c1308034500e40201c40400d50550710100e00401d100c100026000041440480d0704115031041400464482180d0204d160700b0118043c00b280001c0e0080024080162150624a0400850401050880e0000d03401960500c17a0020600140b042038603000b054203010400035450180381e02d90161072600e803841240d40e0310350700044080600c80f4660600c1c990b076078010203c21117414419080030300c2a40c41310031100000c49d00a000107a040702c11080350000c0182d500e8202c207506060300c41c1d500402c1300400d86030300714500d0280000010840030081c10013410714410036448103520b59040d02286c00003052a80503520f0250240681c0b10000440382c80703007881c0012103031b0301d00788080c042e400488880000000741c894940b021a240084942620607108800c1c81900c25640305401607007a20401c0c45070700040c0d154011010700b80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52765345 1250 52764095 52764133
    0xa0f0602120c0a0203060c0405040c0201060f050f040207020a12020a08010903120203071704050303100602070302060d050402130e030304120f080402010f0e060c06010609080f1504061107031d03070305 88
    0x22441807015140c0c42550f5801203814150704035503544803803030000b038140100d2405100b400c070701d07804a100805c06a4188040c98100910a0040510844c4032020045440c0e4598044480055001d018003c505941d0901e05402859058040344510100304001c44c1202051080111712501075446091007a00c54110000035400074200758100300c403c4468243c0f1404002c134280c0500c1c800c4000b5941c0b031030212000c051348100c03500200c08540201d174040016a44120030340d20340118200c80090f00f52510310015070b580c0000620322030307820300701600e0346d5a074a4080003440c4654000e003011804402240011210900701c3c0c1061030115001c03d002c500994400c0b171034600c0403034035030904940b9188581e00041950b0010762310a862035002800500086600c10007590003050071600412041e065140000e48941030f0105000c0d5050500001030b080c0710b069000348201c020194050350b80d0b4205401c0044c0041c45454488141450001100c1440d007800034500c42244c2c0c02002500c04003038034101a0001e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52766595 1250 52765345 52765357
    0x30504020f030a050d031b02100f06080d030f0c031806050411031605041103010501020703060203060105090411031501050414090c0c0114150a060f03090302010905010f02090a0f060212 81
    0x1440c0341030740050700d480801000d100319009000424043c105d8404c0181543d031428466910300032183d440c0e91031241c00003241054058032110200d0380842c03544038900101f80c241c2c032540c070f28441c500e03001c0c01654041d40914a041d10b4150280b00c1f00820650076410b503208035080305201b504056511b00801c0007940400c0d0800e03c61211281c51010307207800685000b50003d04588031203a0004204400d02d498821800d13080c40580045081d503140c140041d40301c5005120142c4081e40020011384560310440840d1120007008004010010614202401681013141c0712070004001c05048441c560040c0156821503a0700e09030b00198034580414045c5040b005016000f222009000d1460500300a000e00002d00207035090040503440c2c940004240160041951805101144814010107611800101d03100d040c60400ac80c499600d460105e0040c0b003000d83c007501c19440d000210070221080d40080040d8a001c8a40a640c0ba4481c2900c8038409040d210b04005603000c0c0e03024150100c004009001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52767845 1250 52766595 52766599
    0x9011206110318150411060d0605030304030b01080c01020714060d0605060c030a020d030902030a0605040f0c030b06040b0f0303030610050403120201060614030f040201080a110d0c0f050309070603050402 89
    0x704106455924259500b007034911159a0700542046290742c03100700a0729042428010929240303050603150800190701c0341074100d024500014000814444035002a4020003024044941e22036481c10410180b100c00c0c000c00146001d68a45035032158400522101502c0f004007403210024042c20820400fa44103801c10300c45d2640f01d01d00000c031607441001070300c5900741c240055a503030303640b11a0090502c6121507031101490700c0c02d03c0311009a1000907050030010f60000c40020292100e007440c01c0c010a0642c07005224002840001c0100034040802a0255a003514103200d102c542c041041400c5007540081509a8000e00001d1801d00d00000413a40000d00d504069140030b45903200c004800b1148561240982e4441f00304003d110b91151440f0f05051520420606504003202850350b0a18080c2010741041036401c04507501d180c0c154000204040404081a500e031610100480981250202e42020514100c3c40508485c003c0081380d01c5040d1440103000f50701c3c10704105800804020703009a03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52769095 1250 52767845 52767851
    0x10305011410120b121c1404030204110403120306030302010507090e0c030c0906040e0103020109060c08030402040b15070f020a050a0e13170409021c0c090306020903151806100509011206 82
    0x3c4400c1d25034207009020843d0078000391503c4101d1a500048031040081b8100800102625000c0344940710300664081c0ca40c1120042001d003103104181303049008540000c2d140040c002c9070b1200080c1c046e804481180d1081d002031106698030441502c0c201c8003886079510081b040000210450300880085910100090300c81d8240300514000c42d5031500301d03800c410720307048213a001401550f802602c00002002246002c5d45801c2071542d520801d0f010241c4001d00481c0c40f082d640c90f050759680544201401c80e15811a21440305090802d4100c076590b00a81c021100000d010440d0b040c1260b02c0c00544103842c00b1961540c5801c44450348032070120380309403200a40c0d203d0010000300b298000300001e04100070f0168555494000b403200e8081031074900e03c2c0d868039048020501e15004040241102e80050005131144000302c0801d0a05c0d044a44003155000c28004010451454403a05080d00444204581096403060290142e4030f440d4000e80fa407040134000100590b090014259114900c508004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52770345 1250 52769095 52769111
    0x606020a020d0c150c0501050105090c07020603040c180c09090506090f040809060403060b030606010315050d0f06050103030507050607030525180b0901020f1506090606070b041101030501141012 85
    0x16a1404003415501350006a06100c80d07028001d0034010140035080450b444201c40c00c1900c0105210b1050110003405240c0c0071000600748441c880c4218000c19902c0c0e80502008240c0580400401c40c0040390b00116024070303000b01c3c1244039881090310031a40034004a18545900c1d910101403400140200c845031030030004124961174400240004601c82d50000c200203040c207041605003c0000c0c81d140c101403034028042c41c086802064002194410742d084610700030076040013070f4012160b1501501442c1048000030406a00c10b0003484c4440c00b034800d0351601c4c1ca8108086059802c1070350b14190b40e5004290320b0020090503401c0340c8c141d8203a0b0600c21622481d9103003c1c40010401d50080c8000c4031f01003111400c81d601400071290458445024040000c4100a444051040586040d01907140c00c1c000070300c1038076484100d5141d41d0b04100560181d143c2864406460440103980c1400282840000600340c040c1800d00f03460400020008186c0b8800c01e41e08858520180942a05240d1180e0316 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52771595 1250 52770345 52770359
    0x3060d02120f031b061312020703020409080705070e0c070602030601110a03020c0109050406060203030a09050109081201050a0b0703020d0f023f0a1211120f190606020a020d0c 77
    0x78002d0412010000d5600c2d0a41c1c40c810500e842100c0c50064800c4e045502040200300000320030100056001d400180b4240c1c4815040f07152901680000f500306261440400620041a020b0311000740302c1d00842e070925856420b910084081503841d08407044043c0180d1000803801d4000d10350020061504140d050000b10300e0518081d081c02d420340240c1c010f903000200039607100000c21b010744425941846144c1c0b030048000c0d645c0c400182898121a9200c8403502000310030b40110b9800707608a220340c2d85074013400c074500605401c00e200d014400e9090301400117150601205a0740718030b4240c4c001d002d45020401d82552005400c004e6003086009001d00d40e40e900d10301d2401800380c040910301404a14181c0d0241e1886c48055018088144806020103882140c3c40900c0c140038003007081001c02c07103654201485619001d00c680d0360619400c20810061080d00b0145203d204103284807994210f40030000750003007166158003820707005800411030600981083c0100a030750910030b00180c940d0580d9070348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52772845 1250 52771595 52771603
    0x210c01020f0304060c11190b1005040e0d02010609090807080a0e0a060507020111010203040b0403051c020d0e1b0f06090d060905011e0c0804030804030e040507030e0d05090603060d0212 81
    0x6070861350696940d090288642c2c0c403080c603540130601d2000605c0079140c01d040e44422403804010092410007030400040c442c1c03184561640c014680500240900d545c0005455140c4a43e08601c40066103043c50016080c80140540041c1641041159140c0b0a0340e48481c203407940140d460b0000d10130321800070003080d00c0d01c1c2031060041143d5542c064442039a0300c0010410341040c600800181e0050007440041642d01407800d800507814100301d42d0711003c0e0560216001d480e15078102d1b10a00c041840e180c4c1059540110040091340400c0e9000c1d000c070710f030840403480c20182d4101e41002c0741805400701c0341011070050860ba503000349080031100040d510f00d003d850100740d0403030700d69440c0c400c010000d000010481c503001c50400300621410000d50801401c0240042001d02048030311004a41450f0084064010961001d44280814504900080d0103018807030764501e031a1066041500d01c680c407620a03941c07800401440c503491900d030034042110203071200c417040c1d0f400801c02c103803541e039818200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52774095 1250 52772845 52772851
    0x70f0305091f080709060306080c01030c1101090506160315090e0709111216080f0c3a020f0702150405030303071101150617090118030503010314210c01020f03 70
    0x10f502c107003080c982003000034908107442d03118405050400d0010712a00d0000303e030a640014083c600001c64052801048503010720111b0600c81c19440c241940082c0000480c81604ca8000c0da14034125901b440c000407012140d540c19549500d1500150074080400e8035000400d2034081c4c2403c0380c80450b180c407406800c03141590000400c10000040c000010301200301400e030321a40c40c22402400102e00400a021103400524103403d1902001c0080e0140721000c081da400b001803030302404814071030f501c400c0356006c0040c0941000c0c540c00c8003a01464050500880d0702130a0314000c114106016a800c0c403c001103454a4111a40024400030032641c80410140d84070f0386d459560400c00700341084915007180d4500c007a0580201041105206090304003034140c1a1044205208070346a03a040341c0325004204559641c210000c110381482709055100e4050750503a4060f0848202e40e6898a28207070390740541100400e100001a600c003541d80f10800040e1100380c100781c0015203400707070400020031641c0c070407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52775345 1250 52774095 52774097
    0x501021b30150f0a0204050901120804030602030408091206012d03061b0f0207030201210603020303270409050712050312070f0201150501050f0a02030f07060204031403070f0305091f 80
    0xc101009400c907030000401c4e130412604a0704618003410315001c1518082d050040164072030b020760784e60b400c0150810840d80110b411480440d20303801d151600e0305440e449126001d203d41c45031aa4200c1e00300020074114122140440d0550280b400c81c0c51482080803640d585c03045520001000001042c0c483c0a10703802c5030344c580b0882c4000703a60610003070640e2a50943c920215030040c041400141d80040e4003e1815000c0310f024020381050300c0b41c600151495402c000e42602000c5420550f00b0900440c14015000c283d0782c00e0000000035081c041203075034032400a00a948080c204108c2d40080041003c2100d01880c00e07646802c5030442482000300301030310300c00000344070796800c480c503683d0a100d80c00c0803884070400c2d00580c80c6000c000034050302807581078040e0100b001038402e1046000f0801c40d02c0d00b0000d6140c4030b4440a107800c14030003c3d00a0b1006480c880c0001c0c00e8440003e04c08400c0b666000d5010000c00741000d1a9101110103400280890346c03c081c00b241c00d00c2504041d0074400c160354801d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52776595 1250 52775345 52775383
    0x2010b010801060f14030604091403030a1103041707030c06091115031303030b0117012301020a050303040b101701050103050c0d030207150c0b100501021b30 69
    0x2a4000051411805a02c03c004200a00d81e6a4450b6a0320484c1c0f0350b403e40200d9401a12500e6100008000700403907000184124004071414201034004000395220b001c000030200402c200c000f60402c0c035444111070080804200501254072130100c04003a0840c0390103454854100d808035170f1035404543e410401031300d580901e2007803102c045c5054050586400405440b05085051407041d681d102001041d00034207040d10b85d880784500d40d102c1c40100b01c0d0340007540c07550219540d40c3c288240b0402d01110341200b50800ca0b02d00200e035540005440e800d1158084002d41c515903442e11100b0918102607d0702c0c2140b00a01000100c2030b10b64200c1c0020302102000004403035140d0718190349007030000c0000500500400400703101084e00481d880c41240e03141300201452038200c410071201541d85440003042c201d4584280420940050a1441174940a808441c5642c0c5d440800840c0c040c40c1d50050760b801901242441d1030340014101c03404010100d00049110444600049414075105652079411110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52777845 1250 52776595 52776611
    0xa1104090602120f06100302090120011e200702060304030c080706290103060b040302130b0a0308040f0503010522060908030901140c1207080c040302061209010c03050c0405040b030102190201 84
    0x80d100e0502007400344c6c2803c0c02c61502540701d001a05083c210300485c0210401d145420031a640300703401c069100301c6d00103140840800002240d10080c0780031140708480301e440c03200e0001d02c0d005900445072401d8004040c10705580e00c59500321002d0601c124211011181840b0880024086001c0c400200c51100301024145012400340c0388986131a220050405040041c100a403880c3d1034200c8099a8060345c10b040212201107443d800340401030140fa400865801d4000700f405035803400b41095880292070001060b9945007098242c0b2420364081107511111014016942e1034082d50341010b520486002c1200d920302d0715869040d030000c89151030307242d445108100d6001d0100b2007483e40103060490395410702c086140001c6119000815100601070385901142c0d01d43c2140040d20002e41d0f00900d81950f03800d400600107139044058035441c03841e42c00d10094550250280c00303041d00c42e40000c0c4415040524000401000e00186641142c26540c20060350980d0010312560082c0c03032105030000f00b0202 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52779095 1250 52777845 52777849
    0x20403050d080601120501030c090b010507020d050309090c030709050103091401060b040503010c0207030506070e010c0816060e0303090a08130e0103050309010e0306070807030903090b0a0e0306090a1104090602120f06 95
    0x405911079170b903801e8940b1006000146181c0c09200544282910019002d030000b00107842500c100c020181d4000c85440741c407002c2140002c000c0188500554203070541d601e071440703184450300007a6641c00108014403018003240d4420f6004960403405040a0581c0981246c9445e0844c3d10640003002c00640010341030000b410240944455540740d880149403107451900c2c0c807615007001420b0350081002c048001e46103030707225900030207806411125080c3d03a2400d10958500950458808039000c0382071540000e0a44004401e8034400c4018101074500f41c11650750301c0307610350b0082c54039510150040d4408103031584044103490103107219500440d62021118000b5010300c5181e10813600c6984071508101280c0c0e032000419810040758240807035846c285180c01d450741c01329a088003030020342c04a0b00d541015405011044100010f40503200c03540c564005054580940500c0034042d08401d41c1102201d042607808000c4550082c140141490f020840080c0303003010a0b181c0b2914489802c080c040da038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52780345 1250 52779095 52779107
    0xf210504050d0203070503070f020a080709050402040b010801050f040c12060602100f061802030c0405060708070b0601050a020d08090a02100203030108010c030501140405040f021c0506060406030804051201020403050d080601 98
    0xc11450000314101782480c0d5440ba0b480c425a50000e0004000d02c420308115115581460003620b0381d441a14011521018020000d25085405920850420f105001c00e5401240594103071180035083c800c03c508690b090201904030f80d00c910b03082007881e6041e40034444192043e100600702c280c0c041e140c1015100c2d0a00b040d2204005000625460f000c0c0401c103007220400700354002d4103a52400f60716580d916180044a002d00d03070101e40c0004000618004010350b00c1d0007005800d20881c001e03078403a100d9030300456490041003803500240c0e012401518255018424240d44001000202c0c0c500c0c458513408518a20300984c0d4641c0940e04c04401030008120038000c03400940803034038040050750b02d02400f140403e080840d80b42c0c01a641c680101d0107004001c07200b0a82a90050001c49280c0d011400f002400400070314107440d40d010300004102c07140340c140501811250065100c50a150400007003003d035250a0441140b00e40d400c1000100088080c48042c1400c511034a900e040e03890440000340207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52781595 1250 52780345 52780363
    0x1c06060c0311193e10090602030d02071b27050402010c02090403021e0d030606020a0203070e180708010b0103110903060103030e04091a0105121c0f21050405 69
    0x182c0c1e000078115410103042d0720100c0f10710740c0e04200d91003031501c500c0134070100001c0e40e10518030001000603028840541041e5845203d280141c41242150011400071109401c15015800c0181c108014001c07240d49a50040d00c01a4041d984016034a40c00c40c0140113080a10350004401ca0708540d00100001c4002c15001403035410b00d0310600042c545a030000b0034806e1a100002c0c410340b070410215051600c2003000d08240c450004c03480007000034082d0380a684400240d034901c0081d0070f091020500a20104a90040513400b0b0000c2003010b0401a8a81650100512280f441c1c4e456100c802c00204042240100030410030000107580340c0514001410340343d401c60244a200b00c2004016200d032400106941101d800d07180c080d880e0500003002802500000d000500040c10040701541e1489455540078100c510840303503503d101e050410616190002e00182c5100151502040849180074102540b90a521480c250a5880c5602412070b4000c44181c03041134000c2da00c20170841001410040800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52782845 1250 52781595 52781627
    0xf2106030f070608010510030e01090c080c04090309030b0402010509090f010509010e010b0304030f1206091b1b080315040c030e0610080c06090409060203040b0406060b040303050405061c06060c03 86
    0x85901e082c84406001c04c0c0040c480d0500400c81d08070350101b0144268030108440030000002d0002004a0514006403041405450002e01505007040040d241c46d00c29001590360644592008500c0c40d1100d0080b02c0d80100181e050150401000b0b5803941e038490032510401c4482500080c81d41400240004407605030080c1e200c64100300010320000c02c0920950f5440f6a0500d002212190541c0303007111400c078084441e004245c02c20344046104802030700f0440408019202c40507c2c00100641296000c4000344c0350880f04a1003c6504007145000004540c081310201c410040c9000450200b000c59000410280010b40c0c0c0324005d211182e004c1c403035540c00000c80035202c0e900c20b041014a6444007c51b011044c0304540004a0750501e44071900203018064110314119124507185c1001d0444090448080326840d141c0b03070002c200f4810f040c081c0c4050701e40580d503290605007818280311803540507554240b520303c1d010354083d00050007409000050001035840c01809441d40c5000740007821000d407844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52784095 1250 52782845 52782853
    0x180b13080c01031e180506070c06050c091804113006040b010501031d070603020306010909060b0403021c050a060209040b06190c0c0305010e0c1003020a090504020f2106030f 76
    0x140c080700084c4c41000c096440080000707a201000440c0350954039080001802c5000d104100580300b60800860341a86000740c1092203640d40b00712503481e0601c6001c11240e40407660000c27a641c0400141c1045070321520030280c285030701c503400002036036070f01703c40c035400c0d2000d181c1d940c1003050380c0e81200b5203c0402e40160f00070600c600307150f0f680d151082414002d40d4105941c441003d50740c0703d050100340c011b0f22090300550b0103007611080010065401141c40078081548101e0002e502021391140604550414070b0700c504003030450342000308211500504440d800041e5902c000810f005102a070551032040c400140c0e103181c00070a2101f919101c00600f4880d100c10301c00d0038440d04002507003000480407450103d0080049180c60910606503400141440d072030048045e10f500000205c491000e10211104d15200d0105c00c421426403086421820000c3c1120b0030420481c240398018207001c0f24a041e41034100911a02181d85c1c1d1000d800a90200d501b0480030b104440c1001d03c41c070107030850290064 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52785345 1250 52784095 52784111
    0x408071502060609010504150b07051501120b0f07030906180201030606090e0a020d1d0703030909050c090d0302071e0311121510090501080c0102071e0303180b13080c0103 75
    0x1380511414810680100e464890b40c2c980000004074a1020b010000291a15a542030422658a54070f40030310000d8034041740000300c0da058041003100941da6002182c1c07161565203940e034002091021303000f01c0a058440f104480041c10a010304914000d0001400165507207600005040d80c0003171340034400344440d85506014003410034000550200102c2c40150b61001a80e03040700081c400c82c8030140202491038100070240b5400300c1d002c02101e000c3d6490300d15442d1111000c408641050f25000c500c0782c420080000181048482c0d29421402030041d54440c40e60b850300c41407c07122034070409100300c40d4810706100f040741d000c05054420800380c40b100035130320407201c82c265141c50f245002010b03401224000740303003030030310390400300150004407014003003075a480000a03901c02d08080302a0141c003c00502003640c0713060304041c00030082522540d00c4a50700e15201542c005404040180102030100404599541450010440c8040c2804450300245c58050101e00b0b200341d44032450304141c181a01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52786595 1250 52785345 52785349
    0xe070c1e060903020d050306010f0509062a10110306041d010c09170c0108040219051008160e030601060e03030f0301170d020c030c120f010c0503060102010e01050c0d05040c0b04080715020606 84
    0x2c440b0ac10301c3c0c2800c1856441ea914000104a0f00076101e10041000d0881e549940b0030302c20b002d600d004241010200c3e81111800242e0f01d05985c444025880100c0007840054814502900b018261400c080c01c0c908043ca590141c20f070944a9502ca01d0000c59126031040050f1784904003a00c0e45201014084c2c04440b1015000034410903015001a11aa90f00c00d01300418190340e0348801e00903c4003c1c820700814800030406095040b00b11105451f00b91005803408010f40944c41ca9194980c0090140003160b003400300c25074041510500003078240c0320500c240380c2040c0220009601a24031090000070a0780d00343d10141c41c02d982141d6000031500709100b100b616850002d40d00c1ca070b61408468aa03140c01d100380c41e043c906506030030411060341c2440c02e15901c2580000003140910020703402802005c00d581401070980c2c0f01a02c0c18009a0400c00c40380e800d038450b0f9030101e40c0040c0319410b038061495a441c0040c0c051b030000e421070561500450700400c86002407001c2411a8002400a401d451401c200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52787845 1250 52786595 52786607
    0xe1512010b030702030f16031d0310201b070506130e0406140a060e18100908130602030c0601092d060b0f03010f0f0e070c1e060903020d05030601 64
    0x1040c09070010002c0085003416000b44150b41c900c1c5078001c030b040d0325441c0202e500e544081255078150b0209030b045031025500307507116429866484000e0002c00c03060360203610000041821400070041c0d010800000403089000c04010010007403141c5481c941810441161400c24229902c4288131b4281000303045440a41500c0050403200240345c61103c681e034509040c0054018198800c0110220380c00b04400f885d02a8840360545c1c00403141c055035661610910b082060a032028082e080d07105155414082144d40c12504100348074800c481e007000300c0e643c0401c240031425004500941c0000c1004000644100304035801094041d00030303c000c000f1107130440255104144940810a881048101001d04030f0f0000ca00903d82004206c0d50f0380420442d850185d0001e00a09140840300000018941c10414003034040d07401c0c400c42c900041c0c8ec3c40405856000300e03445d084900156409581e00400392346841d00c101e0700c1c000d81000c100f044151500074101000301c070203507080c413000740184540359034007107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52789095 1250 52787845 52787849
    0x901120507030605040f0209040b1b0a1b0f05030304050703030e030118080d14012601060302061c06030204020f0a081003050304051002030408030304050307022d1e030604030e151201 80
    0x144000616449604000d0906d1003182806034001141d01c0a010400c41c00c204060300c030b00812041a00c1032400c200e100d003034906c144007a25001401c14102c0b0081281c041d88168002441160800160380b00d5680d4513007503401c00c642c1500c03a500b14000030010306801c145070f0098800210f000304442422405030180c0c0350140d88015000100202d15001a00255400900700c0030183c0c0185046e507948541002c1c0c020102c0200101100440004c0008050140a5142641d40c0144100e003810900722040c94181d0250802c1602c00b40c0303402c2d0000c050303281d40c401400b2041c0c03102d1a40c2d03625118210f020b0a090005064110b80c4e00850000304041200402038600f40d42d0700700c0d010385102500c41002c0f0300d0350003103402284017400000240401c0100000052214500c00c0d9000311100303030302d06840083c0858441640f0450000020001c00701c3c07501c0004008141c41915501d1001e4921801103071610800300e0b0104c010403040260481240b820301c116000c40b4281e000010701d040a8024980248003040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52790345 1250 52789095 52789103
    0x30f0304052713150905060924010905060a0b0a0503040204051501080708070513080c010206090d0516080d0c0c020a270902041e0c080a020c0d08060a12060b090112050703 75
    0x1802c0743c2080001d1240d500d1300a2a4040042c080d100306424040e07100c0905660084103849008081c001890410741051034000300c1041419280e841e0a007114040c01c0010105540441901f40109802220310041c12001c1100c1c0e94003900c0e407030144103000840f44007816035046200c3d0711840030b04070380e8007416990b40404686418101d54a680c001541e09002d5401c500440344040000814481c00c0081c4c41c0510110036402c41d22292202e10500780c948100707500b0328000400801c5105201d0300640400300c1e003944038a9035913182880290f0480103c5e001182050300144184010f441545048003802020b4004a090035910039642c0c00e0b5001407401c2032200c12010b0b07440b4a00c200a40d501c69200c62003102d1003440c100790282d8201d00c1c100003440008120710200e09000046403d6022520940f640341c0031060060400020009080d00c04000040034258890503126000c10b0340302201c0c4584803054851603001c03038100000d1781007100548050304526179890004003108080b49000983c1c004032500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52791595 1250 52790345 52790371
    0xc0209040201030f1803020c0312030603060f060324090d050310030b09030c0a0b0403080f010302060403080c010605130b01020606030a0b04080a02011b11010b0306010308030a0209030705030f03040527 88
    0x2440c840d107009809104640340c05400781c0c2d1746035002c1c541c02045035880c1c038108405980d6104800d042da944d650009940098066000a00040345c00d5001100745802c00300040480303004030302080518400c104402c0c1c3c0c66082c1c00e0208180088082d0401516000701150308009085181c4414076400140d001d2201805007a284030204031404414401c88540c00700020661300c2d000d5150620180c404800d880c02c80000d40b1034000642500c0c920310249051700e50082c109031425245866202c05070304501240d56080d5640d060000711952042d1481c0d548030010440814610403510001e420090000c00c01c0303003e5001250341000207010b0700c000e90781c02640440000e848960700c0300c040f4010700c0308403200c042031200c02240c0d1004940000402c080c1c1d4907050000e01c40211401d081c03548582c004e210003400b0140a20200e45007044580142c01e00d82405000c542c0040c0e55100041c0c50403c25042002e559003001a040c401410700d04041c0701c14149600c4070116007002e054110074041c2d0010002140002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52792845 1250 52791595 52791611
    0x601080c131104031b080606030303010902070204020d1a0a0614091012020a1205010512120a030b180f06011107061209060f050a2301031101050f0a090602010501060c020904020103 79
    0x1c40d800301d0011101056100c0e1075a40324903110030541c2050700301c008900c140f080300150a090001c1c0c250322a10000e0051402d50346055208006504154412680550244080c616504940c0702d020694042989a02c2019402d2002d000140d182c0e40c1005042044a41c403504275440792400301c1d02c1144050703403c0303014880406001c85414440e0007014048a00019202e440780b5400070440380c0c1859140020400c590307980081040a1035820712000d120b0304101d500031802408180940000d00b001e04002c40c459074100700282000718200c04010b0042424400d00140320849800c50b03a1001081c2081d41e1207600c014841640c59019100380ea00700030300c0304658050000700790880c000c0e1543c040f038184020790038a07000e1f00141800b21003d0384494940f103000140c0a00001c0800130358281505081c0c000e900f1034441307030840c0c90310a04081c1440740c20422032910a060000410210250742d13209507600d418084003d003910810b07404441001181000d4102691303600340d40303d8105609003000130f0100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52794095 1250 52792845 52792879
    0x4180b040210110f030301060f050403030206070305040804080111070605060a0303021f060e07020c01020111090d15020c0a140d0c020109060e03070b0c010b040518030301150216060f110601080c 85
    0x280010340c14240c1c2e03004803440444d03641000409103050b50304c1e6444000c41c0ca1032401c0701700c400740035a01c80500180d1244010803d0507020b44e100c42e070001d014103802c81c0b8242d2161401400d5800903017001001c14000100c81d0306201c2c1c14864240c00c0202294604080c92131601d000b95100117000000503010142d4901d92110121680160024198075482e0800ca01c3c01c2e2001a44038408080d025016500380f041032040c0c0b00400c130848410b00310040a114112a454507198000240410305044082c0d003000b400c040141c0c200303c1101401d1068550191081040e030709035007000c0382200300f401408281084900140e03002804070003550340358508100c00b0782031000006e240019030750100460301800907180700d9116042d00060080141074805000da078170f42061a1482202030348201405405c02e000610a6000580ea941012541403040b0788001c3d10b80b81e8030b106400704580c40000130603820350092034807030b400c20781c0444d00d4080b9030058809507140c811840d440b8896014031904ca045000c01c02c4204d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52795345 1250 52794095 52794107
    0x60f070b091c0f02210d020702010201140c1903110711041e0507030c0813020d03020a06020f030103030305010e25050f0d0507020105060a080703080901030b120c04180b040210 77
    0x551403640100c1c00b80d4102d42024090500b003c80b0380d00180164020104403180c9461074111901c40e81c01e0b414904902c5028034002504482c1c012411035480d10b0404881c082d40d044d00c07034000c22042e03000d9581c9000c0300300c030500700b00342e05a80e8505040c24440490356001c208402e0b0b8032425000880e514140c25290b0003d001440080f00303811a46500c050055600591039106504c0707040152000c10040a0400e41510fa455040b83c811307000c010350003900700040c00d1124007590840d02c04c0c0103c5141d200c00343d8a140c02e07600f2030068440c20410200040090540c58010b85004103801315580e01682070200008a5094a0300c04100c440d580c00452890403e1140044440d603084440c00103803101172040640010703042c19aa9480190b003080081000340c9005203200c0e0444503550010860103282d0742c0c0d02c03507554000c0e2202d41d041c5a034030740c06c0300120b4031442c26890301e040f00c050140421000300010072007203401446a9141c07005903c4041400290b40190503038206030112400c0105844145c01202c0c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52796595 1250 52795345 52795363
    0x50901031a0604141504060f0b07020d0309120609020a0b1204230f0106050307051009060f030f090f02010807050306130504020303070f1a0105010503041e140d0906030b060f070b09 79
    0x4280d0011342003200503000c0d08080030f4540d60460341070010680e0780c0140c99104500d03004043c00b2000030041c0000501e40b1440074880c1070305c6030078540d80d5141e81c3c170078208601803542c509860f41511103042604528100d20f004018042031100d003414449418809416400020801000340848020300340410030030070400302c0700c16143ca04859100c084c0c0c41c1c0d0103010f003082d8440c2500910400d20003055524281010100320403d503039842d1a07852808004680142801c500c0b0300c1415614040559004607500034144c9841c0103200b00400b003070f22440010a51000107010170100f1401384240804c50b03480c608442e0b08401405c070003080a481c0d83c000030b0f0540c4140b180c001e0807070140000742ea0801c03101d0a03280200450a403040c101c40e0fa42d074001540c041c40100c5000b420b50800611440c40aa81e8030400c20300e50b40280f01c0c0c121540141040540f070010980040b10100c0d0490508000c025454051000c00c0c0d030041d100c280c20000030b03d0902030540207442004001c94204800201d00900412040b00303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52797845 1250 52796595 52796621
    0xc030f021609020c0c030c100c06090507030305030f100303090515090d0f17090f040e0c040e01150609050d170c0a0602040311010f090501140f04090203060406050901031a0604 77
    0x3036482d81c0d071400c00d0096000301030541450051488089103840c0118186440307203005840f201c001500520100c866249003802190f80316522031900c0f020032005c01c82c1c440075500c683c481a5803820425606105620001c0c10010050f1034840213000103030b0b018080200305da00c03d407040726070480c0001d8014120702075040840d07082800c403001c410030321484168000816001f003945030411a514030003200b262007480d031015080180404003c6483c10705a200f904022105000e0b1001d0841001c0003d0590780403845100240e911071032107143e506a00e07202d800084c0043d0410740c04803032030310010031018141100050607048007040344881c04038124003200c20b000014010b4621407441c03460100d00941103404240c2c1d01300c2c084c4024401e42e500407003c01808211944400c002649402c004554401040c0025407400c401804645941c654034006000034142088001da02c0303203040024001200c07001d03400544281402001000450410300100300f4180c5000700b90b0b01c07295248000309000d8040609100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52799095 1250 52797845 52797883
    0x30e07171e030f030f0a0e01020a0e09060604050a0911090a181a1f050f130509090102070b0a09020a0b0301030803070e0909100b12071205070e01060c030f02 69
    0x2450300c500031034210100c0d035181d6008401604115141a0360b0301920060209101040010604890034041d02c168004000c031404240040d045d1102800e90b0070a4943c000480d200c076500010525040d02c00da6030000e000d40c1c01905051030000021803244d41e510441c510281e650315139003000410b901c100c90440320090101321100d60350b070101940c030840700b1400001c1e903072500007a005510038003600502d038802d008201d82150000c00824040104408220710144101081101140c150100140800031045a03050b54424508400d001c41d0000c01000741c4400c0c0d20411508001400c1d031815960000b9507481e0000b490042031002c140c100c0764035082075000003404000001003180f0400298842c5002c1d5803020006d1320018184040100d0958032188030350400d091424030800d95a01440905000418a0048408a0500c41e041c08096080350015005920920080c082c04000c660010102001c850700e480d0714086009019910680d40141000001291896018801c000d6800312500d000955 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52800345 1250 52799095 52799129
    0x610110a0f080304050106050103090305071401060e09160e060109060f02121b010e12030c0904020d0203040c030302160e061302070b09030a1202041203031d0109080d05060f0f01030e07 81
    0x1001d600c1c0c100304c60807603180d070800c0804545944030707004800300c1035851345030303030741485030940e1540c00080d50410303002169940d580b00007a00c80c202840b8180945121405031420420441d813203448070340c454107c411000110f0080c1701003070741d010449000f101c907940380502c044000050128200b800320380e400b50000c80d02103014065100301083c05a101c0070709800802118440454040e00c2e0540c0000c95400c0c00c2040c4006103400080d00f00811000000400c01481e000e601d9440404981090b02e0503109440101070034010581c04224110110f1110340c071011740030349881091000b81500420300d074040c4545103000e01403a0300740d40566003035541c055081c44052400030900b507507a030085c03101d040014828000c0c80b01010a140300304ca042d1003c0c03c0c2004407410b8140c5040c0c0240000c110280c4091001d104407001c0c1c81c0c0c080c8181041d042c4544002c40e1366501b00c1214a050700c0b00a4500c81c850780c2c020706060301e280e907401900c03200403000f0300b1701044c196142d80d5414108041640300d000c4801116601c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52801595 1250 52800345 52800353
    0x3040201051c020306040e0d091406070f0b07090b13140f060703031a040903051602011e0306050f09010e0601080a02040f060908010e011503080f07080414030709050610110a0f 77
    0x144d03214241c29136042004120000c00e040d42c074000c070000300b004901030000502107004240024900c02c1c10141005190990603541e004032020b00480075601554100e042c0003016030300001050040440c428001e0030b00c5400c140104405c170f110310030205682c402004a00c8580c031190800d1507400302c010000740d16056142030103009400c640440390100d10280140d412149024403500007003a4059031035034101041601100861181510180d0520405074403020030894500d00402410142da607002c41c440f441d040030b11003600000b560031442088030000500441038819601c03540b005d001d1804a5241d110400e14500910549d08030140ba1203800201040080c1c10031540400c846a250081081e00d441d908402d08940101000c2c1504c110f03e8802000410303c0e01c0044d060900c1c0412081c0d140112503a44c1e5100d640c025070156044444411110009142c1481480300a042d0010180030342e00c1c00300c000888144004030020180100b001c50a003a6107805c0244a00c00e6501c0320784007006400b5170070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52802845 1250 52801595 52801597
    0x306090f050703050601031a010e03210406020606010e01080a050709080d0509030606091005010c03110601230111060a1d0615031903020303070f11100609180c0b03040201051c02 78
    0x19418007013814400807030043e502c86d1140c800c044101d22650406031a66000444014940180329a4184180341c42044001000424111410248202c8a590b545496000303420550b005005074180440c04107824542d0341c004411540c44008182d0004207640c547c18155000c0c080350304100c0031440b0b2181340c007900395081030041084000c00c504072089591880c08000981c3c130304503003100800c0e800b10700410565000e00c00b007450b0a8400d081108905010515451400c07500360301190003d850130400038030f861202130000c12001d40c20310f440100c0203004a0780d20340d2a0b00103061000d50b10303918901d1240c180c00302e4401c8174840100c9016074007141060140e042105c900004401e02c40d0152441a103104200122603805a03607168000c0c0d82995143c0324241c0703002225604940a10040000002c07034600306104610a5602c4007100281c403d007000d07140021940385080281022032070030080c801140c0e0680003403045070b41c1c841606650741e450380b00495080c0104400141d0301400503822400242c503e070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52804095 1250 52802845 52802851
    0x60303050c100e0d030c170906011d04110108090703050102030405030a08010e01060f0e010c0b0403020d0212181e0303030c030405010c1e030906150f0918170304030306090f05 77
    0x21103a040940b62402ca044500e61024403040380d0150300c40112040c02500640c0491185082010710100c00c11030b02d0407100380850f03203201c658100c0710062000c2184003080c076071840600d1003410342c1440e09a441003010207100d043d540c18000c40200090746143c0c00c1000502550b8000300964990030b0501c1c1c038035940e800c523900310801b05280000124103c000d4058030340c121000780c1c1d100100d80030000d1003540c00c0d5001c0107141e41082840c40244021902103508030307000b24420f03801817480030f0021300e000f030500700b880124180145080001003814a03508030501d0b10007070210f5202c2a02d2100b090020707906003284a4154042c0004820043c949203081c0c007561046026800130f01003284520310840d12001c0c5011120000a1001c0040c8600c4d8071035803003052a0b40c411440000e43c2242c3c1129802401d006038440c121a850003c8103000c00042070141c1500c1c001e201c000c2203849410b0783d0356100f0203a51178040310904100170001030305251007500f0041c010080c082c4c0070001c1da034034110004040c100171 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52805345 1250 52804095 52804117
    0x40c09020409270c060305040c050901080309010305070f020706081e1603060e10060302031003021c02040b0306090c0d050c15040302040b1e0609040902060a0c02030d11070e090a0606030305 83
    0xc0d000d044401c00b44500390f203030010750180300b00501c0780c101032040c0c00409000c0c0040e10b0400907154040b509865a44019020303240c440001c584481600000409130f40b4020001e80030842240e40314005150001142000c1d1011810504181e0741c0d23090307198418450703000c2852400c0c00980280b060303010a43c0301884a1488a0780c4c1803103280d485240c0b1018800064804030075014000c0c1c420003c0c144aa8040c40d04515600104503010b541c94000560410318101c4000d0701800c640d51160842c541403190000c500c8017038015002a2401a9400d9225005a243d4030300803115480c4040410905000004503d01c004014000840030711120161542203804200c3c0580d203011120300003460000c0c100c50402c8a60204884001c2e00f0005100607900a0500c07190090703124102c40c6d00580c0d94802074241c0208940e90340045a005004041c40d0003003040ca810148654031308001130b01c0c000170038540c0030b0340c41845041c0d0b4907464045001e481c0c440c10b41009416145040c03404010180c1c4000140261440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52806595 1250 52805345 52805381
    0x3061608010902030403020d0e210c0109120f0303020a0203040e070203030a05090313090c121e050c0301080604080306280e090c0310050a022506050f1509040c09020409 74
    0x2103400b2201248816540500964000610350300c1c054406c5014103018180038001c0429044608015840c146113282c00d08055040544a58a2964013143c0500100070180001c0740b070030440d07111140c60001c00f8002078101070b000216101c0444c0200201d50081403408002035091518400c000d449800556000c121142401c011031032203400007054409000c103417031018480f54546414400105a99200c20050001c0d6104070b90850b4517610845020f464000480e1400d00d40c184800c0c0100d031001000c0d02428070050005001c940c00001d559a44a039002021a5981e155640010700034070204d06491094188951a4030f5081d00502003801200c210304101002c40d290112800c6d00d070003651032041d803d540000500301c01101c0c40c0d00402d0300300c4000d04d001131a040c01101a403110044d1819007400c10b80118004404000d110b204040e4071200303088000c412814840310900e1110850000c407403085400e000400c0521010749400703002441d816404550ba1582e03292040040c0c1110444d40301c41600c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52807845 1250 52806595 52806599
    0x615030608060f0709080d0203032203050f070c180e070608090a0206131203090612050103030e0f010215090f0601051002120a090b0403061b03060e01090c0302090306160801 76
    0x4000d000d600c040d6000540941890350720002040c9894500611a1040094150300000d101c6e10510000781c0d0480550702035543d03403a003665070100c0041a40b11803074280440c0c007214008a0351160640b52182010622a44c0d210032505140e000c1d01600e4000c441003000040b000c0c8201c8071150711000d022202801615442540c4090958950320102d464803299040119003400501d0001d0007410440c003811900d00005071209100300080c084400c04401103840e80000f84400383d00184100781d41e0b101180140001d60460740d00a15250b80000014094000c07014204090b070300a11030122131840c0d10009200915180d42c05035950008203546c4089401944004211411f113144800002c5402d9001002040748401d91003155511510f40307041006084a004509240410010300055010b56404508520310b148a603007104200111a01030520300301c401c0004d40c00302000903044601400c0c001500b11032413282074010b88280c0c0a007590500540040041d00c0700202c1d170510106001c6e90b41c021b25aa = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52809095 1250 52807845 52807847
    0x70c0b06090c03060d0609050a0b010501090e090703020409030318110a050f0306131406010605070b0105042a0e04020408030a0906020a0507050d020f0306070e100302090114090604030b0108010615 86
    0x401c00e540411039180304000144181c10a0086005130b207100d0706e00021404a2134440c1414012400406c4881000340c2004000644e402419400504440924030803a4280305a100303940781824400280600e840e052114241402540075050240c0c420910420416082c9001d00c200c404e52000244203100010011a0382e0038406032a441a482c080c1c01014140c1b5101c400c80001003100b40101c2c2c20003944a0000080310090000030300901441d100da030b031103001c076141104840701e05810990141e80380080207800348103003000540b10520b03022000452500681f108071010820545410b40182c000500050300d101c000004101702051643c2c0c0c090b0807500c40000302d845510301c04000d0016448084284420b01c0d240e034100c894580300070b00c813143c40b804a802013810050105c4409001c1a00d138100008141440031100700c80459a2904503d03185001001804000080c0010a5602000b080e0704030107443e000211005180c0004040610350f0352028094040c1c800382c024181503c80d10050102d0035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52810345 1250 52809095 52809109
    0xa171908040c0902090a091a0607030c06140601050304020118050411070c060201020304030804080a120f2a0203180301061a0a02070e010b040b030403020c0406080f0708120a120e06070c0b06 83
    0x6080018005100355180650387c00141406042d05003010403a01e6a100d12640d446004015152103030300e504a440032a81084c0c2e04507420840001054040700042000c5a0f03031120440e0307409542400e0400c0e074001403118081c034880140e0095a00146080500342c15000c80c1c1002d0000306100b251300140031501c40d28128283d000c180c4004000c5042c803400700e00001d01740f20240c03c1c880c00e80d01c1c100001c40c0c00f0604d268140c4004180034a0400e942e00c0c01c0484421103404028190341c0b000240c50307003280816000035500d20402a0007060340c4c0f030803401081141e03000e402c0b80c0024641250413000c081506c03110309990368040d00c2400702610520302c000684144442c1160304955082c0f030524180f51811440700078a91000f08120708500540d841c800c11b640e203601c03035a805451076100401310040108410ba1420301c003a081082c00758400040a404606c2400460711200c83c00c3c60441d20403203109280c0e201030401e031124807007680115010020f042c0d601a01e0b4074120b80c040c8460b4500d40d2503c2040c0008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52811595 1250 52810345 52810357
    0x501051503120d0207060203040f020f010e010f030b15030f1603110a0309021c0b09010b0d0203032a0312190b01020604030509010e0a1502010e0d020a171908040c0902 73
    0x141e00401c1d0302e0080c1004034030280208400041001d8a00152540c405040b03a01c00c4400310345d0004505c05050a41c01d05030040158848203080180d51100090300280c480211403403242c08146d2503414010070354079001c03100d02c200e00c48030407405d482e410312480c03841085000301c1d5600d440800c0e8003031100ea00b43c403d010340741c000600c128640d0b203484c51125080300030b009980b1040e0781103522681c04280d1158011000c00809000b2607117102e1031305081180c182902e44080308903110300c9504403a08050381c0c0202c00c980d50340c0e185516007a003c101ca10807600c2c0305044140d801d40d40e030001280503c148140f4a24017482024401c0101403115240402c950448010280250042e8003441c0080c0000340940c1c02050b88200504100d648a02500300040712065190040041568401d0341d070380c00b1035024018003103650350310401307803004400c00d9000035511031304050090a180e407602550b10420500380111005081e5850b18035401345803803900541520419101102c4004440d08001041c406601c00d82b10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52812845 1250 52811595 52811599
    0x426070f0303030f020405060a09050907020c0604050607030e03100906051012030806010210180b010f120308061c030804020f0a1d06030304090c08071101021206040203042102030705010515 83
    0x340362419510110b00415881c12243d4035603608120200705955040c010705000e0b0301c02e58404000074205028444640c03000745c0035030305650258041520f2541c52009640c01d444050f100c140c0c40340307200d0070200c882d1081030748410741500614804076801000c0e6006188100c0c0521000c1c400d548031100d40a4149529101c1c1800d0240d0003143d520002c1c1c4210015a00900144102e522100e9408104000c807040032642520b9900c803c0b000c00c04004211254a00510343d11004d8000c10b458046a18102a203020004007000807840004089650325007007984048048040b5280510080c500908000d01c01e8505901c14800300002c1d40840c988030140300152261000c403c20b28520702407444407914009008940e15010900c400303d40d8002621510119244d1036a0782100c6080545020300009881954510141d004100c00c084044240e1455500140c09036001a40d943c5c450402000041a401030403242c042e907140e0200e16140e0000103801501d004070000c005a407644806251900c0e500d1091075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52814095 1250 52812845 52812869
    0x60507030e0904030c0c06020109150501081f0908040b04080609010c0f0c02060c06150909070f0510120f0203070e030102030f0403110a12020a030306082a06090402042607 75
    0x80c40d42c10610701c41030f0450f120b801c00300b00c10407041c4d130b9145451520341c21010042c0e548030030b80014040e07082203190303514520a00c1042a54180b464654850348860745001070350303000d01c0040000000e654820301c6a19040b9000a0f1160f484403e011400ea009220303140e1248551800301e0304507801031160503805030140c2c5400e400f5840507802644d030f400213840140e03440841400f180104900600c4454441d4170040c1d119081b50605800f008016040a08100305540c000c06003840411901c0c0c6102c0143ca5046841948501010310226004200350764160246400e0032a0110109095000707140a11500d1b201c00170104040c0781410300305d00003251015a010880b02c0803901003801b41c50408042c002881c00e40701b40e003456807100d101e8021303000c188800592000c1d010506150740f610529014150744009807880c1d051b121600c8951040c1c007030744280745040c22403d0b424560398040c21104000c10152040d0b407615a1a58a00984001885400030000311111120b601d070201007420300c1941d6580701d0707107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52815345 1250 52814095 52814117
    0x140103060602152710050a0513030203030408031b0a0804030207120b010e060423090606120c010f1b030801140a0308030411030a140309130c050f0d0b091f06050703 72
    0x84e0035100708001145200c102941c51880150180084003000e50001d001150500340100303502c0c2120802404004000049400000000d40c0401206c0e042604206085d45940343e080b070589481c00009a0588004c00003d005100b0503080030ba014411402502920003040d40c0714040d01c049904500d0007049480182c0050050f5019440b0745904413802800000702070643d610300d14007030303107214030b211041d25101700410143c1002008000c0e0700171416100b503400c18009008165403247c143c0300c0c403070610142d003c03011440b500c24a0310403250114001d0002000e101800c01a080394401e02a120302c12030051101012400c14642c00c0080700d0b800425a80713550345585810179601d01c0140b000d903050140c4100413000c9511140c50541103210b030405955190307081d5041000a4182c1482c4075091401c2904c902c0c541c1d07400ca0306035180d8982c0c821102d6a28010013140c54000d000081c03803203a201010b0390902021041c410020210300c2055000e1041e007988400c001c4e501406510b80c004d0010b1064140307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52816595 1250 52815345 52815361
    0xb0a0501030f090204050c120a110a0c020f1009080106120c0308030c070203010f0605040506090402150c070b03100602150108060103030c080c010e0d090e060f010c050708010614010306060215 84
    0x8199804501c081c0083c42201c0b030360004058800603641c0f86d0b030407030002c00c030b103070000301924803060300999010000c00100540c0550040b69018640c2c983c0203102d0501c514406644801c2084c41c0d24490080880d1101d43c10710001900c0076510b0700030f040c1c9643c03a01c0c2c3c0209825520200503156541c03c10744645040386590346408084e48001c001041d0140d09001500068600b4014040c0492401c5000300d0240d00300300078801101d90081059110310b807507000f40000368440011340700ca07041c964601641c0d07501046424510780400342d4026024070b0703400401c00026400c408100e41c182c60541d400d40b03000000015521080300c90a02a05442d9000a401000060b00413071034009618883c020003403d00d000b07448810300b16411003480340c000d50080d504e8048010f130700c070752003202404809010700800c0c1410703030119440000d1802460b062000c042845c4003031001c100810001040108001c0c00096160395000b00c40d051010042e5000c2802c00303202050403400030941180418112580148568800b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52817845 1250 52816595 52816601
    0x702010e160308160c140f0409240b0307081e07030305030c0304060e0a030206061201060e0f0c040e01030c030201140a0f0f0509060406051305010c030c260d0f050a0b0a050103 77
    0x1280342404500701101c0400a0001c0805d00c0080c0030049440e85d0490001003403010200242584d5031140b0716003025a40001c01168101ca020040201015091050044984000d217107608001d941407240c0203000595101c00260a01c002d01e50300f4000340c03d8511b5a1605580d45c07440e02008011440c28000207180f92990030146900c40d00400c1c4c0070441d180f201e002d59050a016480c2a001600442d0030485503041541808014450302002004000d15181d2409551070015200c980000f00c11070101e04084000760070346d00a4220390000020a50b9a49410074030000c152200b00d0100740541210f82c1c0b110241420744610182c503407160250100c1900c0100d8164600c4000481844802d1200f41c10f240c0710304001d440038004070345030346079a040b0703a411440c4c2140681c0d11050400c18142c02900000ea4050846003540da031196003914a00403c1c00484055041d44038452901c40001c00d40c103103006003d03000103601d5036440c0010080b80e2038894a100945141203c896007201d8100030030000340d4441d40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52819095 1250 52817845 52817857
    0x405240607080c100506030316081b071503050903030601090b030603010f0c03020913060503070b0309070306020a0509130e060105010f0e150702100c1e0201050d0908030702010e160308 81
    0x4021601d001820740d5408000d410001089180394481405018150740c1881219044182100110b080152841107004051000003005000480100c0d800f15030f10102d0784030360781c0d0010400907980400e803544440d403880160714145900003810071003c25071710369020048074050401a550750504904000b0b001066500c0502042e800d0b40d42c2d41c2400e500c50116100d9060710310b015035800b41e5500f03d0701c420402d04080b40080010b08501d80a010002650300107440341c00c0762001d4204540f070b907444510003414203296a0001e0007890000941c040555400001460854421034902c0f40f01d6880200003403c4a043c94900304844d030040b8018844d40d0302614400d034810341103140490f0300341c50340d0700840c0800380780e410103d490100100d005c07400c52405d51041440090f0514080c07a544480340c0305c184403200c20103441c4e11a0650300b14240190b900c02c0089030601802e07860300344107148481c900b10010798421683d030401540f8041c070f9020b11034400310b0078090320307e1038915040c10207041d9154048103900503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 52820345 1250 52819095 52819099
    0x1061b030c080702120106060e03030c030306090603030705060a0209120c101d030f0706110d0203030109090c05030a14060705041206050a0b030a060203040615060c140c0d0b1005040524 81
    0x18480701c4010f85d070700c22074110502c5100c0e0001c030f8000d20b00113020744079403004c8075081d00c6500140070034044508000240c80c3c0c054402c0380c40040380c1d12210080390131071040700b81c082d10754000e002c1000104441d50b0001c2000800607160b0900084410b86007503283c9424100389a440150b00e0040780219100c1d25020501003149060060042034603030003e03244c804ca80720305000d1608070010070080942c010030340100c085c040001521441d030184500039240e11050044500e059900d00700700b402d00882c5128803000e0300c40601121072811b01400d2118590240342c43d1040144114000600d220307109200340e40440e488101e001604060359038a150113403400a240c140c0b4181c0e1030002c60202d0398200700d4100b0750b9006040050f5242031034141241654000501c0d02043c110504041140170380c4500c403040711035000b90040c07100804106405033860600a40310341d02c81060148641405075071010b46011342d04140050918a81c2c81003408159402240c400e041c03145e0008038581a840c0700c0310307001209140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 52821595 1250 52820345 52820347
    0xa12031706040f0603050609010e010209210709020301060e030d0302040609050405040206090a170d0804030504060f031506050a11070303080c0304060b060d020d0b151905040504060801050f01061b030c08 89
    0x740202e101100c4e016807040d101a03101c1f005200ca40b03502071103600029082000203500e05203110010035042c800346600e40700300aa41032070b00048180d0500540c00036001c0c2110555603540e480300018800f4550482180c468021100d02c01c2a440c000d1003140e089421585444406600d1301e400c00c00140f9005006130b070040e40c10016580260340301c000303a4000c0c00036200d81c191a8041d50f11200c1c50100c103da2010b050120800500004c00e400600f982d045030010703d00002e100000820440203000013074a407a03150b03e07084070081841c40c0c00c4005450080c1030b60b610050080310040d141a9185001d20000e0702184412000c210300301d50080c001c41c2d001303019074004103460700d4807000305200b603000e0840c0d80380c0343e0b50110f81c0c10507551260150414090040343c0b075003440d001082c40e07080280309081100d09014100003000c0c03021402030040d5030080c9002041002416620f001c0c0d18041e001c102e68004010061a001050842c000d0054210710b40c03c10001d00218411550145d031418041e03a805d407028a8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 52822845 1250 52821595 52821611
    0x91209040b12011d010203010f0905090f01090305040501030c08012301090806010f0e06060a0f0e03120f0c010507110309040b1c0609021309030503060d0c0317090a1203170604 77
    0x21218999440c0c030701c21900014005030240d0b100740c07038031184c41312601280e4010001002007040c0301c49110103880c144000003d0689039008074500d4801000510b0302c165081404800c10300d50001c01400c1141d8080e2030500221b5120f2100312051142401540c030a03030340510760b903048400c5050102e4031240c410304085a041e916418003030b01e062400da0214060130301c1c0d00e90500000e00100e002c0368200c407041d40c4c3e090a0039030303a0b440a4032803554284401c0030400036900c0c218055508100e005103111540100da543c03803083c5119620a5440052080801d40c289404a03d07030071b00c01c5941c81a6072007000041c5042414000810020307204845010754490380e146a40c00300048401c100c6a003182c443d00001540715480c0c4107000888042402e6031101d9450030750034001003900442181d0703100c841184c4c6a000d0f035600e8600240204440e4001501c14003840b0b0502407201c030b8150007042810412074010002c944e0316841c0425a03000004002c0c000b4100c540b402c10010403032040541c0107d80248040b581407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 52824095 1250 52822845 52822849
    0x20a0803041205070905060607060e01020d0f050402040c0905060d0c02010621031806091a04030b040b04030914010903030302090a08031813020705030a050c010e06070c030f08091209040b 82
    0x34009402001400b1401100c000401600b000200f000304445a130900c00e030314010000441501500601401c8507407a100c042c03510280a50454003600c0c2061410070941c000304050740c000305000c5030101e000c0ea00d09140070750180c0c044d01c00381040303c000500440c0b81080c4980040301500307030302c00d00c1410f540d20350f0008503070b101032400c0c07400b10040303440403c88601c0024140184240c0d45200c1c0c0698020003a081030003000d41c400c11074015100ca44c43c143d1042c04001098900510030399002411501e00881408204020b002ca658041d60295a17036018080d181c0e04c1400c0450a049403150100c0d140140400009001e074020745a851001001481c00c1d5a890000030305507802894113881440c2e1701d401c010714524160505c0040501410400c608001d0769582d196680d105600d0450188600803554dc0342c40303002500280d0b80d442c540015280301d4109002c0180543d204150106c0204003d400b07258013861003031586c10311442c90b240082401c5200004904100d40c0880c1c001c80d08545c07192040d6910b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 52825345 1250 52824095 52824097
    0xa020a0e040b09061c05010c1106160801050f0604030c0b0405100503010e0f07020a0b0108030a030c0207050a030204020723100608030c101503210305160503040b060a05091303080a090b13020a0803 86
    0x4805981ca45050b600c072740720450b03070030300400801e070445403002e0710300c160304250780b0603109030644100b600c100d864200302c1000607009001d02d90008250001121010408a1058000d00100c410903141d15135042d01194080c1d400d07003c00d0041c0b041c03001e1701c4400035800440c084510340e0060040c1c01503038141d40c20b43e1540034200200343c00800740f0b0b6000207080303800d080d490700c2940b0082c5040d00c05002c1c560b00f410005000d518041c80060310840c0c000c50400e090040312407502c91501610426042c845413041d40c110388a051490110103c1d5280c84000108050084101d40c00c1410060186c1280900c811000000b41100101c505240c400301c1000310000c0d040507510703805080d4803a01c44c0750310040804002d040da20010052103003000484e10b0740b241c05400c001a01d0b00030368001d0b81884036555080205081c02c4455214680c041044c1007880404010b00c00c100e0b003264082d65400420341d6a09003c1c10556000f008000c040c10700d100c0009290030501040c00369404d20043c690020607076280030b100d01d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 52826595 1250 52825345 52825361
    0x30303070f08280504030e0a080a0c090603081b0309030d020601360c0507150e060c04080304030f0203100504240c1202031306050a020a0e040b09061c0501 68
    0x460030409208205580100e8907980c000f181c001e40100004503460507a0300890320300c0c05100e0b440d803140b0110302054016000b0300d40040002e41004e809660b18000240c0e91660031a0603186001034040114106160b809103106494025900600d000322101c0d84101c1280031640008150100744401c0c03007166030520001c17200070035a40c000e003010750505980c684400c0d4110703843d0030720f4949444a5448070312404100182e541040100150f01580d800040d81c0a200e4a04004d0220810111084802e03240d58400c4984d10444400c5803210350701c0006014091045020f042013550003070001f00009855a505000c07001d10150035900e00941a50b070345404d0324010f0b2030445400401248050b40c541400d030403020982c00d483c02c140802524288c026260007051002c15907401c1d00007000403415151465046901c030340c4a10204000d241c8502c0c01c0009411803503450380020805195240c0914050055007550000102254002d07200c90041000c5090b00040304007c44e05201d8400b40414000c2c0b082440f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 52827845 1250 52826595 52826597
    0x301020327010218010c0501090218010312080103020307140301020906070501020a0f03140105121e0d090512070b210411281a0d020d02091903030f030906020903030307 74
    0x5000e000c05444048154036060740c061a88140704460082400e64403000030f400d800c0c02c0002ca500d0b01400c0c014050114031034042e4000516400b002c626910a08080e4100c80c011518000030910001c02180e440d44203120103507055100c079509019181d0f440c1803e10050000400042c6030102110128105802865058803544d60108150f2481303a040b00c024410030006140421101e44200d00007008100103000c0c250040c45c4040c5e41c0070f60791200b044119003c0e86216011440c4103120455035584031a0300d0203020010700c100a0010380c90410210520031000341c54041d0a000c0d042020161003500010f00824001c00d02407208002c80341120101c0740a64000e8a140c0c582c512440280410400d00c01d06449000b0008028028100c07070041c8181d05a0384540c002400501307009523010b0302802004984000c1a02c001164101c0710044d0b4009d100070700b01a180e60014a03624081c80646115611000e001300d030718a1006031a0503c02ea001061051140e000142400c4460000c80d2441d001100d03010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 52829095 1250 52827845 52827871
    0x10603050705030c01141c02090607060603060c090303020a06051017030a031103130308090c03010c08150904170a0903120206060f040608191a0403051306020601150e01020c03010203 80
    0x311071820244818400c201c1c0a091000503040c0c46c620607000e40c440c44400040c04e1031440c40602d900c4040c0c0e011116040c074010310550321980f50b410f04d4402010507203c12112585803d072a4850540118200801c49815030040c10089030b40341c41d0f04002d440c0041c0941401000704402007108501d110b44440c0b8402f90308000c50f241c00000c94090100c4a141044d140c062409008100c0544071007054013642a900d843c10100c2520303001c40440c40e0402406e00b05034075500f40b06044c450180c1c40302c409889800410000020100f10341c1c00d0200e40041900c000e003120314a1454a091510600004c2c0782240880c6080380900342d9948411419000b00c0c0070400040c0c201005200b120b16000c4044503140000311010000a4035003561251350301d81100c060b10444858800742400d05c80c1900700740c8404903c0c0618400c2a24061600508541c4a0507458042518612021811500c0000c00d0790583d400c4243c4501e00003000c41c01524055106400315045101700d800318161524280043d60058441640d20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 52830345 1250 52829095 52829099
    0x5030406060b03010b09040c20160506090901050108130206030f010e0a06060f0c0f05070305070302130e070b1614030307030e0604020609060c16080319030c080a0e0106080106030507 80
    0x424103039401e982c40603042da1424001030100c50511821520b40070f40440307000071b078054100c0003501d43c0d40703040007090070103294403168181441c00440c007000f100c8500d0304134101041d21403003000658050007a00030780041e034060040c0025405000d101b80c00c080030391440e47c0c0300c20883d40081c0c007584c0111152010403c21000420a01d00781c1200c4130f41100e04078030305220700ca041c03201c020541c80d02514640c042000015503541403100034400103204517000800e44501948030b003401560f803c61840124003401b80c034030011204031002d204c2e0406442c1150082d124044c50b000700c0300d030150007900380a50030b014151a407c002a412540002034000800d024646a203403842c809070442e02d00200410f01504020108001640c0f014116400118100c4038152514112103080e440c004c0b40350ba88951504600c00c0119421000002501134060100908510904480d208400348c80700ca80009021503000c40101c2c4500c90283c100c1e0051800e00400016601c1d510410182929556071064615070018402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 52831595 1250 52830345 52830353
    0x170c0708011b0e0306040b0a050612070305011a0909031602010e09070201090507060327030c12051e0711040e0c0d1110180303030b01020703020a091b08070c0305070203160303050304 80
    0x3601c0030921080b80584001d01e8941c540c0c1f2401e200041082607050f0783d910010301c00b0742e1801201c0720310841c940d0444896503144d10300b02c6d0090480c3c01c043c040e40c14441160000e28506a00943c0c031410408000e181001500c9451810001d00000200d0602c1852002d41040781c5860410510502e20f0343d001003005c161905202c3d040c4a007a4001c9000c15050603010080d000c04940c1000038620115055801d20071a0704040320b0034504288000c0ca4000c40c071001c590055031000c0034054610b2402d101c003040c9050f40c1c1c1200d100340302c2c001c070050040039000c0820300ca6203000d600035000d0b40500d03c15541e1002580d800a4410303180c00008a03180c20035903d00c00b1060500c0d0590600812080c24010082e46040b0076461115204c0e2200504144e200d090189403a48203000600040d03178080e0041c0703621615100c0003400313480c001000c401e0600201100f1031140d4401c0e40341a0044660b900e0b000083c0ca0187c608a03001e5200d002c0c05c0e070b098456552295840c0a01c1c03850a40214040e541d01c030388070300700741c50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 52832845 1250 52831595 52831607
    0x5130209010602010c0e0910080d0203220302090106050a0309050708010603050c0f03120a030f0501170f01110406051b03040303051c050c0409020319090606080c030703170c0708011b 80
    0x31002c00c684c0b608517200712a81e008141000800c00840d1541501d5480480700c03006040c540d0404015406201340000000307800001030b103000c45401004840c0002904803607035501c0900c0c48080d610155507001040300380c2c0508004c107801100e80c90b000c15540c40a40f1b1341031030003130306a00800440e99140010014050184420102c0800458a4041c0d103503845000956070803203032007404c0d6003c00c000b803041e00d024000d60000d84030b40340c1203c00384925a50b40004c0e40840e05025540d41050085031540070f070124040c8540c5020380851803a09007082e080210441c0d454106a034442d1030705c1c3c0c1d81c06040d45850f00400107003006512070355a05079903065a002c406400484480d510f110700c4d0409081c88000e81c06d410580e02640c901171801030300d999030030040700000c100d8904040e4009152031240000d002e0180c0000342543d9540c411120a200c843e028103a6600d4603100141c60f44d801e406e4200b107038007000c2d4018022a003520701250f134069190f90080d0300319219080100c91000340c00c10104001c40d0426 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 52834095 1250 52832845 52832849
    0xe06040b010e0d032006010e04031202130905090102090306011e0807030302060105010509040b0d05060a1b05040312090503070b19030e15041b03080d05060d08160f060513020901 78
    0x840d02c4116034401d41c000c122034803000c10008080c0700d508080310300000701d14890504a581e40f10200c0705c040d40c5d280004031803454151010703000074a115020b1107260055008580500c240108a000011728145044000b44406003601c101b0755008c0140d040c85603410002c07075004c1d200400003104240b900398982c00e1051220381c007054242c0c11082042021070380104640d41110b000782009030b0b541c00c5040000e4010400e200c0d48035408000300012a00344000001c3c0b441c41814014410003202c002c035190403050100400ba00000507104200c18000600240380a410a1000e8246010520b032140c000034140a455003004100c44804580718200c010b10400c215000c0701e25040030019800317012207094680800140ca02150a007500106040101e0703a20309002d581005212810255200d2410104503403100005200e8a0304240100d5020300d401292503116560085400b4a81480b403c04043c841c2c49142d0b00b560b0075050f4480761404075042e402417505c2400c2642200e103070040d2900c1042000d42041e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 52835345 1250 52834095 52834097
    0x80c0f030c0d03110324100e1e030d0c020a091e061d0105040209030715020f01050f070c0210110616020105100e0123060a0c0201080c0c0d030b06130e06040b01 70
    0x704943c500d101007020101c0350000e41ea2807891b0400707501c40320808114661114610b030051030f000c210442182d441030142100401c00c0722450140b000e00551000c4001071028041e5164000311603410303c0c10b001d03a00e60810188050036452405540c0c0f641c02e0116180c03c020302251000d0910140c91000f60b5108280283c050032114030402440c6140f0401c441a0500480e40a0340e40003039540d0302690100304850003098200d0746030222100c401c030000d464050034203040e2a6507090030040761509103d18400c600c04c003c5580c5038966041560200702036414880011424013a500c8a200407020b03051040c0e9101d036046210000c042ca01c0540d0003030844200901980310303602c50348030602020f1105080309046902c00d000c8521150181d034064a00352818201385a0301000000f180c004060b04003540004180c000d0321402055034500307020384102d1040c02010880b42d0407400804504900a500000007070f20050b050a007003080100304000110741580280301003002a50810180f880c01c0c2c010400c84484c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 52836595 1250 52835345 52835351
    0x111030334020105191a0f030a020a090b0a05031902061c0501060503010314060906070e0105040503060a05041101140a18050d0c090e010c020a020904020d02090f040605010e04030507020d080c0f030c0d03 89
    0xc1080341a0100803200c46c00e44147c0d20b05882c00c820b95001c0115a850b5500200b40c501e03141c0d0f489807400020701c217100665004880100002a140c0340104a00e181c8504003000c000041c003043e070030072025a0001030b800c5500d00c0c00024907808055144076960290a41d615080c0da04d5056081156521407002d41043c03255220703a040050380c85000c940d807074110300141000d10f1140b600500513a124000d5421858061140c9010010003031f0103604803d002d14019210f1020000d44040111900901070107004003803601007145c45c4480e4414859022a07101d4810400030300c585440000380c0c0070004c1c490a940c000b0721040140900400ca101f800b0450303080304000c00240034000d03000780d01c3c0c1e41000c2005e842142d1090000b4195110b203110701150640c024048002d0345042c0461049040c030036070301900c1c6c0d60320b13000020548a41c0c1070010360089426848040c02c0c2120755003000101d00e030216040310b03840001d01015881035020441c81c6c9540000a0156440d0441d01c0c007500d00d0192014400760406003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 52837845 1250 52836595 52836611
    0x1110307121d10230d05010512031e090307120b040b0105030606011403041e030903120801031a13050f010608010e03030103031707020f0304090203070806011103033402010519 77
    0x1591046083d042c000c181001c2d0040b5407110f01004020100140c070b1003000c440001c022003000f0040d40940d058910031100e03052036000d1019070310380d28020200e4200c15159480404412703154808c0c00f030000c1250050807206815211102d10030300010001d001c03560300c0d01c20014401040700c80c1000f00d000d000290300030841454620002401507030510b0a840302e00300c002010070144849010001550071103455101c224200da03240080030800c0c103100036600e005c800588403032258401c2040504072500321104c60442c42405010408102d006003040204038522500840041c03014042419400a807c00000e00b403454001d0050035982507801d40221504100010b00020350440c400d4108003c003000c144601740d4074010b00f0b0f4504003411603080c0c01403102280c00100d103c01d40e00114415412030350707401c02c5d03038846400545400c207180384211516081400002c28401d10301e07141400120310040a940d030600c0e080400c0141401c0c110302600140d45610811408014040e005106c0c050030003001c000502d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 52839095 1250 52837845 52837849
    0x100b0913021c0213050106180603020c06061e0307061806050403120e0d050307060c1403250512010b03010f23150c010c030b040515090406090201110307121d 69
    0x20803203040b62039801c405214101c003903448900740c2c940da55144440800403542c6405000d004001c0d402610780d10b030f03031242d1000304120303202e8003d4501c3d48040f00003c10311610791030100401140c04902540038040c3c02e14034400d0f50b45d020005840101001c1d2188000c60340026440d81804140742c000c8018045c0410003000080c80c00b4460058a100301e16084940f0f15009000458110044c0400307405031002054000c107100507a070040380c0c0240280c58550300911050503420703e41c0000c503184a0110f940c500050740070032507100a03080c90010f07407074098545550036110701c213013a1003a002540821000700052015036852100040a031180c1c44000e00003070940316500703501300c01c25640c0e9401018800f51a42492401d03201b03031900d4041e110000c0c400749402000040040540c8c0d503440d0702c50340c18034020590170540c40c1030000c0c1028014102c1d651684c0e603600d03660017034600d1080403410000b03601424031a000b001c0c0302900f252072083c0781da00c0445e86c005000900000044010750403408501c1c0e4070301156 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 52840345 1250 52839095 52839109
    0x1e0203030406091a04080306040506011d090910020a030b0a1202130209041d2a06040303030e1002040305030c0d081302010c030c02030106141201020406020d20100b091302 75
    0xc55805040401c0d83d00c0c5a2910700c0c40e40021400c0503074400c088800384010011203034042c604c0790800b546c080019a4940004444004288042c803440f691180c00405050a19010503070b44a05407004852540526a16040403a070101070000d000a40e18088030800c2d18003d4040c50080640c50800c0b80d89010301d40000380000d0310403806071142d90307000500300c40c56211034000c4400e80c00307105140c000d00103244899a403160850341daa0791000030301d501d54102000c10a12080080d070406801941094156502503000748010a00d28201c0e10a11850b6a0400150300060000e14810300156807100c0c1c82c82004c138540706000e180c0005203c021300400900c105c0c0030001503005602460142070f000d02604040d24941c0780003c02941550030101c012540f8292620703800400c0303009035402c488000c03d060203e0308038011401480b005070010480480075521604040c01044007035a411412140070302d41c40c0b407410540e42615010940c0b1904134505520b030a005195021b04900d01c0a0307a105e98581c005181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 52841595 1250 52840345 52840351
    0x21091a030106110a060f0b030c01080c0a03020a021c20010b0d020f041515090504050405190203030d020403050601140d030207060807170903040801230c0307030e011b1e020303 77
    0x2000481014034491550404c9802c0500b074000d04100580024925480c001c3c00d40c8100d0a030081c42166001d000a51081c19010b22840c441012141001305040b000c0b006940302c030400404500c101900f09002d607080003100f0041d003400d511032003c101c6a0003c40030f0824070060300c1c540a41d0ed0714007849100c0c1c03513106503140e4041e81203401600130003540c800540100704c0c2d0002d80103884000f65000c2604482041c4551240340181c486021180c0d1350000c00c0250b0b1412240204150000c80642c00a0a800a0780c0001c0718401000d0f00d08100022400c5422600641d0043e9036581c003030340040006d201418412010f1920070b58000340c80b914562000381d50f0b51010301c580c108010300074000500f604d100791040c600102030b25440e403041c0d09150130f9140e0f03070342c00c940620700441d444e062020f26407001e8408242c0b582d044400b9210025a10240da1030960341000744060107041d2150b4004541c000d0038032401c21a05c511842c00c0b40d003200a2500100602c01e0103c1c290600191000c50303101d2540c0004c20b0340e82c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 52842845 1250 52841595 52841597
    0xb0301112107140f0a1e02010b0405060d0215090604150306030303060506070203031e0c0102040b04050906040618020d02090603040605070e060a300204080a1b050607060c090321091a030106 83
    0x107611707440078408840140c603280c2442c10451102d428151125419005001c1e68082142c0a1002c0c0d1a00c0d0b00b00551180e00c440000d52000300c64440000c4008600041c100e5070100408032030420b942c85041140742d5143c22448400039580c3c8209104154051040c0c00140c00701b03687e0380741095129404030343d503885942c81c004043da440396000c1d5416146003044441e404d4180c0d0095490303680e0303551455038940090065601c5420750a00050860500380305420842e045c40f03104491075078400807030b5002940140d00814029030208a0b00c405925413000940c0524898100000c8514100600902040c07107a04074922502c0200b1603010a55841144075155034140307414030031036650682112814440c0700c4c603002206130002c500010003000200741748103040c3c0111210b1901400500e220410b650080c0981030380000305100140220742d042c1d1202d0003132291420104031046c3c42e1b45500c058400091032543ca071504620008948581c0404044004c01d601c61681c0100801e14218080314001401520 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 52844095 1250 52842845 52842847
    0x180c05030408030604090212150a0903090e0c0909040c0501031a0a05040e030904050103030f020708070815191415040522030210050705030402040b0913060b0301112107140f 76
    0x40195517580e02c00c0c4e404944c0204420265140d0000d840e0f115009250a85004070480000030543daa85000700b41d8401c2d4160b80e505d071070300d04041c41ca039424440648206c041020038460040c1a031075881d040c501441c018004283c80d14078000006007920003c40e884d5805c00720a413620840c649801c025002615000c841c0840c000c0c00205403280b40d0b000c4c05000642c0031341041c00010030305805c0308800040703104a909850006850703040b43e07aa100c18a00c030b02c03004c1d5407203813800ea06261400750100e500404c4582800000007003001840301510104a102e0381a4200038060200c0c514a8088044171202c0c291002d100c03a02d820104c0c910018920f64040f001c0c400404d0f01c0340201032080c406403400441841e0304124505101d0b90007007181d003046604901a41c81e05800394054a03002113031610407401848250094405607880c02c003c0c0c081c00c2d1480b03030550b4031007100940d000500c2015040f903809018004080540300318080100d643c0c040c100406011452000d07540c401114407c86d105d0b440d02c80c08031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 52845345 1250 52844095 52844101
    0xc0a1d0112050a02090a080a050d050d02070213060806010f12060902030c0604060f090b1218010e070b09090c0306060a05030717070804020117061c02060f13180c0503040803 76
    0x1600c2010601000400c41c1c0e107001d080050000066029010500c0195086001c0a8071034403600e030348030820000a08181d21140c944d0b502c95104e9402469141070b003400140c146051b42e40401c03400b5a521030007491042d1220418865031000b044a44c0c01808004588010207280c075002c40c1211030007010180c0703100d40740d41102065440c100301480c0603003806410955166a034030700040405d6140004480091000d8400182040110090f2031884040710000f10a50315240c00c010b00c483d8458040744095500d5400c2000c2c100e07418041003000b800000402c41c2e0f02c4c18200e0400111460040c025544560103100340010780d2900400e44244000c5400e0803552522504002d4070344110700047c5260301030121081040309a40f10446a0140c0d100382c0b05d42890011505401c20a00801c40302c103500000791881300340305040c50840c082e04490000d091140b401d4161a142c5e02c050f40049401d24114101d003500b040743c54584126000c0450000a04001008003000010035901c405040540300790008008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 52846595 1250 52845345 52845347
    0x80f070318060b030106030b040c0801051303051204020d050f1005100b0301050d08040b0d320c0d060b1602030f030f0702060c0c090406051906030b070c05071502010f050c0a1d01 78
    0x4801f03190840e1558003149420700c3c1c142102d40700d40c040c032907265003850003194000000190030091251b064860905101c003c441c5050b02203002082680c1c080b45c0d03031032104042a0240072465405000300050f007100700310800058203541003d800450a1180c100d4204a105180001c2c6d81c159402150451034441f12410542c610f8003440c0c005e8104003000142c1100c024480c0e50182c561310b032101215078039018100c041072440d0040690038031103c51610001130008442c010040241e8807a0403000500d80d41c560081039101d8020480f84040718121241c140f003035142c100462092100c0000c001c524140743c2048400a40c0220407009000715070201c0e448001190a0003203035003480b8058038852a518040c2001005000199034151800002d040e2440c41c00d40240140700075030350031103d12401c50322980d008594400c0c8188090f9244d0041207800b203007075103140007001280250756002258003150410340da02101d00141400d4040d80c402c016002c0c0c400d4006002e07421844070303815443c904508581c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 52847845 1250 52846595 52846601
    0x6030e030f04090603150b09010608061203040f21050309090705090d0c06120e0c13140405060402040f02040501021b010306080a1a01090605011d040b0a06080f070318060b0301 77
    0x124a81e544000410003040c02c80c0c060b400001100e006141c0300c0882c40000b1099000c5034061b250310741c0c010039032100600000d800f800e40190003242c05449410b044e0185007180341140c1040d08294003910b14142d080010801510300e8542a0b140c146c04c200303d140c00b90391855500d106e2034100c01d0083c841d800c0003404040c010016501d000501410106640d00c1910708680801443c0c00352001150498100141c200b0a074401c50ba109a00318008111450038101084482d8201c20800740343d154441b0781c6100c0c408001d42406000d141700300c004240b541000e10400060700c41545c0440f44440c8103020810443c1c0c0d0001c0e03544003075441d0407024004140c501c80100c020b4411500407508511440d00e218080080c055801c00400b2070302071060441d0790700d800340c18003503070910b00c9158001008100701842c0500b40d10018401e180005000050103009103002c03030321410142e4080400704102c0717010881302c0c28184410720380c003c1103840e040004c07510000c00c880880c4521080a08442c1d035070088211181c40940c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 52849095 1250 52847845 52847857
    0xa0c0809090c0c011d030703030b04020c01180b06061206011b0c121502160803090304080601090506030c1203030a0c02010b0d0f170f0702090603100c02061005010e030706030e03 78
    0x1a210101c2442c0100e58600c007680449040e441941ca000850301411043d01101750791421003201542c503140712a1011406007505107101a4402e50804c1148a031007000d21829003403034001c1c0d080388411007840c184958020802801c17a03001d55020070603602c101c03040d40169640b00500342041100348003155013615042c4241140141900d8417024041400580b602d4a03100313080c45002d10101c10810100e0160913805000300c4500024aa180001c002480c80405554004503180c12241070564840c205031601d0001c0c0e000b0399443d07075550240806800c00b40300340550b411064030703501c6409c10824540c0e607aa120051012860603038074007103441514404c5d040141030f5100100212800c11441c01c1125007046100021201504030b014103203101c04040055806444000701c9440c01e000ca82d8083c0042c040340203080c80d07454000c000352110210410321030f050001016500400e002c0c54019000ca90a00310b0790880b5052020040345445240d400080d00c000f41c4900e0324020074a6100d0303050040ca140602 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 52850345 1250 52849095 52849099
    0x606080709150815040c110705190603090201021006090b040f05070c02090a0e0615010306060f09030f060204030602030f0117030c12070c050d05030c060606191809020c01020301030b060103020307050a0c0809 91
    0x40c0c2103001341a885011f100360b141c0034000765000c1d03039036510401c8101c4a4a00d04c50300f04a99070344d01002034078040c3d0b0110052500600640394400e8920b500c8c1c104840c0e081d00420401a0b0321902d400250030544240d101e4036141250401190801c00030203400c80c09900d000070322460f60900042c050a03c65003000900003040e60403a6240d0420201a00c1c1c401100e582d12400240f41c13940000d0700038800e903102e0108481c6501c5917460641543c5444c0303840604104203031840e0b0b800300000000540350b071006622991515191780100e505009201284201c40c0c0c1c000b02180c0c1c01130125180d000804905080300c0b200303076106290303600d13400c1c605510024159800281d100c4410715040003400320200c0244001c1c00c0c1070080e030780036039a90020001c2d280500c0d0f003980050192100c000320054010318084080300548440a150301c2d5071100307420300340d030b0000402180a940101c01042001200c44c41c0c25003022013400c040d411131030012002040b5000380900c0d44200a1030754000ba041c03060001c00c0792104580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 52851595 1250 52850345 52850351
    0xa02030910120606080411010206010e01060c02150d0207020114040b0f030a06150804060507170402040905160803071103030301050108190b192105060a150801090303060608070915081504 82
    0x5130310406400904119415070f4000000c4135540015840400d0303582c141c43d0a0507015032942d0912004070b03900c0101000c102d80000c60079203000425070504001d0218005403d1016a4a002501c0010481c41503c560b0002e024400d000610012040500b56180c1c0380c00e18000d40c0e00ea599919042c40908442d0303019420402030131210100c891341c0414518031a80c0100420300258840540890f805101e0010982090801301c2c0420b0040ca0941c1202c00001d001d042107956240030903019040840055102d010341b070380b00045413020070041040320707611141c046020b03508540c5000c001801c601c4008089120307910705024060300c50b12160380581041d090161280036001c1d13150704084502c5c4001d000e000e195004c02c0226040016000306100f20640d40440501125207901c101c0401a198000c006401600f02d43c2c004242c1c1d0b8800d02c2050701d210f001c1d9078081389051603c140942201c00c0070f80404100070200c0720500108035044200c200c21082071911299a07624000d0b004118103081d04400e91081c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 52852845 1250 52851595 52851599
    0x60311010f12090501140c070206030601050a02010e060f01080d02010b060304021c05100605130509100b010c350412150207020d05010603050f010213030605090f1615050a020309101206 81
    0x8055014164010190406d56015142c40e41501441d0041480003503002c1e03000c000240301544204042c11000c43d150001146c2041032429003403d103107040350795a5034075140f0001000490300802c038612040c900e900003003082642140200395584401080a4044d815008001d6190b440b1680c520f446280c120f410b9400b00c94074121944c0c05441c0c03034400c0510442c960084401701018034030038280940c41c00401003040f042c5101812000d8008824540e05000010340a0400304641c90100110130004507420015800da42d4010907859503400300c48091840706020511080721810542054240c0001d40082290052121070001c0d07c40e500000f50064040d42c0d10320304000f015003104003038911841c1030703842c0c07040e1142d543c41c01c034051122820074840d0071110400104550350711154012070948144ca41c2c0d2003420314203525000b40d4001c203106018a401c0c0c104141e1002c01040d204d000410f25080d0b240038030541d4001c0d502c1c050f0880091140c1c010080c0b401030a40100f0712164600c4449006000d12070f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 52854095 1250 52852845 52852853
    0xe15040b0c0a0c0e0702060402010e1c0b04060522060f0209060408030a091a091306030b040305030702010e0a0c1e031502130b070c1715150112060311010f1209 70
    0x10014403000c4072903c80c0e24002240c04284d10340348511600140e4000c00c880c5d075454004413040504a089640c00c880c564050386181c107000d15242119500485520400e41450f01d0090704441006001075039851006d2001059240c4030b1018540c100d4203d2404201d00c03800c1c81d428002446905141c940c04040010300060081000c0058248819a43c4800445681e00c011200140901c0d02009081301c03420042900180b810595603107074501c81d10400203107541c480e40d800301c100700c003030f1001e502052000c07003080079096090050272868402c4c070001e4210345810b81c0d01c55640a41c2ca004204090710000c684948021000407448002d541080d801410303185060102c000a6114021296910b481c00c50042005c200840486402560150f800c0500c039141c103181c2e003088004425821058069070715540c2070506a01c00d0346009403000d036810007001070140000352004801c074030380042030b17410440c04001090070303400307114903a1b0000c0c2044091560381300340480b0340c8012000801142d45c1b40c48075040501c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 52855345 1250 52854095 52854103
    0x607090303170c04061805030102070311120406020c0108071b030f09080c0a050402090102070b040f060e040e0604110112061419120318170105040b06040209010e15040b0c 75
    0x4a0007a100d203000c08441525095040b441101c1d440010302d0300b00000c20121b4402d400c44003607003288100202249883e640080d0036640031610590008034800341c5500c0b80e200501880c1080700310301010a01e4a4a4064065122100010348505204040e4001081b407402081d07213800352070030100e00d50030a42c514036000d00503081d1022a01c001508004000c2560640000c028000c0c40000304001c11013898101040040c2d403040040a046005110000404042c000013800113000b40020903001d4608200380248140751415801d0710850034a9414504601c3c085409500250070002010280c0c40700130041c2c641e08102c1c0c80e51610b281c58002c000840c03011031a2540000c80080729084603c2014100d001c4034100140510500003c05040ca040003d000351166852074001660a070481c95507125001c0b0480400c0c181031032280d441d08200010480b643d00c00580c0410100c0d011410015101c0000f0000d40b1800c0f1528083c6041d40b040c0280f0114100c141d500400300e8030320303096039000d203604045d0300c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 52856595 1250 52855345 52855349
    0x4290405010b01020f0a020d1103030409140a0b010819110a02071a0c1507020c12010504020f0103020301081506030a080c150c040b180409020621090309030c010804050f060709 77
    0x24a510b0512240c0d803030340c030104000641480e2034004005040301c50f003c12144001418044400907408010b2200d42e44051024000400280030300103402d1888120418515000500c5918118a00549071005a030404055130300500010301348010010255500402000c1c07034a45859961004180c880c60756600041440c162034090a010941d51840d450b0b14003a4010003544050710341010200f00341400742e00b0819580030b085072044820184010000c034440c0080a040e0540d036075100c500300400d50a100d4000000f005081c80c0031440c1d0340c0b4040b004e94551116900400500c3c01d41e00c080792540c0e60402440c164560007841956496a0880c0480c3e610780c0102007110b054608a40080c141184080c241c0c0d0403a40f2440440b4508240000e400c40900c2910a4040e1320030b079940100d0000d83c139408098042e56500380c0ba440d800c00020b05174004d0300c5070001c20f5117895510401c402c030400d46010460385d407911403c2c00e00e1407d980711850001c0c02d00c0c460445500252195104100015034000c6030f241c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 52857845 1250 52856595 52856603
    0x12031618090f020714030406050f160c030f11010903030e060c01060504050a0e0601060c0b010306050601050c0d020309031615080613021611030a0c29030112020a05030a1a042904 78
    0x14200320745c81038043e100e0103240304210100320140402d94800c407103140202848555071007026034207417507035490030080f00c4c00c0d40040d101d140c15480e01500b0449000801401c01d602420403410903482c0da0740c010302807400207144600400f0701041c0ca0303404a20942180c000b81c04010424025403609245e1038008000c0a0b42035a054400c6030000600d00c2d01882c01480000e8101c511660f0320f03800c40d240e40c0c01501c2c0141c8000e04002c0100041c0101c079a080c0030f1a8142800c9038090350b907451360308080528149126070f441c1e1000c01201010024124030002c9000c4050345401d1000c03c07030341c0c0e036000a14207400c403030500300350140000b401030400404132815240075440b03040000d02862058050650314031000900516501d00d0780300600071844c160071500300507401c0580500d0744c01000181e0355031982080c1e100584803280e941c4490118a441012080501001c3d0300600c4082d4803074807441c1100e050009014040300d2920003180620500a032441910400076035030481c44100400c1540049408480c00e075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 52859095 1250 52857845 52857863
    0x1f030e0307050f070b070b0a050c160b010608070e0607170906070308010f060509090a09110402070309050a12030f0f0203070c030b1f06050f0c071a030912031618090f0207 75
    0x700d80a1005d500761440c442d002016981c0e9070303840301410002440c024200f030502c02d10034000c00010441c1e00040401c1c1c58802c11000c0705070351420201425900d40074010b0350620600884980054541c0c0c3e0581d0642508110751f80c1d46504181c41000701c910a00708902d40009001400809054210300c103281203c140c45050220256108000c8078075005005040790b02c600c00c500468003500007600046e2105008407940c410a007250000142240e1007010200c01262900c1d0041013589000d010f00e5006025030780c03514181d103070345070390042280c421102c143c0d040c8444c669a51000c24401c00543e10050f40c844c40801c6960313100c0c10070311091182160702100c0024a05201b648000c1c08800c408104c0e0541e481e0340d41070840d03115408400750450a080000c07031003200400204d02002240304d01189a1288245070b9904200710143d080c241000100000340c034007001030095403000503903c0ca800300911f10740341d03101c1995102e141b03030703c0151603021048050500e01c0800502180e0303401058442c0c8562404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 52860345 1250 52859095 52859099
    0x907180501050114030403030b0a0f060206010905040803040308130b0406050105041803120b0609030304060f080a0605030d080703020c010e01060815090717031306030902010e09061f030e0307050f07 87
    0x4a019540c090203201e000480140c2d0f801c00f40c203c0c150145070400d00c2070402060022070403003c00c08800305681b0100d00a00341c003804010141d0148215800341035080300510241c81c0036141c503802884058001000c10483d940010a02d218106101c18101c0e84008101e2807130800b8185140070300300c28000c8070710861502010803200f0088114020381c103580343c4c40f8142e1065200c10740e01c0040090880c166000001000f520840d55400c5c401400908010f45560103181c1c00d5800081c421071000b00f54908807403a1100c1406540d400141501e01401d0b5454000c4207540c41c0306040340640102c03520700c0201c0d030800410545c07418040d00103006a40022080324418044215150311903041501c2c01080c80d000844c040c4004980301d0000c2030650181e03401c503440c204070380705900e40d9013403603910900000760360b00003101c2151791000b141e07031a0a20444809000d401c4c00c40000c1e10403061f00d070010150b00c1d400100500d0960198000c01da0f81c074010001d49880d0441c1e420b02e0b45d15640442c1442a041c001d41d500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 52861595 1250 52860345 52860389
    0xa060317071227090207060b060715050604020c03030405010e06060d030806060904141009140c0901030c180b03060a0905130813030c03082d090904020d0503030907 72
    0x964001075000380e055241103418281c140c0701c103901e00c06070190700f4400845504000c4004240c0b0401010f1a080069030764589090000071030303020701e881901c650810401c140101e0504a164411035080c04030004040e00d503500000c0c000d2190285100460102000700014000706600c081c000c104104145c89890b41d52208100010b42d00c2e03100107010a002501180a5041c050040d001e119805800025041d0309611650f1100f00100e0350700300c02c00d48525043c42125000d0140a4035038009551641c4079050215445110b401b500317580382d04041e621003007940365501c50210301010400784810200078984402c4c5a810991040302c456000d22581c44000500d045a03103d000d1041e2107144070040d1190340e0307aa03800760942c4800c1200000103c11503010000c071341400c224100139881420110b5481215409998880c2c007040341c150000c01800e00e0f5411a01907100031a002c441044614040301d0380e9510000b02d543c4080d010180041c4404000c12031500c0001903054142ca4a044440441003980c02c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 52862845 1250 52861595 52861597
    0x3050906060d110a0302180106090506070b060d020a0308030a0902010806030a050a0f0c08010f02030106031503020a060e0301020d020d0207020a14060403030c11030109030306061106100b1c050a060317 88
    0x526107070007000b01160303080440c80401c0001100c80c402090101596034a800084000b4860084004402c9100004110f495008003804000b82800c2e0ba00c10f04118560b114840d028000400d030300e000300140000b00c000c40d07403280d4048014592180070140c5034244045c40c800181342480d4201d0206e810800402e10f1440c0010340100e01c654880014001500507a49000c0807030030480c022900402c18070008112001c5c00c0c09911607600d000c160060700c0350b140c003c000b41a6202c04040c0c00041045080074009a20340c0c0c040031090f94820304101c50306030105804203009115881c12035001910108603900070204580081c00818003c54650303200300d45400300854007040b4108101c0d400702c000c00081000900903054035074100c1c01040d2401c22004440080703401d55102c6d2001310000380c0d540301d0900104d0703048010588036800003c0200310340c1c070304800100a8040f1500501c41e0a443c00701d0103020415151501c1c901700d280c546001d1015082010703090b005890580800c44603003130b208045862031241a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 52864095 1250 52862845 52862851
    0x10b19030b01050f01120501030303051501050304030909020f07021c060b060307050304030e0a030f0b0106030c0203040e0c0906041a07061d100c030e120705070608010302031002030915010803070303050906 90
    0x229500c2410792030030003004113a5450600e10345c14000e0102c501e9251044034881c0c80d008601a0b01e000c5410720f00410366981c80600140c0c401c2c14408140706100c0401d6000c8010300070b0340c200040060795a450b0480c4040580142c50300250305c106015100307080401200c032444030312442807405120700c04111003040501c0c0811500e4000080c07007031001070040391103903404150b40c0c0c502605180c0740e5512919204510100c91600740c0c0c200c1c403210010440310f645032240006903075151004d541400e0034900083d034042c0b000703444d0907080039003c40c4514041e0344c0c1808880081440c0ea4040d00d07080005109040070f6000110241c422504e0400a660b0304c4064004191649040700048c000e6208200c000c20b00801c11042c86404041e541c0c1045020410104441507860920340e00303458680700203160540c5026019007151b410094032000400c0140c82c005a03080b56201701c15005a04c030b070b85a035940762800d20300c00c100d40b02d0b211041d400007803404004402880d02c10301956041c000755482c0c1c2c0a1942c7c82c0429 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 52865345 1250 52864095 52864103
    0xf052a01060504181704050d0305211311041103090f0c0609010c14011401060203070b01090603030509090901200706150315090206070b07030e0708070b030f13020a08010b1903 77
    0xf000e0001481d200074041441405c4880300341400e0b1a05e01252034038507150003c0303021480005007038072120b2080345412074403072480b00d42c40418545007504101d50302c0d082200600d4000300c401c880c1e01c140e80f40e400550701c000714841044d48a141c54900255914010b07148100103001f0a29501d001d4202441200c0040c0e9042c3c65241d60200b455030341c07403900c3c807040d4004012950390f0440c0700c0c655200040024003e020aa00441d180c14103800d0481c03c20034181d01c00c290662134602d041001a07040426201900f0088035070705019651100214050310042500c01104101c880f0b0394034449203894050620745014800400214aa400303015292130001e01020744801c100c2c126009046419070424448184050f0116042441c16a0340d0301060b01c0a40d82400840d465074540784940c141004601d0040010310000c00800d40380c140d1140203840041c25200351040da201c001818080d1714001070400c198054002c00000b0780c1c4074084c40c000c0844400d0188141300d11a9140d54028144c40c910041d2a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 52866595 1250 52865345 52865381
    0x602071a03060102030d05010311011101050907030b0601110a150e0d0c060e0114130b13030509040f0b060d060603180201140901020a1406060301050105060a08070f052a01060504 78
    0xc0c1400c860300326000141000e04601c0200300d58010715155004250013940701c0c2560034031a01000001501181e05113030780182c02d0385043c0070049017810000d2003600b100e400040202880c2c80d450012a003214000204003294428140c0d600108400740380e24190b0300c18000300800224005ca801d20b0346821089034000000341da030b04210b2004c140c05070300c000403408a107070001a040c415600e442801c29800c40c0c0070f012010300c01c16100203000031122055400450f2440101c43c0700307010b0740c000d4032a0056080321400b95540d00309100c521003180e480114000c000034441612052200c403800040c01031130048000003410007a095003039100010104000c95416100c542c0f4039111003030388080d50b1700248000c90440c841d4180020200381004131001d0300c400c00c00c01174046480d0510030b15095490603880103008200400040c4002944003210541281262404000601039104121542d0141e81e040100710700f0001c81844003141d2042c0c100140d10400700c003c3c0450f81d030b41c80c1040200d81131782c2c2d50074814801c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 52867845 1250 52866595 52866629
    0xe090c07050a0b0a2c0c030604080403060f0f0e160807050f01080a0204090606020f0f030f0702060702040b03030c070906050a08030a0f1101060b03010303020c0405060f040b060714060709060207 85
    0x300701d0a0103030b009001210029844103d4281440003c2c000008405d4803158a030214501810501c00c84601c510107400502d0380d4101a56644814451888042c248503030310708201001c516650400c54140f2210710080c401e4170718644143c1c0d1a00d4005d04004291702581c5400203607807102054000c22604c0c010200400003036041c00640303c060b40100780c0c0018a500300300100301c41e0f40a116810107012264000e2100120300c60b017940c500180c07020401300d154410700080760540819401c46a03034541c15117005844000383c1c4081409405040c002951600001c0341200140f480080d07a0360840f02d800f001441751a64580a04c0310703a064a00646640303400800184040901451540e280100e051600e2030b0511002913105007180e9583d0040703da00203000004106060b0b0400510080c00c0d02200e0411040c24020300052412445089060049850f00c41d200b21503a5003070309440e8400e4200700b09030400880103800c0c0303032110022105c1901081015001052007440010010242c800071647c43c06818 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 52869095 1250 52867845 52867853
    0x6040b010e010c020301090f030c0201090e010e010522111c0501030b0703090f0b0a1d0f0703030f0201110c07080607140909060a03080a0210060603020f04050d0804050d030e090c07050a 81
    0x40c20b00c8090fa015900c1d1f00e86d45c000030300300804035031429010f0b83e0350800c030080e203100042080355550b03c0b01080c01600001401550f000c400001c0c11a0300031a20101d6402100c000c0e40c07134440110000701c3c0c24034506009842610f0304d0300000c2400a91002014450708213250725001110001c0c00054241280003001a88450282c0d001480c202e008000c0390116404035607402d000001c04440c04800316440300200d4404122480795500c07801d1014000d4592001c1102005035035844a100160411900c1c00030001903034000e40c0292a0b20200c0c5412039074542d44078006554994540c0f0440b04548250700000711a94403a481e103d50056802100d10b11b412900020000801c0300600125400302205d400000043d900800505001da01c0d1380207010300e0a140d001180480301c140c0c0c4030b5003c1c54010800c02a03204944000c4a0a40f130701120038004141c0d20741860001c50051341c00143d00003c0b01071100c1d040c160000302c2c0080c800002c44200040d40e0714403084005d14014002d0082440d40907008020010b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 52870345 1250 52869095 52869107
    0xc0102070303082d090c010206010e040b040f0309080a0602070b01050103020f122205010f05011a04030602160206040f0807060903120f030e060703091728050c06010b090906040b010e01 81
    0x719403540c0108201c03a50302040d5184130300342034540d4009030344a12880308583d46c051002d10300614400e031880d65a131810f130312002c80c0d50070010300081031100030074580b0003010300620322880500927010486081012030300d0000c2c02507000301016a10300c2080b01c00060158803900071110302c4400c84840a0401048610501d0b0801d00641317140028803049030040d0001e405840040c200d40d0003000003082500b001e00103401100c0045c2c0000300b07020305c0d619205c00d14008020880b030031a507000c00c3c010b030745103d0001150b64007821580000e40c4080e00040009150b183e2194080503078513580203840d0000d40c0c074401070328400124440104840d0b0001c210386140da00486107071500b6519410041403881d1007585950801e1411102400820340d01d01d4078200340040c8141d0039a44020a41005160055404031080c0715031004c1d20301031019107240303079418a1903c5407054a02c2810300c1c0c42201d105584810041c942c5400900199001c0c08042001500928140c00340c15007820040e103c081d03140705a20011184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 52871595 1250 52870345 52870381
    0x1020d0f050c0a030504090e0f0d0f020a050d0503070915090e040213050f150603091507020703080f0409050c07150b062101090506031b130f020a0c050c010207030308 73
    0x2404810301148031605014440c8800b06442a507890b5561b80c10090314101700d9080004110081e449120f038115150000241540c0034041820b05480008092000720315104504400404a025109640b071680750010003540c0a4a20fa880300803486448458482c110a05c608400c8000b64140c442006081a058000e40e0051f0000e416400c610010106580a60300c081d100010000304541c1080080d8480c20b1500310300801c2118110b1850810180e11071742c50305550103000c1980070400100d10500d008005907001175078020482515031140c20300c03c44d501d41003441b41c4044d860030704001502c060841c90846600d290722421303540074500c0c0741010f07074010305030810425040f200806c075a08602c400e00021201d8100ca07080c45400f550b041803088001c3d980e025106500a42c0203071032010664610005c04540341d042540c41c01114101c41d4691409042e0b09001c00030300038070000e924010180e103e10601c0c2c849000d0012201d181c3d07111001280d940b900d80c8800b8001981c1800410b400b000f02403102c0701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 52872845 1250 52871595 52871597
    0x201050f041e080f07030e04050c040e01030b07050417061e0c0a0806130e0705040c03050402060304290405010506010906020706020718020d0203090303011d04020a0b090117090a021e01020d0f 84
    0x20816080c004d2101c0d060340101019000704055040a292a1070075026041e0b01208107808a8245460b000c02e4841d01541804010030b0030400d200003401d480d02c90800d450040c00425440064452203500d0741c1d0700c84200303880140c0f90f80c801c00300c0301050744007817160320707002d0000320b002a8982603544204603503010001d4551703035220000101c104000e8055004003201174030380d100070300001890710040108503900b03444110281401c0504000c05a07581350309507913126400502c0404480000d2a003000071303c17003651020009403880c1c0140030a1010562180303104100070b80320344a0311511100143d984080c41e00c100801644490424404401c00000009400c010034601608281c0d407001e18006980081b624500c1590010004002d038081d60002c60000f44500c149004407401d2036004181c20304180c1c01600c010200000d20400503900c18500c940700340e41090b130042035905000250310380341c0041e44026842000110032006c6424030704030143c0706009058005020144149105076410800d0006980c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 52874095 1250 52872845 52872847
    0xb040212011d0f06090d020c0114040306050a020702091503030307031104050301060b0a02060106030b060a03050411090906180c0a0e040206130b03061806011709030408120a0201050f041e08 83
    0x229500b5074284070341011601c060702910000031541000e901e002c00c004c00b004c00d964480700803c603101d6000300b40480c00c2002840d2000048004440c1e015880c4125400248246d00e00010400c060940d5806012880d01c00c6810b05d99584480441415039181e0f1005ca980c5600100041113a0350b010345c0c400c15a17480c800e00f100707040554440000e42140c12503480000c011000040c010407459041c4005405800390b0306040000c2c1c0446c001003003c41c002d8002d2072092656540208bc10301490f18801c80351032a0045c070145152070311041c141c2d107903d400e9030350b650401c0d120a190b421048021484905440000d04803c0c00c0a18110343e0781c0051001501c00d07a0440d01c1001584c2148504100082c05443c440c140c1a03980d051100078020107528441c000f8540b000750405014043c0c0e03100709450034401c44203200760150340350140900e0840c8180c0d40030780200e21030f100300714048164600103000d802220360001c010390742e50346800348550002100c00030410000760134204403000165188482c20fa004010701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 52875345 1250 52874095 52874111
    0xa0c0c05010e010b0f06031311040e0d0306060305010b040302090f060418050a020907030e1011040807090b04060f05101206030b010b0d0507050406020a030c1a0c250b04021201 77
    0xc28215403820480c001c03143d440d055140ba85003880008034a11540540da118034600d800845c5040780100345000a010f0b010110b0540f40039234854200200001c1d144054902c1000980782c00f90003030580740b2604003c80c0c1400000248081d0130400c2d1000c036600940100c14568942c48078440b18000282019805030341e820003458044862081d0101c1c503840356005104c8151540100122000010030315010142018014803040e000400d482c50760882042e4080b40c2d209180e0040d031080d00682d000fa0455202c1c0c0000040c6450080c3c00c28900e0322001d40782088500d440b040040e02c01506801510b40100e1502c2000c04448d21070070f0080f02d4001c86100c000354190f204c3d5a4001403080aa003c503415200104503145501d50b03a109140d00181d19042c0030307260614002002e9241c03650081c015040c01080c0b00084103200780032130b5605034080c00100426080c90009424800361b00003d403170b20307803001195441d5030f88400506101001c160b081001210250343d2a420018491060001074140355220303580713 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 52876595 1250 52875345 52875353
    0xc0203040611191b0803070f0609050c040f020912010615051c021204030e010207060e060703212a0903081c14060f0d020a0b030c1303061a0108040b0a0c0c 68
    0x403800c5220744401c54003420090301d00e0400c0303161a00018170942040040100003080303640d01c40484d9912075004110703508176003003071400d04239034103012034010f42001100202440140e004221064003100c1d886403044061000070700f00c40407800341d40c100410b4140740d01102c50007038010303080a0521000100c0300d809241c0d0700710300b80d812544c039064904409138140710401da007083c501c040c4aa800e1000340042da242020041002800c00041801910001765901c01e00d8441c10120300300441c0c40350312412025640c10090004d041a00245001c00c0220b03002003640c0742d189000034210902035607030520203402e68440c2c4281e544401c54025070700380c0c104501d116100e030602601d050100c405210a2480c0f81c08018094283c2d070011000340316203031582201c80183d64580380c071320580381001e0f0801d44a40d20004040300c1032046c030600800f403902210000080007032a0704203606811003001140300c080c14072401915071050a0710000d000c079421100080500001c3d41c042030100c0c0691070100300204141d22 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 52877701 1106 52876595 52876633
    0x2030609070f050c0102160309080a0c06120603060515090606120109090303090209090703150b0102061801020f0a0c0b090c010c030f02012003041103010c0203040611 73
    0x91218503103100c1d0060301d40181001d0006c56440341110b10703030605803021000407800180d5410003c01e02c01c04c08220100070551000030500d42c2da041c584103503046031082103449169580c03100c3c000007050107400345c10300510451603041c08448120040c0200140000c0005014000030098485a14060341255044540490340007030310b05018582200038002c3e501c40654010b8031581404104c0c01c0104500040768070580c0c9036003140303042542c40b400f90342c0004446400340c0c0007080040d61914640c156503448410b494001031030851510921071964120380c0a01d400500c1040804c02041255140150000c03071440c010f114018a243c002484081515402401c11124030424000e0034000d400164010041240898010480c50901c000c81d4200301d400340da001c01d01c010814282d060603c210026110903a025515081c1001c0302501d0b640d886111400c428440d12041d0310421050b40b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 52697845 52877701 := by
  have h0 := BRFrame.cov_init 52697845
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52697845 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 52697845 ≤ n) (h2 : n < 52877701) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
