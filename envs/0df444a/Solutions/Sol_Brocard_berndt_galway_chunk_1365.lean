-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:35:51.135213+00:00
-- url     : https://prove2.me/submissions/964ed95e-5ac5-4275-bda5-1cfb419e18b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 245323741 ≤ n < 245503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 245324991 1250 245323741 245323747
    0x610030e2410060f050304110d05011d010b060c0a120207090501060905030114060901090e0309040e0102030726060d1e120e031501142101140c0c0a200402 68
    0x900748a50100102c0300100c82e040c254002140032401203408400c55001c2c0d0b56210704542c1ea5035034507002c0451030801035501c620030b41d50030030024000340140f0036048900c0c40c40c4291514044142d80c00d4803001480c8504c2400140403100f00c403200010f903925056008502c8003650742000d50103a040001a40040881605100c000300d001c0e60043e0380401180c80690080081c0342400d50107a045010a031600d690107a00c881c0100300101c0280c1084103d107041c00203403450310960100183c1215841d40a01c80c2c1079402000300700b819900240d5a00705c2d040c00308020380e509000ba51446280d4040100741030301c100382c00d003420410710010003100080e00d54a0040854866500d04080c42c028900080764400070716608010540c03800c010031004c55510881342460b40f03503420184203e05148d51000d040340c020050482c1d0140ca5007003200c0038054003000d0f40000400d1880c4400c0100358600007002e2400002081003048482d03180050187c908940080041c0e0400034410f1302030f45243c0c00c008000d517001d8008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 245326241 1250 245324991 245325043
    0xa1401140403020609270f070f020102120105010809160f030308010f08100c0c06090b0109050115080c07020d020a0b0c120a051c0b03160e09070320030102090406080a0b010501080610030e 82
    0x30b40d1f98140180f2241e1210500300b240e4039000c0b4282d02c00d02c59200015508a4010030955029481c3d20b42c0215060041d680c00110188a034046101160f20080d1070301400c2a08000380b41d0403c903000d014211007081c010002d400c000796180e49082811041c4000760b074ae400c10003c1e0512902c031520405511140030700101d074184c01d20000d655020b008612a0a240c8000012002518044034a412010b0340300c0803056680c40780c2c0d03120250041c2905a03004141c08140000507910000392074040c5c01c401c2d03603407070b1610b411030342282c41c056032240341c80201c9030f00b04207800200790001b09480e0140300741e51080c2005c0e60a0340e0346101902c80c8140064051180300340780f1403c041701c1e003211415500010424029961111003640e900c0d581e41c807001d0324181c1080344001081c2c090000c3c40d046058060005480d104110010508071210f55201441035000415031504001c000218140140b00034601150035041440000b27601e515040c07800c00506a0b5280707600350101060254034066030108a02035500d00031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 245327491 1250 245326241 245326261
    0x60e06040914040510020306010c0b0406060f08030d060503031206090a0906062304180b070302040f032009150d05010e010c090501020601150c0b06010e0a140114040302060927 77
    0x410f8070111002d01417080098000b808610a0702e200340c1b0165503240054505448a00e841c1074040c1081d5511a1034103008101d5a004080d84001811000001c1d0781d100400309145080750a50b800c580d00c01c0c4c10420a142d024070194000c0e0303400c15401c4640004070388401c4100c0703006000b40d0500620a5080c1500041c40314030b601c01c041c5c040c4035646900710518081400304012141d0b00c100081520b0101c900b0003010a021800c401d41c0710403207040c018a00784e1650350214071003500342c1c002c07a80038502c040c490012030b030507003c4110148004e644101031401c0c00e044d15000050030950450090003600c2d2040e06000c002d401c0120480c03034030b01c020088030b40010b4000f0404130071801000e015201c2c000000a0340340b1066000c12158105503104040154a65030b420f65804010b40384604000c18612005419a28910304034010724940e149180507149000c0058004030500031596201d06050200304003584800e01100c2c86050115500c0c03851a1180107450300042003240c0403111010030b50b04204942c0700c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 245328741 1250 245327491 245327531
    0x20606130e1518010912030b041b0c021206010305060103060608010b0d02060a0311071b0b361804050f0c13050603030708160b01050915010e0102030405120606101107060e060409 78
    0x261b50341c01348651202c0505006c180e99230507011841c0c0c226100c4903034140034400c14040c11941d00c01070095030052070090000f45480300a80003903c103034008400410170003441c0c0c41280d0060a01100030f203c0302803903800058045505950103070207001c000404030850344c425400350714607821001d200b648514180c2020200d95000146010300320020900114000300c4241c15100d134080d07040d84828400f880d074076045424141d8100f1326462104110191a101e5075403d50b2009101c0b0f420420144034646410424075010504a0070239507900501148003d5843e5090781d00c000b03040c40e990201d0740f500d51001191551007a60000f03800c9080100301c0c424030001500e4000003031030192450312101d036259010814509020345038460800143c09600c078555008292500d405481401a6403d059940b00410109200c1a1441c0c0c06a0400c6041014a140213070110103040d140b4074000000382d03c00b20f5215900e907900c0c01498184201d903a02800165030741d1003228054081120203101c04080c0d4031400c001c6c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 245329991 1250 245328741 245328773
    0xf120c08090106080712060f0b090703090c0614040b130504050124051c0b04090203160911030c0720180a140603061302040e0d020606130e15180109 65
    0xb5082030b800040b1507400042c0c1c02c0903a100d02c440f204036503030b16688980007420440300241c0406d40f02c4000346565660f1101c02031080c07205840208a010312450040410206a08910140645076a403544402a000141c1e000c0d24403001d0b00e6542e9140b1022031201020300e5901c099441401c100020884288505281320000103a0340114441c500d0001c040c1c80502580004d0f1140782010400c01c1c20320032064114044450006c4d0000440b4440f5401081c1006e014440c034a00f5000d0b1004200007030f82281c480c10010740d0511810500b0b509202c6840310052003025405808000d241e804034081300c581d41043d01e070308140244a207400140c4000da9000706c1d24110b0340c69071414584042651100d1a00d4401880b03540300801404841c2d585900d00780d0002c803444416a04156944640300c030380321042021003d01c10b00d03600140954a043c1c0304114034420302842c400c0c4400e05044010141c418005141014520465003414035950380c802141c180806140704c0702201c3d82842c804505114402003940550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 245331241 1250 245329991 245329993
    0x7030c060f03020a0e0d0f0204050103030806030d0203030c0307081b0d050f13020a03150204090609390e0f0303070b1510081306020408060403020105061318030f120c0809 75
    0x208010396007907080380a10400480810034104c5e4618080c034196440c40c812601c50340e00010714031003540105c3d003191000d0f0001c5002c40e51940c280101c0d403070108410080c1015510042d455460049031814450101a20343c40c20f00014201244500c842480d80d118804104c100c01a03c8501000d10f001c0a00380640e40310402a480e48080b03002548104000c0801a801414001e6810b1031695070b2064560f04802c07a0121075803e00011550384e403103004040080400040c040341c0a04220034010780c1542e0000321441c001d4054510000003d03110305041160b50b40350400c000b0711a0b07a8000f00351070285084441d41d0501000a49200704001e17030f00524024a500b844d402e08180030b030005d020800d0451000301c000700b481c41c40003440448000390454061842a6030141c02c0640d2448124a4040151012030142c0d4445040201c1e500300418003040c0908000028000b0320121280420f0702e4103441c802400304601010a10810390013900c810034071410380c8104020040801d00c00070709114082e1685505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 245332491 1250 245331241 245331257
    0xe0627060717031e0103110909030c070603060f0801060501080103060b010327140d0504090209030715050c150402150d0b100e030f060f061c0203010510060305160f140c07030c06 78
    0x280134500b46107050703e40c0a83c0a10360021801c00300214443c4c003d0412046e0300c42046903511604061001200401454a021035154103001d503800c4003620540002000e0303071410b0400c000e20780c0d2003240750381100c0e00064001a8105003000403805042c9154640300000081c804440050b0807030104c032403809026002c1080760342c408120481d04c405081c40c2ca0f20000b1000d0105214914a82d4002d0090804c024202d07504143d48248030903200115521100106401040310721103a50180300d9104400d860318014519854540d001550088110945814440000c10510b003403002c01d07840142c51740b0340100b88145488514900a114241070170010f40a0300941c00013400010300010040c2c0150409404812540d44000901080a4546d003c04204200f001c0a03c005620284030765801034010702c0640711003134180f81d409415120058003c1e00110460a40d0340002e0741e0102c20940708560a241484005009504030b18031400740144014040c020480c000042000d0114808200c0d01d0b10b444a640c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 245333741 1250 245332491 245332531
    0x6040b0d14010e0c131a030910020406050418091a16020102030405060708090a1b0609080c0d08031b0412030e010f020c0d0218070f0e062706071703 65
    0x10760000030b2281400c00c51030403011403482071000300981607890003049070b6011513545000700c4007440611402c00340148000414000648010f1000803200da28501c0150724142c5014402055441584103040d07000c6202d55404042035155000f5454041c0c0011800e40c445003918100380e01b83c2010303500303400c040515100307018041740107009803440b858102c8080c10940c1e0341d41e54180d54803e401800b00c0610300034000d203400040d004c00007106007808607102c45811381e810004050f01101c1240c1003040715922440070001c051b5180e941580300f01e80c0c0110101e46139183c2c140004040c20500744041c3c4581001719010031450030444007414898000ea6854019602d002e00540748141490740d6840181c000408031862030610203448900b243c8044c100302c2c0140300c1340344031407602c04084c0c40c020001001c80d2441c400141c3c1c0303d280402c803201c0490b001d5250031f0180300c0b01c4071115a02ea01e04880b4080028542000365141816100c00f240c0000c0b00c4d140b5a0180b01c40c0315556170080312404002005141c5981d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 245334991 1250 245333741 245333771
    0xc0d02010c0e030d120b0d1a0402210a11031009050a05060a05060a090e0c091f051005040501080a020412050a03090f0b16140106180516050316050906040b0d 69
    0x40c00300c0b50075071105160f1724408070803900603040040b199500b0640900750900083d02000c8003071013440010400541904240c8104a40d900030700c0305042c0808824001e41c1c8003810082444c0903c541e0120504201085107404a0304025508000d90341c1d085c5001c001000341310000c50700040b024814415110b65a4a03e10300350101e83c0306664082d0130030345280c0140b00300401e07544a008684802c00c202c4200c050700d140010004001200e03010742108801c0c40758480420a210304134060001200c07143c55581ca40b130740081003409030780302c2d16040050701404242504000d504036000341089440381500850b0604001ea030f02c5e1403c6108074000b5106400000e0642c050b5007448003501e08416084c1d241101030011000e084140003025522040c4a20305082051004d1003540001c3ca080c7c070000c150101da9a91540480ba0b00031700340d03401124400c0304082c5141d4010122039020711603d000c400e811070409802c850038041c18440f9904190006004140500c41d2400750603e241c0309042030054020fa40446 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 245336241 1250 245334991 245335003
    0x50109020a0e100c02040915050703050405030a18030206030c040501080c0f160614040302010c120902030604030f0504030804240309020a091109030618010b0d1505040303020c0d02010c0e03 83
    0x200005148031104001502e043c038401d0402120038906082450703a560001811101d000804807602c03486e500c000d40d00626a07010350381e84840d003030030100610710701030310b8185d01c0e4490b03440c00c03008201200c101161007146184500000e141c002d46030585a1030040406241c642c0280540383c0400d03c0e080000342c1640c0340d40110345245440d9000036050001d240d00990240500700003c950440d1118048800d6420698005225074025800070802510340d95005d0400a841d6002d03550031418a00c00001580340041c0041d0442e503d480c0040e9058070b0940c0448140c0100d404c028040c4000140025000704400d00d051a4034034213001951039020307850b001b60202c03010074030025007000103070740c0421a20207240e200365408c08455490500e00349004000a0605808a80c001c035040d6031201d1810a41c0024418000c2d450001d452680c040e000d5a10748084100300c142041c4141922a80060100340c03180e0190751a100c2200300321440000c03011406400f030102500d0303080009224000f15141e500c1c0000750 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 245337491 1250 245336241 245336257
    0x6020613020f0a0803120105042717071b1a09030c06070516060c03090512060a05041e050610080105100902070f02040911030105280e01020c0313181e0e0705060d060905010902 77
    0xc40f90b540ad4250303840121440002410320403070f14041c003001e00490100301011305c1c2c041114207219040ca0600504080c0112020000780d0050028005410141c0b0006207809010360200d4807580c88040c107241c49860480741280072104541610701c0060020f400104050800c1d109071200d95159072130b45c081c480d60000050740030300e403948840c011654480c90350b072105807c1805805000d00c1c0900d1203a0b01508212024006c13212a88100c5c1040822210300d00f402d405408000000d10142c245010500c480242d070317008001ea515400500c0d10308105003440c865070b102e41d015005000c0700c1c40500b07010600c94a206489400381d402c02001174116807050003201c0011400035a144014001280184e00910b0001c510b42c1c4190760030807404200310b4040014215000a9031790010800341010002e44045503004101410a41001c3c40e480d00322061403526030020050402c009000415400c8103450010107074842600107900103521140302c5032a03000a030582e54089020b018690765072010008034416a11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 245338741 1250 245337491 245337551
    0x408060f040f020418060e030c06010f03021f0e0a090606030e010c02060c070f0507090605030f010510030209150a0b180d080706020f0f0307090f06020613020f0a080312010504 77
    0xb500a0040c6410303440100c009000c02d00da4501c29440b561350404480510100380c86944c0085503507030b506841008018090024843c08021042c41c2d42d0201d001511015011490142e2449916600512507a480c40040700c004000411040e521480a00288510300950000905003003a00c410440d050059800b0003545900806055541407000399441e00b041104907500080340c0082d0003c01c000b0008a00908440f100000710603180000700b52800380d45030f8070200c40c0e90401041007840004c2c41201802c903501501e03210851382e903c03030707020805488001489501504d84407010800e0030b011009040e0703035804540c41c10702c007100100030030081c00590f41b002800d020341080640c00150194018112802299074200e0030600d451003820300303917002220300c0350009844203810030403140e1103030141008001e2030015240600303000c440d03841c0400341c010740039009106030340108446440b404903442c0100708442c15203407030303525007242503018aa00f0711a59104a0500c810480108118180c008a0180d060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 245339991 1250 245338741 245338763
    0x3190209030615010e090a0501141801090b180907090b0f030601050d030e12100609021c0b0303090d0c0305060114060a0f02010b150309010e030a0906031a0409080408060f04 76
    0x101c035042100704a849014100101185174100300d132540822a805031400d030304007060030740c1480b5030064103880c400300f034a201e10030106c200706a000c0000c810398150b55401001080445c5420040f80a4000d408690403224a0b1842007048905010807c4829560300e02e07010300c00c3c10048410000890444455507501d50000001005185031003501c050f2000d101e42061500c0754030315000202da000a903a8a11748e035810036044166040181c2c40703440040c0030492400c50a103052440041070f20401013080c01c40c5503589040c040e546580400640e000f40800400c6121000c0c0c007841c0c200a20b40162200701c0d0b00303120305000491002c0c0720070040c3e141101d01070415800d047c003842080b5025112030340301d031055540c3d411160100b9102c8400c1f000c064509540e16a0b9241088102103085484840121030705d5002400032842c1154006498001c50382d4900e808542c440d0506490440801d840f00b17001c3d030161400070980f08201c0d400c40544102c0d285402a2416965694100000400201e8000384540212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 245341241 1250 245339991 245340001
    0x60f0504021e0c100c09140616060507050d0f0209061606090210030b090f010302010503010510030e030a02071a09060405060708160302071403030415140c12031902090306 75
    0x1940540090501a010440c401c03107108600e0450f68440d07101d1500035000b010750307244030001500540312000704a151099041d454002c0781d804048011b009580b00d0440080d0b00428401355201c078900076070b0840c00801941c14010009045540529600046141440650122807026100795140c040b4060803079460301403c01114056604021360481da60303581c514644003d84c0b00c00c1c05c56042c013041610002142401c0c20208011480c00504001402c100200184010f0340d0207415281155401d0b0b46c1c2c401d8010551005070b02134000c0c64509101d5101c046159400c140d80010894125514160080740401d110701d461182442042d0308590810801c0200700541d007000c500a00c402c900410003e07050400900d42840d01c9080010243c0050340205002d00203803104852444c44814110000d40c0b40ca4034084010b80304c40403000c00710b006d01c5021a40b5020655034101140e056941840550b800e000050155a501790400d4450150703040c043c0c00c400d41c01031800c2c421210f03a600c0040c010a0680d40c1c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 245342491 1250 245341241 245341249
    0xb0f060f04052206090606170601090510032307080903040f030305070609120801030209010f030302060606210712201815130302030c0d020a0e130c0611060901060f05 73
    0x307030340c80c50f1411548216280148194810715000d0311207142d02250305403806a00500d4804001551280c01826105214650707070042c0040c0c0c21507205581e00c002d00414610150300906448030b200181703940070440500c030420f10044041c41135429454400003a03c601031074558900590050a203c0c0d20007078414004680100090140300d44200c0001c40c05640907503400d100c48a009000b0320210307c3e108014800c40c905020001c0c05070503e03891b50011940380d914003c0d9141c9001d000c45025103c000781c044c215404038060b115010101040407030300c3d410002001407c0b4000d0402c035280181c80c080041c3d840c041054030000c04402a00095030420490a41101410007001c1903141e0010b1204524250b40f12500003400d010400081c0780348005146005050606401d0745c41c451044002032401001079450a002d0410307140342038030701620b9950704203a41c5190405507a000d020381d10711640008080758848030640e00140610142c078040d440e01d04c0c0041c265481d43c045e83e1550401c0c01e106000340c1c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 245343741 1250 245342491 245342509
    0xa02040305210d0608010531030c0204090203030c030c0601090603080702040c03200405090c0906031b0c0a11010314160e0a170c150909071b0b0a0b0f060f0405 70
    0x810b01e5503140341030740d84030140301158013550011009944030000c20080c01007480a4603590307101100d02030043d4800640403022403080400040c2400010f03c0243c09644455000c1e902c0c0340d070f014007200d0b9a4410080225966001649020000e1040c48d0021608491a0007104126648840040d0a007142d540c200405000c210101400705907840e26000300d081d0140d600342510100080e1813690350340c2030000b40040180e00410b4080441f40c100080c40c0e444d210401100d81c8104d010036480b51082106244180c684901c2d0044001840307001404414003090a26002c1d500c042602d00701700181144100031075880c01101c1d0f030540c00046c0080031103214000d0059000d40ea5000b0484600d060b102c01844030f0031014070f5944c5095500020910007181803c800039102d0403110622035003400703038141c001601024020100c80070003410407036181840c0510000d09d80b5499101d00300380705038035103096103000811801240c54131540640302e04284900b05141140e03203034241c8400542c6024142001d20212207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 245344991 1250 245343741 245343793
    0x507020102130b0306030f01110d151d010f060c03120c1421010e04050a021903080d05090d05090306061009030213020306031209181504020406090e0a02040305 70
    0x550204200b40d0042810010000600380c80d0240b682c4078206003090503d05001d40700e01251680c0b411509400e90b448100541e440f400400078041081501141c60b80c5000c00b4a030300441d030952030180b031864070030355000d502810381d0501a1000c540c0d07a0340b440112407007200282c0103404070310b140804107020306042c1c0220314088403505080a070800700c01e0b40801d080c1d005c5030710303d0a4950b03d00c240120050110362003d00404210503a1052810291145521640e0201c4000d2041c08006110302c128849c08403450002c54006a00070745a00c0c4180182001c1c0c2402c4030622030700e004072101c2c12000382c003402c103840c41107401500070840d41e40c620080c000101ca86554100a002c15911700000581d2603140b69540300040100240c1c03242000010326250403482d01414a9502003409000025201c034901c150010414555140842d2a81d5941d2121041144e42c5260031500014001c2941504100d80c01d048569400c1c02d4001d0350340b450701d07641c00c90065000007000ca400c0162032040c03003108080c95014a03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 245346241 1250 245344991 245344993
    0xa020a2906010309110d0b09060622020a0e0402040b09040b030601180e28030201060509040b0403120609061d06120a0209070509090a05070e010201090b06040905030f040e180a080a03050702 83
    0x11744602c4000038241144840102c4840124030b08101c10000140034154011805450010341c0b24000c581101c04007000c0580d181c0365541c0854401c2d011841605a4112094060011591942c865a11040a074082000180210f0500e4034003c007a06000502d641204d101c00805036006883d0300d98000500b1204120b61030601c140c550103c0303881c60f50ba549810100a58002c0900010b441c600139095403450b40c44248100000030400000c1825400c41a61061313062a11090356285014084001c1140c0c1d0840e0005601d400c5c0041204006188c0c504480d01d4171000307160040d075581c4c04100700b004000341c007440950003110f0580014240203003641c2d08524a418002e00b05540100487e0320941d04a0b102c50301d964540e000d22883d180c0080c440c0400c504284028812189907858050f141403000e0400750056540c0c21032003090080c14006d46801445402c1100e5a40b030742c0b10001081120291440c504104482051b144140000101120341580c0550002d0400041c0f12060b002030000505010079 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 245347491 1250 245346241 245346263
    0x702100c0e06030c25170903010e0f0d030b030c060a052a0a030e010c030e1e0402030c0c0712240e0a0614060103060806010e06150a020a2906010309 65
    0x100d0b55a460266104a800e604290780720011460036913081e0004e800e506404d10002035031040860381015584900c502c504a185640e01410000319004004050702c404030b0f40160541c0d05902d1402090000d1012419903043c460714000d00105a1106181c10081e03030321250421001c65070f14082c0e8050480070f10345105020400510312a00808011192608503598000f546030f0020150450342c2c5c000c07481c4082c60041180c0c585030340c0c0a0700b1501c0c1800b015100f0701b2542e4900c00030b06c221440d01700008101801c295164108000c544400b500075480c0701c0003d01134000003044176454090a1100250481c00f00c22200702140070a940344104081c0d901d608584811080c04e101e03108101c61440c1a220b6940000d00c03008030100340c02d1011000c0d04050405003010300400a0f0340000540038107441e4080fa04100d141c42d10000240f0400c40704804050003100803c14085003238001c11109000d80c000c01e5211401c0414224031a0f081c803140000ca0a0740c6428008103010754030030380c42000c030305214001600b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 245348741 1250 245347491 245347517
    0xf041106030403091e0501050315030106120507080c090c040308030a0b040606050903010507180501110c0307030309080d14040608060d020a15090906240504090507050306030d080702100c 82
    0x20365034401c40d015801324800344010000c020031110000d04401c594400c5041803410715000a01501c0081c01c41d414071211038a000c07116550a500c900000c04400d400300e000914a4505151241000d1090303000320702030012404104c3c28a000b1943c4920724084c0c4807440c103400c42c2d40f56201c1d5000505251a12640e8031510401519180705200282071251101612144600101800e40e800284120104070f510700c545039011a200044000381d41e801d09000040a05100143d45042d1415401903858401c4200020a06403c00b58000c150744960056401d00841020166480c506010f510503001c0010001000810322841c10160821001408818408140d030002240d0384000d03048800742019511140000356008100c0000a040100c000d0100516040501980540d08040301444285140c000354150384580d04036401b81000f900100314505018600411b40e03001122100e000c0c0c480c1a4aa290a901481826115100540c0140f42150301107101d01c02074141d1090001c14406054100c01e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 245349991 1250 245348741 245348749
    0x90a0c0603050a050a0e030901030207060902130606021c0f080c0c01050703020c010e0f280b010602010f2901050a050706021204061b09060302031008010905011a04140f0411 76
    0x5040a076804a40d6092100749401218000391184600c0740c544000100035000c040300760362080c4424200141c45e85441e003400d002a0100303820080d440301e01c2d08103c100400e032550010068614581c21501800d03d40c0c5003003c4072000031016100410b41c000900381c00940310b0510154842c80d5610307800d08028403031103803d0070340300240c2302500444d4001c9903664005000b40700c1c10a1540005004040d005200c8450b00d460b20440080304400034039568007060094284102c26104a60211408040c0d694030080240200000d00c1c00ca0142e42c2003c1d1001c940c2d1000254540b2580c20020011341049046001580d441d4403002c011820b2040600241000c143c95201400c0458200c469961035450325185c6541110708402c040d50782d62580e004800c12580d842848403042c1c80b80c504006a43e0349a602074448010720543c021001740d800c0c401c0c0d9004004040d00903403501c14140122003040d040c88030030070055951700900030200c0006480054041d2130020380d9950024001c09009010708170740c2e4046 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 245351241 1250 245349991 245350013
    0x4090209040c0302010e0105040302181003050717071211040b120a050a1a0f0a090c0b040816050301110901080a0906140f010f140105070302070b0307090f050303030603060c03090a 79
    0x191814041d2080c10025540c200d60721b06082002460464a814255400100040225100300030041045da0001d40911000e8035000040c40e0408101da10b084d80e590491801c5481d403000e0401603000d03000002440c1e9419110b40d40456074011801d504100d0071109010040c0807007800542d00c000420b80154030311005201c60b0a078940144c020344107070040d03070506101618003c6000e420300d4031000200124900c442070010f4101500b0140840c135031b401030903d9007070507075281c008000c040c800050014100000103100304030404072000000d071265454042500700c034050001d81c1e90007801000030389019881441420391002c8034030800607a5807001d445440c200c0f070543c2c1040d0707004140e1100380701c104a0000c82c84da0050400c20200f10500b4145003050b1011280441c0c000c0c103000004c903000301094020300c031030006402c41c01400c6840386004030006000f6041442003000c0d1300c000c088040380c607081c0441243c0c41a103001c0c00a28103034a0f0352503807401d140e100400109085c02019007001c0000c51a410b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 245352491 1250 245351241 245351243
    0x6120809040519050115020114040203031e0405060406201f020904062102031e0d0507021807051809040209040f02060c0607030507030c08100302060d06091b020601080303071704020409020904 84
    0x7010b030380008000306c081d085403192300c1d02e41e070a00d60580030000180e074004102c8650240d0407000807000c1c14403043c260160700031a040030782c3c000c90202d03010840039407040c001d0301040680e00319905034048181b00103071250690340164180f0250488850301030242500107050110000d400050017566905802d144100103049010580d000342060301c044d89420040404200c2e14591010030601e031148100d5610b41c615440c8009020020a0050656817040032402c1c1c0501800346010103468880e000800a0740300c00f90450101800340c6101c0c8107420f110031103d11540e8040c0c8809442e848a0310b49041c042d5504000320380c4000d0821803180e459070301303029550054055450200b0b0350b00740303d9030140a58281403e0720f0100081807041081d042020712200d403c5980558681e6030f40c5405021a1001d065103410080b40e160400c1c424005030750004407840d040740c0e00ba509940355640c03282134940d100d100c04e03558540090403030711800305044240da07000c541041c4010f20008061306a42d02190401c082154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 245353741 1250 245352491 245352509
    0x60807030203011508150411100c151a2103070b011a0c030a0804230601030b0c03070c03050a1803060f06080705130b030a1406040303061208090405190501 68
    0x1000c2045040c01d001c0c0c0108120f909030710310721190404000c20b0b51000702c0e210080d0843c0017072010800388201d03208410101341d4060a10100030040d04030150224500400841d00c07841c0d100c100c201c0080b080c0c814589548000c50f54000300a40b04010004100350a8120340b07150308a0044003c0080340800041c49a9032040121210541c904500d4502c8900c0d460603c0003a400300700494a81c482c40882141c844075403034142410103858a0030008108401c41d0058054082d510803c1015001c00180060407680324200048096070382400c554a00e000503038454002c1400621090002030181c009031101c50114907000c10703111001e10034007039400019442510740c541c0da03990002041c42540100340c0685030240060003800d141101090800c0c00c1e0034a482c4d507041e514500d0007080c1d80c0c181303d8525090b81165100018440e06001b4544840098408402103460268000b07000c02401d00e4910b1a00d07000080d03207040104180910019000050030a4a0209170b2000500803900c940300d69406044402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 245354991 1250 245353741 245353753
    0xa0e040318150804120c060213180c02070e040807050d090603140c09010c02030a06050406050f010e060f1002010219050408070602030310030f02030a0614060f1c0b06060702040608 79
    0x1c880c10390012040e005184a04201d602c080000d541101c0c03c0c5820950103000194442c100a900302c40f07940c010f0b54000c0185000182092483c40e00400354020345141e0081d401d00d584902500b0710031941c06c071410a0251f000341400f0000c50241101090303100380070342c540c1c0b8684806655590709206c403604250004c03a610020a01c010780e4184500045c8040301c6115201c81c1c10030486142c1607000708414541003240c488a514119181484541029940010700f4800303400c01e0f24204001c1d0004592410114200e0700000803031001610009014040c007a01d08044a01c041d000c0c00b00031009a4550700039503400700011418075010002e21034224405554150310b03a424201e040b82000c2259206404541c406c1c030620413a40c0041c840f09040300d5003c0c5517150038002510203e81040810500034041614202020140c1d245030800c81d0700c229411180480c05443c0041040501140113070004d01e20070320034cc01807001928114041c0d41010b002880642461000d90018040e50556003180031150010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 245356241 1250 245354991 245355017
    0xf130c030c080105060a0206160e130f0b0612040602071109130215041421030307110705271f06050d0f020906070305030403090b03090606122a0a0e0403 67
    0x2c1816180900000c541092070300000010007540d811000d400901c990607080c00e495005030103030184103000300c8040c01a54003121649440d000a0020b200341c2d000850a050940820342791550880c2c1d204070a1004000d1940c07a2601c0d04002500100001c94500003408009801075540241c081d11802540440d00c0034961a881402400004441031403142c8034280802c1c0611049009643d0360014140d801c030105140c403001c0c60b1080b0b0500441c0202d240000401d01c0905036011844084e1100b0000442d3b00783c83c0d40303406200b43e0101200002c141500c1a80c0c0500d0304108007101550071501900d80c0c5002c20452865911640000b07030321103c08500001440410420f5a00071440c43c80030031031045080010303850106a451050032001410044000002010903005003204005007070380b481c2d590348a24040d140260b4a5009885003840390942e02d1145c00c1140002a03601d03024414075600c03070951300540b0290013160310200c000c82e500400c4084003142603000725294512490290752150812030710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 245357491 1250 245356241 245356247
    0xe1b070818040b090603150912040f060f0f08070305130803090109050f161e120c0306140601090902130902070602070b070503010602071511010e070f05040209090103020f130c030c 79
    0x21000307400e80144c0c1c0400400c2000e0f43c3c0410800101d0842e8114100640c0c1c402d0b040f14202440314680980c0d0501c049404148841e84e0304403c01038a0450b01d8603a01d02600003006d4403105085203088001034540c86c00140c10500c01e800094104085021001e22181075940305c0d80140c00c2155801700607952841e918007401002c10600c03512006100143c098000381c1440030305e40544078040c00303090b440c4228403480c81c1c003405d5996200800103204d541d1980c05d05490000c00c1242581300c25503040d410b042e084440c1c0a0214091030103628140c45103040740340f4203040c8201942102003411025000ca02001440041c2800200200b900c20000141e441c1054a041e401a000c09000707981003120500040c01100e0300040e484040d1001241c01c05040d1401220450300c0d0700a001c40e510555080640503202c0e810009080410340300c1c800c003112440c0c4e40301d0041c03008038022982702e0350340800c00b2001040542000b100c28107440d40c01414401c21114050f03c40c20a540c03000740a800000d030b0322030300c1450f03040c0c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 245358741 1250 245357491 245357501
    0xc0a0c02030c030d05210c040302190807060f030c0206070918090614040618080f07110d14070503030903190303020f030c07030f0809030a110313060215060a0e1b07081804 75
    0x141c001c06c140840c1040943c0390078900650000a0040c000303265160f00004100707800c80000c044072030458100540b58000200300ca100d410200010904101c40008140d0000c01c21f00d2050506541d5041480c0c40c0080340f50603643c0c005902a0040d41d00c0c2c0d00c95000c10024056128940c0401d08010308a04180c9458002c682c51301d8138418440d240104a540042e408404980d440c83d4004c0d20700b074507136106e414082605411401807a6001204013010402c200c0580c04c0b14cd40700310301800380d65a09940e0014580c80c0d11600e0a140c0c6e05400031703401d40c0b5415002501c01d0310a54000c0c5801805c08032900d112011940c030550703010103680380100740c0d8806c00d0303400180289003070070034509202d107402c200c1c0f80580e4a002d40600502800b84203ca40c503070040c0300f0801e95501c0b00003005010700c0e041d03445d68069118801076031140c01070032103040003980c1130038614210350446a03445c148001c940d031140b01c0c4c0c000d06441001503005c0142c08006510205040e4400340000b001c180f00b0303d906000034041000700b291 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245359991 1250 245358741 245358787
    0xb180312150a030201200304090c08090f0601080a0201030213080105011212031e050a2a03060f050a0605030c0c012d0608030a030c17040605040c06080c0a0c02030c030d05 75
    0x5074000e0001c1c40141d070302c1800c3d02415207030110100c08000006e50b245040d802913401c80c01c04140340c0347d010b1209591001455004400a0307040c2c0d5400e4100f1901c1c1074489409024851480e48007500c00c0006502c291b0040100d155025501b08410792100645801d41d5401c0e44146035030411034066005010317461001a04407104c5080400c520740411440714151366400e010348000c00d9031240042c45134007240c0c2003494200c400500807017083c1c600b42c0c0103651a4018404040000e882c4c0a0089001d40c0c03003000500640300d0052a0142c1d451901c0400c4030301758002000902c00c00703010710016480f83c00901030f000c0c1d4201c1c81c54528000744202d60a56000f0184001c02641c4103003014010000d1003404402c8540c0d00d82249070210316144030403c16644101e04400400d0017207002d408000c28001603034000341c0140c1c4103000d02d05d40c1c1507440f1000c03213000b01c1c00d4600c8220300104010354410381c0d002d0000303000700d80c3c03001d0305840045d204640001c2c02c1440a6041e00b0118100190210075048800b2014400e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245361241 1250 245359991 245359999
    0x2060103032006040609031e0305010f0503030421021206070309111f0305070c020d060603020114070b0609040f06021305210a20030f1c0c0f0b18031215 67
    0x100b807880310100d6881002500151045a540140c0303c18548540705840004450340241080300350001070090082400748684200d5035002480403901d4a004003c8030229801303410440803601c00d20460194074058144100e9028000c40022a41d070207051068510482c226240042c0000d42400c02148440d14880224030408402c541170b004180401c00ca0042072032245400110340d5a8083c040c1c400103800e0501030743c0038414042c0c500c1003015640100f000d9a1003aa5101c080c42c60003094143c43e4003071040000d0003980c24100084660400c450710603400f80c010f07490821600c55544a090490f0b0041c40d07000c00006111000b4406814503c906000c1100104d040303040031607990640d640c0791448420010f11101206080303d0340c02e0440200400c80c818020140c030b04042000d98140d5551405501400d81d04040001220486004110040b01c694001c660700884000c69550780541b42e2000705404040e854845003101100707810001341c05540000c4040a413541000007404018a01900b0810302c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245362491 1250 245361241 245361287
    0x605040509030723100f060e040c030813051002060f01080708250b041e05042327070509180309060309100f0501051801030804050126070206010303 65
    0x10101c000200d91031035801c2800311001c441409040c0070304200c036419404051098030861000a8100ea202c0d0034500e2911710304100305d940c3e8405800600e44101c0d4060100660900c080020030440d01c02400201901e00210620b140c4803170008800c144030495a50050b841001040800220212620f004d010008010310341d2600e0008803d40d03400080b034901c100303400c4039181c00039460840d9116078007500d1518030f0701e91110b0b1204110240907252070f43c006d589030328990740014203040c240305544080e05250801d9844040761001c03072020b890043c01445240052040d0010280c3c000606640d6140c05032024081640c60101041145440604104010b842d01840e0005c1d0040000072629142419030344ca0f0340f603986088400c0d0034118152017100401e0300b40719081c50b41c5001d0f503002d01d05841080f120712010b85a031040e0389810030400d0000804100d8100300c140055800ba0514005440d109080004000b991040f4001241c405940c0c41d0090ba0120005004243c0c002d021b01c00441210f81c00d07081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245363741 1250 245362491 245362501
    0x304030503150a0810020915160312050c090402031f030506090106090e070e040302150c120a1a010e0f0d080c0607021902130e0d08100501030e0a02130b130902030106050405 76
    0x2c2c8615401748138445042c1d002481c406d941e250440e50300100c109072040240c66070b00300e19850700c81020852003100080c00c031034090042c038400382c420f080c052011442103a08202654003400029400a0941101c2c50107100341c2c40c0d2000c1c010031080e005103200360003900b15820481415401d5030b0b210b800c81d400140c140307102c1040d1280c0002e01d443c11a8910b507528282505c0d00c0c1026801c18400c819200c1001c10035000b001004120007000b401920010541884580d80b16136503401121100d0701e500b8200081500c1c2c24040c0d600c1014008641f01e0014443d0f40714034031344000203c0c201c2100f070341120a40700200d01c0184088041c4107965200c00030380003410000e00e0211203100204c1e42c03210000d2280035045003411030404103034880d4042d000b0740070031150311550f0040c0c09009103601315400e099040203580d0202d4030f54803070b008403030080071a80e008000404d91942040310b1540300360b0402c21815550a101c910540d1140380b440301d50803c040d000200d5841d03500605095480c150041402181008103100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245364991 1250 245363741 245363743
    0x1015050d030c08090a0503120a0e01050c0d0e030c220605010c080a03020c10050112020a1719020409020607030f11030a0f0e03250f090c020a1709060304030503150a08 73
    0x10002d0303036110004a40e9110b4820010b03400300e0658101a03003500c00c560741c18040320080c0004140031816926946582071405004560342d01c1503070404103041c2c12007603100c2840ca0003088414001c13031b00203040d910300300e07030303403808211000d0340340300602040d8800318121400300400303105031005080e0a10340350200c2c10143d1102101e40c402c800300314042503400998040707064020300c01c1d108400b450503028001e030f5944502100d51650b015106903c0b034900c8620011d9804101c1c2c0c8031148890041c40074000c2142d80c070624031114031100ca020ba8125032903a00b1840103035541d000900c081da12a854403482804002c04c000d228542c01c10090019510802800b120aa04150040c880070aa072800742407a624007800319043c0400328400f0840c643c074030b07a01442c02211000d03914003034a003080b00501103107988481400c191400d2944800c0960456108030f4081103c11001c0180b5502102c3d195183c81d8a0101041c0103600032581030740010008000e00290a105030003200d003100c02241c50042c00e505024180d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245366241 1250 245364991 245365007
    0x90312160e0105030703060b0304060209090a15060e060c06010801020c060a0b030604020603041e2d110607020a030b070306090605040209280306020712030e120f030709081015050d03 80
    0x40d0600c107004c000070301c0d95403080e04013030701501040850545908052a050f80039400c0140034070722604509000540c0c0b15080d1040200c400c110505000307030782d03250881c03da41c03000c400d0b500c2e00e070015400c01040b0741c411030030015075000380402400180d45408401047d810008040d001d150020304101407030186580010301c00380c000303804a5805942e40c03900e16100c10000200c000301c07007a0ada09010074205010362020860740038280e5030014210000b5030820318101d2111404000c3c000780111a4240e52800c01c80040d2005a00c0542a0042c080d101d440300c0c1030450f81120034100080d00c03100700748440040c0b40651001030805580540c20f0841c00c2c1c00240b904074248081c5000d000c0f00000524507001100340b81001590405002c40d5241c005042c0f0b405804202d030b0161010030304225800b06412000102196501d0702c1d6040d290400500580c0400d15500241c4030781d04100d0b009a010603d9034060085203104001e034400042d00c4500c6416140c2d40191503440b845c03180005110410101e40c005050b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245367491 1250 245366241 245366267
    0x3020d020616031a120a0308151302180904060605130c05090d0510090b04060b0603070503070309051507020606120303061c02030102070c0f08011503020d02131409031216 75
    0x1010035859200c101c80001d14141c0c015a940c0170440b00f07164422000085032410160740642c2d078007081d0342d6540d80380e51003182c10000b82542000d0a01a56221854250b01820000c3ea10315000c1e11030f000d07a400020326001007035800b5106030b9a60300d800c001510f08400f000080c2580140103000c4841d80e00d03000b0b800d6004d40054140101e9034181c29004104c8280300382e481d00d94107044204003001c00d50803d001a034000b00c0b030840311149410b0710b034000e0389402007d40e17108011942d6218038565510320700724040c2552840440340d9109203100d4942d54611450310318490b0710305600501003480c18404100c018180801c1e202d19580041062001d591903141d0f54207400c0501860a00a00050f407000c00c1c020b00c91003101800e076907889a8080340c81290126075004075009200207101c6031400305090074030070005120080d84130b80050031071401810550000c040d01c0500010000d8200c1c806412003010310411030320702c021038000050051070079402c40d55558100700d0210b540310b40321150724401781031484640b07a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245368741 1250 245367491 245367497
    0x6022406010806010903150606030f09120f170712050f04200102120d020c1002030f06040f0e010507050d0f0b1302031f0f0914040308010302040b18040c0303020d020616 74
    0x2c00110f10b41d014410442c02180d0001d407000c130314005a40302d07500800c4217000b6100000d090400c0042c0003005805100906030304203c12200c5c4116210301548c42041035803105042c080403058441e1101449926144204119210480d09800341c81112046400003800e0038462641c060034040491080000e0010b1205050300c01008034071020700503032524010050707200741c0540000315424080125006000307100030600440f064040d51b804000305030700084410a880e1400c4070b000641300c3c68282c01c4588220710101c0700140d12030001a801d420f48804803110340122300300003030b0071440164030320940c098080d6195041120344400c500084140c0c099800d0688207079000301c04290072035807004d80021100c3c0d00251076142c8580d101c24410340f892280c411b2950107840c20159201c00c40ea503403c0d6610540e819a90401a68250380c01c100c024a01001a5604404488149110b41194803081802180501040b03181c641c50346c507001785080d0740041c40d0b03400c6400100a110582c00e0070900c07002c1010641c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245369991 1250 245368741 245368757
    0x6060501170c09030a1b060215040302060619090e0106030221031206041506110d05040b0a2010090b0604060b031303140409020a02070e01060f0c060b06040305070602240601 76
    0x1e030020b4a4080e1520717000d800150011840080d24004e40b03003001c02c59516809580107502c45080519640100329005000350f005000010b00e030b031a0039941c1900d41c3d0404510504850f480b0170b0740b2011a41c20283c1c0050300c0e0342d541d05c24415031415501080c04041188000c0005070300b41920141c4a020b8085009145010100403e003596100e41082c8109100f040303034661460369401c40100110380303001114955014102ca0320340054131500c110b8081d030341c495a06a1814081d042c003200d05545004c60710341030b401c0908407030b544403070203200414204c0030800001c41e031228035041034118020060401c5111f2441c0110400900d042c08040d613600000007548582c046032281403c0e5500c0c0c0302d014441c01c4000700001c0100f58000294003815030918940d080f40d84480d180e4030140300d000028000c40007c120b07411081038110f03100d42c41052840f44220401310303a8007501008502c258001341c00444480e0400441480030b95030422401407014a07202900e500003041c049070320070b17011019100d9410807501d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245371241 1250 245369991 245370007
    0x909050c04080102070b04120201061a0306120d030209040e03030103020109030b040f0804060f0809010b0f040207051905010209130504080301091a030a05100b030a021809070f1206060501170c 84
    0x4100355402880c0b1038000350350782d9007240b0703110000340c800b190105c544141c410080711040d4414840c0c00f007a21084001500052407010803103d0680004100c1c6030f01c8010505c0c10001c81c0810304c40341c55440c14544002d81c40744040c00c00c002c16210382503940911607106100410160703900c043c04ca02200c2d00b208170440d0545031402d01500d46280a6000780c5075000c00100001c0b51540140802c8050b561a0340c1c00250341c0302c8014175426900030705020303540b01142074180300061030954000e003010380c0700b10304a4205000305c05c02e40680301581a0140d8a81e5030110310070b0700391308029845038070004104408114a29141e40d070401700b0b00040c003070b0011503603172400c001e900c3c0954006010ba411200808581c0c0100552521a540303e030312103101e000880c05e061049880b4140056649840c0e94001c08540303024031044a82a00b214004110100522480030005a81c01c44500c1c5000030304406e071100c00c030714421800c024040d034201d43c0c440e40c10401c02007800c406243e001c2883c26000004c00f02ca069030f41401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245372491 1250 245371241 245371261
    0x7060b120d4d07030804030b0f0402010c0b060a0302041e05071e0c020d060203190b03010204051c0314030c0d0b09011809050102040b1b01060501020d050d11070b01030b0603010516090905 82
    0x4102100d640e02c207010002c01805019005002140d225188c4000665200f10080742c0901081d90024007180d83e103059140003401901915600c40360203444505403c2e9280c0000e0143c80554403002c0100ea2100d8412032000714900883c4da002c1c120b428000c42040c42c9914a41000000c1c01c0041d003003103032a011084c11540d8030a0b511943c0d070f4020000b03640301d04003000354080e640342c4040d41000d00c034a8401c0f26680d40c1410b000f6a0120b840061900031501d482d400c5190080740408400c0342000400c00409002c0f411003009180500c0d41c44400e42e80314039108034004d04485940c030f416031280d1446001007240c1e405c2011206481018040c3c00301d1002e00ba45090780c0640980e4103c90320540c00030030340c11448440d01e010b40f1201d0407210001d105682c0e8a1006903116680e1021382710015a04004e20381c618205030f0004140901442161441c010f8240c540d840c40404c203030000c1b11900455028020589024001d640e0081020610003402d1445500068440041481003000c5542c4031740028500d00c40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245373741 1250 245372491 245372627
    0x603020d08130905010b030603012403020906041d031209060112060c030e070602010f050c030103030c1b03020d0303020a110c06041e03050d0305101406030c07060b120d 74
    0x3c3c04003c184075550315414182c2c181d40044403103034025071070900000448514241128609909071840444a07400c3d90240100c00000400703480d007040d29200d0520f41c411301445521140701e0750f40c01454403020f1100b842c01400201800171314555200b10014059042e881d60008a41d0383d00c85000254403144030f105501501a00c4001141401014800101c41e44c040d003000700420010701040040703964151406299000078000900055102d030700b95400a2038404a1802900141d01034144195803035000510380c1c106404118002a000304404100640080105500340b4250026105071028000841c42c280241c0c8a04400100949103101c85a610b40e51020080d580000540b00a040003080140180c41c00b581c001c4082020100005049480442110314003400148241d10f103840e0702c4d9120741030760068041590b41c5581c80b4003250f01a0303202c0c6204202d0074540750140900010250f40644500b079090150800038030402e440d502814000d0b402107901440480c0000320140301e0310b00804c42c4c08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245374991 1250 245373741 245373749
    0x100e0f0307170136021203070606210201020d0305061801080a0b0601180603051e10032109030f08190e030d05040308090103050c1e0705010507030603020d0813 70
    0x101a188010507008071044000c0c6070600340000a0106070040d00381c0041d8000750b691180c2d020210700406011307550a400c0300d8042c0381e000514805460740d0804100742140e0103044110780d04c56840360104510310b860591060080c040b02402104000b05800107521040080644020540e8603000100140d803620480c607400303d01144200c4c0c583d84c40e001c042d55129158070054655404980010348a50300c242c0e965080107992210304841d89240000c240d02411003d040c0c1041200c041c51107192800c100c0c44400d1242041181c0f0881d5180b030350801807501c12841d00c003440c90903450444100220f4000320320300c0c100c03075100506401c00030709410b1003003681c0550464441e24444010019940550003041103043d0310084050b2022442c85a405032024402c922000b0040f51090100b030035158002e50000307a215200000252134001a6180181044900389988003400c03408603448046c84024441c460b03215485003001c00220b410360300024444c990844000340010000142d20034000003084002000f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245376241 1250 245374991 245374993
    0x320a0b040b03152b03090909081801140720041401031b030b0a0c02010b04180302060f0c0327030304060e0d08010e070f0221070b01090b100e0f03 64
    0xd941c60300e140d0311803507009030f0b180008590340b401c03501c28510b0305408034069450811402010b10310743c490711200040c9140825010303c07200d40c0002402c0c01545c052092894418120700395980c2c241e55005216000c01243c00d030401c201058020301040401040f142d1803600410500000d26281c050310001d0b030442c6c014950443d003030020014460302080036281c162440380c10040c0000604c1ca054102c040814030000d0424400600801c00210503940014032045041c800400c66812032000b081c156040888000c2500c0c103004060814076074140885504920309105a800c070b418079081c6207801e0f0002034030405610001106011880501c0540004044c860f81c00340c9884e071429051142c000c11801400c001c0710301800d83d45e904103503c54100380d8141c82c160310510f81207848070a4112402840c0d00e456805600c50189250000c520580d00d1000c0415803000712641c9542c2ca14041516840681c82056210b04022030b5080c0c40c4d03a110181c502c0051249050b02040510750b001070a1079850b41e00c8135401d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245377491 1250 245376241 245376247
    0x1c02061f031502041505030c0a2d110c030705150903160305030a0e0d030807110304030c03050c19140112090807030305240f0613080d0804030207320a0b 67
    0x480b200c03e4015000700d07422120017640004003d501592540b00c1101e06818000041003e480c03801c0c0508861410b01441c40081d110355080c000c4598050650049200080303212800761700d0b507900003040b00342c541000a5011300002c40c982804a42d08282044541e000e0b40c0011405082c00e440802a0b410851b01c26550141441c2e92405c02d59280d500041420300000c1ca24802d900250804001980c1961783c1503407160f815a036040c00c1284c0f0701000c00c0044007640030401c00000800c49824190f4040d500500241510b060b00d40100f02d0345504425082481c03405080e800c00030544500f03441001c04d072083c01c100c1d070380200290754580100795224004000820104904040c584e060f070040703104800b00c40385d2184141c4041380e1441c2d40111541c0301c0c1e41c8508510414011401c003e80540001d00c4010614052203848281c1c5030b060641d16001d40300090100301c100302c2031541c108114001000b0348032903281061a00031a003d030604d000039959000c00340305020030301c03030751504070304600140401031710140c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245378741 1250 245377491 245377523
    0x3020c0d031707050f03040f0c050607050c04051602060a050705071a0a0b01090807051e0603040b04170310050108070e03060c04030219060806220603080a021c02061f03 74
    0xc55a59040c440071111070000f6040350040c4121400000200840741c20356440e60750380c00d230b41040c03800300302c40981804c0d10004151b10780c000a8803145200b10090070f050307036002043c00304580c0014040c030540d0040c42d20098040340c02150309904000000c001040c00d50b21000255850310410100074211030700d103641d002840890907001402010b0004c42030011600341401164803c51b14005e00394180c002a008000601d05840021814501d185041209000b1400015250b410464054508041d450304001c02c100d40344416600080240c1030701d5007113013000c119403440a03080303000c0d1905201020020900301401034176081c184402c01401c843d15441c01c40c40c4415039400a100890007a4900d01c0f198004100c03d100c0b007000d4403e1640c9503502ca5407100100020a48182d01c40324010240c030300d4498025845020300805180920325040e44e07403088400c004d28091808810086400d4410a81c08a1a07404160f21380c002d448030011113180c0e6240500000e1010099000400800071034004803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245379991 1250 245378741 245378747
    0x40209040f0b16030b04090830130c080f060601270602030c0c04140a0b0111010e070e09030c0d11030f0c0f0f03040305030d090809091504151208030403020c0d03 71
    0x30f52941c0700d40e90034040290a036081c44141c0b200c14400802c5580d050007000760b00905503c8504444003c3d040001241d42c403261001d50074402074072601d07604461802804240309107241100000c0c1001c9000b80807254110354030544a00000e00014104100d01000c6020070281ea40480307203013040500c0314036200d81d65000295403540b1030a5100194040c0100c0b03031076246010700c03c0d0144c0e0400400351a005a866220a5000b05003100c2c1c258103005d0300d811526400310342482041d00c0400000000c0a451b4180300e041103030100b006111612661040040d44802c00e804034105070300381080d040604201c0207241c440c50842c040c00d00305200d0544085442c0d1040040098070980100349007060b540f99502c01042180c4a12543c00090010390041140030140341080d4000025180268034040c00c1c4000e680014214401c1a60b010394441e0b450f081c21f14191409115520148404590f2a42003d203403c104006a05819102030a072120101c00101410b0003840300c80b8a0f140003d0035039180d001189002307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245381241 1250 245379991 245380021
    0x1309150606020607180308030c1308010f05060616020409060b2d01020f060117070315051510020a0f050307060c1205010f12080c0a0203240a090308040209040f0b 71
    0x6102e20700c00315813072034041c0d00340c4c01911400d000420405030071038507040c8042e80007a1810980a20400012041d0103080101030045c0c00f580001040303224240ea001c1064800c0549024480d000400442002c01803800030310800e150b05550100d456440e90610304000d16142c00c005030416110500740158000e401c40303403244841d0b41106c420340c8240c49001240d8440d00700103c00c3d82980404014405199108040c13010701510404490a00e03441e659a14281a02708412084054071101808040c00d8044560762550b807040c2c41c919074558512500a548042f5503002a1040141100075010300c041841140c20f810b400060501c00c3c07101c6c02000512a8601410710240c13607161600208080d007003005039004a031005241c1045031555625040010707406004000d882c1c1c8100344007803005880c02e101910004410143d1100c900c0203401d44244500740080c17480d00e00a161400c040d0029410110258106406440b2021240e50341d20305004c500b60881005044d01d003d581c10414440c0201c552 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245382491 1250 245381241 245381249
    0x307031b030c0b0c28021009090f0e0d1409030d1e0305040b0c2206050c0c040908180a0b0c011506080f06011d0a030c0e0f040804030213091506 63
    0xd89080710b54420700200385000c2d43c10000602d070000c5c0800200080c1c1850307012080f03024409900e01868440d400241010302c0141402c000c544410300070003c4d00300c50f2047c10a00052003200744907002086e5040c0303882d041002032801c14800958001411021408181d400180c005421198540420b40d4042c00c188003480b04a00003e1120381c44803009807103409031900682d0f0104040190391560640703076141c0d400c00c0a0344400d05030110240f00444c442d44501000a010a40307910341d0725400302e011242840f00c2400c28038003c40c24144200b0000e02c0010071201c105452007401c410b404800c40004501a801d0760161504002c00b2880e03800707030001944010502e00c0b011500204007a030b200d400340d40c03507602203842440703046004000480d80d50042d412120384582c0d000724120898440d03400104440056041599034422105080c0015008447c0058001032884501c0d0160720b82030307444808038415130000038003d01400a0380c44000c48182c000c01e04659014030300d81031081c03c07404140001e0095201d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245383741 1250 245382491 245382503
    0x203060301150f03081c142505041202010908030a080106170103080316021e03040e0901020415031109090a140a0605130e12040611070801020a0c030e0307031b03 71
    0xc0b00400407050b5080b040c04492000000072443c0c4c1c9940c45e81e5a480d00182c10f5030501e0660380c4001041895540b00d804440c0c510740321507070300c10300704a000120605401c0740c18803800c3c00a045540d15003a0040140c030101c1c5c2c842910b10400d5102d41c40100c074001a580c0c00003000341b20104c1c051082613000034409050711029a6011044102040f0035001e981c001c1c0701c0035041000400100c1c072400350f604030302d454040740f60040b80d8000c0d008022400041c4000701494a483d00041828000400c00004050f00100480003e40c203040c00e120b10a8189250b4418400c141070351001580c1c00700f0980c5040e111000e070010301c3c008961511901150182c490804018083c0c102031000504104c00c0c2d10400c0c0c180d404c05045000501003180300b14004081c0034201c440340b8803804010486101c400b400800c05007020742c0c0c481040e158181c5040d0701d071030380716002540d0340d9005001c0112010380c0074030b41212842d01881c01aa9916071080403030b0812605030005013440c0f00c0d5440c030880102e180c007819001c60f40320364 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245384991 1250 245383741 245383751
    0x52d070b09060a150f0506030406150f0626130c15030c020c090c0301090e01060306050103050a020102070f1413021c0c0905010207030c05040b13020d060302090708040f170705030d0203060301 84
    0x700e0031880410240c000e8218002000d4410300107811f10001841d4050710415000885814030172040014502c1a8040c00380d0209007101800699070240c4040124105c007810481c04200200c20490391250007030500149a00040d9a0018005001c48500c010315440f82000c5400c0610540200a05081c160000140c0700305d8111141a040042440b44a4403000014ad400c590030240210040e03d0200c0c043e204c1592900300100c0481c0003407140900962050000300096081791001a040c09020341c4061500800402c00304a448c44880164010782001c880052480c109111030710b000340542444c41e1601c0305858050300d40f1710290f0703014081454458503084e000540d207a00480c3e80311581d02000380018940c400400c410b06150f040000103810080088054001911001d02241c1041910341c2d102500c0d03032410010350030308052150f0008100e143c01030030b5240c6520351301c1c0040300306140108152012084840d13105a100103945095501c0800d0701d42d00c900c0300785440040c8d0015501d261282d4030302 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245386241 1250 245384991 245385011
    0x100609060f120c111009060b0303040e0705070201052a010608070515181306180c020318030705130f110703021b01030f050a05090d052d070b09060a 65
    0x19405104000c185079403800d0b200c01c00740b0300d45805040b60300750180c148103c008500300100c400703001550b00030260714400520300302642004410396000404850081c5c1040105000d2007004030082c9070b100302c0c5410295610100d80c03004840511403555450120030f000035502e415128200c07c00040d0710000e600034091f0315119580e940e00c41000340f0941d54840301c4c0b40c030f40f40101e00042010b450300d29a0100b00b080f0462110001c141c0325144e01166503241c0e69920303000d1004403600065948004a05039041152001c4445d0180d604d20810000c03444690400700307102c0c1c03155020000403019042c064031600781000f80b0345007040a41015614510f4403400c24a50001c3c0e0a40322003a03629540c0c00da80201000640c501c6446900030000c03000c141099142e91050a48881034011580201d4420340c0000346860007003045420400750519003810030904010380d1051443d102d10000f43d0f0004401c2c8603103094906990012a4032481200400009081c2e041145030400810424070800c41400240104544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245387491 1250 245386241 245386247
    0xc0f1221090315110f0a140306060304021909061203020609011a1e030d0c02180c0904021c0507050405010f020303040302120c01020c07030c05042a030e120310060906 73
    0x30080d601400188140ca0400200f4100c0c0140c103000440043c000071911802e400805030360b030040c008240b403070400003401804503034025244030100916011780d5003541131001c00200035202c00703070001c3c2c4100c844c0c48403c601b00e80c41d0222440208180d1104114280d40d40000034581d114003141039003d40500d0001401d00039041c050040c0d050300080c00100d6115101040000c1d0fa0343d204030718070015000407081e00d9151001c000c0c04141e81d905403076038094030720a4810451a900440304400004180005100c0f40c10510000d0b503101020484015855440083e4603c03402c08002e800608102d0031712080c000700e1138003d4000d100366002a40c03003a021002c0400d09036502c0c402554010016400f868001d5401c0710000040c007a0180810005482c0100c030b909214134165450300705a4984040170000c001a2406104068800b5212030031410004100b2400d005210451703c040001e0585505007224600820700049400c5103109121944a0030f00940c03914440b1070501518002c96201d107004103010740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245388741 1250 245387491 245387543
    0xc1905040e060f04030c03020f16091b0c110d050a0f0507120b06060313050d0207080f0c130b06070819080c190e01090801020403030201020309070909080301120c0f12 73
    0x201d11055400c45131100d42c1c04131001440c85034294214000e100301d80310b0025050005182540a0500030007503682003017404805c072120103c651a80d00d65100c15030310600c0c1c21400c0314002c207401c407510030420700c040c1000c500c03920114080244180075000b460000c100201ca9a1240a0300070780444444d581c4420400018400c6214041c0440c0c2c6100c001554900d488001103600800c010080d405031111030b522030b490100034280307035005030f08010020300c841c0c14100312082c41074070b5690060a5240a580208900a00a0314080701d0191242031050054856030120364482d603005442d030b60780300d01d03884880501407130484058000483c0c400c042101d01c0200130955034100301c207900107a0301c802c4010040d1807080c40a000f041c10b1000310000020849400c0c0f0103880194060340015a80c2d00e094640c2c82e041981640000e0b4a9500c0d10704004003080e2007905403030644096103020402d10100c0d09141d18120403540c02007009803800b48000c5070800304800d2103c1d03503510940d10345c20340150941010790700c02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245389991 1250 245388741 245388751
    0x1504090f0f0204060308040806090c0301060501120e0322060806192c090309040e07060507031b080403060b0f040506150715051303140a020714030c1905040e06 70
    0x303280c1145440071a62024503108034034801400003940355902c4c0d0398520290400da00c0301c000b5070000420081d04407c103004519646004034000c0000506240020f805502e0044040b2652943c8944c1e045011100300b04450616481d00e8800d04207501030b5a400d11885001c0c000d043c005044200407925900b050780303074114040a00000511240e01f41000c02c2d01e0b491582442d818119400b8a20f03480b000f80d0701d40100d01603241e0700c01a55941031000d0038801503599441c00703030076158400003041005d42c0c0c0c05005c3e6089141c2c1481c2186040c28030841460604410f0080504940000200001008840c1c0e10000e010f140966240c1d0200d640e0b28204000c44504035451900088403400b18009144003800414001348071385030451551034400f00b000200c1c0c40403200c41c0c0f0f001441e080410181500b1401000003108070650461406452080003504c444440c0b01d06240e030648501040883c0e1b400b8000c9442c1ea140c040c21030b150b003c1001c40e5130005c10807144500b6000d1490201400c2c044800812214829 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245391241 1250 245389991 245390003
    0x203031b221e210201021015230612130b0115080708270a0803130b06100909051e190c03020a05160303020705031303030e040b181b0f03150409 63
    0x10243c14a0700031408203440100301e046019128415815582c54440c444140480441c0801228100354551180750740b2141c103110f24210360401050b8039500e0400711a000c4443c0046042103444454600b6900c0c150031314001c0c40d0020400000c6508990042c103c80d0030325140d03994902e01c0d110f070341040c0c1d040501034034440390020010241ea40c045c0000b2201e0541c0061035800c0798400c00c250307214400203070015035006440d0055100320314244240c0144454100c6411281803609840e4004042e081c0d144520078105010b4580001070103105440b104c0d8600c8650503442e4071722910b03040104600d00e514503001c43c80e00340e00c2d000703000b11550321910991701103008035210310f45810350307a14800170100d020403400c908140d000c012800004800340041c182c450005c2d43d41e148103a0651a010381000620003403503011b2072030b080042d0025520048100d2480ca0150b03071120700c0d91105c8221485607203100809109581000821440c0469800b00940c45184045c6402e2031070349032541003005a070741142d40a402d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245392491 1250 245391241 245391269
    0x203060a050727080f1e0c0a0315020d09050f06161409040605030a03050703020105071b030e0d02041a010e04020c06071103091009050f03010b010203031b221e 70
    0x900c0d00341070b03950640d101c0700c5000c01d420540e6481145c0c40c003800c1141000e4590403604031072440061b60519a0156070300080649490600c0c24003041804801d444080c208180780500e4001607030701641200e0240c1c5e2211001c1c0700700151418a070f5a192010360481200b48902c00c00a0f00158882d04081c085104540c0c80c8401c001429841c00d001d600315000301944607541d040c000130340d0381e810007d2150b6248240c640d161219843c1c00d003c0d0031540010980001d0210380c07900000e14140780b41c002c641c541d62605245100640e0b0f0804503400c5500e14400035007007482c04440d01502c280c1240405684002641c0e000c4501105d80148001da00030380081300d49513840780010403011070043c0f04612243c820502182e04004a107800900c0c0f501c840400b010204401080c01d0050f4101310019407030b01c500a50080c0301038103079400001c0d03403803200500ca4000000e2560228528a90410440d00306406444000b0103101351139400b0504190036118031142d00c805401c00719440150750340d444c421210500d01c4109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245393741 1250 245392491 245392517
    0xf030c0d020307120c0e011e0315021201080601150e030d0f020f030d0b10110a0b0a0b030a050706080f0708010b0307031b080114030309061605010e10090203060a0507 73
    0x20080340e052000c030b905004400c0f000c00d40c5510a18510340303560190400c00c0b115850118020314102042c0c001069109044c040e11000c946c104c500340040300d03441003260070300340302075600c4100174027680f109480c4441030400006052840052114140c2d800c8000aa010885118056a2007a460031907580c250300503002074070980b130141c001c2440800c00c500541fa6801001c007203107415a40b00d80b40c0741c80b455035600c072043c036036017420a42c1c80d080403090300b0200d1075641e1024034242d0b90b4103079030360090150180303d00203441816036401080b4080405821962500301501e001c1d1f458002c94000d1500040044000034102c040260900d40a182c40792030340802c50b400d0401442081d40020908018152036400c41e80080003c03242c1c46c080900c0e941e07280b010a504001076982c20350810b170382d647c2c401c2c0e0042c0000c84495035500121440030010310024031140c401c514006005d0b15480041c0030440c0103007100504115000d0308800c50040c0b084017502c1079603527000020012100250740160003d0790000b0004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245394991 1250 245393741 245393749
    0x40e010905060303040e0c1201060f1d0406090e06011406271906020c01140a020d0815040608100b09040309030b0a09050f07030203010608060c0f0703050d020a0e030c0f030c 76
    0x140c00c080080c09480c505034032240882c46d041000e650003280200d00040d40d00c1b5060030358a4803409425180340c80e003104a0005c1004190b40b00b20b0010a2988001d4071041c002552140d11000080c0204a800d0042c0b481d400c03000f503140d0402b489020441c0b120090030058078948402103900344e030402510355250a0000035401907001c600b0028070380284080030500d84c6154100f982d00700425840e03008004010f01c1000050003015210403d60b0585400c0c04070241151f004681b4110401092034040b0322640c542084d41140c6010108003900646030810100e0b0181c008a03d00c0c1071096901c0301400005003000512075031002c101d0b0040d000a5503c0c1d070620000304940b425903084612140d010503050510340358a8241500401e40c0d805a602c46c0c40d0800450030207024010041c28210040c10141c54a00516070251150346482d41c51102c1c0094003404150050f02590f030124800441107480e40701d0a403010381a00150011140300380b00e88510226a494070441101e03035004060087d000c070341506402c2c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245396241 1250 245394991 245395001
    0x80708030403020a080f04150e0f0d03050d02070303021b070e010603020304030c060c03061d040f020607051f05040c0504052a040e1303030e070b070b0a0204090207050d0f05040e0109 80
    0x2c6046002c1d0007050408100702c2e10103000e944101112030340c0d58900d044074103007040c10510f0880081c070840b0100c400041d45c920251544d0580b050300c071170f00301681a20381100e040c0303c0c2d000c0456660b480030420005059140c0d02500001d078030903400403541501e501e540c070760350005441103101c01e81c4207500510542d8031035009103400074400d090403400381d20545e4412041d038121407801d2000a544060400401038a000040340c4000034031340c0e400d0b05003020345501e007644000e002c1c086c1c080c000001d4044104103040221090308004040401e0792410280c80c1c0101500d4141c80030303542c00ca044100400e05207488d201d0320b4000c0500080321510240440c806030640c50f800e100c0b540da429028040007030b0032220662a10301c1010f010b00001d035404164034028048480c134a80661460b13005074403d1000ca450481290700180d000002d58516a0758648208060301c62034009211071030011a1400802000050741c114000c420b48609503801440601190316000d1403007908104030003800104070521969000e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245397491 1250 245396241 245396243
    0x1060b070819030612050604020a0515090603070c0804031a07031a1003020f040609030b2508090a170a270923071701050f0108040602030a06030b130c0b03040807080304 74
    0x10613016070301c840018a40465400c180d0b400e40000e0300700802c61402030614006028121100352012510360036a40490098030f0806015050000c0490512402000703084800340d486860035a54503220b1610210350b10104100342c039200d8444000c502e8147c06402801c0e0401c450810000d10743d60344104210401c04640141c0c1d0a2590030801c01ea8041513000082001e01302030703100c0452080c5540361032a02804014a00c00a43e0030ba07481900d045551411038154803100c0d49024115901e50f82d04241c01d000c2e00d50001001c610710040d442c161080400064804a0804d40359890f1203c074a140d0407444000d002c5120ba21608640400e0003039018580c07000144500c0c207128194034090005a080601c40251011800311303012000381100404090805c2d40540030940388400f8082c5220006000010b0150008182603004000a820032006034084c000171a00200b070010103050510800e00714071a05c000556209540d43c41c0031611455640881e400703545e0143c040381c0b60082d25226a607081c1c1010300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245398741 1250 245397491 245397497
    0x30606100318023307030206040209180d09140a03210c0804061812050c040228030f14010f291c0515130b0114030c090301060b070819 59
    0x881c030805a142d202c250b01584e064656580c1c2c3c03800b196000e64039181c1d0348105142c3d004408110394800a58007048040d00180c0c1942c0030306098846244807026038031414000030007072140c400d40e041b41961041d100c0e412503c103481052100700302e50301030108407141800003504100b80c0080724554200307059070108a561281c0f4100542c0002a03446107100d90203035001c05c0018110a0410804070304001c4010010320384e801b401c400000040c0d0710640c482c0d180d81c1e81d140c8140e0b03010a0a60903089101800344890070003031032405a001c01c50f038000d402000d909284040e030070b181010f04502d0009449056050380d82807400800c0c800d182c1004d143c4100808242c4072011074070805245200a1441c0151a1001d100c400c41d000f200f1071110014116200281002c004100039503802683e600c9100d0304009100c622140810380b2030707005005031004900304d001101042e400208000c0108822070140403603490840c0240200740d43e882068555004446001d0000503040103035450118000004140c81400c40c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245399991 1250 245398741 245398781
    0x601032003090a08030109091202032701050702102304050f0613170601060f08060108070c0212070303110f0120070303060506070803040308070201020a020c010518120f06060306061003 81
    0x503866134081e40081e8448203131192a46501c000b0010048a22541528035100440c1085820402c0042442d64194410740c242c80d21100d0306000d91241003210041e0380c002d44402003c0101490051080d405804000b140d4048a4a4a80782d100d40b002190205c440003808600d60301061010090b45620a01c400c41983d010010001a00503101403a004802042c8001c1d190640c9405070117003200c4240610351013040100020401c05070f822100c034a802c0180b500d00000440001d101240c1e20059011843d98907204040d0000105507000202130071084102041d2140441352605040c00c1e110b1400700004031260310070001c24141000c0c0701400d0401d029140200e1410380d14408541e803035106500c1074503030b07007000420482031580204581c0d0700306007107100131490a01032900084d15010541c48080c10000d0004220054222502521403030050040c01c400c4609080c0d444a907841844844107a2140100c03800074449103808921248a880702030300f100e0703050b0f241882c120014026200d4003160703d4900303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245401241 1250 245399991 245399993
    0x30c04080a12030e01090b0c1e030c0a1403040201020a0201112121010608010b1c181502041211121f06140612090712030e01080601032003090a 63
    0x82101203030a6000e40c19070b220030711841d031005059403d1100e01c0c0800e60b0504c0304040c00110140d14042c0d00c105901c0410761182815051440714a003485036000c2c0e042004002e0000e6180d55600500d10900107840380002100134005003005070104660103400750f00442c415101550161700c10b080c1419034030303080e00c0d48031446072452010482c074003111840c5141d004c12250780750810a01400c0007a1049400c0481c00c1d854210b00030090007050007010740c0700034003003001c030403a00c0b03240e21041a840c1d46070418400d40c032030743c1051200194400c0c8103581003020512000398143d01d900c02c813003d403951010300f071002d0103594441c01100306800c0c0c0840d811010504150303890850a008201d4550210390490241094100290301034400e00c0e040740c010042e020004900550318041261f907403029409200c003840c0e8030401c981d4240318181d401004201d205209060070075600c220700c056150000d03292080c0c59101c507801141103c401e116400c2160500a4141c442205003034041e62b8000300c642c5c11120030b1206 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245402491 1250 245401241 245401243
    0xf06060906031609091a040b0a24140108010b040609051011060a05240d020d020a17070305010f0903020a112106090106060228050c06071b0b040501050f030c0408 71
    0xc60ba000c040c03101e64034071801081003441418001180006c2c10b200a250400761a1800b8540c0041c03e040240c1e81d4030410030f1150f807000c20075200b0700405000700c000c4081d41c40d90404500041c0088050000c0c844c0000840c10106801c241c1d03050310300036aa03070306040e0705080c244180c01900c0c01c3d5000034000e500c0d5002583d0402008400e100386541440440c031418103410380e00c00440c0039880d00b000b4600a503804182500c504041041d00c0c1d0301202c8641d810401c5001051104405070003521100040501224071071500291042c212440384c4000c00100075011902c8080780c5444030300a005822110032980070541908818000307410042c22181c1041040f20750700e20b02124070700e600809400c140200f02001c0803c5c82560010300003070016012072507881046007452903030304071040300e0140340c00b21120600c102088041205100501000c7c0c1d1034500f82804186007001e0107204c03001c40d144503008105000070304151011220107271142410b1100c0302803c8885030300010940081c05d103081c84000703031181c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245403741 1250 245402491 245402533
    0x3100b031b1903060803040810021e0c0f0c041401030305030415060f0602100207030e06070809130902030d0c050d210c0c1b030803040b0c09100f0f020f0606090603 72
    0x41d126240e04241181e10364094103a4140768401788403504240b00801990307201143c41d814011b000c60340166039600c480c1209014814006074011201d4000c101c450b0304410018803409140c84080896100251040c1000262602e40f10401440250301d001000040d00400103560080c3c400d544441c0403554040005040368119440b0542260024004106113501401401c58000fa0500c055141007501d403000341c01b15030103c4409009590025514052040c0302c41074450240d00107115500c5d0700d28010808002c2c140544c1d09911078002e80703050344803950081200e8200e25134000d02a01c030003000008142d9160100c4c40c110604010a190340035160001e0380f103011a46a0f40f82c0f101c40000589040c03e04c2c80d502d5142296000d05420341c8140041ba621600b582c2d27015600c43d4044c0c82075503c800e0403007814015040001d82000d5207001030040e02d40c200c072210700c0301144d5544910f040c403004103040f03a40d080304078600406c942100c4041285420546480c81d4484030141c1125080c40700700039000138941d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245404991 1250 245403741 245403757
    0x50702010e0315330f01050403150b0f060a020c21030f07030e01050304081801030f15060e0409080304060b010c0c06110607050406021c1e05030402041103100b031b 72
    0x80720203001c00450b03030440c880d502d5800c42c1c01358803861000030030804000703520320a038401e034410440030084000d10780c8500308513070142d0360001a41c2d400c400744101c46030240c0080c134125880b80d0000b5010002350b08000d815600000419801000300800250900c8844040c19100f0413a040e40184d00300702c3c140382000248408000300d0b41c0140d681c015402c00503c4500d0b103941c0b640c100301040081c8030202d40394005030f80713160004605044206020034010f8005082184090710800d0504003504440400f420302d00c021a0039584550721301c40800c004000840b100800010b02030307001400885d010a800b50b004c00381606041c10700510843c0580c54200200c802e5500c41000980c2032040e52001c64014049150040e00c1c42c01c10505041c1040d0000c3c1d1910711100300b0040424882d03200c03c81c640d200f440355403040741003070014085c0c42c041c01d070004001e030b0300455003640658100100d001c080a00e032030441344104000f0740c0082146051032050102d0307500282c80d00030240300900b0290300e01d0b4800401412a5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245406241 1250 245404991 245405023
    0x3230705100f050408030a0203091c031b08010f090b03030403080c0a21050304060506030111040b0a02151521030a1106060d03440711030702010207030201050702010e03 74
    0x1c01c034404190081e1a40c10307566404640c185010b21001030450010389801040310300003d43ca1360b031051981480e00101e10b10300c0d10300302c28101c1c42c4100301c1d0309036000c6000340d00c039024529100119030b2019241a8000c0c40b40e026400d80c83c0c83c0400007a40c01e5401a200448001d0035681380596035141d405541d00000311200217034004800301000c01c500132710700800b0700108441da404800030780740b0050624000103102415894490001032844e580a511514241071041041501d803070b103a00440d40c66400c400d0705e102c094801c0b0300e9030002e40030441c06031070300c40c22002d8030494850507038000784194940301c041c0c46504121242c44000342100b060001d070440c9407140da02c1281c143d400c0700e03036a4a42000501568003542d4900081004250f21030401c1e0383c03d40c544403078040003040b81d079035421400d038855004004511000d40702d403405000d042d403400d0203540c29a0310554407062005c05e00d9241e00c66035600902592003040304000650180018100380c600505201048600c03038000320b03060800c465512220 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245407491 1250 245406241 245406253
    0xf05061f0e0d1a07030902030a06020d0b030a05030a0311030c180307030803010306050a0b0f0108061504050301091a010f1d060609040504030c0209070f020714060f040f0603060e1303230705 83
    0x8840c00c83c0f0006500108526040c40f4034086900440c0d240d050b1864050f2040b5000680d0980202064001c81d080304005002c9031a040c0c1c0362300305903880b90042c280720400241000b100740d050b2100a029603019401c1d52040c00d2070a40b0700002d02070404015011981c06024503500000801c0320340d030240d4000d5002d80030100342c0d80f07020314800044804100c503c40c8104561092440d469906c10b00644d440355003900d410a90f01c0c429a4280300310b0045070302c9180d1540c01e0201c40d10410120501c0e0a14100c8883c0c1d400c216030340ca4442e10312010009015680150b44035010120107a41d110410980182024042d50f2404400d20042010b48100729410303000701b62480c80e04011800c0110000c0d03400350341460003000d02c844d0b010000b52503000038800c2c01c100010707100128840380c0c0d50800b283c45101001141981d0b81d5550301c1e05600e11a0030f44030f17000210345040d00000e044444824054824880c02c002e08152100300c1d5015100700008541c0181120900b0450940415420000f85252800355004240d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245408741 1250 245407491 245407523
    0xa14030a0c02120a05090907020708030a020c0307051c0809010c060c050a0e06030613020304060e01090302160b1801050d090602030c1e0a1b030c05150a0f05061f0e0d 73
    0x103e8034401d901400c0300d22508000c9881c0d010b91180a9402044080725425103075141c03054101d2810000d50484c0301280000501d00c451150001003001d10400142c5c180c1e241607a9900c1040711000c40003800070000500a003030800091260340003400c05500c1410039080c296020340b01c5c80110745902280c2000b261000500c04680c98110b84483c8150404170b400601c0c507c0c180d008514016022005080855008404181080210380108078002c000c40001c001114203428004d40c0e581100244100d00f0407158004290a40d4020448200140035512602d001d2447c4004403055401014281031166980b40400001070080c0021030080003190162074451070000182406400d580400c00300c604003c221000781d05070000820f610301e074401c001118480d41c050405550f4240007050051440c001c41c010600c100c500055150b01640012208018028103a0000030446000381c81d401d620076080c402c03910310403e8254088000712407500d45148584407404c04200680d03d0880c00326202510541c5020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245409991 1250 245408741 245408743
    0x628091409010b152a010606080906070507030e18090106050103150305070506090a030b090601230d1104090602040923010b0301030308040c0305060708040b01050a0810020a14030a0c02 81
    0x80c1d009140c00000304250403070040080c00b40d054071410391144034004505811001c99106520100246142980a0455180d01414000c00d000c0c050f04011450180100b0307040200001c015125030003170f840c0c892408100d5101a60b0200f090344640fa48088408018003d45000101c0140681135440005c03c00b1401e080016095480301310a08802d6980c0050810204000103403140c212681640c106070740b40c1c0b0700ea01246410705541c00240c5414515070a00440c0300d030000d0036504940302d0013000380c000d0300380c6000c600d02c0c2180b6511040d403042d1041d86160110740d01d948101c0d2905001031001507015441d642c0c000136600168052460b035680c42800785024020341c541680001121080c0303032410740c10440651440d02042c04040e04102e900710000d81088000401000a95003100803214035141c2404010000101210101c03028000c03400001407d0814a41d200c06545010f8082c3c03032000e0719404128029000744401c8010400e14000c100d0b801800c040c02540900c14140e0041b400942000005e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245411241 1250 245409991 245410031
    0x106080712030c20120610140916030b041811060f030106080402010e0612071706060909040f0b04030f02070b0f0711030f012f0a0206062809 62
    0x8414003494007410600180d4003200068103280d010450241d45080244a00300041c520b4481d65040005004480c05414001569034450403160030851030840e120001d1a0b100c0d1203a4200d00d4003c040140410071058904e40f029245418515000408010801c0090b003614010b017507001d024000060068203124544491400f12903099940e0382c03514500c80b001d4406031005105250030415540042011a0300c601c84000c4414070003081d0a4503450601880201c0520030340e200c80214012064a9075140140410b0511440000b0142424400d42609112240348020000c541c40030200d90003030006099221800e0095019a950403a0303000c80d0071002e46800321070b41060040d804148a444130101d4032004441401d907024400c9410b44402d180400c1c94140400f4401c01c8950801016140c010f174110303594040e4105400b000074642d01ca00740311f41e0040c0f0034040e0540060b00610001a00380c20464800d61508455041c00401c0003905d2a8a241d0725000342c21000d03107292100d140c8522b07544d41c0064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245412491 1250 245411241 245411249
    0x1f0b1b010b1924020a021002030d0614010f0212220801060e06031504020915040e01060b0a1701151404030b15041b020a0311010b09010308040306050106080f06040f020d020a0201060807 81
    0x25070143c0c103411580107503903a2035091009101c0c41c40032036841441c510901c2910490b840c1303031000380040c1c0d4890014001050940061500040c1c0c602c1a42020610004180440d8054108031610b02100c0e442c5c441070441c4070584166038101c48010029406809104074401000211002c48560800e2000c05003405480e104512050045200b0310004da0f81d12081207030000340b4007070998808038072000810080e120160324458194a405000120800303031000500b40248030781d5604c00d14010b440c224580d1814207004801002101340d01d0841014014211400d0b01c1c41d080410500300340d9255501000c0000460312406040411081c50700f0303605041c041c480d0b0310002074040250b400740d4400029902d0400f103074040e040201101c6c4c1d0303a0100307200f903204400345400074284980399a180d080c54181d607805444100c031b045e450600001542440760402c2c90142c286003c2024051303c4000800010341700341f45032102d03290b500f00841001400e0600c020410340d4016000422201c0c60240b0490900d000b80e44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245413741 1250 245412491 245412539
    0x201030605010c11101709061503070e010e06060417030904061502030d05070e0a080a020909010c0f0509030c10180b0c0a03180e09061f0b1b010b19 65
    0xa00800003008250b83c6a82a4015141507081c210740c460b0407520340c50b9445080204407406c0041c03000303011002c54910b03c907002c5410800d40c0003080c02c051586d134200f07511841051003810001030203449020803800b904100e00812b1942000e48461600c2912440c00520000c90391000408081c0350406001e030300020004a00b43c0c065412900001948038403d081104d5892070f920800500483d0088a0814502c0720180c24400b24589802400d551041c003036000361b10841d002d81c00109004414010441d030000260b4031821845111201aa2190000900164103010385a40c19030b658680c003d0304d0344240501d64804800401c0e6604007044907030b00b5004104045410408441c80060020307001401039410301d0001e1070201d00e01049040091281c0081602c01010000d02500071800140540502811000c558080103a0000808044001d11440503d11400d011030000c0e207004050b000035080c032040000c40c0003200380c0000f54004070395850060001c0c80d140c00074082a030b9224010040282061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245414991 1250 245413741 245413757
    0xd030b030a02100c0c08010507021b040603020a120611120103020112090818130c050c100e06041217040c0f05030c0d06090f080d201e030901022104020103060501 71
    0x107004100c0442c003d0b800301042c0400e1448181c10800c80090750300041a051000700540d051102e4029107503503444840c0c030790f4107490001080d0140303418400d8808507035000b0182d68070145010031010160403980800c1c2d5480d9641c045281d06108010018440b085c0394030342c0e00d0300643c11031001500303400800c3c1e0f6014546150103c6440043c10720b2040b141c00580d021980c035800e9040703070300040400507100714440a250501118604880e04035001d001c2e4207e0401c10786011341080481841110000b44400402d0381c00b0b040828089028800c2e01c50003600315141c0001c1030040c804204d15845c1e000e91b8111f40124040c40704120360a04581c5000103010101e0140490080040000c0e030082c02400300135085c1d0b0b5513400c81108108031114044405980a015203444e01600408000240f940e2a021a884640804036035494840d000440d01c90030b84903480007500803803412195086820050951110359820840c0803920041100b0304000d1000000088540d0302c0c2a10004058607030561190f810b010f094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245416241 1250 245414991 245414993
    0x303110a03080a020f04050409050102120f0906040b04060906140603010f0204060203070809030a05060406020903011b080a15080a0f140328230306030601080c06070308040c08010501080d030b030a 86
    0x22103285500f2885441001d80c0301c0024807003411040c490769109030b621500e00f800460400c01c0640142010042c40d10344400140d4a91202d9014500e0807140100d1540101d0300040c0041d80e440201900f05003d407a000610031803d550b000216030074241d40580a5940d00d00b007015901d0b09008005c00c401d0001070550a0620700403010b50b40740a941002400450085464012500c08000e4428071a800c002110f80c6410281007e100a41c804030f2010300a50070529882040c10120f00d503004040300316590030105982e40d4205100a00104080718403204000701d0001c1e048808002d01c442c042e005201c0e40c0c0c0c086009241c4011003440481e45ca41c01ca800c00c1c00845800440314201c196184460032107000752060640c42243c60007400b100a001d203070303070310360088541c04444405036100d07a405400f16240750b41c0383c00d2615582d813181e20001c0d40c00241004014006072013500c41941140c0b242400005590b198240f081c2503d409810040c0d290b40201d039040034103541405a00441c10040c0c014061055103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245417491 1250 245416241 245416247
    0xf0204150f0501111606200c13020d1119020f12030720100911090411061308060c071a09060403050319110a021e0618030c0f070303110a03 61
    0x4184660b505010400d0440040000148200711414004000364426170703071500b90140242a24402005481088103038085070010300103145881c1200042019034156492030030f040c0a58465814220045c0d2240c0300b290140280c4005060603880c04e14500030072a0b64010001d28043c14299a4400343d80032101201c05561030030100d0343c01c107030545031130a98140c410003a48016061044091203500c141c05500044020356800b01c00c410384900340e020034031000c00f420000f403000c0a69002e4480c403005901c0b140c42c0e1401c074004001e50765040700150102c03651107020604060048a200080440000700b460070400f004480340c062201d03910071050b96082c4210101e0f9115030081c801828000000085000d0929052415504841034081448007100b050114080c40d0402e40701d0f4805881071030912100307565030071b450700f903a410514001c02e29a030f2454110380e02d41c203000281c40c200d80820030060804242c14402c08000440b1040100380081c9185401407450001c1b011000b5250010030341c030000264 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245418741 1250 245417491 245417519
    0x6080c15090906090603070f0f0e0c0a1d03010908031806010501090806222108090705030a0b100f0b0a080708130b04020307051908060a0e0a120302090405040f020415 73
    0x3c064456611603651100070900e091501d401440601c83d000307600003050340e00c2d18150815225001e00500c0b094a55101c000218002c1c03125000108003400819800e030740c40d03c0710600620340d00800209034004251070304850303a802600c080700c8039183c5a11028000c1d1302004560f0050900380703460314a0b03514245440e500c6490250402c200c07044c0e106282d55044c0400000801d4041d040780904611001c0d00c2c80d010905422960f0050208201c0400900d0124011501c00110390001e03010f170040c0c2980e0ba4940c106400c00a140000b0980c0c43d00300809c0d203000d44205000503180c0c050040e0b0f9265840c880c064000680100b490b81000b41803800c0100302c0e04070001c10038117150f00c03041140c1c90352201c0c400203090032640d40081750800c40880d40084803111110790750045400030020f8800b2511106400c0b016148a48144289980605040400507000b03510551100d5090301c4c00500701508032002800b600d1042d1010f85490b4000342c824025131900e0700c20f0700110000440c072070500328030b4001e16010201c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245419991 1250 245418741 245418751
    0xb030c0613030308130b070c1406010501020a17040b0406050d1406010e0d0203010b0306160314042d0519021809060a0b0103020903010203010e220b0115030e0106080c150909 76
    0x10242201183c200300c00c0f12a80035101d0f610011b051070515100d02c0c014003010540405035101e20b10711807403d416520100d541130584106901500710841c01c0d840d241d078111a50202e07003111030010080041c4030480f01d00a03101405266030f0303e596901006241034141d5000c0d05500c6801e400c85d5043c06130070ba070402c4010907601d4054034035074500da07031500021b40100040c1300315030f80500410040164030084030f00c1d00b61851050b07031001c000c0016200d21580c00c62000316002491054040011074142c0c901d00500c10440e072a41c10011500061562540d0400001909034440c0741300c8480c001d030851a2202c541500d14100c3c0440c9a050300c1c000d1001669034a02805142005540b2915144164840d40441d4040303440900255501d50b520a00405040c0044070090050071400303800a4194102003544418160000d210070901d90070b01460030310311145440d5a2007410f03524042800d030b009080c007900c0c000308155405030031003894020a016169a40f500c1201c410841044004940d03a04d081107546c001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245421241 1250 245419991 245419997
    0x3020c0d031e05190c0201021602010809071a0a08070f0c02010f05070b100302012d030507090503012f070308040602030c130b07210c0b0603011e0b030c06130303 71
    0x80440038445445180024500c02e40150600080000260388080720360b6180c2c4074010200103034211224100d080380610000e103611107032090911000342d03200301c5500d03400801034400e5600d030580d2054241c5500e205c402d80c0452540b00440c410110340d03080710405620007001c2c02e00000200403544018500800c81000a060050314618038500d40e00c10007d80e42940d0740080242000e06010341100403113440c0d88401c900180e03c0e154545400455036120740340c92100d120521071001c415200039005400010588010000340c51000501c03583c00340507540184901e091200900e0200c1401003a000c69004003041c6621410004540000d07802805039030f01603085007005807261121040e42c406071048140113a40c0034695840491001c90f81e00c0100b1009200342412070a6074001003284140e0002e6098802c0410302109030003000c21000c4003e9903012400500024520800a0b40c00036184c1010b641c41d205107640e10060340b200d080c20000c3c04d00c00c61040340c54031305000b80400382c00100c4845010040030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245422491 1250 245421241 245421251
    0x50c03130501060807141e13092904060b1c080d0204080d02030301061d09060d030c08030901150e011a0a020a020901060c02040f0c050a18030209040c0e0703020c0d03 73
    0x5101c0c0c02e60102c0050b140c80401e0341c000701d03551049542c240061203049032045040c035210030010407000020300004500500911366404000c0042c1c0e0050554503002d40d1035004070000000c400d0000305a240344110400802c11250030107080c584111415015400d004040c6641c0c0c0c4803001d040741c8001420079901c41c020550b44d50141410b0406801203501c100e81c11300c5407041500c1296004800380d41a9607040c0c0c1c0c1d0043d40399a03c000c044c01400074002440e080510500800c1842c01c1c40c0782c07141c043e180a8201b07400c0c035030030303580d54002c1542c011942d0503a136954650100842c0e07000c00030440d0003020462040c124550400c0103015002c1000b9202002c1d18130004ac130000d2075170003401200300e07041e00107220100071f6a4400d400340040c3d0350b030b40003280300754070302400080c44c15a6881110b0400c0310326076407141080e140800a407200da8440708408402c0c4200340c400001030b42c45100007403161703100d030380128802450800540c55802020704607130281030051043c0b4403032010004030b560810400d4500803032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245423741 1250 245422491 245422493
    0xb06030a02070203070f091d03040605040510051e0310090509060f04140304030b100b132601050a020903010c091a1620150703050f0f0c030403030c0312050c0313 71
    0x41713400100c0d8004582c40440c5040041c031503100b5070013260102d0307000040081280d441c2c15425164880ca000d50b20200b001401b082c03081e400c007180018001112810714500e0140034011780703003d0031000c24950040d5100041003000402d641e0b10906d0042603c2c00c0240703c00e0410703d041c103880c0c0c00010851000d0b500c0e03040c006410b012480c44007990141e852401c0d6035036107450b0301b44081404001c0350200500c42003c03d00280c40c07401c0360119010407141c0208407400904022415501c88104010b890030b524102684e42d25a603020310805000d002080300c0143e44003181c00c145400d58450b944108180148404108040c0303010900d54000c0039487c2c2da000381e64a0b030064840c00c03030359a555400340402000340b954801085000881c40a5100100c0700030720f00e48418892200144240900100004c109200300c03031020045501506c0854042c0c1d084508003180c40004900e150410380c13040d000030300e0500031041450b1308241e800a8218400c4e20502071440c00310040300191002a0a9555500008203104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245424991 1250 245423741 245423743
    0x60b06040302060a021005130203031e0903030d090c0e010803040303032a020d090506041d0a0f0e0706030614060702090603011b3c0c0f060f0e0607030b06030a02070203 74
    0x5400741d640101030300d4441c40848002035a07603503200741c04c900b154600008aa29055035940e425000b41c1d006000394a4404041c600d1410b490020352103800e070b00c0302401041800d503814005080c403030800314000a000140340c1030007441000aa40002e2144c001040180060740c5d001c0708550543e5050300b40801d4640e0701c48072540343c41144504900c24020300e00c0b44030114a6010034407090242c401c3c0d42d80c40d0307010b840314204a500e2182d0711901d2080110303180710401e400c01e840c03461a88826101c20000341201d442c120041690480602814143c00c050300038045035030503109000143c00c410004892404640d40842c507144038100b0081e105441400010304e03165001d4000b180c880000e1100700d04418140c3c40041c02034503030000e6a5a4a030b00e9448036250410003000b03c2d1a00e4103440b2501c95608050943c21386a5140000054994004103c0070102080c4d0501840004441d1280c1c00905201e46150060600e00007402e00b004041c1410f280411680e14802030382d8003c231910341d005030f44464a00c000303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245426241 1250 245424991 245424997
    0x6031302090c0d0212040201030b0103050c090d110a14010809210d021b0705040e0604051e03070b0108060709050103050f0f18010f2316050a0e1c0201030b0a060903060b06 75
    0x80c3c0d0040c00095801c003003014608116002d207100b80c80a004045043e0015010740300704031a18492a98240302d007c3d00c40c60310306103a001036401401e0a80c1348282040c08945084026044003400510a542e1403042c0e50744510780d151701400c0c80b4081c0c42420107101030449502024100742e104803201240050349851a941203490780d1022031100c07011b91234410b8899441e00e0040c4103080c8541d150070b510042408020030603e01c544e60100c0581608089840f40c14400b03200d241c0d01107820701c024409180041c220f801200d000e004200020221882c200a00802d490800e411080c100340c1005c00380018060003d960940003081c2c540710412566038541c50078082c400390b2142240e95800d00d510144942c0460b400390401913102e0703000a084c0e0149400404d0810416500c00d00d40e03124044003a100c280c42400038000c02e84c4140b038240010b250402c0003c080c0b8503400c04c003d1a0001d01070b5004219130b018400e518092109640d1002403524281c1c0c0a82040d03000d12000c2e045179203411040005031f64160803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245427491 1250 245426241 245426257
    0x120209131d1203042a1706010302103b19030203071d070806031207080909011a0a050c011d03030f0a0c1227030504150203030f0c070f0804060f02010b06031302090c 72
    0x21020401b250426881c3d84080030301c01640200703040c00249082070b10541c1001c00d010350401945501100324003400840701c0d140d040204189484007042c1d070840c0e55076081201507140901d501c160f124154010503040c024181d005807004482c082030140411134001c000c0d9400038003814560100d546010119050082204440104010000d100000c1091301da01138002e104080c1c0d9078451aa072991001c044020911500303040a6206001c2000c28510810040407182900b03000810340c62840d500b101914031412081d58660341000c805c0201212036040d840d40c0c0152428420301080544280c003030321140c007503022000c2003900c45102d02c482c03100c01c0040035a9105003084028219800703050041894015010b940c13420b02d15a840200340c00d1002099034090322080540581c540c50f107143c219069440702404548414031003039503c01003100c040c0644010b040580303d1048924140c2002400c6601031030030389214403c04d001b0310190320200c0e445916490307416522401c07103803035801000702d40380101e642c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245428741 1250 245427491 245427509
    0x5041505070203130503010e120a0e031c03050618060d0f0b0708071107030c140f030106030311070e040f300e010e040903120209131d1203042a 63
    0x500c000c1d1a8000001c241300e248050708203400c42c0c0c492040609a58011121354003d81c001801c400301c200c2c8400c000c0030301d4034a0b810014024149500842c1c28444014801d0200390000b42c040c500441e014003e0783e501100480303003000721070b4820036003002085001c0c001e2401032030480701c60010800c1e590755020005070046a01d400b0381c5450b00d00100804d00c112083c10025a03d01c3d1103a0024200051260a0340e41c0652040c860320f0074006614405184541e043e41e122407a0102c140e159102841100042c40c001e585140d1240c1800380b28502e400000e40c044407511a1090070000031844d180103240031154031100c00c41500c0e0f440e89100860380c078084410700e5003818600c164202590803131180389101500307884164000d041ba0040004403150590094045107103a5601c0200e515643d0040484101c01800505081800702d030203c00c0f0380700c001e81d144400d0841c40b00b42d06035071410424204280f8800700380d9840c61500c2c0d541c1c203400c003c41c15031101c0e040012110320b9001e507040d9544940036000400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245429991 1250 245428741 245428751
    0x907120b0a0e0405210301150311160c050f03100507180e06090a06060c11041104030b06090f01051315030b0901091b060f08060604051c05010b06070f0204050415 71
    0x80d20340d82900002d031030841d01c41c86642e07040000005190445c0c2100d40c07015241c541540c0c41d000c0301c503075000390091001c01010741d0f48041c42090b580600141002450825080b003216901d0301c1c0001c00c101c0d0340d403c824410044621000455600014154240b900c440740220303064440640c00d17a41400781c0c490320000e45240c0c540108020040c1d40d543c07072003940111f440c604591031b40348602e002c070340850103002d0000d10b801c83c0c0c0c64041070b21030002200010b0094030003c3c08208c03422013040150407507001150107a0b18081030003070340d00d410752006410901d051100091945403e00080e0510800260a000540c03560444c1e001003c41014070710045d5004808a90103140c01940341d4003d04424204a809400c950a01100030200b00050310903904070f40c55142d901000083d094441c0d600007001d80c1d5006070704010105030740d202c0720342d001e802040c0301c4500b82c0307280d031546005400d440754046558060341c0b0030301c03803100070880140001c0400340d010b03200041d15448604207542c14a10000e20f00351124181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245431241 1250 245429991 245429999
    0x3480c120309011104030c05010c030207031b030203011b0e1306050a06030207050628110f040303031b0c080f070f05120c070f050d11010c06060905160507020907120b0a 74
    0x4200110302c00c8112800800058140c40703d4816a8080ea00020702481445902404154010f604201c1403d0290040314401c5a982e5502403e104401d1001841043c80c941d041085080074040c0c180c180d0130740e040189603c00c02e00380080990401600301c5111700d901c0059550660416800380d0701809018021400072521194050301035800094200c905215101c0025240c40d180803000004803800b001245c00c5031484460f08010f04824051803d41440c10000050707901e00c0c1b034000b40021842902c022441840798890608040c00c0c2145020520030034039045000a00181d0840700516900030000e80c841034076051102d91032003124401031a40c860008865203a200200103805150040310840e42e080d5101c8150070701000f9144140740d003000c1da849455000a00d446000c1c2061407040c90451651406922000e003560120341c09060402d986205100d0a04000030044185051504217136160403a641e02080715145c0c01003000042000c0100c0f5080720a45580080000c00b4009010680180d15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245432491 1250 245431241 245431273
    0x211403030a09020108010e060306011e0f15020f2b09030503070303060e01091404020402030402123c0a0b100b040306270209070f0e0604030803480c 65
    0x1903944244d0100311a240000303184600000c940748140710140180645918000d8403034481d40d031020300300d228401070050100d45450310215490040601820500110034460f2020b4241050648101d03a00c0d0081a050701c176503a034100c101561002429512100750740444030803941d031060784e00018124000002e44da000e056041e00540240e8005001409199a0f540000022500390b111808034048000340002e015180c564091a84240050f21400320900b00e6004541081802420500282803d9042c43d1b40451003050700c3c2c801c4490840c512060a1403000e12582e210b10342030000302000c3c403090000d0f10714040e1901301001040e424108035101d80d02c07883d150f006000460046005401410400100c00c50f103000045441a0042c2207140e10307440d4420211511400305803544280103021881b41c0e15510343e100100001e5008a020b40d49138140240c0c03074000280c1c00405600d920383d410315420901401844010209000c0704400c0f00c80c05400c00810606024601ca189142d0184008030750507000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245433741 1250 245432491 245432501
    0x50106030e0d0306050315090a0f120e0d0c030807150f0207050111070c0b0309030f0304030e030d0e1012060302030328050f030103020d0809040f060f060207211403030a 74
    0x9021010341c0c244030581502107003280e1130340c031400ea4994041140001141c000d010141c1d0085911426150540ba0b507803031790402404001400c90f000024050000f801d194454010074200408a030043d10341c009503101c1c180c440515010282185070006803010811000720840802e9a007509030501c080941d526210009404c2003009448650800e4054404481203900310b0300015406002c200c003032804c20190f100d80b80c20081c480c58940c4402c003d168900d90102c0051403150b40300c1c0d503078100b1040e95501407605211140c1404400d000c00c07240c01c05841e641c1c141421007488441c0c41c02c0d03406985c04413103d4010b41a2544041c1d05804000794506800040d65400754004c1045016107c20007080380007240c442c42004101030207004244018001441d01e18424011980122041c508200361b00d0001002c54501704142c0030226580c8008120104030b18136032034020309050018083e40340c07a00c48141080c0030064040181c0706041c035526020440400e43c001c03d040fa29030204c3ea00c03807614020060080c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245434991 1250 245433741 245433761
    0x10501141302091c0516091a2205150a0305061f03081813020c07050102070b0703021c11030a0302041806080a021306080a050c040b010c0c0303111005010603 69
    0x500722140d0715548414000c551480002034001d0f81070f8542420020401001844112094007034400d1a44030449840e0301680038000401000451702c108028910818400d003043c14000c02045403090400050000c0d07032001c14a01e908049156502c0c0340b00c00704961002c291559100017000004000d20800042c11840f5610300524030310380b0600109803150942d554800106003500400a05d80541c03e2400782502d011009026220018018440c030310a0f6007014043c0d079060f41c0041d0003081250ba04201c804014481060001c2c07070800c41d40ca00030346810004c1d00458841c4100603007145080d100d1200c90a070340b0800404d907500d9094400d4010041d5000b4480e044c0007080300030355134041d42c0151040c1001c94400c14020040c0c17028640c24441c2410881c0b0003c4022a80d450001500c0300090000b080c10034890340203000701d40348902c100804c03a41080d86090400686851020004a050f0450000d0740d4042c1050349003104a442080e10300441c40303200404076410b0400006440c1e4160b00401510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245436241 1250 245434991 245434999
    0x2040e030f030f0a05040c290f0c12090a270c120506090f07030b15040f050306011a0a1d0a0303030b100816180801241e090e0a0501050114 61
    0x203134581506501c00e03280181d40141c040c903a00901001401e44010840c107800b842d4241806640b002500a40340e56003003038085600e51880040c101010400500c0105401759030b410504d8140071a0601041c145151402506582c81400119814200b0a031800b104c00c000c001e1400d00103a540894010194507012000d580076030b04102c082903040c503001924510071b40503680a4280765607603c10403030151180c0e01c459900220220485000c0c46040030003440030f0510641100c200310314110a0614003e4141c0c021780b5112402c50004518407144000c40e504603015107002007008031214140100615806c2e601039020298074000810150150042d5100800445440c141a1b0403440141c902960842c1c02c0d600400e40c2148501045004d1101044142d81d20940f04685544800c040750031103c980b00100700002d40c94210108100401048038040c0c60b0048002d2082004003001d4841300da4507000792401c054032909014a403a004020f240d0b01a41c0040082c000c0b56501d01500c50584030041d510b40c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245437491 1250 245436241 245436271
    0x20a060305070206060105070201170a0e0709092112061503050601050903070515070503030406020301080d0207030c060815180103050c120a021306031704060f090302030604020d02040e030f03 84
    0x4040d000e031142078070502c0700f0340207003001e039a0b1480112001e5002c1d0300700724103100a5440d80180702c1c8115a815118501903400000c000d409220540d282c02c1c1c544e442910740340d04208400300013a8040816440c10520004030400c01080c0b0b06003622098440c200c0059200d241000000f8480c00c8100340b1003030300c8044c1e00d041100c1e440360030044401b13128034141d541d0160b0101c0c1003000030b8200254011950407100c8021410b0010b40e546d2241941c0c0161026940340d1b8001c00180300094042c4842c260150140c0020000540b86681e0800c0011280c0b003602d05104069002034440001c40c0c5800c0c82e07009006010041d0340050440346c0c00004030a00050b07030076214121041d00c0354105400c0d815600000d03000104404806a0b007007000c041c400010900ca2151180342c0000003031403010248458903040c0819075221070074060003d200c425661520010080c00b01d1082000d1385011502a80241d01a1041400e01003940049005007800c1c1c0c0d0420003601c0001f891325542c0c45000043c2d8001c040303844036040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245438741 1250 245437491 245437499
    0x30b030a0302030d0531021527060c03070c030212030306010807030b03031303061a060301180513140a11030a080d150308030901060f080c030d18030b0f04030f080f06040216021507020a 81
    0x107149c0030314101c10b81652440302640d40c013850345464000018030001c01c10b07032802c49948906030540d0000001100c0c0c120011800b030085291114a0340e02c2d449012005500710320b4510002000560042c02c4c0f1403c0c103036129440312054a0a00403a044503c00d404d104d58002d0381c0e440c1c40700043c10760300380750401c4502d0b40218040a250444c1141d04841e038030003001c035602d030b00007407900010503020300a0b001c2845d20710076181c00103d80056000c503801d8004003409464034a13080c1680d054520040c0584290088100d64000034603490907604100c28480c0300007070007040301041c1211000650406481d04502108029400c40150400415103000c1c010030b100480d6510440b9070364010541005a05820644001048503ca40c0a141c41c8a0100c0031496084da6243c4401101c050151071100c2412000e204110a154002030720491540140c80c00080901e4524804004100003a220030b00c100d03000500c1c009d005201a0003404a50340040c0003d81c44081208041c0d05680861422400f54030340d079500003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245439991 1250 245438741 245438779
    0x6030b0108070e120a2a09020c0303070c03050d0f060f0503010204080a0204020a050f0c0307020f06090d0b0a060b0d1d0a03020a06051306050f0403030b030a0302030d053102 76
    0x70702480540d00e030a10f200522004000740b20001d07496083d00351140d040c3c1d00c001300e40d007242c1856243e0303161041c0100b12110042900c0c1030b1007050f0440c00c0c0031741c010041542c0041000003180e07400015440d044485903001c0c0703011100c621801d59159070040c1800148000c00e01103503c440115a42200049849a40c400500d4203134092407040d070a96420440c007071000742c00c02c1c1e0005d00b119851890300c1e42c680b0114074010b0704660440180c245181e800480c0035811402c056840003030010046507081d042017090000104014580c0200904003100513020a40e10502e0b41c1040c0050180404495101e141c031000f28001031280191007070b00c2c184115081c0a5401e40803620400d06a019070150440c9402c0c0e4403090080c29000e483c0d00c00000d100e01580340460840e01c5207500401c10302505400710308103410002d080e0341c80c02d243c091090704003a05210009400104039010b0074540480410303d0b58400c0002d00c1103c42100308619100035200c9061110b040394000c0c0c08404d4821500b458041c1c801c00340c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245441241 1250 245439991 245440007
    0x20c0115060c050717010b031614120607030902010e04021b0d0f0f0f0918021809070c0b100503010c0504061403011a0d060305011a040b0409030816032406030b01 71
    0x181980d000130001344080e032150003651800342500400410007480304808a41740c541a140d040450080d000014880881c40310803034010210105c8605900010f18401961210300c042c01c50002e0542c2d4141c8502164018000d00280c031400910840d10b42c3c3e03400c07500c5600d951916904c00d50501682125a40490054101514080c1c481d0341c0c007150b2010390001601c2c2c08811804800910101007000905400d44a0340d1250700291302c200581c84840914004080f0f02c2c0006d00c5074414410103003040040c503446910400011741007001d008203030311004920401c40c40d01d1b40056405500b00012034102a422000420413a041590303144143d1b01c140c59a48035a000a015044031a05084140030b5070304680c8010300030034403020000081c400e071341ea070f0761600b1100241114070040034020324010003441d062242e200c440c0d0007078509009244107a03070000c050000c010940015a0714006c10203185500c60340c800c4c4c90880e40520324814008954500600702e004034450703080002d05100f40d110b01940302d0016 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245442491 1250 245441241 245441243
    0x5060f04060b070201122318010501060f2c040c0507020901030f020108100302012102190206090106060801080c0904050a05010c3507210f020903070b0f030c1606020c0115060c 77
    0x561f080d94000300e600141d00341c00c040e02c3e030000c05200f25030f0300d8880704080c070a03180202a25282d20070110107891000d0a007455a586090411956015501000c1a0701100b800d015104880000e83c40199402c10f031154019030002a400006010000c0208441540800e403802d000b41c0701c4000c1d65580303180c620402c1b03c00b800020700080b680d1001c08003d44119403a0482c0d0014008003500304410f041e00c031281103462548100c0141d0002061001102c2c0a00c42c90010702800c0c9130610f001d60400540c940c0e034100c3c0300e109901035081d0200040074044180803102a44d60b01c04000d020190032002c006080d01e020a640810a400c010b0b0a8020041d46403010070000d5500461201c0550340c503801990030120201c0c000002e00e40c4000785a403d0903da100d41030b0307a401c00c0c100050322030b49080145031405c0a01d812101e048102040000800c00c15a02920b900c44494100b09913281c840d60703c2c02c3d0304040c1d80c0e40300400c003900203d070038100031406401c0380101020111495a000381d5650301124a8902514 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245443741 1250 245442491 245442521
    0xb180108060621041104020304060605090c0f090d02011808060106080c03090a0308070509151201060503010b04150306090504060f05060609062a0d080f0708061305060f04060b07020112 81
    0x180f2155030036102c60b2095102d030186808002885e003c0010400b039174000c071812140141d445005014900d0462a015040041030038a01c1c105013000e0418052071094891140c401e0710804000c600716842051508405a41c03a101c210b0516500c085250341c0320400e0003a1030214408200040d01d221114003602e200c0d030b98440c024a44603003262820760b030700712010701400c04200040080c00601d4407001c074500c01d40542d80b11190740c0d8102010080c2c40c001d006070803880c00c200c01080104042141030341a01d00741e507101b00c44001e031108140e0301078004009582c0601c220a062004120a001729588075103d184440c50381801269100350800015104484103294480b2050011803000c40004406444031000d8154291145d800c880d04c90341382810010500000540560421111800700c180e4507800c2007807800c00c4581810700c080090300c01c02c0042c00c401c0c925540c42001070840d0b43c64442c2da00401c038014000300000d07500d51040c1402a4401c0b14164042001c00c0400c0c50340240c1c81c4075601d04000703006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245444991 1250 245443741 245443777
    0x90e0703110403060209010c051603140a210903060f020919060f050903010612060b010f090f060c06150b0c0c0102060606030604090201050403120e01110307020306010b0f040b1801080606 82
    0x90b1341c12000b500200701c01810040b02c0941c1390001001000f00c28518100000e103855402d19624000e014070601c05001142074000099072000502c1d03100c5403480880080303401c41052049141c04442c1141c865101134829810031480d4504803000f640200001c00303042c2c9418101c941500c407450071920b1180f25800c0007030a07401d514468903110340060705c04200010b00126049944040540b040600c2110a481450303465003421003035038000b00310341c0c0780c4003080c117204003407500c0e162030b01c01c62100341c0c80b40030103100c04080a9030401c00d070303507100880c442d01101003141c0c072940fa80d803844015003006001209522031320030008c4040d800001c40512540c4003c040c00c0c61680c40030240805403580d0041207040c04400d2001000003200a1210b822032502c1e56100043d40001400040c15040e2000c81c0c0140351300200004809a2401f0401038191035008004642d14041400c4504107803082c0e03800307805603a1000c00c08a5160703060f20342422034040241d031118455180c0e1000c006141c030840007180d282d41141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245446241 1250 245444991 245444993
    0x210050c0f030c03060a12031e09080f060601091e03020f0409080315040f18061a0d03030e10180b07020a0209040b0402041d03070605060d080a090e0703110403 70
    0x2500140e80c084065010282000d03071010600056030002d441c0000000b00200800c1000d0810320160b00041c801410302128150540d1005005132034680030112800d110203c560712001d00462940b8010704410741100c42c4c072a14142426100e0905031042800100c070240001000015007002900d011144100b20013414515070070030401070301e014001c9401039128401000411690400386104600b5680144901c20000d810001115544060f00301c0300391910509800c1c0c0c44a030b644248190781c0c0540d0000310307220109640300183d01030b0b1000755030009050344004105941504030380c104c1c0ca480c1049400001300d800440e02500c0c07440c0c40400e01e0b06e01c114010760124030001800d540140703040c0143c40d10b50081d90041152210f00315004ea5901c076004c800e01085061901c1008032484544c0d841350b140c00d40342d80140d40c8910a1a0f405002c0645a0000c659541c0d2450542405154800b45159440784a102e0180003e6118443e0001d82d0b030210300003400140c000e0050001541300d50080ba0726160039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245447491 1250 245446241 245446273
    0x21e0f0c011206090203070c0c0602060c0d09020f090108010902010809060103080307140c030f07110f0108011509050301090b07080708040b160e0a06020708071406161704030c0f06080702 82
    0x3106180440d01d0303d8460015035031203c0d1000714001d44195540401c602000d04000c0640c604540c454030440d0b004a040060304020441074880c1442c2518010900825a000041200040c49102d560007528103000055103641584010b5000703100380ca0f0b482e000e64420320010349501013403001810703441c01000050040d45c801d2481510741c402403d507540c2000020b0700c12502d50f80107080002012080000e01405200140448040d482c5045070303120248118240000c280d04011720410402811800c01c1954260252013150043d00002e0020000c44600341009010300b2019a17248000c2030004003c40c000c2c81c4030307049442c030a64005c40c01c1303500ca031100c0201e82403a02d0421200d40400640c455040300359920560f00400504055000f001e100f8208000141488981d45c4102ca54041d12201c2c020316466080645800800030f0802074a6a841401c2c814681c40214444005c0c5640c001004020040903101c0c2c039050761090044503400e203482d00e2090381c0c800f20a43c0c8520140c4d100040440803500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245448741 1250 245447491 245447507
    0x50a020307140717250305030a06080c130c170a0204032105030c0d09080c160b0c0c0d0501060b0c010f11030405150403090b0d0e060601020307032a08030403021e0f0c01 74
    0x1d000440805820f074007842c005c1081c3c0c8421085000840020502c0310101d280d0140f0006030003d040a4180c00217040300040070440441c080208180e26100c2e0683c2950040d25a50020502500101540c1c80c1640940000307501c940400c8032050f2004003074051040c045008400c00300d0a82c4c035001d207591130b2f15020b00c00320b0700b2031400310109944600180c00042c84000c00340c03142240a40c008d000085003840701c070904050035002403451600c184108028150000380c4040306140070b40c0c043d40c0608490a0284c05031085410011442400042c40701e4140e03015840011a5004410b08001036440c4100d202c10340e21041c0c60241503548800780307034010804011031481e0028400d00b80740780c5055a42d940030a03203421001035000e4155660703c2c6054502d40074005503034080824405146402c10130740d00a401044a0800100e00d40301080e66003842840010103983d01d10b402501482d101c0ca03151134001d50320400601d46aa0b20911a04000c12220000a20040700c4101201a01c0c200c0021401152540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245449991 1250 245448741 245448757
    0x1080a18020a09050a14090d0c05030d050c07030201060501020a2f040e030c01060e13120203160807060b0406050a1406070c24020607020607050a12050a020307140717 73
    0x3100141030200690780c407072102005291900010900e8030344040c0c001c04440c2c1064080510854140410840200c00700d42e00903220407500300042e1414103424124618001c45031003003442440e040c2845059070a101c081c14205100307500a12045480c2c1004a03220464101c0003024844080002d0000c1c2d109404444290101e588042d143d03412048001401d031100607007900095000050b107102c111200707000d00300151440f11451811400c01184180f1910840c510150143c0005402c01c662140b080c01101d0300e000820f000200b1041b2103007400d540a902400f01111070320718145510509081c2801800b003240c04c003d101082c62494100840207919007414071b964480000c100720130000d004420b000001e4a0803481a40c1c900b0103145050000e18079142c807041c195071010f030801000c00c1d80003800641c0044207107449601c442a1000a07200d4031111103100d01400d09203020017218001c0c0c0d9003d1031285540341c2e04e92001d110b0212101c11507200340c05c000b030190b0410950301016401000000d1404c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245451241 1250 245449991 245450021
    0x3011203050c010c0909140903030703021b060c0d05070c020f04050903041d06090105032b0905031c0f0c15090c05030a110102060a1406010806061e0403060e070501080a 74
    0x104880c086210708440300c0e1304010010030b040c2c4c0c500707000c0c0407000d01c5032840d085050042008036090008250780e030303400010200e00805400083e4001c4501a01880c145141a450300315025070820a0b0824899000b05003030592381c1e031030600016203841c1310b40004034105802800c035405802d403400c244409004020f02e060102c0c0310400c0001900c21b00350b420488c141181c0ca4022055080200802c0022641070b480b481c46640100c510054019075884403042200c0c2c1c8401c0c3c2c031000401d080040d04d0583d11641b00c9585409040b0352414504110848581e032412995aa446440c081070b80560f1a400b90240141c8030303407074084101d2580784060340300220603806072080c41000c03a40c50002901c2d0114207401242d9108800000c3c004950301080080c1e0050450b6009200c00c2d454141194074500c00240803504000840300030513060f8849030103d420081034143c2080c03115003c144c42c440903a01910049458501d0142080d140c580b01180f4002036039416036418403191503408014014054014400c0c5403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245452491 1250 245451241 245451247
    0x18070c060c0e120705040c090b1c0f05070507030f0f020a11030319020d020601050405011211190f1d010e0f0411180a050a061a13120317010605090102030301120305 72
    0x840c0d510810200c020f030b40d2600080c241039003480103100988103909003150034026102d0052000c9102002625030040c3c0c2600000c001c46004035a0a0141c6201c41295680c04d02d40401d01441613885802401100e0103a1038403c2c1d1f6142c54102250420f51400654006802412500d00040d22a61100000110045c02c0b2400e04c1c0e4148142102812084080c6016034440d80341c40c41c0503501400114014441254108042d61620500c8540301c48107a1005104400e04110b5001d03e0340c0380000c240c000c6440943c11504035440b8072079800300da401401100e4040c2c0562484003a07402d410111a4140e425a800f555150f0312130a07001964000040d10803a0302045c0000b40c1c0301c0c2c94640d441e240f1a082102c4003644040d041c80c40f2080125540a04038200792130812800b07110700d030315621910fa02c0964240c10725a480c03000710603032690b00402c0d0b000800300c40898402a414181d10440e248104c0e03048410301242640d0320795040d81c08d4402e031141c82c0d000d41c00a100400408542c05488001103001c1e0608030701e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245453741 1250 245452491 245452517
    0xe040e030f0406170118051f0906050301061208160507031203020405041a1f0509040204140306061801030209040f15050108011b081b070c030303050618070c060c 71
    0x42140c00c030709003201580e1000300e0104590340d0321181d0701014041100440030103504100d010b400c0007481c040031003403143c0c84901160100075120000302d4454400304807401d007651206000c1016005a1042038420341c02e248000c1070006610b111103101c26813001c030303c52a18908a0001182d441451802c0c0c40354056800000085a48912500c41000d441ea5006903658181003c020031200301d4190350b0700b10841da87c9141c0040c1c54407524140380c0c2a40740307134940002c07482d40f0046030f1502c51480c415030000e0000c0303000162110554039140c032540084080d5000780d03880005211510f4060740d840d94000d80e40e0401000981481d04e0b00d00e80182c05015039090a54190f10348040004a01c1c0300c007009240c0d01e00041002ca10203106a0302c0d070400b4030030440056600c8182c01859801e000d403e005205101102c035901240c04d940c12900900e50101501c142c00d07640c0d04029000740000c40c1d065000d0407454100b001c8200c0d1100203248910701c15151817100800c01c0c0c44110052203800d46410612000c02c410032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245454991 1250 245453741 245453743
    0x60304110d0b0c0d0c0c032c0a03030c06060506120708070e04050403020d090503070605090118122312030a0c171f09020f07030c0303060b120a0c0804050d0e040e 71
    0x1600c40d44201001c0384ea03a5103132586000c01c44221944c10320070050ba4050700c2c0e001903400242c2d2889850008105080614040d0889603480901c84804d035010324003003800410503070818400c082e01030203024100101d84d0f54806200e0903100345140300340700084031000145514041c00645401c0344040c60a0410b112400d8042012104182c2d400d502592000720155000c6034842214005054181c024180700d42c980391001c3c2c8030340203850405050184242c803112610010025803c0113003030b4002803c14004072400d00c08465001018031503500c10018210400c0d102c1e001508083d0075403108404c41c9144e503814174180040141006200810440d402060688080b09090a016000c2c50070101113640c0952407041c008085940100009e600600401c00803110010640300601d8060501c0d4080701414541100144515045903032089400310fa1490b104c015480c2481c030901401d60104512540b180e41980c3c1d4801c220340c018103c0c0c0c0030b108103041071445040000082c240280020500000c03081c0c0c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245456241 1250 245454991 245455013
    0x1503020d0308090a08070b180a0302281a060306090d02060c07081201030b07020c010318032106080106170109020915030106050301020408030306030c0121200703090f0f05060304110d 80
    0x964001095106211406005540014603030080748e00a0004081643d00a07445001e0900300f01080011112074101d140090125241c0259210b60740c48103081d0601385005070001c2c1a200e0700d0192242000203424850b0015401100001c030f0740040280d6901c041070019070707a11859084800300410b200000c508130900ea1042d0180d88070b11451441480c1080c0001d00e00200d100f0307054109414200d1003121024154203540c051758041c42d090b100ea80e504039801c40b200403003041d00b41c1450b10b00b0f00000745a1a041d07000c0c4042d10001600c550860f4214607205007030b2110300d0b001030351124403280442d9000480304000010b091010f0000314803140e0b1040003908a0300141c3c000708040d0030000402074586420701024551583c00d08086444000d00402c0040c010307000701c0b4264406549202000f07043c00780031170500c800458119500e9070b4900c180303802800c401c840d10455800c0705000e10302107000081800c04005a03000074000302d0450391152210151520500c20079500034002c0841400443caa038041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245457491 1250 245456241 245456243
    0x3170a091208070e040603080702090c0909040c05150307021b030f16030b09030a0804080c070e07120608032508120f01080f0d0f030c02010b030313091503020d0308090a0807 76
    0x1030301520310300f04401900b006180c4000c00d20540c43d0a1040c000160000251880903405442d40700d9985d0b60341c44281c125104050509601c004040300308800c0102d480c00c1c090581e101a16001540310013013001c64554042a601c0f0400741e0070900381002510381444d00c504000b2001000c9541c590258030606041082c0f0608000c1c048460100a000b0b1001c0610202d81048900700298540200307080000c0c6440400b80008100220014095483e00820841c040280c42000c405200034104054003a005141082030b480341c01d418980006200003004c0103440c001d04c4260428150b414081c403541e080000c0610b400c03981721100b800702540c200700c0caa0b407640c42002c002c2402c010550400c06031503e001d202c11190b8050b40c0c040728401425a50040300c03568030007020b003004540043e0440d0164054101114015010311000c51545404840140c3c894100c61100000300202c00c4104000d4034140d495020286d0484806581c4c08002485482d0007035000b00840203a540c0c9400a0341d03881d031a5444040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245458741 1250 245457491 245457497
    0x3090302040e0c0325030807170409020918040308011412031602030f0a020a17010e0a03020c0406080f0a0206030408040b030108150a0203190c030603080c01020301060201150303170a0912 82
    0x1410024102003205500c081402080c01407000c20381804c41c0301d030217010300000300481c40104000e010400c100845004000315454041d44550311601742400940100b10701c64801c544218040308803001806105000302c0d09a035804070305e40c4c2403c1e580700c215801d6400c610340100000c081c2c0500f0350020b1015040d0514092030790b511070112801018a4042150505003041e0404015640140d5034075000301c00300c0e19903a162801c03201c1211806401030240d07403940b521074001c00031f0700401c00da070120700e0b0556038404030b60401c03070f243e102c601c502d90b90007034814801d01940c089261340380503140c01e202441c0c1c03003481036903d40d141503140c4103080203541080e44025030581c810b45898a46444092140c7c3c0d001c06464011801c501d0f008140e074000c040c080d50200c0c0c0181d83d4910000d00c680c0302e03802a5000d540c11045d13480d611100101030714001e42c000d01c1000b00651801c210220000d07940120001121703055a1400110701045c4025022201e0250a10b0049031762441c420f000215a030346400450131482e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245459991 1250 245458741 245458753
    0x7091806050f19021e210c0315090a06090c0c020a120c090911030a0807020301050a0e0c0112230402030606031504060c1b14060106020c060f2217010c0f08010e0403090302040e 77
    0xc1120441030018105420441f0103004200ba648446065914244d6044a120566403100c0c0342d160002c0ca80d58010360661420718200b142c045411400a001442c030913075800d41904e50b903001ca00650b46003d04000c181c038554400c2000318a105400504001307002d2103d0b01110446403000902d00f40c03182c1c908840400011400e0004d502d02846410341c8560f4807002400701c1819420305940350311210b038845040c40040d20300003940b114244d02c6040404c024120340d1400251030002c60b03c00340412a0100c0c400e20074840043e10508020031200c020340c241298012035030320f41782e0350b81f80a003611180d0141000030301400c5100e08180310904d2a0300c1d500410f284a4410303e00c5c0e04290500b00142c00100540d03000c1081d00c0c070a901c41d80d08941c0c0340754040060944542c2c103048005100802080304030b640c080c02a4010528403258951110020048402001805c00084003583c25200000c402d4004c145080c0040042010820049a00510a00c1c094a2042d100c0e40082e045a03034150391801c0d02d60003c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 245461241 1250 245459991 245460037
    0x90d02150a02060a0c0807210e01050a0b03010b030a0f020111030d0609020c0c0906100c030e030703050705030706020d1d04140f07090609050d060b0307091806050f19021e 75
    0x14820104a005c05103070000c000d00d0100d601034011181484d020702c2c1402849020004921661300c503086640b1560300900441c200260280040c0011409091003946041c004d844103140019500701c41e583c0c40500c000049485400540700c0f1200464201140d00042040030f4400d2150b101380000303481c02080058403900200d404600d0029031a020764060a111401d1215655a00403a0140841281780c445d851243c2ca150442d038118640d00c9079074162145000101c200b00e0049000030a90700160100c40003a6031317529040b6a60242000003002060380b0400100364101d00c2c0c007000c45c442d040900042000c0c003c0b001c01c0a40d200b0101d565840e410620310a000551341d0042101c8021702580c074203489003505040000350100f5107944001c200c0e036a19020b410741510f050103154010706066004000e8604420840a06140071090841d040e900e014009407404d44010131090140680c103031010404042406110025444203900060902c1c40350b5a5403c0302c60328034001c28aa020880348003a4986030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 245462491 1250 245461241 245461261
    0x60412030c1a040506041401060302120c01110601060804020f0f09070c120215130c0503070305030316030504110d0503040915090b010e090a05040c05150a09090c05090d02150a0206 79
    0x4802014107001c0c442c60034072020540004601d50000d4100304107091400360400810300400940e48002d4100e1000d60042c40d02800103e80c2e0f000c02c442c2030729600703030442c1100d00041d203a8400b40100350101d98410701003405424800003511500e074016104410500c8c00d0700006158041c100e86010028aa022a41c4100a0322110215414205000414414a0401c0d0303400d9450002004c142148110b003d12000f804900f01060b0000d0401406448810303071a400d0007501d03a4030444100e950300e103002940c0c04030305110313215651185e6088282c0582882c0034204204003540050700581d803510041c40089040c8241c0d10030b454030b030541d04010070400d910f04010b0b142500c4407500e0701c60500803000c15107441d03910f4895130142d010101503000146c0344d48030f10b0b00d00d27240100c03500304c20f0300f0046070202e003441d11008500600c00326007541c80315403070f0360340d44c2c00c2c0c40d4199041c01e40c10800090090041d03250b44c0c1801c541c403c211500c0200783e443c6942803007841c0c600a410000300d240040e48003400b40320804139 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 245463741 1250 245462491 245462513
    0x9050a021b0303060a030821040503030709120b040f03140c030c190b0c03070903150608010e0601082817120a14070503060d0c03141614010c02060412030c 68
    0x41c00d40d02460551814100003092102c00b4800036050060002d0101300000b0300380b582d5000700e10341c080020494141400c056669805c111241404a410380c5c034003103020a10080c4c2850711342e41c40003260b88145d03215910000060603580048081c0040c201041d0080340d849009002011500001962500030700610a40341c02c5061040584140f00e900310303032010a082a105541c1300d007507407e28643c0e0f40c9403020215101d0031264005003502024410354224002150400c40031582910000d02520362114402c0b5250701d02880740c5034185e880084004407440110100080e4801510016640b095807502d854a400c1e040d614854150100001d41d10000d1880d81c0c3c0140c0c004002803400c0103900049410000c00d00000341078101841408400035505a48070186440d41640c054580a0250b80c1c9250640d00380800302105803040c000e80300070030392680d181000d9a0886100284000950200c48010340341150740308000e0381c124800300030100b075440c0d60fa90b080440c00e1117584c1d0148441c1c3c09080111200b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 245464991 1250 245463741 245463787
    0x9041821180302150708040e0406060b1614120d06090e03190c02040603060e010b0a0506120a050603030c03040e0105010e04181101090f0b040504050f0402150307030609050a02 77
    0x2004003520180d4015400c00030180e0707078161003284d60b0b4083c3c42c440c0580fa0042c880c004100c66000100030a0310600c20b0700003405648280818800e0680382c4020320b04034001e000035940a00702601c0000c01082c454269400185204026241c011800007890721056012001c600754050301c0d104200305a6031b451040c81ca0b913200b00405141803001050300c0710808a084d40080b0100048407100f84195501c0d41e0103500107561086040002d003000e0002c0c06d01a20080b105280300340c01000c2c002032103041000407203030490301c814000e0310a5900c40724083d00030314001e010349130107100501c00000014000c00052010305210800902c0c59854000010009066500c41500890800000d200c0c103081c5410880b0400d40d01c030311403038002003003800100e803849543e92014050102c00c240000b80e55610500070010740304155801d00c1141c0c0c80e4000300a070040160380007500103a9119440e01c1c004a620099a00138500d40790101d0510340d40c02d4403800340c88064070b00d1440150300181c91000c074180703040034808503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 245466241 1250 245464991 245464997
    0x216050f0c09011203050d090f02090601030c0905130905160801050714030c030a1b050d050a0e030f160b160f03060311010f0302070204091115030606090609041821 72
    0x3449100200e915080306204a080340c00b2299000805c25001798140c0c2e2098458000030045001141007800700071811013410703400b803480c0030040f07500e5500c680907114820f0490780741d402c0c200b407820b42440001c1c0c2040c032000f00d101d81e0f15100600010001e01c07132005e0079107100701018009818608102d0071100c016102d00240544020740c100d5440c1103d0641e03512a03106422142c50340c1d160310141c0b0240a0299141c580c6c50b850310340300210b041c0c21101030080503418000c200a90341d1000d4020301111595040707800164404d0100401c441004e07002410b0500b0040c0780f01c00c060b203050f501c41052280540e0002d428200d021014014950301850401c43e42030146410b010952035500d9804481d1120505076040154010b8401030450082c0c040301c451641c0500204242034643c00c118001600c0220502d200d600b80e00103042403080c498042d00d0040300003d11141c0383c038210a007000003070345c4120803194000f6107c86580502e00580c0450b22034040c0540c070310805034200007003d1050004045002824 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 245467491 1250 245466241 245466253
    0x50705090306010e011a0c1c110f06090a240e0c012a030f11031201080d090e01050904020a15020606120706170c071401090201180302031f020d0216050f 67
    0x1886d4060310740446010098080c80ea0303800e1800c00190900c1d1040141c1100c449a40d00c05252859202010030a040c0800054500b01c5000c1850142c0701c00c8180e81c14444c0d40d0014a2002c0130035281c803959484a543c400a022012004240000c00ea804424a6400c0d07a00302403026800380d60061880c100e84031070444103916050031041c41c81e842141101c000703410001001304000b180760088030030b085103000c0d00c821240c41d8804c850690240c40000d00480013207000e2008400340e0b4500030386090050300d00300605a48243e09160601103c6c41c1d000300144c0c3c0c8120306440014ac6400c007001c9a529120300c69019010b245840000e0242d40600c2540d440c06d43e0f80710003000c00603254004a800d05004500421304000d071584000c0c1c2945001344540034040c00e10724062440320100540c8113940f44c41c801e0701e0f2240181c3c110702d030302c020f50809403001a4041e040042c25410a07180b41d409440c80900c6a440141840700c0386c081e01080343c05c1044420480c44588502c03034103000e020040c91030001044401064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 245468741 1250 245467491 245467499
    0x1150303022815110c030c01020304060c0801050109060f020c06270603061c021f0f090e010f0e0a0f06060210060e090a080a05070b070c0b0906100614070204050705090306010e01 78
    0x8140b198603c09051030a0340c9009446803100e00c8422944603840c602d04607510340b2842039005000b03504c2900c0c1207442505c2d00901020442c0601c0925048400503100c0405041c50004107851141d121400c4000310300901060765a25a0f50310054000b1643e41e0303203000c12084102081e0030130015400d01c80e910440e01441001841da46011503401000d401b000c100000040303a101051017580c68910342c0c0400d4401c000310007030301c691000c1c0c4407480d040561f5403804090b5440b40701420b81c100a01400f0100c01009a00380120760000c11010741000986000050742410802c1c0c02003254040c0d0040c800503041000042507146450165002900d40c00300003800e142085c0d02455926640d80000030050400840d0740040640298107440703486811800703041c240d16110200a11041e40800125002c41164002c030700211000189188181e111000c40513036a810844140e400219100c1c403c0a460401c0100100585941c0102405500c0680f40e143d00c5c2c003001e004040c141034058100052202d02000100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 245469991 1250 245468741 245468753
    0x70305090c1f02011e15230f030a0611030a06060905100e0a0b0403080a030507020307050c090613020d0902040c020d05040506160b04030f031b020c12011503030228 72
    0x3482a4042e40303881641c409107010590150000c4a0462036802c0304002034603118a803508218400d07829074402c90320041d100c03c42c13014804045145141d0003003010180030003505051100074403108008040f24442d581c3c50766030200f0340e003080050000581000c4240f00a40049000b8600030300050b061a100c41030500340450070821156070714004021401801d00f03042d4403100e1b080c0e00a003091182690342c858407428900c0d110b80c001102c040001c2d2a11f0005541244080700b6201c010354003c1c094050f403031201081020100700540507641c000e80113186000071901d40d10017007040c0d140c2c9d80800302c2c18802c3c130300420040b40e20a444000564210050b1000e45540c00001c88080d034008407101030b1074200c1c40701d138032406040381c00d0018442d15210060200f030581008600416808a580a100603d03280c0414034481103210100c201507804040d07281c11340d01c0c0210400c0152003150b0000516041d010860b01c000d07000960003900035030414045560364550b81d800680c22012003103601c54402e41c541d03030340d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 245471241 1250 245469991 245470009
    0xc0602120a08040b1f060806011b050d0305070e0303040f05120d0206070c050c18061201020906040902090f0d0309080f01060f05040e0703240b030a081204050a020d0803070305090c 79
    0x2024041444001045e205008488002c060070500c00241591b840308006002d8140036114103020070203041d0120620800d0440030300505030300c03001a003078580d8180300c164082e0401a00c00001e00001200d20100d54030108060b100a200c48089002d841e89020140121070004006941594021542e07020142c0d0700058a41d410407441d10b004210f98030303682400f905080036298055803041390004401c11081c0c0500c98140a00310444201710820212465a400c0740318100d006500044141320070803001640c0c1d8040c4c51003910140036841c001c4400030018041d9450803800300c0200d80941002e1011400c02c100d00d50344000e1034402005010304213520900c055481d07100c3c0611803078450048a4032079106201501c000c581c072a105141c25545150b11040020b80c4905c0311054900c3d2980c0909a072500242c4c1174800350700f044030907261044c3d1038582d07450003000a209440340c3c4a42d5090707200603150344509440307607400790241d15224181940001c086e0764000d821a2a6a8850f03161208a40d40308002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 245472491 1250 245471241 245471243
    0x706061a030f150301020324120d03150b12041b0f0b071514090d020601031a040507030f0305030f01091e050925050108010506031306020901030b0d0c0602120a0804 72
    0x100b14156500d500c0d540b40c0105081d80055019400807041c0210400381248030701e40d29120520340039000c03450000703011500d220030241c01d005500c04a580c0c101c4900951250802110b00d02080580c06c1c0c50b59451940c691040b4200b4031741c0311200082000b40040303000c0514400f642011119121840c00d050018158002c4c02001c4113860005000b40800400348030f20800000c101c003040c000f00a45c211168221841203ca4080c28000d800320f14081520101c1d54506880d4807020710421711003100354180c100c41006004035010f100303503500800400c5821000410040c46681c5181d924a407407e0400012041030f4030480505003014582c1456140f200120314449413109400141d550f51034400c20b14058450142c01c840d004807100c0d0000704c42c0407001000030b450080e00c2c1c62b81035903600c00c20f0100b1031000b1159480c40c0d03041d84c4605070001d0619001844c0541c0140f41c0842ca48110340e00003410703565581400c4981303c075001420800382d601404590901002c40079264140071403003901409100c80244 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 245473741 1250 245472491 245472511
    0x1030204020d0f0c0e030d090e0c0a030917030106090e010602030a0e01050405210d11100f0618050a0c03050126150f041703130204090f170706061a03 66
    0x42c0300d60020840354030010f1181e508400a010004c10301304043e003500c02c0000000e000c2e0040c480f01d01041030042d15010b00b16041071103a01c1403940e0308604200c658200e50010010551552440000304800490081003281d0075503030742c2d50329490701c44007420603c41948030008031a01c0c000100300182c8c000c010350b0320703100c080d0900000b00007580c4012600d9104a0b0040b40d0300075200c000030103030070038100d240a0003900700d041107402c0c102d9004002d590842030810749000d290310051a07844643c480d504891940740c4007000c04200d25840f070443c036881c01d45500b50000e00e030b0740d5801000303100e0b102c074015140d40342400e0030204003d50500e031400c060300c031041c00808001e41800c3c03400d84102e88108844031011010b100d1004a038181010491102d141c1960300b0355104450700041c059101c4001d08407030107800b107003018014203035442d824040038000b0a40140e80810044bc0e207640803501c02e040d02117078011006255544c4050601d081c1044603816080342c000c2500d420301032a1642a0a800c036508510b402c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 245474991 1250 245473741 245473747
    0xc03030504020a35010218010c05030717030603100b010e0103200409020316110c01031a0d080a0207081216020d1e02120a0f120203070c0f080c0111060103020402 71
    0x800843e280140a07400040301c400496030200c0080c20a8105102c40c001c032a50951611010140c1e95080c4d004141c504038035005510000003681d0f000c0c03034449503e18403406c02d0380c0c1001d40ba41c40b000c0103441c80c04000c18544c1000002c21034076140c02e20209034100d502400c00c101407685940000d200600d542105414941d07a1503c00300303c00903000e105803c070100e91010a030395507110030200020750400d40e440c0f01c1100404c089112242d0003454400c0c0048081401448180002401100034103d0407410000c010303095001700d910340e120310203a03004490040c800d06d81c0d00c1c0020a0002d02d81035041d80504030b9900000b04100c40c5006010840d20045011941d0b080600f80a0000a890f42d00c485001806080c4e05c0500c880030400c040c0d4602642402169100c4451407842e2001e0b844002100c4000c010400662444000600440442c0c03040200c5104581c01c0c94085c1e1360f050101800358001c600300700048541045410000c020004500100b840c0607140300c609402175594441c03040c00001d11454002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 245476241 1250 245474991 245474993
    0x90c0b09010504120818060304081c0b1008190621050106050307090f0b01050f2205030d020303040c050409030504030609080d050f0a06050111030d180b010f0e0a0c0c03030504 77
    0x910b00b038501400301c5541003095504039250020050303208206420554080b4501a00e062a060040d03901c556041a4950b207490b43c82120a03c03d03100220002c0c802d5580c0751181c40141e01e03001c03401181a10a602c800301141400d03241c280410340700341c542202c00d42c1464018807001c40c4a0010144515007100343d1924190740b40780160141030541c1105c2c1c0c252050520024030405942c000803500c0c60713031050420820114800440341440b8504004484c0c003410007212a11441d1201544102000d011004800540340d100190408601e00c10600060307001005000901192050050040c0000c0360308000810b05942c014207180038134400a010150345204110034004000c00b200da005101d10010803003450070009803c1c0c0c07200151031400314940b0b00400483d0550150041481040c0300380002c50030540c5c80c0150401410595591804992005040c000000c071301c9100c141c042e29500b1a20450641002c106040096005044400003401c200150070344030b8010100c1011250135242c045056612 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 245477491 1250 245476241 245476247
    0xb0406120b0421020d140315010804050a02040e100b040e120f0d060f14090f0a0c0c081209150106080403030e0f0f01050a0c0e03070611100203070f080604090c0b0901 73
    0x36070071001c0f015110346508032502d50340c00701c0c2c4028440410348600c944501d550b480005540401c0f030b030050403008a4001c0039400d600800c05281c4c42440b40c8101c0780d404000ea40400c0940f003428503032101603800300603102100600d43c0503002a050055804100001c03800a0b129900e8030049203e10ba003400014400b00480e0012080b104801c00f07289082c0312550741c4158406800446100c1c480768020444020b841620709002c0040c084c0316645601c500c6d6840300000e031002040d528030036109000c4a000c40c100000d5590020b40740102d0020b103800d0807854442c3e01103052840118251070f16103200c00040c8242d0f030b049081c80d600580c140c07400003204040c4081c40c900c3c012140043d60514810308801019040054025522520101a09000400003d00256400041040d480f83e140d0000481442440d114480401030090301c402201c0c01296191000300490340300b6100c0c8400250202c070414a02c58100800d01c3e080f0304180c1301000501d603151180800425140180707200c4120000e45070421b81c0c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 245478741 1250 245477491 245477513
    0x4061803050105041b0b0a090b0f220305061308070b1302060706060303020c04020702132f0a0318050606040525030b1918090606090e010902040b0406120b04 69
    0xc0d0000080180d410715040036445e40300d880910340181c0c20190b00c0810030011131b000713030782002c08952541580d00707080c004400303480e80258030107610004051007036681c1c4c4100c022842c81019004480b04400500318244a8205500240640100360b43c1303002480c0001d242000f1104460f070414262181134989900c0060084440303d406588100040303034000500420340d11480c00c40f03100341c080b210300000c030070144030583c010f02e6806503100a41c42c00d400040c070300c3d5801060510b1800701c002000c0e50010001c1801d01600011401504070010403a0346603580c16104000c4001000030030855246140d81e80c10340d440d50b008050030f01403900c0300c001c00c50b0801018601c0c1180c01c01c1e40306401d4030405c0c0040040c000c0005980a5109a40030507840380d007400307210705507800e0f14440d813001c030024040340070810040c150b43e0400300c2d640c5548102c006140481c500c40d040858030290000715003001d10703004200954076882041c49c802d42c604031041002207207101c802c0000d6a8000010003060b40c582c1055042d001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 245479991 1250 245478741 245478743
    0xe0f18010b101110050709050402030a020c0a12021501030804091805030f0c0c0a030b071404090f05010302210c041d010e0d080a090c09090f02030a05010515040b0604061803 76
    0x40001080d03074925a80000c104000101c1150031103104c40c040b81e0004083d00c0040d130301c00c03021801c0450240154102030300116801044010090320301855640010315050b1140707000c1d2550368080480912041d8103111071419040714561006036075045840e078030002e1285101d050b8a450b99640d0350350b4042124040c40d0b00d5560083d042d00c1d02da80054038000c0042c2c2c4018050780315400b0741104482c05103442e01480c0c0c190307904181546182d41e44d2080654074150b04110900311350000380400030703900106008500d0b000c40038035000318540d41746206210090380c80083c404040b0b010340007900790311131002039180b00d00c110494022031024aa844d050307400c00f4960039030410303650078482000c1c85144005150030024410740d45503005940c8142c40d280c12149414401046030741411020040c60116030000103425000d03642201c1440c4556001034580640c07064102e403036945640410009000403107210440a409450134086250044009603040c0300c1d5004600501c1501d2088815800241c90100051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 245481241 1250 245479991 245479999
    0x71d150102250807060323070c050f012003040228030209010909030f17010303200a03030506010e0f0303030f041a0c0405030606120c12160605040f0e0f18010b 70
    0x2500091252518070b03036103000b07084040c40750180c00500d10344a0712a0401844c2c03005a0110850340708041d40800c400f0107007801c000c200d885010440855400d10400a00345000c50000549005200b1001d19400c650b08110400070b00c1481000056251000e5000e02e54070b1490070f240d50307441c0a1810100403000d582000e500a10104000304900745141c1c0301c0c0002501070303269180840380a20040380c401c1e080c0510300f0381282440c001080000d00607501b40000100d82c021071740c4000e08403e4058940742202100750002600d4806102c103658000b0100055140160f41000d080d440d480c01107035507440054822284142d000e00040c00f40500000c0780c1d02101d140c10074003c101d0910b440c2c0304ca400c1d00180656882405544046407840c40c080a00c1d012400000340a080079404800820140c030422036100410f0740a201d8068490668654008011f040551600741d20b540c20038002004400c481d42160070720104090600021100e00502c10342d01507490394052180c0b05101305224090010644200c1d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 245482491 1250 245481241 245481283
    0x904031101020d0e0f070b0f0304020406090c0e0109080f0a03110123010e01050f090c0c15011e170c1005090303031501110a0201120c05090a03080c071d150102 70
    0x780c18a030404104020000200c4410b05d1070410642d454000034401e042054904003e0046c400c0541e8002c3d40d4007a0000300000f403415900c0f804603082c0c503c1c3c1040480010310420f2204690b41e040441900a0000c040040807048184c844240d03540c6920003000d07040c0303c445908410780d010250440700c3d02001035444100301c00c003260380c10810040d007030145288100c49203001080c1418420009002100010480b07219521201d000d1001c03584031641c100d080e4010b44803c141980c10f00c2070700b18000c0580741c1054032001804c1100320084136854000c0c45043c08024249035074600e00150101c20040f040b140321001213080241507a007403103844031a5403d404003004101d41852034180c9070b50001800c0c0c032102c4e0002c182040941c0c464505800081c0030441d0101e401004895503444080ca4039a2810110700c1d1100c3e0300006050a0f0196000f1204651f0001d40046110b02c207010102c001c00384070000c003440c0003c1d0859450848401000c0c00c0e90f1244043c0c000c0640d80c820000e14105c107207080e1180003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 245483741 1250 245482491 245482507
    0x110609041e020406110102070201021b13090503090f040509032b050c0406030608010e06011a0c12340b06010512090607030608030a12020702060c0f0a03030b0409020609090403110102 80
    0x2a4001303120fa0004252601200c4c254200180212501e1940c16406880d00004446240e01340442a2a807982c2000d00401303a105070034024030a9405140c041d900039038946051200701314600c20307101c2c6920b01071070402d07091200085000013500c0b00d41894070000305105043c850150355044000c07400341911810034080c0030016000d18001c2094900755901031080685030001c060a07500d5281051085901080042010700d501000302a101001100c0300307460700b000d54a80c1e0b49856030800b21240240000240c200c40c01000303818104684100e22582819003040101c882c40c0c0540848002d4011030082c0001640740e84650210381c0301d0203030000245283c0c01c1003600b403a61400105c0382d0501281c41c00d200030a6804d0b000080c0e0f0000d91550380d92104441c89130b10700324041e4101600c1243c02c03440501400d40002418842504204900b0005010408a0341030084c1a5000004054003039403500941c0b0000d61518812580480e0041d42c55071110b40703e52070112000c3e00e80d459645499407010032041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 245484991 1250 245483741 245483801
    0xa03201c11150a030b0303090406081c1419050d062408010f09020c07091404060f11030c280c14120304021207030609031101050f0411060904 62
    0x1403805004030403218059011000784184038030304980e41200c140040c400e225155119801151714000301500760ba041034a42000309041e1074164120804941243e8450140011049200004101c1520f0100011200741c94000b07054800d50f000b111000e608021045145400340080301d0311110303500ca080003013903900c07640c1907a1072070f002e80c101c500100b041034003480c490320481039203041c0d0b2480e40a0082445c07038000c030711000307500c1421044004d00803107000142d10180c1c0e100700220f80b410101c2840607480c1616020040320307112101020510b00e0160051080d40c1a00c09aa40c0503a42455140c4c1c4d0394031142d1450710142c203000e60761250062405116010f83c0c1e11102140210748184011100745030404521600c4200c0d03c03c0c2c520b0316007018070004016141244002c01d0b4640d601d41513500b4030b0f0720f90b02c5039410f503513481506902295001d40d86850050b024441e890348407207820782c1003409041c00e43d58002d1980708881868415040800c040c104ea0b5519480103111505140f008030207000c08960700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 245486241 1250 245484991 245485039
    0x30a1d01061505220f032303032a1912090c0e0c07050715181a070206040b040807030c050108090c060c03090402030a09060c0f020c0d080c0f0109020405010506090a0320 74
    0x1200c0c607000c500a6a40e299184406501002c030095014508503642c82080c0d54003104182c2100c002c12b401c00c0002000b4032103060041000e000254010810b00207540300250141c202440d07078007141c0e860101024085036640b61003000707031250344c1203221082d1644080003009000d1008090501e0142c8040002c40016134540c22100c4001c9859020b00741d1070146203080c1c00203a0f48203900c1c0d4812041c070007004582c000e034000c1c505548000c10007402c093300d6000282c03940d001750f0003032041c80d40089010300504c4890700242c802400240b030620054034103518607603207801894015074002c0308041000d50100c081031085c0c4040d030101902c21034403403034a01100350107083c0700c840540f01d442c9482c072440706061040a1a42c03000207150020240641c25105205c86080654415035044000307004560b00c3d801c0038440d95400080d4180080b0710091a4010042210010303401144a03d504014206058554107100012260048018020b01001c100010010040d440c4240d42c002082503030070348105105051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 245487491 1250 245486241 245486243
    0x4080d030b030709060305030912030f040f0503210a2a0b040b0a0204081b0402070b04050a0201090602160501030f0603022e0201050103030804060b15030a1d01061505220f03 76
    0x40729103a0b41e0704c0607244116015400050815042006400340c182000103980903080b007038130100da180224985152540d80c009800609680400d403208005078602000ba01050021844400c004581c401c2c092809511461103800c05010359800b02e0031040b2050004140b8181260f4612031f1498a20710788091107503011541240c4034040326000c1a190f03c250301c29107080d103980c800200513500b00c80d0b10800700304400c41c0c55030b54090f4003000342c00000307071907280750358066803080c0000c2c0603032080d84c4009456001d80d42c100d0811503200561040312070342600e00e40c1080f1007080c00c000076a00f0b0301c820310001500054001942044544000d110402050b4020380b814042d60034143d4100c00e6440030490a0724020300c400390019400c0c00105000c21955032142c42c002400400804200313606500341505900101d611904880e540c104000d00f07003182e400c41e01c400e1410540200301650510ba04048444104441c0030f042010216054032505420304003000700c000c20201c040384176961790170715080380407580c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 245488741 1250 245487491 245487493
    0x170309060a0f021203191a0102070509040807021003090302010e010515010e030709020c060403120908030103060e03070b010b0a031808311401030c02010903080406051012080405010206070207080714010504080d030b03 95
    0x9882da00020080e2072007c45242c164082d1080e01e10344000c1055459000d08281c5e10240c2c20404800160f031440140300d000c00303090300c0c00f00303240c59103090283c21162102d122030035a9041c9010070000b0700103254400c00c903460900346503052120401c0482d150145a03005140420310010300c0c40344405c0c00056085c03089100b961407001c1c142000034007005407005031300018059642400103200081d0b1b42e80250b5091840c074412a070038901a034581c10322100d070a90100003c44800920088420761600605804900e00d403038440500055039103c580300c0c460301d0380c08081590390101134020003514241e5280a4215400070490030707600d0f0005581c2c8145440706640c04070f49809800c0c062640103005140100c0d8150311104e000b9903868480f1380c041d01c40200f0000b01105100e1000c546a1846168481031a0060210644440c140f000184c03510101400c0c107000c2d51f000c4681001140400524541502c131002c1c0c4004003207a004005840e140201e4114240c01e0250280c80c49590303505511455442c80110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 245489991 1250 245488741 245488751
    0x11d0601050f030f21071b06140414040c0c020915010921170d090318052e1806210b030d030b0a120b01170309060a0f02120319 56
    0x2c810160b83c1c070320960180d0200e401c0803103000d00d41c0c1d041000b60210121492030075031500680da583e25050f505910139a00b9000031203c024000164003010390612001449070041c41c0a04183e5036000c0d40c507003401c4840c0f0482d11030710000555803040034a0075100d58040d10340421030030261608941003880c580302034001103840b00000b1301103550600d01c1c4074041c0c0500403001d020440b5101c3c0640380c0c1c060300341d103000010100700340610224035100302d01259009540e07404500345410f15401808a940d88100d11596805000f05c581d0880c2c0d003601904012200308001004c04280000c1c0d9180c5010200041d814905200002c1c449801000340300c03040c0c41c0003005100c0741d01c561506d24206d40032440c449400d54006141140c0b20f60080d4030180e00c0060090554400d5552110014100404614102c403e03d4165004014445628100400020025000c1d608001d04200403030000e0040e00940d40403c400800340c007102d18020310502d81e0b400c03071115429550385030900424020010b00c40d418502ca910702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 245491241 1250 245489991 245490019
    0x10b030108061302300304080a1e0b01170a0204020418150602030f0a03061a070c0f0303050906090103020d09030305090c12101e020406020a120c0b040b0702011d060105 74
    0x3524180900c1c684c003d0400c6285520803025441228000d420007070b850880700826040400c04001502c002c0c10800d00034583c080d06840c00c0c5c01d25252038045034103160317101c0e601380000944201c5002d056034040803940c840d10784030020651801d038400b100690000d200150100e841c0c00307011002070700110312100c248464601b110181d460350809100c3d600060300309001040401761140700a0041003824030b03001c60442e44444810208080d580700c1d05402c10070004692080180d0040e5101c004e1040c15886811103140d81c41c0a400740c4150465248201c4000811840c0b580c06a4107540020040c04401c100003400c82c0b5002e402040f091710303130a07400d100e104036004003841c08468161450251001900c2c2880510382c82c8405412800140024034600701041c0c001c4509601c05440102407950060086404a0420060540c401c020000412511001040108460840312600540d11641d003010540c0c0b941000c03801000e0084c0c02c1891024041c5030340c00c6111380081c482e41038444c1224185207201074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 245492491 1250 245491241 245491261
    0x5040305281e020106050306100f0b0a090909060e0307030903050106080a02010c06050a09050d02030315120a0f0309120f12020102030402090708060f12060709080106060c02040f060e010b03010806 86
    0x1000924002854542e12485402203030004009020319600010032090344510020381032003012076000c02c141c051034504104054689245200030250320800314a07005422800401521031405854a2030f42c98850840030041c0542c0400050203105050703a889404038a4000d20082e400e2100792180d40c24003034041002c00c00811000200390b8140c40c4c04038682403599a071006408028a0314680d1582c4013441c0e0702080701800040c9002e10320f40d01844e50b91609031401c0382074000b82d029541c00b0703240040f8603140300040040c02e007980d035400c88200d0914101d103103002c440c03901168100c00f510b420512541d500f041042000b84409520803a5110002141c19000304d080340402c80f00a54810942d80208408502a5101c0307034204501504c512044807206000c00c0d40f0000003903c0583e542d21401c100700515034424918000b400c13410b4028000d80c0c1c40e04000406044603140081d01ca0707a5500c17506090b014540d0b05c508020603408030342d48074075a503c1c040500d8581091189500c5401040001184011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 245493741 1250 245492491 245492557
    0x34060c051c15030614040b0906010e04080706060929100912061118030c030c100302090109090e1c08010b0a0f051605010c0f02060921070605040305 65
    0x2481c04410346188000c01a18058580080c040c00d58206402000c40410514001c107910040b01e081039041d182054900b8000c8404024402019500402c006000f407441110740b0f540c10507040f4030016100c015901300203004121540c0044295071a06030403401d40d1407468601c0d4214958030317905001e5a64038a00380050003200a5000c000a45680e105004941b0198440082140600f600040c10045140e02c084281d004c4802c000c00a01803031400e20040c070b410004001690030076070107400340c503141e100482d590030303070000c803036030a16401140245403a403099210078000c01004a09126040c0c04102e0b59855a400e82d000c4500c03002c00341c4038100440e0141c40914100c6000100b607901d4409028811140400c40d00c02081c100f21042006179910f0004c3c9003c150710314018000054a085020000b03441500d40c81074090035034101c0340c10810740c1c0c0030100381e02d8044c85207440c42e0081c03d0300720b03001500d07148134144004004524040a000c18943d00c4070150400441703120803201d80305100c50321022110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 245494991 1250 245493741 245493757
    0xa0e0705090423030708031005030a03140c01091e0b0105010906051213080d0c08070309020a120507030209010602010b0301060501090e27010204081c0302091534060c05 74
    0x1c00048003050000714900c4030415180e040034040700718101c00a0850703003107a0102e402550100000310034022078884200700040100400ca0041c261a44a036602805c85030306e858400c880b0030303804280c200940c0829007121180940c0b019041000c00d049420b01f052070202d1a90594200d482c1e903001017029400342600005403001500e40c01c0c1003042c11048006c8981004003d62a8104185444030002d503200340900884118041c001c1404c50042400800040004040e10109414050a035000d61941c1808005543c112440c6000c210414205949000326035031000390030408d16000086c03d95410340c000190004201e0080c00081e54a00044403150101d0040051120031100401c09400302003044036410b155801441e064104a41d003002d003241c0103507018048076000088070b8020102c601d90b00401030b09140c103045040c9055000032a41180c045898500c2d42040000c01c1c481106001c4802880d81a01c0041d4155145403281440310309490351004035036041c10040b80401150042083d11094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 245496241 1250 245494991 245494999
    0xa2705010e061f0b0307140703050c0607091805101715070c150209030f1905011103040b01060c03020a060903090e06031b01030c0908010609021b0607020a0f0809180a0e0705 76
    0x28504100d84d00030baa0748003500040a005208100307482c00503000020300f004601944409496007001d03560b450a2640081500e0108520301105200c64042c1150725460705540040005032035031001900a103030007150700b003031600881c8580445072012000911050807400d00940740230f00e403945001507590300100301c4001c211202c0c040f0b009590f2840d65000c0c04a540340107048603101d240754085035080880e032000107034a1050058203030050090074051000500c180030a080d285141c50303200c003400b50406000c0d0b1420030640702c86c0042403503c00c201c1c010b01240c2204017080b0205c914940a8209210392060700781a6921030001000c918012801340c02102c0c1d81d030b00c8812650400c000450040c10bc603900c18052100348113011443c60024400c900c080c2c480030380d00590380c2e40c201440b00d20709006000d010072940c2c0000c3c10070241c140c0c00700e0040c1e0340e10340c00100601500181e10300022103004001180341c1000301c20704590b112030115044940034080c501010442061516207854030f4800710700a250304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 245497491 1250 245496241 245496301
    0x70213050c0a081f08030409290d020303040f1e0501050a0905040b180108250b070f030306080307150c050702030c0904020105040315020d0b0103050f0a2705010e06 72
    0x26650080c4a50303540084c00a68000d000c1e00c410b2218400c000303254000303619551000c10b0034080c0c50024400d24142941d08405a0103245880c45503209001002c20054019620381d20380c801151800c00540e030140130341e41c0400e00c581d0380301e0003e240c00695041d00c5503025a0000702c006a1540150100e561690303950380d4070b403401d60400d420301000c0e140503082550007492042c0c0d900403910340d44400f0341c080e000c5200502615182c00c0c01700c181441030420048450305652504100f200c82031022680c06a62291032400c02e05801e0070154010401640450070300c0c040081c0c07880c00c00c142403030b00c01c0c240034040c0c0c41000769801003030048803107000390728000390103601c280c07003031005032402802c1d007a8424414540241780580301c0c2c3d20600c4103022407014504040e008901d180040c6860b0080340004502031804000520700a84403c401030710180003403201d40d03070b50418070310b0070a514085c3d40030104010203c200304026034034185008010b4002e11a0007801001e001c55001038940e00003d120f94184c1c960054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 245498741 1250 245497491 245497507
    0x3020108130507051302070521030106080901020d020403110307090506060f0702040f0207030c0c0605130e0a09050607020c041104030201020309090709030b0412031a13020a2102070213050c 83
    0x4204500448140c41c039114240f8009a140c0c0c2c0d00340e43d403044d480b0084000d40c545003070f40b804a20300440170075845484645800000100c120b6081500e04440300ca1502c02c000e1380302c9805060091080302e1040404c00d000050210501410302401e803014041034088039085661901c04e8001c54000f030322025071002e820483e008000c0700c01e001400340c290000300300189a01200031510200c2c1d001d074200328041080d50510300103001907481801c0060919040c030b546440c0c0d8003a0350008444503030040a1180c3c04803400b040c41d951655001b000c000f6032010840c0d855003060040a5a50417400c1001d034821824442d0b13400c0111800d1042d64203c0e641038004508180d2803008102d6010310041641080101d20000003000c19250013081707001d180281d144e121000f2240c075005054940046901c441400c3d0303882d0310740c2151109003000004141d0030000581315010f2100440c1d04000304440565142e034011462840708035950700400c1810310845580011103941c14250302941e504032254080c1c4041130040b03103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 245499991 1250 245498741 245498761
    0x7050a0b070602041706070206150a0501081518090f0f0a061e09030309141902121011030105180c04290d05040303051f03080f040f030501090312020403020108 70
    0x34115210360030240c2403c1e00d800d00b1144210703917403825461503881002031192840e0144505600f0032002084054070190950200e20150301030b00c80c2e141007002010020b40c448038035101841a03004001c1440d4407442d0280d900c012014410754900905001d034030380901c46900e000030480824650f00029042482039629140000c010100008070f028512014001c8080201c1c1b14140c8100c2c46920300240301001c50070017406403507003642c00b006244e10200101d00410700c40d000c0013181642c1151032038288101304100360b0402d00e07100e0015000d035041c03000d00c1c07142e010840c002d5410703100142d802034080c4003090190a16120241c82c1480943c40400c801c3c0042c84e01e41648442e49405d01d54031810503505880c85203a20b52084000c0d680d503982c1c4900340010103a050080f190801030003070b0780d60440044640902c101008601c40180990400208440f1040703901c070071b45006028192a510400d0780d2810054080c0c480700d042200080e4012407152503440647c401c2e1030a0704d0b010303504c40c1100c2d9501503043c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 245501241 1250 245499991 245499997
    0x181119030b0604060302061b070506030103150f020d02120108100c050a0503060f060715061e0506090a091b0f0212030a1a0301051f05060405151e03040f031107050a0b 73
    0x61604144c0750b201c040050f84a15005140040428104c2c01c00c0e07020300c40c0214144052030f00118400c41d0100010400305013402c88200046422000c00511925542000e100920880b00204c080300d00106109250400842d1294104c850030030640713044000419042088400001002c4007086040c0110210540b240c0c01450344600b01502100c03003125070400082c1d039600100b104a64030040c80450b01411240d80c02914001c081d01d800c506682a034104100414901a000d03031400740c0c4001c41c5684003035641c460000001c0c0442078041000c0c0180c844907a5203040380c0810716020440b01010ba102d41803001622254003901b060303030181542c87e070540380406403644014141c207011f001d018040d460750b020310031940602816101a48048042c102d07a42c0800c0c03103a40010705c02c8009000400954442e01509542c0a803c0d0101c40c1d0f4844039045194400100450300403c0440048200000c22420115030340c01d240c02074a80d81c04868420140c103a95810502805800c00e0b08004204018404000030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 245502491 1250 245501241 245501251
    0x5090a1e030e18092104051306030b070201090b0c0408072c01060f0f0309020303030103030c0f05030a030b210703031d040e0c040e060c070b060112181119030b 70
    0x10b5285424070300c2c00103450320b074800030300c03000c1028040034407858400800040f00c2d400c44141603010b03141744c066880480f60049101e480c2c020354500740c0301b40f9503100541c4010083c6505c100f4042043c100380f04000d0082c40c07212070450f21055031401151188003060181c408484e81103000700540740c20901603041d000c1c0320740541409024400102146548400304090180090b40e440241c5580381e8a0000d118108120042d804e043c41c1800850168a020040342e055a03050300b44075215115074070b0a01d6660000c510041e02034000822070a81a0764160000001c10710210b600c10f6680007045969410300c803401c610a036040d44500320800009000300d40702d0ba500e03012405a140b00c00316a0f404501a02c40d102c1840001e0340000d4000003840c0350038802d0340802040c44005021a2070a05800e4103148550302c400f800c401c038048001240c81e031045400207000d10b403403042072200c00d0303080280501c0c0c10840c3c1001c882111500c0e0185500e814190300c01c0311101511400080c6c07252464607450144080581 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 245503597 1106 245502491 245502497
    0x50d02070f02240d15030c03050a170a020a110402090a0f0302030f1c0c0809060d020c151b071a040b07020c0402090604050613031502070605090a1e03 66
    0x41ea01284a8090002080c2512101200717055145074802001d600c008400841001008501a00301c14420842c05510101d9003000b6046c0c1c3c01000002c500580c007004880010131040c00c042c3e00542406000149030920810100d82c406107a0f0704030714038090110030104210b00b0200105e80080d24880060300090307880b507051199002201164104129030382e401c202c1400070f96000c071060394600408c00c0c1e5803040b507606223801135001201c841034203018840304a1407480007000c035144100f205462116500c18001101c4520380c101c943c00b651281c481c0030700514a1080f03d409540100e00503420b08000f440c005400038a80318242c107501b4029030040c00307100520344a180541c0d058820403140305868000680b0b10b00441c001c250300240240034a400110901e00c429401052802e00484c8180138998915549070351700c4032a94401400340288180d41080e01e49510820304100303110349 = true := by decide +kernel

theorem cover : BRFrame.Cov 245323741 245503597 := by
  have h0 := BRFrame.cov_init 245323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 245323741 ≤ n) (h2 : n < 245503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
