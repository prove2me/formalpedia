-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:08:55.551852+00:00
-- url     : https://prove2.me/submissions/a0b6e6f5-24df-4b6d-8968-c0ecb8f9e2fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194064748 ≤ n < 194244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194065998 1250 194064748 194064751
    0x60606030207171810030f0b040e060106050d110d1d070e270d03020318060709090b010e030f061f03080301061b080c2b021c0c0215030a1103 62
    0x10001200d48410b2020340b0700c510051301c0b05140c6440c101d4603142210010a180c03400b0b40350100c000a0b1200c110380c1307030021540251503010a003602e0401668582249072911450306009032400c00c06d001841c0c1c4500000e5800104060b00c01080e070310350382d900501100004041122445c40308c2c90781c146118802c4a8042036082c1120580c0581101640e25507904552030425610031142c180c01c81907041c0d00070300c82001040e0305918103480060703490500c013048000486014035074020a6028900300f00c0115800035104049803802d0340b01141100038200140c400b80204002641c040c820007000c24440b000c0040c1550243c0740303800700802c0044800400302060545400068500e213001c10041240038810301e008641070b038800c59000036101007a035451003258010150214583d2264100850501034070031015400200701e034034664248210346019455841041800500d4080b156822035250300078010301c0308082e03000701101983c403130f01500ca00d0141c01c15164200481d00c3c4c1680d0b503802e0000c0d04100c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194067248 1250 194065998 194066003
    0x90f090601031502070b0a0e0f07151b080d060f120201051e040e040f0c09020304120e03030d020f031006091206020a0e090411040b03030a1407050f0f030403060606030207 75
    0x810590b82561641403248191641070480c90394200050004500e003e4078a501030340714140041500512540d107103280c00003803040c61032140c20480e0200880400c0d0b810030800e9407032608000c01c20070090300c2d0388560660312040c060244400000d21050ac4c0b92071758007070800d82e01c4c2c941d4061295a00c403c482480100c400074002d0114200f001510840008410340e04040d1400203e92440e00e0307101c612807000d07444151422142610344420002c204030000301007030043c0540d0b003002c50440c0b400e502c034090480d040d86404014040348421100c059103080c81112924080d858083d580e51092100401c030790741c0100c0320750038210800c00000c2403542c82000d1141c00c691005101c1d420706200c0e0f4481c20000c0d803022008005020340c42c07181d0310017a26005403c0d031003a4040c802c200d040010f042c00384015500143d01d114403035001004200c0340190048603a00020506004d800d131210401c1c03824901c2c0441c9014016900e00c21003c0048120400200900c10390f4807581c414040e4581d10b000650982c002c40100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194068498 1250 194067248 194067253
    0x305090d180801060303020307050f06040f06090c1a0a031803020706050d09020a0e04050105070c0206030c07020102190f03180602030406030b0303070204050a020315030c091807081b090f09 83
    0x8103041d11400d489030301c0c0303401c18410145480d51204410f013124003551088003d0380002c125441031141c280107404a07842113031302401140c5440e61b11040c0014051000074032a40c1d8034150711050118155801025003081c2e000046501b0020321034280d07a030459020400013a0909404e44116002c3e80c2e075020403c1e6050300105180c0341440400c1d600c0b50040f2000e82e5900da65498588003507540c180000008100d600103e045506003400c00b1829214000c00c0ca034248500700f940400107803107820850342e2002c000c514050b1a0415880100d04164044651922079000c4442505c10f001c41440261072980c4652116081a103800450a205419a100d120090780050101b00301c603501980141e003950304000d094902d84201c641c00102111001d4032240c1c92140d0102c00c00040c860000564a6005e82c11001400401310b0040000c410380001003081c80e800030303650302414010760108251005024004299007546000d800c6144090a413056000c0c80341001e18017190340001c000340c81c94021040b00c1d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194069748 1250 194068498 194068513
    0x10f06080c1c02060703020a05030708040e06010f0c1101090905160e1906030504020a09020a0806031002310b1219090308060909071505130902041d1506040902120106030509 76
    0x4c104858200c44c01c10307000c1d4050003a20310006803080c0001c1c84561300c0751130360355121400c004400394201c0d0700829840c18800000c6c8811602d81d0049184035103240c0c00384800010340c00c502e004036026180d030361083c42032604101c00e210030a40d04110400b005c45c0580e680c2140345412400b0031060301140001045c4c0581d40740414020300340300303400250348140064441c0f411582d40c1c80c9400c040740d009080c00c40010b010340f41031001314603060000c480950591801503040895030358280d000d072840c107404072041105180016042c10442ca040350000c142e81d41419403036000e4951010802801100c0040c040201d42c0c0264a030011188144104a500b42da1000c1056a0784000c2c4600c0741c4014001418901c40d01c4d00018020b40e4080a1001e6181c00d55121611030000e40c06903120400c4940001c100580107100a000c2400c1e800402ca844640c00c20113548903031134007096692482c410361410ba800040010300802e2582c81c80d0018185640250085030842c0c3c0d940a0440864106a030104001c1e0130034230 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194070998 1250 194069748 194069753
    0xf0307020915010509120618060115111e0f0c06034501060e0a0e120a1404121109070e06090a050307030b04020a060516080a050705010f06080c1c 64
    0x745182d2a4541030500704d10b0025094001691000313407804806980d40000d04100305c401000340c080ca5510504002801c00b5414104c09000c6110144045002c03c04000c1100003c40c40400550440b002e0003040d0b032403802d030f24001680d100c0f40d0300c000c6100240306403920304c007480c18a13008603403240041d004c40b130b4031640c003149034442002c05200001c4141e254034180603a046110304041c460154015000045042c6000121960103070003c03c20b5010707034030b00740c0754268042d070201c1e250244c500d5050710360395204030038a0300b69443d200387e0307000ca000c500d8081030215481c0303c00d00100c3c0c2501d006004101d0441d0000d41040044032046911100160342140340800ea030500001074400d580000f0000902e49031100042850700c003541d8000e44540c240d0070284000d41c10000046400b80426141042c5440a52110040400c0094000030140c280001c0d42d00b640e83c1c451000d07076403c0d65000d0000d00c051401840c00703401a0185003c1d65209000d5521058520714010362100c250b0105501e003c5c0307443e881074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194072248 1250 194070998 194071021
    0x314010b040f090c0e120606100809030a080709030b0703050a240b0307110307050a2108010b280c02010f020c0f0405040c05030601120b01090b01080a0905030f0406020304080f03070209 81
    0x2000d8000c248211010111151b82d608248100d00805030340042649140c14800c0113900030000d4001c8007880416400d0212201000c01150887d42c1c460421405a4039106402c84016415510185c41c00712030600b030221060385a080303d4064408041d05111a10b00c01130340f503000d0000c0741020761500401100c00c00400c0c1c100005554004d02908281b000780d08a24040ea08690005204507069040078404008114487c94400108000b000043c1e00410681a015101d80b00600401c0181100441c00e00c101c18612202d05000c09103944210303600c48c10880004d00481c01043d400c86c007150034008181e00091001982c0ba4444030300601404121401000380801800c000d401591400761920b808a100d07201082600d00230100780507610200c03002c0341440c0415103010b0300462001401d15101e030303441c0d81c0d00501054000f6024100021040074503d0080d24502c140624001610400f00d4009565038000c800b1f0811120b4040903038841c0c1201d240001d850303104600d8000e6105240c00042079071140700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194073498 1250 194072248 194072261
    0x10f120b0f060c0606040f06050d110d02060d1407051309020309030c0f0d0305090a0b060f0301061a1e0903120a03090614010305100501030b072304060314010b040f09 73
    0x140660140100100202d14194403060100c01039034068420704c00a410705109200700301038454010801141014005405204000f001501c110707410340714034a9641d54441a801e95550040580c1d56440d030184480d400b40020642841005540400048803c0d0081d4126042d41e4441583c2400c0c0c1800c0c850964000d40010344841e10500c0300744106070200b041000900d1009410034018a2a0061140d0080c2960302c0101420259004100213100003003403900c04542001c812030388049506000004607004084a034012982d0805280c0c400c11082076501c01000300883d5040b882c0010001c410f0415158410380020b2509136200000d175844004401d80a805221481c0c6000320f1417444c1e6490b070000380c86940050b07070750440503500108100102082701d0451102d08410901c019851502d603aa04650018203070703010b100d00c9081b941c036404030300228102ca8007000711802d034545843c0c80c4000c005201c400011390713036030800e10000b0400780c101d04160f030308581c2d1000e00d942501d81041c802c880035050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194074748 1250 194073498 194073521
    0x30c0e0f21150f100b03010501080c09030d08070f170411150d020a030b2409190e0609011205030a03021305040516030b01091409062e030b010f12 64
    0x210350245040350341c0d0900000714280e1403100030000c80c2c104028140da1051014044001c4905002d400b084281740c2003056030704495090a0800c810396407100015541e1185402c4264540a03040748030322050380000314107000d40d4140e075820480d01c440070400d84603040881c558500084019000400090360220b11146801001d41080c51052845071203020540050719072401068010072664400c03541032250b280d0400040385d0301c09210520500c280034102002e01080081c020006941a0a4130f07401c07440c8044180310354152a180d595800121a410006c0c1d84640c401d54080000150340710240f07241c2400c00b174200c801340d49400c0c00346809078000d40c44441003403010030706002d000a0341e035100c1c03040c0c0c0e2040c0c1351542ea0120071000340030000c080b50204198503051205401c001d001441070050b090142c1441510144040d460301400144560007843d03607501415010034591300f4218214044104000091310203003d0000018019100d00c0684140c810014060187d9560000c26640000d80c4020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194075998 1250 194074748 194074789
    0x1b0d0204020a05070c1d1b120601110a0c091a0303120717090a06050c0f0d0b060904090c031e12050304060902060f070309091812030b09100303030c0e0f 67
    0x4c0c0c80d0f9841038040c5d201030b0b20600c210840b8401ca2481c1c14040f20405900500c0100f24a000700c0607920804180e0003404c0c0c4c0c241c0039014000015070241d02850a504140022900700d030b00c01801490500d45aa40714068108001c0c01e04019800018200600c2030950750001d0280d030818100c0154155074000041c101c2c8100581e01e9000c46800072604001e41c012213200ac050040b8181030b00f868000da0301c024040601c0301500b04a0908446451070039100c251810081c003182c80c4609000050150003080c945582c0030340761080d1541000306811a00c004c90f0302c0745901c41c4042c00401e00a0400c080a814090030440c0d20600314541ca600c01d900855000d4441e01c40081c0152154011500c10340212454000000000500c0420b140d0489090380080c1100a0300303210440110440f0380380680a041c0c001d2a040c09419028038160081d040b038825800003401e810f10034a00742101c107160800c01d21068000c20701d00b03001215440d00c907400d007504ca40300c06026039020042d500140003510f01c0c418180382c03010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194077248 1250 194075998 194076007
    0x1112040e04170703090e160f050c01020d0203100302011b08090d02061308010b011205010815040804091b030f05040b01030b0c0d020c03090306090a0f170f0c0f1b0d0204020a05 77
    0x146036041c00341400303d00036640e090080d41007015400480d0b5000e00001485401c080ca030780d4400350300c80c01d81d460042d049d20b8240d4a07a443e80320303494064020b10010071040d40c00802089400001043c1da607007103038000d0340c88036846440082c446680100c00c0002170448203041101c0501070400301040c1c03103880d01c0502201e03d0490303a084444c0b0703c4590303900f041c0c031141d4546406d48115a4002d1000380b820715045000c110075498400d2044c2d07103020401003a550000d0600001c1c0c140081c2c0030a440084c04100001c0c0b01a07541e5809072103024201190350300100340343c65028005640313941705440c80f0b140d00c03550227802c0343d0075034a0704641e1034170050401941c04c0d002c0000d4040c04d05d03a400a841290740c500c1c021502c41c2000070416041090041403094030b0740c802d40c00f0401151070a400c2034140c940041c8038000c0740407160345c815500d2151003084002c000c00040e05c140c044c8800211490420b5000080d100940b0780081c55940454103005050340c0a41032003514005490a680206802c000c14203016203031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194078498 1250 194077248 194077283
    0x30a0b010e060313020415260c09090303011503050106081f05030d050409060e130b0702011b110d080105210a0c15020c0d02060a08190f06061112040e04 67
    0x83da1080311402c068500000c81c1d1002c40c1400d014010803408000c09020103075080101d20303001c9800284c0c9801002281009104496505114803041c21002501201407490b2108045540c1e03070003881441c10581c544003540d20381c54420700c1164142d4030f6503901c0b2019038549000001d40403a50b0301d1906940c10400d5000107495604000070303400807115464198403185050040401c4595640c81112414040020440078000e02c1e0402c3c2d0740d4660054001d5810b48400100302d004100d0024000d00d20005503020008003900319191503000d880007411201586103800301256010000c1c0726442e00303c10b180d0a8203100f01d890851f1040134019400031200402c00e40d44030b0201c2014180d001d0f20910740d81d2500f00030301c560b0502c111594100309981000c2c40d06503990101e40c01d8418600b240040181c50b101050313141040594441d400c00c03003410140720000000e0039940003030039284211000b04d168880003088058010610202082c001c0c1e15107400c2600d08040000408030041c400c607202c940c03112400301d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194079748 1250 194078498 194078509
    0x130c060f1202032404060302030c0d0602040503122d0a030f020c0607050405010206070f08040f141c0314090a0b061201020a021606030504020310020d0b120c012003030a0b010e 77
    0x82030610504a000800590394180c9084c030740b00340014001c0d0704240050015880009185034010b03002d13150303000840224200780e0001c0c0690741101d0b030f15001c0da100055140f10300b0801f8181c001460700803030401400301c020b10182da01010200740100c0001740000360310b04d4020391208010b58152540949845944040703d414044101d07001004144041070500141d6810804568084204d062082c80210702c10300281001000400c014061118070450100b0009482580e040100480c811145050400b004291101485080c1c4100003480c01e846a00341c0c030201a8518003ca000304082c0000d11413640720440c0110340100000d80015074010040e440a009100401d218142da03030290480799680340488001d00c0c0d107503218404041c140b4050101580c0c0c0800d8005244a4164006035034410114080024064203408294445c0019002d011402004940364001c0c43c3c0990740d00b0420000194074660801449034400c643c2d500500000b0031400c00d0350b0103c400741c01d05040252408025600182 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194080998 1250 194079748 194079751
    0x12070806010f06030606050c070504020d061d01050f0d030806040e01090525052e02070b070503040509010905040b01060f200c0108070e0d0b04020d0f0c0e130c060f120203 75
    0x3036600d42c1c604030800000350b2500c01c2d940a804140340040c40c1044d02c01d0011b660b03d003180911441654001040151b81525a205000420100e00e8010351a0312046c0403102e005000d100b454010441003a0180741460102080040d247d410380340e104690b12004280b0004090051580d100d540d6108401404141700b040700b002d00b501418003a41418500000203e503924655105900030b010f0405171400307040c01c4066480506901e0b80b00e510340a0768951003240b03012141d5200c140d0410000564900744400800140192141a44c603000980d82c1d0343c24070001c0750740c01c54000e131080c0521801440128447e5a8907400e0f80301c00d10b003030004400c0c0100300c0d02c201e008400910b52a644013443c1c4100550304100b805600222504180b03010418002c0400c41d00884100d009000d40364100000d011517503210161101941c02115035403900c05245044407500d007080c0034039030ba0404004001101e1914022425245039800f4056103411440c044080d22400d0403400a03030288211381c8032031010764101d0310145 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194082248 1250 194080998 194081009
    0x30312040609062a0212071b0504050118050c04060e10020a0203100507030b0312180d050109030c05060f0114010305060607060c2f15180d020a06050112020a03021207080601 76
    0x8001000008958084a1136032034100c00954010081d448000c4102c203003503481440d00280300b0314006501076030803895600309070000f5030700900d050000f003000b600c80b522400c90299400410803068580b01c80c0c201081c0100e2044000041c0c11840c482d005040914582d500f6220354012a0305240465002030305203007050341800c0d40c0c3c0713548004005c1e40d1030341030003815400403003039016111925110301d00681500c80c140f0120802c4200344401c880686400d42c51040300e070f0304000200403101007450000c0101c0340d05c0105417024464500859034454159180504a40880706481c003811420001900908801850541d101000f40044804650140500094200340740c2e21414903850200e141d460400040080030001521301802090750040014455442c00340c041d4141710a6851381c001c28000751403064801d800340207860143c48104d40005010a0151146c0030502113682c80d240c400c5481c4880380000f80d44244240001c101606145900d6903001a0100684000d41e0312a20340d0b9107420402c0c1d114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194083498 1250 194082248 194082281
    0xf060302210a020315040b10050c0f030c010501060e1207060e1c0f061a06120408190905040f0b030a02101e0203180306040b280c02010903030b040b03031204060906 72
    0x4220b0342102c00d01040170789517400c60f800c0020340400030200751114508411030003817240c00651030404841c100305212001409008583c2d03516114411540648030a100d0800403c0e00300001408901d000440062a16041d03001440c0043ca001800c0324100e20809140e83c001d2058900c610200c190780c1da8900303004c0e00030440303580c00482501d49034049404421000605504030200c0031031554a038000c849240300861501541384d25203062418480c811544c1c0d8402022080308041a41a001442d22040341c00c01c9800300841d032803503a5107009462920442d00e070b044c0c210f40a030000514203400c0030321400d2910f10b0000c94500b01c070b00c803088020501e05a03001c050b07403000c82c40340b0000c4d0141c54040d020301e805034003502c501d007003c1d07035080c41403c03024241c041c90b55284072040c070b10081e4441c0c8000030b01c11840030174041000100c101a000340403118003500000d0404034004404d003050300401419070805802140743c494009111490000c01400480e0700070f03104d2142e10040b86203405030b89500c445403000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194084748 1250 194083498 194083501
    0xc02010519051b190f030c1b02030106090c0903031818020a09090e070302030c060412030c030e1804050f060c0a0309020f0a090b090f0705030103020108090f120d0c03060f060302210a0203 82
    0x70007400107170035414100101400c007401d58a039560700185500c45040a0103030f0704110b8405100090141c191508046180c901c2e00031080030980d13201c2004c01c200c0c1c0c02030325102203100b0300d0410341c1804c00c0036000304080340c045045024410364080d4000c04600c0264502009483d446800007010303912180d5440c0699840f40d1414400d40c82c00340701d403600702181100c00500d01441c200c00168000c401000c06424020b106191200349402602e1401c54144000c010b2407848103451078010031030a0686052310305120388a00f43c444060002105401408803110032424460404000c40290009010498018050040404040d11503103d4000070f05401640811180f452206004504000034403541c204000d000c141f00d0000e4009085138152602071915078425034880c06214071741000c03501c81c062140705000341e035494040c51170080c00280da40c10b24140b101404954044060314024052a010445584e1040014500950082a1040d22032078508038940d00145400e4810200300d54901c00f8a40010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194085998 1250 194084748 194084797
    0x5091309120206100f030c0509130f0c0311010e0102060f06030a061401090c0f0503070c0f020603070206180106060801050906010c080c010606230a120608010c120c02010519051b 78
    0x10140400745c41d0400c108007001d0b1564442803680708092180a0190b94003802081101c403d01403104180e503040b80300040141000e10701001c407803240344000d4a0b8180041c0c2c0c5d0b980035610445041e403049005900401c00ea44407411581a00040640990390500c502031301d510000c0c40c2c138000d82000c903000d031095201c030f503140002000945080c00c1e040001c001d40034480082650f04001aa03410090038030f0103400250241ca400d01140d09860710183d44042c01104014883c0d50020b0024403818146001c110082c0700701600070300703840240c02040c0114450600502203424803440e06907100c90140b42441c01085642c0b03821901c1c0c2c3c086c45808150740d440741c2080c842035421500181d15240c05c1084904005494052004140074000b400003c005100c102180c1214542d0404c2c8080e0281c00020480d8005084024003c01d40d656150324003641001c4181543d1801131054074070902980300d4402e01e00b00c0394144007001f0540200456036005030315803164000b204a502034802040051045440c9500c0030303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194087248 1250 194085998 194086021
    0x20100903020604051b090f0606040b190306090b0d021c0b040f030e09010609050d0311030c0a02040b060c0601031401232712070302100504260a05091309120206 70
    0x3100503805e140035400c2803c003191240040c4070350003014464496280d4841301c00103905803089a0289552500c0811051058505034400780c0003410f8a4904024490f60f410044054a10840c4090b80c4a81761001c0140541003003001d403c5c10b501424003032602248036954035024801d060300d040c1c502c0c01585400408151b00410070380982c450841707098042d90315068009180030b10900a590090301c0d110000c2c1d08043c0a080c0203420080c103c030030769807a0350111454540d41e40c500074060344245c1c1000010b50440c01c0c07980486d041c3d043c240003d0103107617086440b0303403100030030941d94500340d07650300d81419601405580c0380c945041071a0b03013010000c1c181780381400308a81e8030305440500220601c1d003811600c10700141101d120b54a160b02c1646803141800c0c1603060503c41c2c0418600141080108000c0001d001d2041d080703940c3c0490700080700034640100e07948500500310307214041601080340d40d1061030152407111103261507030004500015566141035084044038206030169202905014010a04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194088498 1250 194087248 194087263
    0x8031003020a1d070c0201020c03060f06030705060903030d0207080d060e0604050f070e010e220b03070608090601030b06040e0f010903110111160618050a02031c2010090302060405 79
    0x2c0e00d0180044000c000300f21240b1910240c082000d1141d00d1390f408046900a1050f01c01c04030008080c0c4005141c860100208002d007180e4a92003401840004111482c00c030b025030702924005401982860126140d00000313611494007030b940f600d424040141354000600511018056440c150307030040c1010350601090761400f403c2e1000600c100400c10210503480202d0b0701e01e40000741b07030660481002201007640321b4071a030788003080314008100e6401c0701650ba4000d00c40400d002c2d0210341d0b074a40e8070041250010750030b5030a0401900b0000c01000820005400326401c02c0008000052495001a043d03180034400700d021703030281e515548403000380341d0800340d8030f04c2c0754a020009000c01007030082c03800d0303031486070703e080e000c0d8030141041040500c180d0394029119031440001e05c01810905007000340c1c1da10800c2404922074030800027034040c00f108800c5841c0d6900141d4903010041903961003088203030400c6c024080c1c2d46200d180304401c940940c50140c2c2d07031203034081c0d000340846003000e00f00b280c2446003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194089748 1250 194088498 194088509
    0x6090b070309080d0b0f0301020409090c0b0a0203040b0d0209120c180c0702060d0906111e0a0806280f03060609050105011704061107080d0c1d010f050708031003020a 73
    0x2c0c0448402c04507041c1000c444400000003000a03c000b054400038460041440b481c03030301503202240224007601280e0100e00043d02844410310141d85d0b03030303c129145100705100080141c00600c0f08004011804025060301e1100420150401c000f440202c0c111039074090459000d0f42c070101380399800d41095910b588c074408100580c0c00c81850175072030360442d030310078600002d02034070001440b220780203880e922000040303903c0b403820300c02c8004021540c095600240801c10303000f58034581c0e40d0b01013006002110040e407800e445124195a44400f00304000007917210140b512b4a503169004808610031202d0400741191106003001c46003941800821138030a6007011080300d103010700500c40c40c0e0700081c0c520300104203a000e44c002d5035951302d00307032024000c1a82c019540d018040798000811003140045d0101c01d810210130002401510401c884000e0070300034501d100001d00221a01e0f81d403007140705c1d020704041c50070310f1880e10005548011042d4004c461002e40880080320900031071800c00c503094024807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194090998 1250 194089748 194089751
    0xc0d1e09081c0e0a030803181c05030405011d01020a0201060b040503030f090604030b010602061504180201050a0306170705030c091b1803061f0602030708070803070e0a0306090b0703 80
    0x41c00e0240d107654850308403004640106140095105036032103810340d0f00780c12070060910422203950345001540d0760400d680e402010402400c0c1118070000000e805602c00b091116450342c031010361081511036500c044e105407000d548030548040340404080b42d00807405a50000140d40d0704407480d00908503981a0014420381c04200420015943c001060359030310b140c610701c5569036030301c40320020f01684200e60005200d84880c8000040c8070341c0104000d44900140750b02c40329640750090421048480740d186045040710901681c00243d4400c4000c2c20000c18036040008003162112076065800d051010000280d510022040c4000d09050195560801c02510440a60708102644c04003401c0c814044900b001e01c0401c1070080130410313200c0b1250300d41c0b014003a01c0244c28400c1c211b03241c03610710082640108043c5603000810701d20010071520345c5500942801c6c184400341e0303181400c0b9440034049408110b01602e450305a0b55800303108a0003135215082c0010000c4491604501c0e95600408520905 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194092248 1250 194090998 194091017
    0x10e03011404021c1502091804030c0b06091612020405030a2f130207030203090604091a01020706050a08060315010608150105090d0803060316090603030908010506100804080c0d1e 79
    0xb000c0003204036101c91700d80d0000d030b2154118030201d40030007450448010241035410074130044c1034100d04110b01d228050101c00d803442d903c41d002d00011150035034160400c51140c40e0641c1c0c025100744214a250500081e01515150359140080d20b444048001580c000c40710429087d02d6120001c520300340100424150102e5040c6e001c001a510040c0401046155800180c000c04140c42402211401000102ba00381c449407910350724002000d07140140d03c61070106480790052580002070b403000310b80456480c6854580c2c0d140c42140c500c0f20180240c0d42520070300542964400604e40824017828095492480720301e000ba442e0b010045000750500e040c00010447e80c5004c0e02c6011180c0320440e040700c070307195480d02d4910103c2d10303000440c2d048202c08580140041085c0009421080440f8000d5031110f21054464a8403401c0302c4050b1601c0c1c1c0d01000600c50a9001c900074140c059006005010042c10f143c080e03414581820a00d00c0c4c01d4000500902d446000400c6001c1c2c184003041c0035180a0381603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194093498 1250 194092248 194092253
    0x4150318030e01180305060c0c0c010e060301141825030b0f06031f03050d0e01030b06090d03050403050a0503030709060203130603020f09060d091109040c030f02010e03011404021c 79
    0x345221004103a0401c2600f4907840130700c0e00002c104034010355000d0201d40c02868046031022340c5405c104140481c502413400704515640c4104400d684180c0000d1038145940d10381002c0c6401034500c002170a40105111541c140c07020300700b601281c4a00740703011610000500544c2c4440d501182800071405261030105041c0ca1a1102544510ba500c020b496960380d80d2102c0306640d200b40210041c00d2900e2582c0710000c01004004509085507040c21348580700d1445050005509039079001d00384941040044c0044084c91421259001100e03001e81401c5243c60344988500f410000208010f0340c40b0391002089c0030000e81d001d800c010003000c491000d1800e00c01d07d1641c10501c082c0a200d890201500851468580364211013203070307040c15008100d15516403a04180074007a00351440c003598515400204420f10b810300146039071050381d00600d02d070040c904550b10803410200001042c2d0402040242e0901c0548091260082d00b01034001c14075068a4244100310070002c12801103010105c404490000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194094748 1250 194093498 194093507
    0xb030303100b0a110f0a290a2a03091e0b0402090603071706010e0907030f122c0307091104051c0606180c09120605041104020415031803 60
    0x3900c000700380b1280e891840d0b28007210b40b881c00c2c3c035001035a80940d00002681c078a00080f0300c0b881911414482d40d07c1c282c805000c150020601408100002c001000650007000b02c0e4050344044d0003e00a94200000078410381c4161756100c0c103000c0101e0340d03a1640303500b80140f40c400d040b503072038203d0a14141d20300075945e503044503040508001c2c05041d440c004102207039018040700b80900480340d0001600c0ca00541c041d0764420f800e00c00e1040611103800811100ca40210341442a29040b4000f412285115622103820003040119170f000c0000c1030b0890b04140780301805030450503020f0010201c05036406400c040c10300a0365400100020305d024003910707601101c0c005460469600f2516004002c140044050130900c0e00380303006244914040740030a96103904148186c00304891401040b1410304694166030781c8000f0b00410305808071205018000840341e030401940700d03200e2040d240100c404540440d00741e07041a000280310180400100300e00d1589482000309002d590000718443c03400503100500b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194095998 1250 194094748 194094781
    0x30711040c0c0318030b07020a02040e0a1208150301050a0c080901150b0901020106030212010c0207270209040f0903080115050304080904050612160f08030a02060f1e09030403060b030303 82
    0x2428800005131030407a0b080300c048080c00564100c10b8117191803138440300094503040c010808034400c611303150400d01d15140c0010114441a40442c1078006044036201c29244420001c04a8011050311403011109403070a004480c05106c080d00042806070700e44d000502481c40041110ba4980c0c5404288505c51051590003000c40f041d499001d40d0310030107600101e0140000341c0010790001a00c5000103201c09055011043d03591596095034040c03516540e41c0c110500c0c1d000c8242c1f8082c0c00f800e400704007402040e4020440024014000215140400b0141c0140c81c142001540446d2040004000708400c83c01d000c014042203280075451880d0990399012103029200d160750044d503440f4005841500e400407202c481c42590004c40f142485440302c00f00001c400c8d405820071401c0144c4000800328800829501c840c1039540180c40251b580694400d00300da0000c1112070742c0d1200144018048000ca030140d4003407030300c41c006103658504600b0001d040c3e6401240c44c5c1c1c0203500400c00c210a60102c401041e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194097248 1250 194095998 194096003
    0xb0301150f020d0e0301060b1206091003050d0e011b050d09060e150702041805010501080d050702011b082208060603070b0d110d020f0307120608210f0408030711040c0c 74
    0xc50130907071070100340180510342045c83c0ca0717140056504a4076492041c040c0c801c1d0021580404943d0703980075980c061120b1403100400342d0b40203000c1900490f0259400d1080c84006140004180c20300c0491800f001250540c190368980001d02d400e5803460740709081c50054000381c14215451300d1030f03501190400850200014081a0110b81d80c400c40d5210f40056003520b1098000405450300c90801e280204003c1c8a104280e02c00c0080748d400d00f60284040e5008560142c40320109003201480604443c1020b0f0401c0b00c210308200512955070485c4883c201d140c25041075140f0065003040501440d00130003926552181d844410100203403c4000e0480d00e901507001004074055130a541620514040c3c140c030b90400500102e52642c4142404000d540300315055501c0101c184400c150b5041203502901952000b81c000780c001590280303040c0e4041d0324006032824030501e00030800c2c07105003850300f00390004032a40c1c00005603101030040103d402c030883d10017140c0800c076500b04803c000c0c0030100c00c00c0c0700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194098498 1250 194097248 194097257
    0x20c0310020f0f0309150604091e110411040608060604030503071e020a030803041101030b10051e0307080405160f06080702010e1002041d04080307030902060706060b0301150f020d 79
    0x7585a184000401d450b103500411043c00d40b40e00701503402c143c54051010168400e03104440000711680341c14000c00441e0b9400000b000c0301d1200155132a52002e240c0b1030305440c070201401d0200c9164a99214500f2140394120a95803501c0c10a0402040840007400c418800c10b0240420b102042e008002c4918041d4003d030082d03030141c0c0c120341d1001b08480034000650300ca100c100c000014403100c0001584a40c3c459440c1c07090390011100154214ad2a2004140e008040c0c070040c450b1007400342c8020100c0c100c0c054061210020358120110b003a0744200c60740c07400902d00d50207020401904101d0401c1c0a0f8400c0a000c02c030a00300b483d0402400c00b42e100740b600300400e400100c0c2e540c034000e500041c0a0b42200d8103586181c81080010f0b006580a403148041d618060405a5240902110741c503000720f5101c8051840d40d26405000c901500200d40241c2e0320000410245002903100c0c0304140017050240a6152658034102c4012002e5508040200902203500191110a9404103c0c40d44c1801b80e400c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194099748 1250 194098498 194098507
    0x30307030b01170901050a0e24070e130e010605031911120d020c09150604120804151d040b100c240f18020303040303050d0212071707020c031002 64
    0x4903801c5900b4503200c8004484401413000c550019004a40b00308000c910911105201c100125680c441c202003030b1219180b100103108604036040242c03500982e5901d006968020040d0000350302d003180c0340b048040d040d0340c0c3c1c514107038201d030a004110080408401070329481854001e00c0d00140c8003420000d144030b8280f260124503070f031003004415400c18014200c85071a4080400a5a90448007140c1442400240300041403000c1c0c581c480016100060060381c10f10745854090700602549030811610440144808183c030404002500b0b00301226035900e180c1c0c1c0f06a840980c04070b10603007110901580c201100398006455080b0b03489a00903081c5005481071082e800c000442c0403001a584170340e0a21850480c1e4030a000340c000c1207081c000c4440070003001041d407811464410b601c00c4002d4254005010800119000c2c5000d440142070b0b8050145c940b00001c02101d1681d28102d411001043c0002132045408005480d115030008040c0020811600804000f03580c640e00e0310340c6560150740009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 194100998 1250 194099748 194099771
    0x70e0f0f10090c050c12030112060203090a141f060312050a180620030c1510080706080106030e06060303160507090606080105030f0102030f0a0c23040906060305060303030703 77
    0xd860300001d0840c0c2c0b0341000030700c035880070042240d8004010148248103401704040310503040780031a412034030003501d144a110800d586000180d00000c010309440d01851100c3e40200701d01c0d0b008a03201c42c80d000054040c29141500038000b8001c91416205142d00d081c10502c0060703a500300c00c807002c914034100b40d07440344030b0f48604446400341d8120400d580f80c500e600004060740c01c0346100300740c11404002e09124144441e415540c07030240e1103080303c3c5640100803850040004c407044641141440007050700b0345803661a05840c0c10480e40c003030380005004a0041040c0c6a0510030034211420040103054641040b83c00660f03203006400f410380b407183c0040000400c1050400c4032400070034203040c087c8132103541c61002138031001091080600a024a13812a06205c07810b20841e03128500007902090691190000c00000700340c04020002408600b2044180c01880502003007034542c44062120380d120300782070b01881a0390350396000005040c00c050501943d9035000c415030380d0040c5035150001d040710031380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 194102248 1250 194100998 194101021
    0x204020904060305010b0411180108130507060503010e0a020a0e010e040603050a0b150a031a1914070f0e06031506040308070501020334030e10020d0608070e0f0f 71
    0x14424180d001e49410000002c00c1410341049865000466003084002641c0d2140c6030144540280f0580241d10f80d144580e1644c0a8503005800015000038041c1c3d00b4001c0d52090300c0d200150300701c5008941c02100400445400070b0310b00c0c3e0302c928804001e40c04c101003240090103e001706108141800240b445540d00da441c0e07035005000442e082412141104814180041420000e444400880500000c461610706050b101401200e074041c20b0500145d100005c59095048060840d0620104021482403c20b00c10301a44090081d414503100190500d0900609211600103864003030008104080c2d805540c0d10050780d504c0f294039640340d8820741001700081d560384217a0304002d100000c045456000e20030154081c51089140d8024124141c00c90200401c000c0030004e110001c0164244606c0740c11480b03a08450003807020501260401015041403070266042803056640032591210100500d12040042d02d0003440c04505900c40f81c2808070062001d000024038109158501c04040340c0c41e190392 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 194103498 1250 194102248 194102257
    0x9061b1908071b111c020604090221090607020606030708030919091b030509030304080306011d1005070b010e01290403020901060c052a2103130e010602060c07030507020402 76
    0x4600e00681101c040c2e250401080c4510084d041c010403070100c40102085040e445521296001882141040d181218642c06540312802c94520b194024106130000f034000240a40500101000340ca014600100001e24014005102920030b60115404001103000030007296440300007074400c085d0541c0d69425a03ca402d80b954031040990307240c50400412100c045032040350104c040e540501147c0c0f60070f0a0203039a8041a140034100c048100049105507020310151410b440220b4511150300c008140050401518003916030701180313002074404100649145001d015000301d0700b0308000ea5041050134003880725040684507070110b0380380c4c9400f05d24801c881a503008560040882c0060340e1a950b00625103605203008440768820800c00d0308500d04004ac010f4550045a51499440010007080110039407816030075805002c0600b40d04d00102c80288014140702030100d00d0b40e0000351a20068403001d60050b409403046400c03e40502c500c2c4c200c440c0464840d0358051800320380b21000c5000250081c0304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 194104748 1250 194103498 194103527
    0x903050708030a080703060303081302010e0301090311010c09030c15020f03030106200a030e061c02030405030a020f120306041a030a0f020a0b0a1b03110609061b190807 74
    0x2500c10029071480000018000f81c48160b860f08074640f42c1c00340a4064840c1e600008010030400800240500000c14204400768014034203200003003040c8001c6421101070325001d40000b0006101e94041409c02d000b4090b480c009071034103071103180c034503101d00d03c0c401c0390350294220321010344444001c0c042c400c001801c403442c810740c20f4a84d83c0d6520600540b0038584000c2400e003400c0c948601400a5801007054080309415071541141c0320900d03404c011166011708a1503902c46607140c0c034540462251f00c05180305d80c1c4180c00440d915032b000076019141c0101d0401880d00303540300484031058408100c1c00e8a4114200f5907012520044c83c1c40c3c12090054000cac0b09940511a180949090004c00040306e06c100d4025070780c80e1091525601c01d49814403c16502c00c000c00c180710182000d482c440594072400500038982050b501100130542c9080040903202c0b40400e61255060004074082c00784e41203c492400500b8500e8400e601c11ba1f0704250707500030401c1c014000c9034000521464050b8415412420303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 194105998 1250 194104748 194104753
    0x30a0812040507060504060f030e0f0106060c020f0a0501020709050a140712061e060c020307050a0e1b0412030c0f1401020a080a060f0b0c03040902030115030e0a030816090305 77
    0x2451030401418440219820344051144070000039009014804440c1500c0301c594034100c48095402068000c0c161464820005d03104000ba0202012000e2041d100508541d82e6400001c0d1080c0c010400b55070100700e051445100c9064040107186c0c1c0004400080f00c000320f00210300707655000c403180c0c02014070340034011494440d5800c208031154406900100b0b0000c151007000b641d5107425800e440252081c03998000c00300171070414000a401a5910700000340300900f03c4420685401c08a02100600c1d8040c40b000c1e044070341445000c042001c4201e400170455508503090524003072440710000e4140740003405215443e1940001e0007001e45803103141c5038210300d6034010740c08807015440c000d601207266980003410500206045003031500460307003103900d103126160340300e0f0a04d004260580c0c05468455140d100c10040010141d106001441c003c0892602e840311041e982d000150540750303500381e40c1c0519040124482c0000b80c1008850303410203141e00000d43c240d00c1c02c0b1011784041805420240507071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 194107248 1250 194105998 194106007
    0x50d06020904020a08040b0906040209070e060f0c0d1d0603071b1205030a0e0f0705191205011b1b0b0c040302030613021f02030304080f0f07120305010501110606060702030a08 77
    0x103174012444c107010b00e2044004140071f554984210392928003c0d40d009500420041c0454019880303000007903141343c40204a80d103064400c1c1400b03c90b43d40071072800103454100302950201c0b04d8102d554884888000e480056000c00004c1c0080d5070742c4002403c240a1040c078242100075540e1071502c0403c034a62060404500d00f09150300503005400c110351041c6502d00304014412400400301d01001d03199248001403003044d00740001c00441c030328120601c03850340c076106070006140c0c08020281d200040c06040002817040d14100700c1100856040400018485800380d09114001c403010b420041c01c0d000307a0241c040d61520005500d45210366400a54144185000d00c8003807020314102d1441d0034401c5073b40c0c120018041120b440c4120720040408090f0b001030001601040032480100911403d248005107008401d00c00070b50302e504500000c0e203402e01c000d00c1c00c0900390381610a8902401c0242000f003a6220005a425a9000700510303860040c4800700f81070045403020810206625402012661034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 194108498 1250 194107248 194107267
    0x1b190309020406080102041d06060c06040305040503060a05010e040f030908120904180822051305100b040f060c0204090804080d080c0a050409180605340504050d0602090402 76
    0xa0030880c2800e0b40b09901c2e18200080004052080710304840c1103040e01490b006480c440c880458030002d0515400071b00402111102c04070602805201320321a0300c809454a06140500d4074000c0002c140f00c0280d86010014410300d0071001c0c10b598001d0f44164044c6484815240c112148002548a0400f512a202c0d00c00c22000f01c0310003400b801003054404200c07586015001c117070309134a5008042c0111078100202d08150400301000f0b40700101e5038803114a0a95188041210b60b800c808400e0303a0282c0d241c09104510208d4540c00c1d006000b401c0440341800e090091b0a9507850040c4035075002d10240c501e0540840d15560800800c603038000a29984403555003c550b61194070b000d01c2c0c4000a907821000950100d00581611003161159450b181010308020503480142a44403d2a4074a171011710864001046406031f03522609c0c4042e9200b0920f40c401c403411301c0094a24413126502c40300001c0d0f01d0100c5503c07000f075404031502213595000800c907900b0910028403c5400c1c182d086030000500900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 194109748 1250 194108498 194108501
    0x30608060a06140f060a050c0304050d0602192a0302011d01022223030c030a06020c0c0a050607110109031e2a05060307020f0109060e0607020a03081b1903 68
    0x443d1042c0307800301d489480100400c030500311020010b81d84a03c0078030414507068451000340030fa8184070310440f071400c1c0c0c072080000c00040751840211a4150001011030b131142c4490300300542201139080a0740c1c8120a01d66859805e125481071404603440761041809140c400d404c1100d00480403c000c0c0002c86114800501039446080045510540209142c54481401c010541240c0b11640b1104651030341c3e40c28031020780b99409149a040c4500400303281103650a10007441c000d07100301401a6a15100031141c1d0604076072100c614403039580110104038903100c0c00103d858003903015061191040400c00141c41688080e0006000d2100d1003410000424414104415440c061048140700c0122040c2c0803094a0741000a01019400c0450802680c00e2001c0915009141801500d000c04041500d4600319041484240c0e152501c80d07402c911580814868148c01440c644068120240c42d0b07100500654000b400914481108048074051407404400b5641e0820240c6112201400c903d10001c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 194110998 1250 194109748 194109761
    0x91107020409121403070e010f0c32070608060d03110304080307060f021602011101021c050f0a0506060334030506040b0a080c010509060403060c091401030209180601030608060a 78
    0x3030100d501d00e04e0000001d114201500e10450342951604180041c0c0d500466038000c107186410107001821002a00161510b03900044460b00203030580d9170340d24148404030703041300365042030010f5030042d200a1000c1a80b002d41c040c1d015605441c07a00b0308240c945812540c0310320082c3d080019010118000c10741040102c001c100e200d000300c8041c4000c5400a13036100c01c030301c900348640c0922021a1108001540101801544034031854001404c041c100405038036408102c1c1c0c10a504940c1c1e48080000004220100c107420180d903640410880c68080c0100c2c81c1b6110242c40d03490b21a1f1106000e181c84207150b0b070031003021180280303003d05e48140a50f02401821066402c10b100d20300f007004440f101d0621900e200c0807501c4050082412580003401510207074064480240c1100c420080800420014001c00200c50800e0740c5e0340070f009141940700902001c0c500b104c241010f0041083c40c90f181d5a040f506028130f520490942c1d1252240780c0140e0051170704e980004040d014400c100880a0015404003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 194112248 1250 194110998 194111033
    0x3011b020105090d0801050d1b0609030302010609111c06030516051806031e0f0f06041b0302030d05030a0902030d20030f0f03040c030803010b091309020901091107020409 75
    0x20b0085407903410080b9214008582080005061940104003a1600183c54507000e030140c6004010000f4081404c071044569410003408100c075607004108040e42486004014074441c801044100c00058030000144174401c840c1da4616140400c1d0244040c00b50301800003194000c080b10030446a001e545000700e1080c0c03154034490910300c07000111009004103810b124031402000f0345120a014840d141034045110301400b900d128020028401c1801040b003c40708090a0006213400d01c0c0130b00e4280c44500158500742c0c060075003d442000180c40c00505800203c00c181805512543c4400c0c26030024000d4a00180d8907108124000300b800c0d40102c60030213140340f0b98100b034a42c0c2c400440511358130300c42d503600000321080400030500108481c5000e980c0041c4191544030850b5680e03101c86046030070030b812100ca89980066007042c585072004d0540e010105000c0184210140c940006c0c00c40c1c07005200790000252500b259050080c0020304442880b64020004c0100340e40701d0910003041080103902 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 194113498 1250 194112248 194112251
    0x90e1f05010203030717072001061a0a050a0503070e090f0604050a02070213050907080601030c05030c1e090c1303060f0510030f030c080f1204170a0207091a03011b0201 74
    0x41603552012080301e100301d4480c0c640d5008070f828629800d8035540000d09a404016030060124800309610400810040500c00003048290902e80b018008640d001071801507030804002403550a50083c0070f41d0300114480c20884e0722940e840c0e006aa040314031400c05079000101108200240c0401d4580600458095074204070990b20329001d04100c1c417420304003175400218404212909e0269400c050f070700c185085c02796008540c1c1d400f080d0345005800c1e0070807104e120700c4910a00140c00d08000c00c0c105c0010071070310000c101490910340c0c0c10300a040102c2502807450700c80081d40b0850b0203021221800ba15003160801c80303a0780c0c14020700500c184807030040305504001c04115008064412401a81e40144070f4840c44040c555065451002902c1c0444882205104040b00003810002030302041007005601c0c0d102d0f05d000d28015030b440007124180c440202080c04144003142c0e0009e000740c00e940e00804009242d500168288000b20081c40300076034191300748440c0c0080c0d911380200044c0c0b0107031541c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 194114748 1250 194113498 194113561
    0xe0a0c0806010b0405300708010b010203090a181b0f02070e011a0a12050a0504120804030504060516060609140f010b1c0e060720070503120a090e 64
    0x4255032507210038440d0a00d448401d102c213012602c0c0c01c00c40c1041002d200c09001c420401c81114801854405942d044140c0c0c00000040181c01800c1c0900d00c1c0741c1c0001d00c0a1131030814910002400b0801760b00610440325041181c81c40e080580f03078410b00302800d0f002c51a4110290394540102019000f108108c01409102d0001620003842e0074480e060701d00000400070307078400840d01c060381900451001001c110f51484200c1d14041c0070720845008900050700400c280c900307810b05104003802044448200310402e400c0102099100041e94103031070483c41e00380c2e80c41708001d08000e0f03040081c00d000352142d80f80c4607001481c18807036440540c0203084001d22044036a180c504d0328484107000d1081e40130740700d03080080b2044460201d00300c00300314480402c00154107e0250301d05151203021074942e0b0104034107040f841c1e400a0313882d0040d0422580d10005002c418204030210351a8403c01e142484110700200b00492402e018071601000350403000107150551521032501c1c80d0081701060300d080d842c40442e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 194115998 1250 194114748 194114759
    0xa1b05010c050d0309080d051626010501030b060d02030109060e070f02032a010509060f0604090f0f0804080f012708030f1504020706020918101203120e0a0c 69
    0x70440c050301500700c80903000b81489034600340c01900069804440703042c41009140034120151103550b0154000e9907001100742d80c50400600a03114401da58090052444100f8195640c00803400303046d118280380104558080341c000c2202401b0301c01d40740300400c0c008000401c00840d146c0c40701e0210703120700700001010303155101e003a96400c800000710300040e0010400e0158584d61020413012480b450507c0c0400702e0105840d8908580c01980c0e1940d00d90440300a124030040342006040d000700f402c540c10442c04415544408102d00710b0b0310000e1001545030142014000c046007958010400c1000703950f8031400640382c41f4000e000e1360045205107072100b016801c2205c2076480808006038842d608600c0d54031441803000324841c00a0511000050451409403243c41e140051704050348900d40c09038407800b184040004c3c1003502481504940200010403004e12010750f41c420480e10030105203504a500e506003150070b903801c020100065410b0041801441c1c800054844100b8020059040b6464458 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 194117248 1250 194115998 194116007
    0x207110a05030304090c09170c0a0621090203010e0d0f08010617010902161b09050105040903021203151503091b0a06031e060b07020a0f0b0711030f0a1b0501 69
    0x1d014041e0141d001384028400c80e0300c1940400076803601424051420381c1e0380d000041d81d03861050b03044045030f00b00c854809045d0034015502000b8080d01e040c510810501040c00f03038a25451401c600c65240c3d111090324055403820740c0301d0b1170a0100b11003640c8000200c1e40010300700d03810820348000052044000000c1c103601c12041545a0ba09050074210141d1910b50900d02035040b09101e000c0e40c480c0a254940003440e015042864034035a119140c214034580340d41d540840340140d103c9402203080c9404000002d9020840d2814440f0740c0102c9a101d894405085840801c85040e0640000c1080e01200b070f80c0b10340c440554440d2028201310b0f00c00446c0380081d1180408c00456035038005814031401d0000f14043d8012004c40c401c402c4000c2e0441810b02c4501050f600280d01440481c5800201401941000f00080016007048011241000c3c079050745c460041c0324440c00580418080907070750f465550180441d825440c0d0701342c112640c0c034440d4100314032002060504030401d45803110300040c0da075004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 194118498 1250 194117248 194117269
    0x50c0418020a0306022d1605100f0c02070f140d0812040807020f01180e0702030c0303012409180f0617010c0809010e12130503030a02030a0912021c050705060a03020711 74
    0x280c60146d82009004400000f490450b040200c0c1c882c0514038062400c200944504044124111004908012061006400d1089513000b48894940c00e01090140900007061410444001c2d00c131070405512030b0030300e52040c1c00307815808118090307d00700340020300c4281c01c00781c10420b0080700c003000e5815000c0010f45560794074009080e0080f038548400c21004800c206400d902c594180140c900d0001c00c01c01d030b2030665000340c01c054044150700301605998000140700c0700d0b00c810035003040c00350301e070502c01c4003590708a81e010110382e025100d045103140110a604080000e1800c1040e0740b00480c44020340d940a0200080558005a8010300117521503070140100b0100490510282c00440c0100c2020925544a181f49002010402e0000102c5072000c00040000304540d80c0655103e10405400030162007495010181000d074458008005da80d40c121404004108405207003000e9201c0d141c240c3c18a8429481294803500120306221a6074064004095052250b4280341e141c3d2118420802c9100c4d0f0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 194119748 1250 194118498 194118577
    0x213060201060602060c070b16021e061005030102040b032215050402120102030c04050d080910080417090901051c0b070e0306010801090f0b09010b0913120903050c0418020a030602 79
    0x4011000ca0710504c680c0c0d4458020305410310546e11060301007404030310805412030bc0080d9640c041d1007049541c03180d9400d08000350100b20000e600c0c041c68900218000d020103070a605480c8480e9210382c014007030b44040380c80019884207000d080d05030001c0c140401400b040710b050b400303040e9001083c40b003030341e040c0300301c1e4868040c0311a0f4505040c00c2005000c030940ca02201101e01036030030486800940d0301c48140100300032882d51903403c0c914007803070503071820620510410200b00c800d00c5060321300d5035024081410760b0010f0340c162425080c09240c43c040c0204112019007034032400d405220540c0d50210039085010310545c216192a60380e00d01090032150315101c00380c6028210901c0d01c00040e60604910740201500002143e04403240002841c07448082c1c902500c0a04001e2803842000031f080003c14580400c1d040540c801c901c0c3d521020b8440800d009102d1040da601e02125051141c0041840842c0b9005840150115101d1600f030009600124020161300b0101d031500220142c00a03082c2001603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 194120998 1250 194119748 194119763
    0x1216020304060f05120f010305120c0a0803040302013b0c03072d060c0c08060405102706060303030e0313140a0b0706051005060a020714040213060201060602060c07 72
    0x5103030600480c0c00d05128006001003100402c041440341490305d00c024043c0f854141301640551451519610b031820741040500900d60601c1400035032036000c501e02c100c6070307081410550307244e50f0780c6022401040c140b42140c1e06c44021840000b001042d5940d1542c2c9104242d070503203001d0010b000c03210750301d4100000e195455403004809212180c0c803100c44840803010721003a01f425065142c5003062810458120388001280100410b080c400c4e10f4480500400c030307020140c9118105074a581d600c4540342708120603000c0e103511035100004050060b230320400740500c1071821030348140c0c50403801822540c88164006801c0c140c4d81860340d040401104c8904803103600b140041c0d0314010419142c441c024050b01e600013100e20001440d400207900a0248a00c2141d0005042c81e10a00348007065500e500b0450081c0c0303007070003041240c1d600007404c030056031a822414882c0f1103141c80010060f12840403e101c00c001c1540b0300254a0387c0540205043d1400c0350240e034015642c007040340342180104000980941c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 194122248 1250 194120998 194121007
    0x605070512280e12070f02120c04060b0a05030f06120106031110021f0b040b042d020906090103051005030703080d0c08131410060f1a030f0610090305060c12160203 72
    0x19000178200c0e5842000c2c0180b46283c0b0b40c0010b000c1035801021125990080c40300510546007903c0341c100035004241d020340c02c2400c80000108640002031210300c80d080043d0204665941c0c1c24460700344030251f2790003840b0721922450803081860148081600840110003064085800824407144080514290120601c00745060070060420617100540040d41d405102d101c0d91514068805142c9003481500488024031040445007900b1500150100d803040c4500c1d201030b95004201d0302166030920700840c4944551058021002d426404258144181580002040002405040f40107d0f80b402082064402e60f02138400120480d000701000030242054000a45841c0c102d104e840c1e86401100c00102800100760101c5030aa04032500d0700c600caa100300045038118000b92407403003400c5c43c8241113043c00030741100340d07040c050103040c03007600112605400c05203c2c142080c0150f0b0418202c40d89418908849035580d070003c00c0812003186039034001101d00c1c20404200a031004981c0c000c502d403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 194123498 1250 194122248 194122273
    0x901020405040e0d1b1b06050a11011103060111030409020403050c01110a030813150603110f0303120a05190908070204061401020a080c031b010608060f01080601030605070512280e 79
    0x5116076210202d5050300319a500e4000201e845058030050107e640b0b0f8650703181206107000d030100010703031020621383c0e0400c2ca440800d20341c520b0030340741c00107800c1c286080e818511000700c03030650003103400280500b8070108002090040004038589176070300c203807207107880d01e6500300d070380ba45032008443e0140101d004440400c4400d40f0a80e9000c900c64050464200d10104000004040e503141d41d00907200a881d000d00102589003100010120b070104034010740c5442d02640303001e80c4542d801010015029034030000100c00100380d039402e8010716400ca204000c1041c0c2460022070325000311005a000300d25014010468840480301d141c00c40205070000e20840c101c44d07a6101c455400500c000015001c1800030304141c019159100b1204803025001042660812270414031b4014010700d04020000341400402c040301c0045100c40c19a1f410440104403645d03014416505881945404201e1743c0114081151130030811b620344030039011214101001f41d000380c8408040e958542d00c2e14001350004c0c2610500c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 194124748 1250 194123498 194123537
    0x3041203091202071707050108061509131b0309020303121b04080703051507050a03020705030f030906061323100f030803180a0c0902030a140901020405040e0d 70
    0x10000410324012800020740e540b980049051070741031402692244409000085d1114085240d400ca120000d000715403030140002d02440001d00407030300888111541980300c2c11000101d4803401009440d070014802c3c1403800030010200607440c090100440c01004a81e00d1003401114a403c3e0018002c5003010043da5282c4101322000d0501d408485040c1c0100c40d07446010400740005000b84c03c0902550781c65820b0444c10480b569607981c29160107101045030b0160010305036800c215891a0068452045d450304a1031446120340442c03824030007004005101e000052640c7c45010241c03a9041005002c100c41c10580d0f10b51500c152402e41b48216081001030910031a5600010b089030440c0308030340d01c090440c500d0496070419101d11000208016600d000602d00050001080d03000700443d003440d80721100fa400d030b1742c051040040d8000000c1000d0f20515000440c4c003a41144c1604914286105440e000b503125100e0140107604114000d54503071400b0038070030000e0009441b011980501c4114004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 194125998 1250 194124748 194124773
    0x8030907050307090e0606090106140a032d0c02070609141507060c0219020102070e070c120e0f0604050f01110f030705060106090e150f04090602120a0509030f0304 72
    0x1509803144203400101541c1c00c1126070001c1c490001e00045090f5240300050034001c005018074041c0c10401c00401c602c0e50302041604030b41e071410021940340c00c1c410208402800744080101032880c59a011410441a10030030248001130ce25003c00000704200703003d1382ca510091040101150f10b040040107045c019840c500080d40d8001d21002e1119a1301c048481150031001041c2c44070369903480032007c0f082e01000402000d050000c5025501c600550000356120118003c0c03074039243c400004100424050481c60000580c0400700d07120002c00c0c9640102007501c0350090f28070440c200071030340c10399041500448007610b40240004440c0e807070040041d18068512900b6018510414808000b80c0078144041c00e4024070502c090001d0f54504200240f01404a400002114040100344440f01074051035221502000342c48020b404100e00d40000c00411000e00082c0c0030500005012404401101c80b1030321840250800308000c0c0c03145081c0541d00d005d90300041100000800104020074100400312 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 194127248 1250 194125998 194126011
    0x6011d0a091d1006031101050301032d05031b01050c04140d0201020a0c0803130501051809090c1201060e0702010e1002070807020a0801020c3327030310050307030c030803 75
    0x40034a0071030842d446203040071511003407180560b6a1070074810001c00d4403a03160100070918101e410743d419900c90000c3c085500c01003441c00554108010010400104101601d68104086c0d948035004070f000002d0600ca040a218480d5182400061115042400307131030a540c1d4101000146408000c140f02d90504640c0040e41544103d031380c20000908140383c901b015129132005540c0b5041e00c0700000f0883c14145d08042d042c0401888804242c90300b0050362a6440012039548565440c0c50341050308041c0b8200100f504440c0d414413118402205400c400c0840d400000c000f51565034044c4200d08a540d01400100e90341c110b050204155052900601040da000e01d00852504009500044403802035601401d05030350081450903c03260248500c40e500500c8405138018a0381341c524000c41f040c010282e01d0760b03107542400407800008140008071300c004244244080040b4440402c0c60b0769030000c036a0030340e182c007262101044034140481e0314011203501c00319002c445410359a511803543c0004084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 194128498 1250 194127248 194127281
    0x41b091514130b0f0d0c020c01080408090a0b0316020f060f0103031409040c031a010e0f010c06110304052b02100b0111060103121101020723030d0c0806011d0a09 71
    0x118005640c103000f0102c1a4081048580d50303213600031170f0001d9903610032401d07055401c14031404510780d801001702c2d540b06038402840c1d0f6030780000600040200055400541c501e000200410820030312074507803028650302c2c9030200c43c18102d58640315552154112b03601c1c0050002c59004000007801100040c42500380000c265003400c11341c1c0045001c4601425814002985034495100f0101c0c196030700f00002c080038a0b1000d1040d031000d010560100256290b40e04001b030720301081d000d00499601211003c44407004a035603904045c1840c90392a00903070707540950380034010b51000f5140015007003c208651940c000d00100c00c503800e12075005001c1911102d051202e01003045d58840c000380035042c061485900070441c078590300c40700100202080c19409055a20400251012954005940f104d03c0350400421814025980031182540244000d4121f418141700c03000c05400e4110352500c0c0310301401c1e81c6540599413803817081807161000710202900015450014060420745030005003181002e03411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 194129748 1250 194128498 194128537
    0x111c0c090b0f0d02010305181c1119080306040906050108010608060609090d080402120d111b0a052b0605040203060705070317040314040b0d0605090106051209010b041b091514 77
    0x1c2c02800c050082d03e000e000c480410074409c0109400c000115503038426003008040c0d040304060800351040d40c03d400502a60004000910596695007008841d16406038041c0840c0d40c2d80e50900740038120034003403ca01402840300142076802e080001c60b1082c5044402420081d1000b94292120720f170142050b40c00402d000000380d10088100b02c0b81010359229270300c0880b140717007802d6424105110b680c20050f68140031003071248290344015a01c0141e400407180d90002600b40c0045080c13003140c042c61551b0b100c0c81c0003c20030500000c2d0340030512803130080d0f0580305075035103002d0115140d2092090042c0411044000310ba0003074944020264003620904000b0044e800403101c1c0207058225900001949ca00040d400e01c40c0c918501502004000c20b0310343c02038a50512030068840d014001405003034600c0407000826100d0f0035004083c1100003e0401c1103140020176130710b60105403503040800814100c0d080003075012852031500e131a003075960780c88000c1c403441c40003091030a1744209010b070940d000580 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 194130998 1250 194129748 194129791
    0x6220b030102190c050f0304080a110f030106080a03081003120503070c080409091401050f1602030d18230d0518100c1518111c0c090b0f0d02010305 65
    0x4505600c20750144c9440d010f289007860002d29102c0d880364510865042400200480400010003a0f0102c2c0e06c00d114083ca10301c0600800e43c2d005503020000d5066081400c0000c00110206414004078003980d101c000981c0c2d01401d15030385903000d2000408050002c005404814401ca01440c2c0110203403428180c4503038283c5032909181c0181e0050808141e0fa04022010410081d40c1c00c1c0e040900c0500a020780e2a205908410104004003206610280700801582c114030030303c1204d01c50090200108284e00842d00032085207103400c03208581070056810700c00040d00201100e11400f40d500001024502d00115040340c8980001002c00c40c041031210704007001e5a540c40f1074802c400886d0f40c40c029030b0240303810440701820200c0c990f021940e01d03050b02d20b443c41001c9500511800c0d00110b00c0002c101410380440c00003220841c862010303810000c20741d0b0401024900d00c4044400605050041850700b4041040500b023100e180c540c0041c14800c0c04006502071b41280740c0c07080036141d07407615200208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 194132248 1250 194130998 194131027
    0x60f09111209060106020c030a12030e03040b0304050709060b09090601030b060d0f020304031e020c010c020604030b10090b0109081509030909040303020c2e0e0304081b0906220b030102 81
    0x9a030400e03583c1d00b10700018000c443d4100a0f0200300b180403801094130144a46400042d240324104410800d900c602c400c4507400c0007001154002e20030711401d140d0740d2409080c42e5032542c4960040b0300c3c07c1c600744280016000d0002055074210b030001007500301c1580300d00005400801a914126400103010701850007090707800d00c0744107401300074010b0150b6203182c030346401062854a880c54207010003100000b443c10581c00201d801e60b1010a08116524405030f0000600318082c503407004160036000d000f04103281d04000b1440d400c0395020a018461121240010b48405113580560040c0740d0080004640b46480002141e800c803080d10181c030715045100c1d003c202092030840e010307004250005403038403e08000b008582c01a10000700d8844001d4200062164281c2d028407250b400107884d441e40030384ea40002c1c000c03240100640000c50720804d800d5882c0d400304000c6812003501c980e080c000003658030304101800e01019604c01800076041c50030180e02c040100440c02030b0039010344d03090114403001000d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 194133498 1250 194132248 194132251
    0xb0301150f080601061106010b090415060e0a052403060409062301210212011b021e010506010903080d0f0204090f05090f0606100c0c03060501080709060f091112 71
    0x101d20820400d0a0400c000d2a10106038840c0b0304003e00a43c0500290070041550b6054600000f030855507440c2450026000e446030030a0420101803034140098041d4225107440c010800641d111148a581c4038100041d11941445084203d408100c2c8180454400c0f030045500c0040100b00140d440b8041d00d52030f0071501e40c1d030050007403603030b5596100703080c42c2e142d100450040100c43c0c04212034403096000e196048441c200002e008210410356101107800c00c3d045011000c400c08060180840000d00003545c40000c1c5514030f00086c0d114180700c16403801802403a1007880c0c180c494200007860b56803044542d5025550040c4095a00d2602100c85503490000308014410414085010610052514200d9030007401c90040da510105031106484004580a41e21032000c881030700d41103418803025134503542d10300c00c021718a10b408500402004030381d17808a81602c90741d208845107540c485e10f44404603a07441c0219441004008401c0148c4e0074250040c2c61a104100211400d0100184841100540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 194134748 1250 194133498 194133509
    0xc013e0604051e01020702030a02100c0f030302030117030301031e03050f0307020a11120607083423031303030f150819030e06092101060303020c06090102060a0b030115 74
    0x100f480081159500c0c0030001410b4200c0b200214031b42403603540001e5071101d84003c001d00402000d09424843d5000d0b420300304602e900006841d0304800329181c001c0082d403090042ca0320341c88400100400319a400426241070b60f07880b5950409203d803000300440e01070118242101000380400000c40c00b8601c42c800b1b50b004070300705d070000e1008000500d0f2801c00c08c0740c5007071501d01940041d0746041c4005800941150410400d0410000380d440f6220307003401640340d540300d1016003050341108000b800b02c005808000100255030b90244c1c15407441950903102d600403110200340100f40b0100760000344120310007900b6442801c00180282030508074000340c544500310801c01001009082001c48802d10200006110025881d180c0402565000d0b00d01c80016a00380e000d064049121030031501e488043c04804811034820340503070321000103400e02800ba00c0c0000c07001030080381044034203400c0c50001c2c2c40d070000c0143c01401c400c1d6940b807041c80080241a401c00c1d4559210358011403252150400b0001908 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 194135998 1250 194134748 194134753
    0x50319020616110a0501030509060a051005060a21020304020907110712050c01030507230c0f06010b1309090308061215070f1404030f021201091b080c013e060405 71
    0x8459040201204c3d41d40c0c40306040c541407508100c8000004142d00d03502c209040400a21622071240c0320b00d004ca4950009500101d00241103203085800054900c80c20380d005429800c0207103042c000b1020ba0205550007500890707000d0115294a000f040310001d0304603a02c084460880c2c0d80d1600c4010911811002e4680750090844060a96414000d250f40684a4204456400400031032a21000c0405511400102000c60030864070300050000e0049a6951702c00c903556561280c1441895034401030313144c6001c409040002400e010180a0f02c0c00d555055245c03c44155a400c0a1002040d204043c0d1409802003050050207800f009070164052045541c4014840d813000901411b244008890904581c00911007040010400c4a001d072415038152114080318000134200c1e80500000d40d8010a241840c0700000ca40385a0a810710341200d01c00402c507035505002000549914901e401030710055a400102e99455140c0311001480c07800000000100b00701c101c480300f5040240a4400b00c6564 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 194137248 1250 194135998 194136023
    0x120a0603030201140609070c0c030822060f0806040b0607060504051c0903080d110409020403060209040b0906010c0b070c08030a0b010f0f05040e06010c061d0610050319020616 77
    0x41d03091083d41300614011505407141d04100c40010860000100311000f0003030020f02075010007020342c1241c0011940003401548070720b00140701900164020099641042000760002103d900c2151006840851a112001c0341d4a840050202800d100ca078501c4d0020000c0055100044091003a01d1017140900c020300044040701c41035042c20560f190303045080240c40c01052010a0f410011a0295504c0c01310008a0706586914400607009035404840d0303082c8003190001c1030000c00c0d0010201150103c60400010440d03904101850340241c910f0390002d00d810031000d00003840109116004101c2d41003c0582082968814510354400ca805811150b15030105580558028a41020b40107281c10103d091204104004040340201d12941d10580d440c1c6011411030390103840000c01c4183c0040081c0071811004d51481091080146c800b0715510803800000c400c2d5100781222015508018085d248501303150641e50391650580b0400e0381e110404100750820340000e40c000195a070f205025940d040d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 194138498 1250 194137248 194137253
    0x15010902030a02070f030c02040e0c09130309030219030c15020316170a1718030f073e01020d17090115080f120306010f1d0a0603020d0605190302090408120a0603 71
    0x250b0741444802c130712b6079100c6400f1002a65806040d641d00005640025050080740e08044681d2000b950000e07401895500d2103940e1042941c1484040d0703802100006051507481d5655a840520b0030468001a0018004034248281d400301c80c03000301d40501c160801c0107699001c641c1c2254440440c881c00709001010007002c3c401c600c0800c503400082c0c030f04030380101e01c01c01003041c1d100d1040184401e000540041c1c0d101c100900f580c9410195205200007c801d00f480b18600c0000e0901c01200480244008590001a6100150240c1d918041e030380c648050312800c004040c202540600300c0741e500d5403250700c1c441c000300180c2103500017004042d00030702081508041c15402c0c05240d010b580714880d420410001b032640c000078003c103244400e2070702e040b00060f02e03141d0042072204003104992129022400040141d410780180c1460001c880c42000030700d036254100451412a000010703518010013108002500c0c0480700b8651080c000c044051a101100302c0201e05128100d0b84e580d111643c544046c0f06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 194139748 1250 194138498 194138501
    0x1902030c0a1407113105090c030a033c1707020601031e02040b090406021312051e1e0a03080601030504050a1104021210050f010215010902030a02070f030c0204 70
    0x1000307007440302e20518021844e22040c00c09450f00c02c0a50080c2001d0174501d00c003d0411102e401500d80b100255158a000c0840c494041c1c002610b18a00d244108901c2c40c8461601003121916198941c4940c800740040800325610f4141d40110b00c10132413086001741c4003004c000150511103401c1c43c3e440b04060000c7c202d942001d681d02030b00710000c65001d80018400a603000003011030118003280e0341401c0300014030005010300074600d01c15810a291000b80001c00c141031f0003810780804182d078804003454407400c04840442c8079420190403544014014240c01261124441e0f000710314000366400c0e410548044a83d607007501003070440ca940483c1089090550019261b80c01030300900c0d0a000030305040d201d8070b80e103144203100034002c9007110070552529552a81201d03080120004840242d2401e0260061741040600c142401509010301051aa41c80400c2210001102c040790800c1c80e42440c540b14000d40008100c07426540e4208410741c042241000034444080c40f9654181410b50144140b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 194140998 1250 194139748 194139767
    0x720060610080c0403060207080c0a0b0a05060102030a0c061a0a080f0705011d040506130f14090a0507090e0a0c08010e070f0f0536071106060a05091902030c0a 70
    0x2049040028842007242e850104d40c2100e0b0048800341e00c40e4101c1c20401e09600c1104410051031142450306000c12068503941440348041803402c005580d944001a0b03102e100c0d10512000182c004401c1c1c01c00030300b241c0e0004c0000c85007001c0920200a520000c224504002d03007000220750b000c200c1c14141c0080801060300078103401e290021680d601003005c00700c10015040c0c4203104903241c0c40090300a03220185501441000c602062188650410b100342c020000c9e131a490310714032010fa0001d0180800001d0a545042d841801801e0072440c01c155034008240920401410703001e884c03105800b0034802849200588403400c0001540e00c04046c1c610703e0311080c0c3c1c0c404c01c0408108282084211881d81000d000c807501640c07115694090a413100707250710f03c040e652861061400280d0300c1000541541144a544c55445681070061885a0b241e40c0c1c1d41c0031600035134032510a0350284000d042607003240b60460840034200400040c660b52042c246d070812101140011004240003100d41c0e448078480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 194142248 1250 194140998 194141029
    0x61e0e01180f0302010b100518040c08011205491413050a0603050105031002040b04050607020301020904091b061d01030e0f06090a02040609020a0e010807200606 71
    0x200414611040c801d010588105000b82080c11414a110140741c000c3d0001e13448030400501e181c030582d55025010b000390b00302c074413210500820b05040103020700b0117104208034099592502c00b102e03071030b085180c440c00c10258030440b22400f400492044901050440c162540c40c000c62105001116004582d101021100b60011551600c054903a40d41d8000d18031100034104840d14950f0758000115181ca202c080e40e21168100020000c0020b0042c1d2582c0700605880044043d2003892044000d080168002c40c0500c0c090000208410007052500c04001c2c05100d1020b000541084901e0300054101c41c0e0440c000e0310741d48640e40d9080e64546407a0900300141100c1c0c140410201f0700680f64408c56110850b146062541d2915030a41207801006450103900500d022034015142c4130040684660001100b240100d081c050041800c107014000d0720b0b4200d40701d41e1880500201c0000455911002034202824012828032450300004105a0000505844d40062040c0c3c18060184200780854002c107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 194143498 1250 194142248 194142251
    0x5040b1b0702090601200604050607030501050108042a0302091303020d0c030203030f04050a0503031e0105060910030902012a0212010903020601121704090c0f0302030105030307020418061e0e01 85
    0x43e41e40ca8007403600900d0a10708031003203e1a0300c00c0c05422140707050100d0b003a4070541d8100410404002400b512580140d40d042c046a43c1e2800107460000c0299001020902c1020103040c145080c0304100500070180c10000290984d00c0c0c02054413404141c0c1c00b030442c01d99a0384c1500506404100c80400c02d03e40e440c103070b4403c80f5130303490003134aa0101603c036862902e5030502041c1445410424100465001800e0702e5030b070704148130510361049110209810207000e61000046500e400c0040da200001c010f4240400c041194100b04d0007021200350407030521414020030740081003140490a4815054280300d15520800e00400c8011407500314606038030307810000f440e00041d03400311f4028115121100075003480d40701c0d1300d05000c80319104d00c04000d047d48085000035111485403c4055070903403984811081d074040600c2182a48024080e2980680c0200914401800e01d640445803c00411241240c02c01719661100181e8401d1100d44d44410070b1203020410401051242001d00c845a000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 194144748 1250 194143498 194143507
    0x3060506090a0902070c05180f0601170a050711070603090515091203220b06010e0d050706052505010213140f060304060b030d021c03180f020303040905040b1b 70
    0x801d00c8186004000d0f00a0700802d0b03800410107104400005440d004009440074807129100303052108080b50007095158245000c02d03d42d5010308400b07a0840c5109140340e0f03e66032040140006890060541c10410081d424800c112880c00d10152000c3e28907944c010881c00c002d4105545800340c03100c841e180e000310b44c00034041c0b01c400002d145138100456202c03182d12aa54100818a251601c842e04440c50401d80d801400704124521078911440003601d9814150b000513061050303180c041d24004249a01031003052080c0c9005401030810020346100d150701d032070802c5003110b126000d00c01044803941e402141c0540550078030041400980441c503002003103070f01074200240b00c5c00d014407142c0d03010b610b0001c08030342809425040090000340140c100e403040d001c2010002c3d0b6a0303441007000310f40540c0388104c461600d4401d0142000441d56500c1030000803601e600c43c1c080ca038140d1142240d061104100000e078050123801100d2103140140301c2401907140044224100901c410b00d50000e0150411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 194145998 1250 194144748 194144767
    0xc0c2601020414012109050601031202010911041a03100b010809030a080c0307170f15010e150901090f0b040302040b04051303081b0f090a0f080601030803040501110301080d03060506 80
    0x8031550b070000c0c3c24030741103031031040402c4805955196a08001042e5080580c04000d000700080d020f81201e210300315510018100400880c03c03500f40c0c46d401020002100000c0d0350528180e080300e42c40e03004594651040190440c006890b1007104041d24482c5a16421a51501e42e00310f0480c81c1d02c480c110018510b0260380180003401c918004100c44144a400b10206000a125034000000c001510403985e080303060160f1b428026600c01c81e01142126982d51061000d0352040d4900030b07180e80050052505004102c100300c040d038204e4440a810803504020008030186010840d100800030001c42a81c2e513821401444255403a52051038000c50900e0180000c03002120641138030f07582c0502c1c1c01a41900c070726404240d600b66910150b91141c4010803080c01c0a07400e48014214030300105c0d0000150b0760740c1d028042c00710b80c4e244110305050300060010404520280010f50f4042e1060300005001d8050101040d13042c0c2082e00190400d6005441e0b000300d6070b403d0f1003201c0140508660280c00c00b078501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 194147248 1250 194145998 194146019
    0x1507020a060f0903020d03050306090106110d080a0902030109141005010b0405100e060307050d06080105010e0c0a031415010f02060f0a0f060506030a090c0e0402010e040b010c0c26010204 82
    0x10701c20032040200250560708501d1003072402c41c0107554010103c0500d404035090051542d001540e4640c46480d1120000444074010410003901c0f0400f43c1c0035042a0b100b00c0d80c00d0f509503800610008400e030f210007103800103036401e10903010150f110314009640706100b45626403500c102d2000b01c0703607107618100061104415080c1900c08440007207407100f08071221450119100d030300c1720075143c2d0002e2022081c003131a283c000380a000003507410102084519595113031282a0b45c1f080c032400031620700c000085100440d82c2001041003051508001c81d5408510041235150501250100900a04034803500b510b0740c3d0040810340300d1140e910040c841420040410880c02e4400741c00429510341c2c805519940000c2c0343c2040303006200040405840f0b18044410f14003800d152002140c0c0b1b55110384c00820308604205070380340140d0701030b50303550950030039101070100030f0902503042ca040c042c18125400c0014280000480a0121450007220020901000c00b54061035078010740d60380c2c0d005100078800081e03c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 194148498 1250 194147248 194147269
    0x30115020f0c09041103011b023318030705010618050f010b1b0709090218040809040b04021b0a050706030e101d07080102090f041103060f01031b0c02150702 69
    0x303c0e0701d007080c0e032074914141c0c28000d000705000d074055080c040744210500709003c01d030490207501e40039074030145003000c030141c0b0440022946001220b0a1032107a104515840840c0d035001107030001400740b0f0070348112082d1964000032012100d681d11288180b2000c000c5050760004505090024081403c0084c400250181c0c140200004131a01060b4250319108000c103401040c0c40410503507210f582c8407002800170303100000c002e9020b40a01c446d5800c0c212259540d19108e250002605401d0240070360400c0007612502c080e40798026000d00401118401c002c010015032810b80008100300156850311904042c101c0d4403c07421b041c900b0544170100003001c500408a912000380002c1d030301e1203200c1510140900c40d600d07041075114250004c1010b00055005010083c0300b1142812111083e50411007951280000040c600d0014404100c0604086441d061140014180402c8025040044000951008159500241401c043d210541c00c2501080c0e040784400c03610035181c62079540201c7c0b600c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 194149748 1250 194148498 194148523
    0x5060a0f03120f18060c05190819021c05120108071512020c1c0914010507030e03070519050901091a0108091501030c060e0a03170a090b0708030115020f 67
    0x4111403c144030030302c00e48200c1d03405244c100741d41041c02d803941402058420310701c0c1d040300c807846a03220001c083c08424400509550b80041c0140c0f40001c2e030b000a40c1151401071f010400d500c201858280088614140c001c0c002e0700c0c2d81e550644842403000ca00b801d288041e800300c00a42c100f1030040c010442d803544d080420103218104484200d404400200092181000c51a12400b0350065078000080c40b580d1074042c000710ba5614040c0c5501e038080c00300a40354042000e40492002c2000e02c0003c2e01031809550234490040640c1c101c1541d5a001c1384034000b8418003880200c0e05010b003408113240c804200c0b8003600402030200510700800340130502c070012207200d0034140701d81100020a150750400c0030035074000402c2d80a0707144d13580d289450040803a043c01030b42c0c04100b044840f0251418070740d220104482d045100310030620300c00c00c00042c0310750000400d1010080310010201d580c505001c0200000c83c441c09460743c0d203614144402c05c000c61040e05280441d0007403190f035181c0000000c0c02051011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 194150998 1250 194149748 194149757
    0x80f090d0206041415090306043801050103060807080c0d0c03080408060a060512060115090f0b09100206010e0c030a0b09100807120b0c090d140105060a0f0312 70
    0x8914000a01041941900070740c0607100160101d48014400040040203c0544003030403a4460310300307001c1c0caa000f200f8049416a10220006004c00d1114101341101300d040740b49500c542c056041d50b039094403001c080341007150802c6001000301d0350345840f80c14001c20401c0050200e642c101710310941c5841c3c0c0b5014080c46021010840e0003802392091011000719031180880d82d03216940c034099078840f40215041c1442a1411f40d002882e03043c1015260f0344a40d0340c2c0003401280e03081c0300c1c0c40354601e0035160280c1c0400140c03001c0441c01940d040d40240c0030b0320500518a1710b0f24140c1003044606040410040300715042a8010041440700c0c03101144c00015041140d03440c2d60799242c0c9040280080905e551b44110644107000e8039402c051028000e0310b800800ba280301c10f442d581100c0042c000200000e105102400000340d4040c1d5400151a140100401045240007161154840d103c50514014a165903400601c95a032410b21420f00c01842902c5002c8031151954540c201805a002011000d10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 194152248 1250 194150998 194151007
    0x51c03120e070b1306140301080c1003021303050604060501090212010b070201140a03150602030c0a080705070503070807060f09030c09090c0302151308011a22050f0919080f 76
    0x700d00707120035005040c41ca800742d0f40742c0c040024540c01c09501c03841514041007030340241e080045210400c0728141c9a401005000f403d415000f0b1106132415865030130300b0550b091002c18101c817021094180118040c1c0020940c07030916080c01d0381105e0060f40040d03056441004074604500f1048443e904451421560320345442d614001a66035a100e03d0740b4013901721001901142c1c5c0d60f0154031503940c5020510a2140312900c9034010783c0d4a200c1d03048070307115580c08080c6844c00152f1000041c003030680f0231403e44e54425600c0000c01c0c649005600010481d40101e0818403442d90322100054155045203000c410300c0749581c0314805841058000c00e80a40d44a105071410300511040240045a0203402502d40c6032000810b072800790044102d0714145600d1703e600048200381401481b4030b070b81c82020010f0207102c4100820902c007070050050f18042030b0000d10070b40768179050b05c074551042e02c420312900d109180c8030822505103c3c00002c40c0e1440024101c04901203100d01b070507103403e01c1002d17101e2980e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 194153498 1250 194152248 194152271
    0x5071b0503040f090501060f21020d0f33060507030f02190804060f140f090a0e0408040603140f041103010908041502060609040b0601031a1306051c0312 67
    0x2140305981118803c141030b180f00050550741588118100c840d265512020040c21103c00c80e03d16000000798100e0752000c07110014140d0140d4010030b5030315882c5200080d20a10f1000c120190303035a0600240e9038000900c81c4010b641c074043c000050120b80c0c0060705100d9420200060a5400360408c00340802c14030f003035030301181030081040701000e40c109440000701040514085415500601441c0c0000f0701a15a11845502070014098200c00d04080300e41015185100704a5075080b6100351a8090460000041c084110350949409a4002c08915981c1e41c20700d000582915080381c49370000068020800c1240c42d248031204d9000399000c4003000521080c400001d001d820851406804d010f00090005a60b11440d0142031b1850950303020350324a43c3d00d1030100700c089031044078041d20381da0009000414030341c800e82c88064041642c0d100341019041031740c04504007002c1480e1081d01a50790300c3c0c00b40104c0c80d0880e041e000c3c0c815241c0320005110003a40d00281450b1700007081c25101130302d50303021404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 194154748 1250 194153498 194153503
    0x90c0a090209044b090516060f050318030403080318010506010914040b0301060803130801050108010905030f070318030803060909011104050d020a030605240d020a0e07200a0201030e0105071b05 85
    0xb848000f148188207001e00350602170345918507014528885945180000f41e40c50040d045180e070390340d40d5142d082c1142d035010b000461144d000f203304040f50004020100004a10001a40c01410818070024500d021603d0300d030b003140c50140001c0d040c861091003c2000705540b2902020800041e2008a441e6920300c2c0440d014210a8000e51510b0001141248500c1581c00e10310048800d0740d0000d1190366a100341d0107088070182c0402401c80d420401840d10100c07075400080c69403034481d25048510000d04030a01e030000c0401c0e04211000f800000605c00700d85040f608440d00b1150703820081042d03002411181c6041d10403485500d0045101c2442002950344900c4c0c036070300030740d00201c051050303103004600c3c2904512004040c0030704031240c1801c40394a0400d0703a0012101540030304501d811904110780c801c041341c1e00030080d404102040e072a103103002d264417069580000156000b80801c031315502c0050242d800c80d04503d03400307070b140404101c94198090a0146c461011190010000c501414203e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 194155998 1250 194154748 194154881
    0x807021e0a060c02010314090a03080c0d05070908150105130e0c09040f05060c0f0d18060e030c010624031d0a120806010c1703090c0a09020904 63
    0x2a407007520803200194082e040109500e034503200341ea0400c0107044c207440003010b000703050b100c3d009a41c2c04001800c0000e8011000c02d600104060b00107402d002a68886800b612422075a080008a6a00c01080104800c12069071070314154101200c0329810a0045903042c0c1200c0e100a030029151003101d02100000e018465002c0c40150858602c0e00d0030341881c0700a0b0480010440703842c0700b10350015401d2003002d41030310354199650249514120507401a440a031030315070080044084902144c20000f4000c0c89030211281d91711018540340c0a040b90074038211560f035841400d10040745c0980c580d00440c1e80301c210000581ea810000740031003c1c2c0c5542c14840e00c100c418240c0d140702c0e2000b503009108454000c05180d4001c0d5842249958610004403945a80100e00400c0c80e08040b41c0c200c2c0e1500002c002d581c5c881180b00403901c2852600c000100000e010340e000b00001540007038025105d0038240921004a0014500c0329074004034031031000f81072201c00f401407140d004131081c01c0807034207204040d54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 194157248 1250 194155998 194156059
    0x509040c1e0911030f0c302a0304020103050714031306110901020705060c0a0c0e010f0504140a090206091302090a090605130903090b0304210e01020a0f0503390109080702 75
    0xc101100c047c207080f14a120040ea07104c1c0c400080e0a12040c0e500079011900b07000d01e483c14501c1411619150f00650140c003000d0442c0c0d05201103d080320074040d03d008007452007902d20314030794542c40c60743d41051803c0303031615018210030039001c01080c0180d98001910340d0848209840721991601800042d40c20300d0060316000b07018001003240022054207589085040c1e4410344104044580d48104003c11165402c1c02226803450310400603215012680c4180300301400601503a04d00f807525000506031100316407020100d2580812503070702c0c40c2422845000a0004a0b204108a0f414000061441d4400c5d482d01640203844291240401d4410024100100307405441c1684905207481e04030b8486070b030b0152164405041c0e18a41018a1184502840c841411b8010340805406070301ca10f21540e8182c8d5040d112817108115400c109c10301854004003421107c01d600e2007090126904000c40d44850700b000403a603040218000104009800300e51240e9411103080e00031020715040001d000360014000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 194158498 1250 194157248 194157307
    0x4030b09281203023f0901090b010f050102060c030a0204050604061205060a0e01120302010e0f07050a06030606050901081f080120040b040509040c1e0911030f0c 71
    0xc00461159040c520054032403008a482590062002c4049025811840b4400700c9892440800001041035421705203064504000302c5600001482820810641b1460031581d5990341e07200072320030b5903001180074043c0402d20512103880e10300002d61301e44010301041900d42c1c0000100d400300711b45034100d40040038040c10041c2c031103582d84005403a01f80c0040031003c0460600300005e401e0314100e850841501c42c0304134440702990030075070600d100c1303c1c0c0d44d0022001d6660342d20502400e5402042510022003185004090007420002403004100155002005150a101050100a13005015211016400c2c13814211581d119074001c42d0a0014100b515043c80102078040307a14941034000f80082c1c0d14681c203417403c1021212417411144514410103801d614144001e00072460440c800c503070040d01900c0450b80c0c51352948803401e00d91810003181640c410090004120508403801080210048880307440e0a51074030280d0070614082c01004400c0c01c403000211410aa00c4007200d520065001204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 194159748 1250 194158498 194158543
    0xf03010e1b010c120201050712020307120c030204030f080c07171b0f0d1a07090f03060207021908060405060a0603330c030e0c0d0302030a0e0315090102030f090705010504030b09 78
    0x2034007c200944012001032034247d40f441301032545000b164001e412981e42d8002191800d03092070000c01e0a0004501015020031000000c81c4010314450320b40c5002c0c65885560b51022121145448000d5110450304480750405a0341500302003590ba84c030781c100010341d0014891000c00103850140d1030001c01c4d4807007000000310b000d01260000b40413162100591100c0d01ea1a1407406507800201c9114a1883c140c0241c0240f0000344130b80c005c1c01140c0d101500a0902690707410742c41c210444c0c1500a2607803544408100800d0100030414103800840c0180b0822215003151241c01d030300400f50380807040300820220451010f42142000300720380300700d02e101080007555456005004c0c0105103656916403050303940104003803400029a01000354540c00035490881103160664060005000090340b5025940344c41c0e0924907403000d83ca1140c00b86000059991034541c070030381e840441c0504050f180d07a00103c401d00042c1d0f080001c0354141c1c0d0300503654010a556001c0010b20f000d021034086900c401d01c454 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 194160998 1250 194159748 194159783
    0x121101090905240a08100e010908070807030806011d04020c0f0102270613050d0c0308030c120901090201080703090f1a04150e03030112020f0405070e0f03010e1b010c 73
    0xd9000582002c2c92960160f80032a03c1e08118051200d03014050013a00b02d0081e9a00100680d4002c80740c0c01910400810301d828541c81c0e0304c111b0b810001043e6015040000c2c982c04255000c0c4502d030340b0010074281a003100300c0600420708260200c000560095030700061050342c10b01d0130010401e0000f1110000d542e103080d40c1041c94641046444603001440c21004041c04d18542207082e504d0724074076001007020f002e240108028006964072001e0f2b440c0c449898006c03000c0784001005601c5162803120b990360781d0118050400707884e0030081c00d040e0140d240090401c0180ea000c0030940d0030003224034002c600c000403410003000c25191101c0003441138079001907510b0080d8a14003085e104074090252210000c80c0c05418070266010988c210219810802c0140542030a000340141040e00203001c1404454610700420101c900030b0354860045a8050003540003464100c0310402c804500740c00078004540c031780811566402102030340c808041c2851500540c20f03441168480e80700e94000740c440c400c010300d41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 194162248 1250 194160998 194161021
    0x60f020a1407051206060607030e0a0b04030c140d03170709090212060f010801030c0519031202071404090c120515010315061a0901080907051e0a050109121101090905 73
    0xc0c456140980c46501c2d011108140105d0300c244142c1014100619040c0c00b40c0e012203003a00c1000400d43c2c0311812000200e00000350101401c0503600ca8030600300701504041041c075191014140305c1c2c2c810340c1d202d240000081d80c46090300941402c0d84280c0002502c4202e420346805400f40c02c40c010440c408201c40441200b0070019500404051300c01c10501d549500045825240900014041c4419070104022038188841c1c107102d048034030f81100c41d02c180c40c2d5403200b18041080820a005038805041800860b04030b003584d9802d80000c03102049119001d9607040f20b032204070b2003030090500246c84940d0502205100c512150441035840304190745e124075005500891039481514a2881d0030300216184005c078640001c120314101000c2d040240b00c0b0011600602e004000c1e0103030307024000c800520340c2c42d0680c019401c94400e8140b0b07160391480d4000d000c000c01091740b03c0d0b4100005010308010380c2c0710403d9aa05d52681185001800b150341c080165100600c990100344d0780b91601c000c102102c11407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 194163498 1250 194162248 194162263
    0x28050603010b060c0313050103060e0f090c0a0e15010519030518060c0403110307120605090c120c01170112020d030e0d20181305120a0203030702060916060f020a14 72
    0x1c1c103400b06c07a003a111401101210464050b1031041500900070a040c03180b80c0401a502040300400c6956000100c40415041d031101d501480d03c1503031401c00e20020300d40c04070b03041c0d600c400207103000c81c1045182180c0c507070101c81c0a904c2c4010b16a8400115880000c8050400780190401e82100c10604205441a0f07895100e03101c1540c1c10414459920000e24010509100700c45143c403d041007400301c0c2d01d40e80e00801c40179021448034031804454655544507204580003404060010f071054080300d0b40007602481206a40f202c020010100500074001d104201100064040e9060001c413204c900c3d041d80c2d80700b9110b21440c1e02403030300d05241080041d140c50822041d41c0351007010303910103a0b81003440f900154038111205840007110024130201d8019814405c154026011030740d110700d21044503d101c0d80b0650651005030000410000304a404018140c0c22480f228000c0042ca401040300c01c9045506010700d004016601d030800c10518400c0101c1d0300e02c81d030024003008400311403411169a8400d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 194164748 1250 194163498 194163517
    0x20f0601030318330302130305010605010e01030b24040e0f0121120810050a1e0f081c03020903030a0906030b0d08090415030f0302010b040528050603010b060c03 71
    0x41d03c900030484400c4e003461400e10313142d0704885660707410080707201d00c01822410760010101035007804851119201c0f40d400400442c0202c000003802d03414080018075162084500b01d05060500c6403018003905d400300c804417000d07440e0f4404001c4a481c038816800324420f690184544010040c140300101c0303507200d0000d0488041c1c0c201e84019a1040c024051940003034003016103081d1000f000440b40c18041c0711100d0b4485400f40038003100d6a2100c00003581100340b0780000750303104c82d83e01d82c001d00403c401190601820303c24003014419490701c0145c0b81d0703502101510400d000310340300314040c7c1c5602a0b01564140d22004064907154000b00c20f0003010700c20544146c0740001c0c10650100300360705101f40b18030381070350708201e28a260000e06400c0c070000c0d1204404581546240303034400400b00d012656207800c00c0c0c0c4240d00218a40620404010584d00007400c01b079564515110040a82200000d80703403082c032040600494150349480000c0c0c014416560280d81140300054521003104010008000008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 194165998 1250 194164748 194164787
    0xa0306060e01090507020319050c010c02031c020c030a050904060909150c0504050d08090d0c030c03050c01170a050a06030b10091a03030f13030602070809090f2203020f06010303 78
    0x3c0c1d0714007000041e900141c407020701580003000521410411400f111030702d0321013402c266203045241030b042c2c0d085550603408180107805c040f1b20062811044100700e5080c0351115401e504000c001844281c59106001c050001c5c010001048141c0c0e44940c0c01c0000100701700f4904000020107810305482c822884e149181d4011b103000319202c05603018030305440070f840e0003908800c041041d503562200150304c100d807883c0c2c0c001c01800f65540000c1130f0303098203005144940c001c0c0781c9140c0f0310b01d0080c1c80c00c05407104403414021500040100300c0d40101c440c03035001d441c0c40310100300e0f516035007100e0000b451250405490100804100890000d0b5228210101ca5403120104140d01c2c4800d80d5495681d5011700c036540c960070800100c440b000011020300080c0d481440b81c0c050499aa0740c594042764410310080761403030b0020809034170030316144507116444030b030b035007601e9449103007000043c1c029075102e02c1e09440b0800030361304034000d1500c200300c00b000c03590303c0d00c04540040d6181c0c1005040418401900c00044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 194167248 1250 194165998 194166001
    0xb030d0e0103050702012c0a060c0c0507080102040b030c0714061503070e06090127050106090302010e0603130224030406050f01050d0c090c03020906122a030a0f0b0a0306060e 77
    0xa02c144111003035a442c0b080003007949070220700401f03461413050316802c0291040e428171b0b501042c607074071440c15911100e448588213420185405400c1290b141d000748100e0344180400c010105100c030480e0b0380320701e1082c4c1080d6075201501d8100080e100c0c042003a003251085608101d004860709125041c202000c90455102c1e42ea0b40b84100b40b1a001140c0c500e800080800c01040020342c80744140818805000114110f14540507484080703270801d0380303c0d8000034a0701c2010801c0d035800c06c8600d9007804099030214134500d8021402a65030384c010f40001e000700c0d001642c03056a0610f0302c8401107070880380e130110b079900c1c01d10f801e08c0000b400c01070b00c8112600d040c50000246628012034901845ca03072002d5410141894140b804006054407100300c4203058007004100042d982d6680240b00c00090403200b0402800c0060990b000700d906413140410100c2d88040316240d05c0c0c0700c6802e6035480680c0c0800401d0201990311954068864010303100d421100c40c0c803021040101541100080e102e0090070710596 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 194168498 1250 194167248 194167261
    0x4020d0f2301090507050603040620271c0201050f070f05011406010206240a0810050f0c0d0f020d05010803070b15010903030c0309030c09020c06011406040e0403030b030d0e010305 79
    0x807140e00b141c0c02009075006060800c500c1c00c0031f0000d50fa000340180340001e0604903142c80c0e90300a5101141d044ca80b01e20003d481600c180c1c00c40c404803c42c040210501c0c2c014241500841c2095031121582e080321703103100c84000c0440e0712032421180c0755205018100d4545a443c640011100f1009000b140c107542021404c1803540c0c0300c88480c611501050303005209a4540c01e81403030010740300d055207100f0070280d0307040f2140c1074644119500c018900a4000d00f814482ea1a0200448002501d03070130454010030184040c03a6042002d40e6254610780c40c0000d112080390807080300034400c101d900307507100341080f0000071200f1010002d03141041c05001d01522507a582004510791881c3c6500c200d001c100e001000388042807013981d00c0c43c5401c3c40ba0030100c42c040c1d20713a00d0301c1d0401d8843c3c0d801007884907000140c03940780707200600480e4014101005801141000c90300014407900841c05505a11194540018240b6201740c01611340c02c207005e0305403540c0b9400504020030680d0850501c0c0d012038280000301c0c90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 194169748 1250 194168498 194168501
    0xe031e1e06100b030c0f07200d12050c070807060201061502060f010e0604090f050102041707080604080a09090903081005190302060a0c0506130b0c03100e04020d0f2301 74
    0xb04000009480d00041d04020700c600b1150806030401181030824030002c8200760743c0e03000906c05140a0b8403c2d43d0601000c0c00310000c58000c6402c014001c810030f05100c4000781269010b00f0280155061041d114a040040d00e40b6150b8a940000850b200d039440001d82c0f19011360160050b03d83d03003240b83c40641c0a00c6c0007607958045c01d076a143c290390700303400040000c9100c0e8090580c00c0710780200003260181c640d0710f400344588640b180650b0180d5001600b080020b103103003041a000b030030302d0007e4040989000350721798642800510141c01640006660075426200b10044400750640700070130014100d140c00c000300201d2040b242c04140c05c124480100721807901003043c0c0b407000400750300c0e450f81030f0039a428000701e900110004810310810740e41c9240051414030400d40301c0c0c5810403c01848482a00b0001d19081001d00303090301c50395003041405580b09602d610402076031100a11082c10f40c80314404074810080d603c80113032081390351a03000d204200240a1030800f0358042c107125590340242091850 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 194170998 1250 194169748 194169751
    0x308070f02060a090804090c170603010618050901150602030a09060926120d05040605070c050703170405270106030e0a02010e04060902040e040b0708010e0103030e031e1e06 76
    0xc01507400350340001c903256000e42210008a205001460800d40c0c0d440540041e41c0b085e080c8040426485204400040468002160b003d2001c80017405018034020005840040c41003100b01a2038a890000300300f07007000d41012801c01000450b41c02c1559403a48029104c4d04142c904500060b401c0e44000b4141d0300c68049070040d07840d4034811601c0355410104e6801546114800c004060050700401400340d0700312000f0b410b5030380359a40041a90b20b0729142000440b00c000301040140b01d071122195022942c001103042c1600d1f8040c02e940100654540c0740329245c05240d1082e54000442c603002c0d400300e503d03c4203022401146261090345640c9410056080c0c407035060030001c41d5071140f68098013561007039450301c00581002c0c00004842c2d480d01200ca050340d001e5082141442e01c03070400d0008000c4840a016480101440c0400039541420840011600107201c09410000300e443c0701803042c0e4040c400b628818099604914072b0702600c6407011348840000018040516150301c103460004004203241e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 194172248 1250 194170998 194171027
    0x605090f0703021803011b1202040e16110d03091109090615060405030706020c010207060503040c0506070503090904140d1e0c1a0406140a0c0815030c0a0b030103030807 74
    0x40c005540303000045009400030207070800303100003d80e64045142c4081c0f040d105500c440488203001c02d014040041d2080b5448840190400c2c0b040100308410740181c6400c6410004442d4001d038542e10f150811140c450f08501c1b40300d841e000d40c1403e24840ca0300360780400c842601c05c1070383da8012255203041100014044903100c20300d4101350002680c880030b001a640d0b448000a200b40d050940750b1010a140800c0c0f900300070301503880f00f0000c01030382d80c041020f0001840f0a1038954550314003503840b1003000003148201d5015503804503845040050074403d917507120380d000e4103285440c0713007600345102401e1803018181d0440c0111610b42520307a202d241d450020212183e0344060750800c05500300c8204003401d1054520000d0001001e1501c0d4140100b24007490142c1004507020007607240e00303143c1c1c0f80d001e88a0b8240c0340c038100380c92001c2c0744c01c9160705a000d92010040c10880c40000086402c1c151140b00c0203510094a40c404140300c1803c5000e9410703240a5912500300740d80e035010589495480c203400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 194173498 1250 194172248 194172271
    0xb1608040201050a020a0b0903120c0301030c05010e060424090b0c060f060102071e060f0905011d060f0408060a05160c0b13060f2a0909020708090a0303080a060509 72
    0x80e0265000384010f100d00111441151519511344c2c86600c6044000d1399031100075000020030200883e400c84a440d002500d5001c8140f80d0352542d170382e0300fa414015101d02418000307020002e203526901d030782c07e5a0080004042c41404d203600440c6c1d040c0c00082c4000c009000c0380301d144011803964a101d00352825070801000410468403541404561680d008116074118443c8000100c0c0000892409041c00c445096800700b80d070781454070150010099102d003208020042400b00b01c203a07030105c04641061748240200d042a081030010031658494070700784040da0f070400a40061890000240389200e001500380400164580c1c26102c1c0403004c4902200b13000031f03200410440400d21212103150040700b5180f0760307807034a540c0d0790303901c002d41c0c02920100c0202e96440112180d095803d00a100c4c20304445c8810140a00041601401c901414090540826804075580003013003000000c03600e041d00018502c04001e1b42d0b07071800030515141181e100720668104040003070141400c2d0803c0c0d02801d08402c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 194174748 1250 194173498 194173501
    0x60708090909070b27100810060503060a06120e1c020c040510030311030c1b03060a0501060206070c02040603080c0a020109080102032206020d09080904140c0a140d0203130b1608 78
    0xf1002e034903401c00c0c00d0401d441d400072001070103199030b11356026111b28155240d8880d01e2500c0e0500b41c2041500c1e901c400c040c40010820800c0d40d40c0ca03000b0090580b100d070304101e050440100c0c082802410300c6185000e044c0b2480440c1e21052980c94040c2080003042e608880c480c40c4280c0c10300040e076901b03482c01a4011901d003024000680580d40f4078108041000c1201e040c01c01100b2078034504102c0004c21954004501c402c45a02e048c1405410703800074030100140959490204000e6448030001d00000800c04110091021513845412400080d80c0281c4c6542c3c4400300d64032916214950341c40100c0c04900e101e1700c0019402010f0007a28817410320f040c0c3c1e50000d04110b010200e1460203e50085610950030801d1028540582c03003070030703e040e004041003603c4000c1c50080c04100c520903400e06004d02d807044100150080d500c42225590000c9141c11138905000d0340700307a11140100003440f2541030000c020031140030304200c00e0400f018061000c603101a125004500d0031081c0251445000509010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 194175998 1250 194174748 194174767
    0x40603020a062610090c17040308150303120603011506050a3e0c0328030302070c0b0a170103032021120108011b03050a0b060708090909070b 62
    0x4802000003c5500c2d0815084900601e9000340140c00c45000782c56040d00c2d08207115014082c820006402c0b92400c020101d07620100141002c1e900040000f07003000101000a404030302c03100300310f90402c0b01c090700b1a911820039203d0004588011074090703000303600e02100304480b00380000c8150119aa1600c8543c82d00c413007544125100410b404c1d0f850000d40c002c69049803064940c8040a5a200b12480141c2d0b9058024030018103062001c11941c1c80703a441003076801c90240390022020f81d000911a9428142111460140d001e40142500075010365611070000803045100d8000380392000640d0380d500c0d03d600079083d00806400c1300303003c0031740050b140440c2c0180b44501041140501200341d03044074280706100030600307032200082644c42d51861000c41d041220740800100f240c05840a48000d0046103000d050117000c0d0812485150101170302c81001c580c041619038480b1400c801c002d00382a50755001750401554079400401460b00a00b2440d001500410022540b11305580d40700745018a4883c00c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 194177248 1250 194175998 194176007
    0x70503011d070e0607080c010c08150103020702040f0c0807140301060516060608010e030406080f13020607080d140702160501080a0207050313090b0a171005090a0f061a040603020a06 80
    0x182844284000100441040d0f41c44c0009400e11500c51070700c0c0c55640740d00000041c00d541e0b01c0380c03040c014008001d003841031010039580f000c21014400c1c40d00680ba001d942c000600900380061080b50000c0c90032010501640e0312240451049105440d4a024180000480445031000b44100b40000c1d00602240800078441100800301500032000032952684641e102c40c2119110407541a9942c00041d080080c00d070052455540705541e20154103080c038201d400100616280da41c000c1c480c42000504500f0404602c0507110a83c00c0c5060400441140d00022584140161484005445890346860202c802c81c1c402c10140d60703040c0d44054054441004150103074000041c00c031103e000501210440000d20100500240304003200801c2d89600c1000f8440d01c110903821000020046180030090480005074000c101301400600003500d0307503810b9940d401c0c00780c07030703a0000c1c5030b81e100d040071500b4050187c10140d4002071411008500142e083d0800085501c94400290407802c2c148bc10000346004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 194178498 1250 194177248 194177251
    0x30504050a051c1808070303050708040b03070201020301180b101803080d0209010e0d0b060d14030c100b040608071502030c060106020d02010c0c030c06090c0504020a0c0b070503011d 80
    0x2181211411991561481c0c24421035100c05007455101c45800f1000319440b01c0c284500e0085800007040040c201001d0f5511000b0074080079050202c00201d007020049280d080b24000c2c044003501e00e4590805545c0207020303610130f2240401c1042e042d00011103000107442480d15100b1f00400481e1003818048040d0f98100c1d60007502107e00360b03010b10000100e1442d1004044400c40154010f039124030b00d07400074010440403103649001d41c07032400403d0001380341004029000141150055a1300456181c003100042041a506000b400007181181c04440e0004554034405c4001a003400344115140611003202c01e6441000860f6024031820041c40c1c0d242c2c1100e03110b082c0a4410b81c0e180811002815161180a038810001a840200103003100d035820b115288240e0ba0510300f080811945880081541800c03000c00b034034007960303285000100305d5110706480c01084050b00c195161038042c4405030014014503c10340700000a500002c41e002d02c504202e9058840a42141000c3d402c007081c4c0c500001c0c030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 194179748 1250 194178498 194178503
    0xb07050f0702240c0a1407080615030313080a02240909060f0a06080a0606030b010903080a02160b090307080607052703030f0d1401051f020a0f050c1c02010c03030504 73
    0x826489441c031007070088000f0b0000e115020002d0110001610300f504083c401300103680119081160b06005621010278020382000c0760340392892810134888002420b43c0301d4290b88094003250f1202c00a0380e1100411201c000f24000c48a01c0400341c07007000d01008242002a1845a0034420000ba101914049034660781066018000b01c82006095000c1120040c0e113401c0b150110340010100900315a0034001c01020300403614043c8044a45c00340042d000e50702a010042000d00302060310200a80708010141c400310802545444040d0344022018040d489240042d0081c00f40b02030101d800040040c08601610b00ca41d0b44078907008049071541c10714880d408501e90400050b0800b00301c02d940400151800402e2145101c6d500c802c1503003c041290340b164074900b00d03078145500411043c0e41c1c28451407090320100304403901e1149100012420000d001c1d030f004002c180344176400d000b800f00004110103888419550516115a200024200ca4010b800c00a000402940700f51000074440d41010381c0192 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194180998 1250 194179748 194179789
    0x1419060515040302090a020a021b1807050406021b0319020d0f1b08010506010903030503181b010201060e0f0c0a0c0f0f02031e06011a041d040b07050f0702 68
    0x58581000981c00c516410541d8120000403506005600e020703c14183c01000c0030310114609082c0b400c019407200034092481c45140c111501a42c2540c4036480b001403c00ba0205220341585010740380500541c11a004a00040c0315081c203480380d0a100302008036081d01c0081c020003401141404d5480318040c1e51908a030485803041c00c400000b0a00d420210103144200c029006003980f03652194058600d40d40842c0380c680c1031a0038010180d07041294601a01c1c2c2514106680b603440281801c0500c401c5240100307980700d051550500c0c440b00e1000f00101010981c020b204090303881c51841032203901920640d05202641d00880e814160300703c02010f5004860420300c10b0a1202e80703840d0400540d6980030f076188442480d00904501e000e00c03646c4603070740040038800002004070a0150355006e05000b03801e2000100d42d203440711004007405a0b8010b02e4003500e000c0ea480e1100001031122481074400b00c441c40c0031a0085034080e0f003e8400e0318070550f501d4070140e050031702680800500f603000520101e00c0e02d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194182248 1250 194180998 194181011
    0xf0a02040f0b0301050f0901050d0f0335160801060e030a0206030703140a05090318150c070e06030303011401030203072003210c0304030f0e1008011502011419 70
    0x15045814001c0288807008000b900c80d80350105001d96100c1c0040b0644c4122082d4006208903a82c20b80e580c40f55a0700001c01c1c2c0e05124003072806032004001a40103107401610184012010b0184243c00c3c072030300d131202145149548441c41c102d1140c0e250030400d9408190b543c0014480c2da072040c0516100d280e0020100d612020039500490200d03401680e044000940307814601b110081080001030700001000820800351501c00da005407280142d601048440704100d5414440d40c1d03821001406482031864241c0d603840c18050010740d240c0f0244600802d140800d0001195440d001c0144c904840c208001c06045500c68001180203510007480b503800c2c4040300704103000c200340c105100444040d440c4001c541c3c882248045180100025203840b16805e9040d04209224202e54160f980042d1302d401c0010000b001207500391184001c122071180c00100006080b03140c541d10891f0382e4101e407182c000c0b41c0f8031040484012800e0b03a00014942c0b500305503a80c00714a060317190f5040544441c10421000506 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194183498 1250 194182248 194182259
    0x120c030c1203021c050d0b0301142e0605031303030f090302010b0f06030103110405100b0c0c09070203091011010906090f0201080f012117030a090312090b0f0a0204 72
    0x118003160030000000901d40728100030550100a24030316540e401600080508004000510038403901794601c81d40c0e80c44290802450700c094000c021811803031400c0d1042e5190030380f5209800300145c62042c01030120082c8440301c8076a1051203105642c204e507035581c5181d4604175001040141500110101591201c0c4a298005a4800d40003114442d03400403880d0032006080043e1a0100c0f0b440e50310401042004100040107541003482041044d01d010540750340d820041100c010850340201c0c220390000030600d280c50004203070105020000c8400703403410303126928100c1e43ea000301001140c10141c0b210301041018041e42c40780f03480204400011505075200e43c0c444c000e503050a08101e030b94402501070982150382149496a020013585890982e0350300d00060207040800071900b65081c005103810340300901918030010601c180014040315920309185071b06e04014510010b0580020b000760000c103403046094020614059000b501003015604c40da516010010409807210012030740c00c2000046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194184748 1250 194183498 194183513
    0x4030605060d0b040c0501020d0e0303030103020d06150f090c050901020c010e0a080709150605090315061507080702030f1204030201030b0a050a0605040806060d1509030e0333060a120c03 82
    0x1304034401c10018010a2401d0000b80c948000030048400b0302c5001c008030125601c0c00000d980c1101d070116503d00031400e090130500c0c01000001440d4580401c1090080340401e61061804221600d08008002e101640f41048416000d00101d00c0d005800c1f005100c01190f200d0400d040a5400040032454202d03912560549884003540c080f681c029181d00300200700518a050b0600101030740d0400c1403400e5011000243c95480d0551509100c450382000314080303454002100c039400301c1e000c105603500d50312070600f00c186401c5514100d11a08c00d803d00220384020100c5c10034440d2002d109a42d003050f04580c0194054034a034414613404c1080124002200e60340c83d10960002c01c8d0300d0315007a5540c0d0410100d241048070051000c1d00071030081c040240080c031481c007120342c0c50700c03040c1d8002400c611520301291540031a01503150300d0b204200d105454076090350028101d0031740c041030814525040c0c0c0900381598400322502944000480b80400111605001ca81c2619100b0004150960345030790f940c42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194185998 1250 194184748 194184751
    0x150204080a150e030a0804080c0a1a06030a02130c0e032b050c07150c0501063008070b06150307030504120201141801110f18060a020304030605060d0b 66
    0x905a034040400071041c010700d1030212225244000081c400700389000c0c80c1981e81c0c40741344c140c00200014000090280a0b044040c0d179044490a0180c0b1504005803d00c01404030400410038444038020002c9011490b001070704d880c00c20f90141007400d81e40c0c85400c01030300034450a070000d0140881d04501803a61b0390280701035104942400c1d100700310708807450b40f0700d41c2158101c00c10310244102082208501d95001440a088950750040c80500003040c0030101c0d104a48142c006015608200700030034402002c4c9000b44243c0200072114624200c076250154801715000c4024090314001c00040c004254580d01d502da010201600c070700120640f00c1c00e681e0a03544201e617241c2c000381e515800d0004008a00d0b820309014440d40c4020b004402100c0101c4414900251158003c0c80604011549142081d001030095150000419803a4184a82c10240760f9002a8519289241407481000780c0e03d4a0f00965949111603402181860f00b1a5113190044c58007070000c9a0090900707040f039001481c602e8129 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194187248 1250 194185998 194186009
    0x40f0504120504060e090a0603080a11060a0603031205060d080c0c210c0f21030409180b04030309080f070302100c1d0d020409080313050c0d08090d150204 68
    0x18185041e04000207440c00101c122000c11104020400150342e02c21003c40c2e817030384112402c0748952a1042468010f281310f03440100342c0140030504a640640125004c028085507030700f83c0c0d07078035507614007085c0132541c445c0030041c00b051102881012204907a84401c0d80b015028048030070200c1582c0b1509aa41c018025000d01c540c0203141c00f603a2400d00f41c0f900141e407104500b90940421a0b0f5a034140c8401406810701d00a44144031340c40025500c034240c2c50710a00480841e032039213507522883d00b9142c0d030140c010351140c00d05008041d01c2d43d8105482040380160400c1c400c0c1115100c0365402c4028107017010080e40c0303980301070041e03030760305241c1360024071030f45109400404000c007000490806440710044024140b01e0240310301d0030b5050540d20909404802210030b16040986880050003c080043c030140120b40080304024402031240020740f0100d0040040301d42c2e0880e44010002043d03500ca0008004070024440d00c0d40d40d003400315800384c8043c4504114200005009410030490308240c0c4007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194188498 1250 194187248 194187251
    0x31512030d0c0504180506010e060a26090715090f0b070b0f0108030406052203030c050f030a140711040f020406090909020603010303080c0c0f0a0b010b2a0c040f 71
    0x4409899542c890610030701c1030350034500d0030709180507000c0e81104400c01c0c80541c840d860741d00050305680728500f1001004030081045031201c5501c0f00c02005503400f0708140b40c52100202c4020220250401054450315158005001c098280f4494401d5440315403541400d01280f00c50115a031100412100c1c05000f2a0f1074803a2a0b4200e130600c0d130311154014021405944030000107010142e400b008640030340350942000e507661242031005141800c1c4106d0440d6a50341c0410b008001c0682c85901c0d00401e502030b20884122619000303e03e07480780b1030144038601051219465001c1c0103450b0f406840460700586a00120b842e00d00045001d55801c20100c01c0c4269002030103210158000c40e83c9405000c0300c202c10028110305601007400c0d80b00c180405001e001b5008005103540d6260800c94002c8035038202641c0c3c004074080c4402c3e0f955440840219800d409001c000b00703895051400f030301c455603411160a0b240720726400e551605070f003080d15005014010030800d91440d0f00d0f03d002d07a05004210280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194189748 1250 194188498 194188507
    0x9030f06040f060b06030403020c090601050f030f0406200a1b0209090d02060108030403030210050a150306050a0c0302160f05100c020714010305040206300903211b03151203 76
    0x1070060890741001e20440c17051700c0600c01d00c00401d40c0056013407582c90040d80d907029191188001610580940070b0109148000002004116001c030711216025030312a081c10300004816610320f02c800c6d1264046030041400500903e42d000d480b90105040b40b42d0000143e8644404039004220002e4084506203483c2e0700c984941c0341c110758100000c5005110080255041038210b50b0002c0d1601c2089004503030540c1c44101113031000c104c584c070001268001e156051452956803400c18042d00045820440325480c0c03012030206c02e40240200d034040d103400c005940c0d04501c50ba441c0d01070310711080010795084c0306011488004010351711480c0400d10f440d1f00203201c4c2502c2e164120700c1c1c1545213070f04241091300382014440107841c0c000c01d40d0141440131200383c2c40022000421903035541040e044d41c5e003855024042c011048000f200a00c0700e034500f50b0a001c00134141401d00d41c0c01150903121001c0c01000c840d0305000c0d9416003030155130820032400034240c100040200243d2480c0310400c50310543e800005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194190998 1250 194189748 194189753
    0x206070f1109011505520b07080901152303010207030509090c0f04091406150901030b030a0b0106090e0a0509060412120903050919080a02010509030f06040f 69
    0x81280d41c0240040700d1900391581440c0212041d40b0b80400110203001010414111454503982d080400e020309030070484618424460075080c0e50000d0009186c046a0203104032181000300314070b000b20b00c3c4c00034260384464640d0801260700f800000c0201f0131035566007007180301121614110304020085010040e0b840a07201010380d104808500141d03200307a00c10420a40001d4000d401e445000c00100c82d4214241d46840b03088003030344100755403c00590f100160100d0383c0d800701e03844805c01034005151101d49030b40740740c244440714501b64440102c40000388010201036101ea0804403203c007000e030545820b08040d540d82100510203801400106050b54004c0c0300400000e0005584144100c0050105003402d500c0c1c42d4490b02c015002a1010fa4144a0514000d0250012200300c10380324008020400c03007814001d00b00c0c0c00108105118202c1c1c101006154400040c6c0d050950355054090500d03110541c0c0191816070110290980600503d02c2030b0044400c1413015a100e14000c0d0344840e211222403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194192248 1250 194190998 194191013
    0xa0501050307050105341416082a1503160f020a1106090111030a0c060f09021302130b0f0a020c0a03150509030c01110c0c0301050601080c03040606030206070f 70
    0x350803081c1004003d0103000c0405980707480c2c4207100c074001807442d80c8040c000c1c40b119007091050341010344800700c0e00300900074107c800a60740d0307121131078100c0d8a0b4446403036511168a43c1503a041d80c60401610600200c035480c0000f070388480b00f0400805180801e4581d01c0c40c003606800407501180c03031101c0300350072404441e04111201c509103811b1000d8409540c40c0d40e00c0b038040203100105603010340404190f10000c1c2c2d000341140030804140504880e00c8032084100100905c1c0600705c100c8031a8289105a411880c15000d0104101d5004104151084d80300d500040250040e4403108c008540480000548180d400020041112a6841700c0da544044400c040c3c50290b1a5031014041c0098100800c0071500f1014040c0c2e00320a274620208194503800c4646185000700404811130754a003101031640032514000804ea00d40302c40b01500c2c6030300604000c2500b21801102c40a0205917181c00241e030b810000d40045502c6842203030005460ba07240c4c0c011802076003200340121003d0000202d40360130700040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194193498 1250 194192248 194192263
    0x3091503050105030a030804021813170a05120c0712020706180f12030908060c09040614100c0c0b030f011d0123010201060810140106050a0f0f0203070b0a05010503 72
    0x382018485035251001096561800f65030140070031103880302280c1190b40e4241d10801071000300c2d1072204182014411074072440310140044560f41c10780494494905020340645102004070b4903540d080071200e0344810b0707209600034081d180109042011600003440c1c060b844450070800c5e401004030742c0c00c00c0f1026050f0690f07054069104031341e41b841000082802d02d103a1007514481c00c01005603900502c0e040d0b4080489400c034076034030b0041508010385100c0910180031041d0040384c05000e070076070711500a01d1b83e500c1c0c1075003640c104c0d000b901f60015950003050164a10b502c10a144681c40e6500c2440303d11b690030942c0d0071403410350f680004120302ca061015001c10541c0481c888081d0394580b110b403032844c0780c001440c04101040300c0c4000c880c5038001e6100304020500002503480714103038480c40300010200c07041300e000c000e08140d0001c12024468002d0388c01c0301c502070321007941003100b001e000d440c2d03940c4104490086201c100900c0300002c0251309a6405030043c0e000c003082c5541071204240c10000e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194194748 1250 194193498 194193539
    0x12090a08070b030601030b0609040905060726010e071e090303030b190320040509010c020706020a11090a1d0106140301110403110301060b030c07061406030a03080604020c01090309 79
    0x201c0001800001000c1c012203030008000d090006203805580c011030b106008841e24141e000740303001c45850502402080482c4200025518180d10741c2505000f6102c0c030780d0803007129001902c950014802051480c1c40e26070082801e050113000c13400032144d06a287c0c04400403100c00180144020400c050301406080c030850b90444400100480b64a603a28a90752300d444050540b00c0c154260380d882110b00d40c50788203030150192042c40303541341c0b01c0c1c2c8142c0a0100c4c8190100140b0641c480014020320100f184d042056120a2000030328007038408204460301e01420201c03200f581c4402c1254030a105c09103110940c1007080001c83d40619104041064200701100c9034083d0f41402e4005c13090b060044111402c1e00d50000d0a060113000d4480800d0041c49181c0001480341c10004c1030060800c0c21001074800d152090b5001e10114143c01c03074034000f026042e0750054150f400903107140c0010f4050100b460348041c026200508110110401c1402c0d41d41044007900451002c60080c030194000100e05150b801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194195998 1250 194194748 194194753
    0x309030905041406040f0204150504050a090e0307060f02040e04290735040f060516120902010201140c1308061509090705090103120f020c011d0d0512090a08 69
    0x755a1000e43e01a81c0041c0110721999840e404100c000e140d550584019250140c039800c0100141200034080e6805406098403a8460a02c00102d1005902031b6007121107441c005503003448155030300c08003d80103040381107171001d40a000208802c414025480c1c0300b9405250180e00d006204804140750034880062401481e81040402a515800000303072508d402c0003110f00703640700305041c1c170b010700a01e001840c021040b0300f26410302c410700840e82080242140100d2082149072151603a90703d120380e44081d0b03c80443c5101c6002950030200d64001103e20717006000104600c812500509401a82110880c803820000f10750703011044080200c20001c0c120301c00041c00c00e07062000b20b10041001c201031040c4980050400612030f2a0184207850080001030311424441d42c6914201900000c1d0040c0c060020f800318481e040c03494800074100f0810001a1106126030070786c00030b03c00320401460492a0054442515500060410040c10840c4407903010243d40b1070400170308008420b80540e20482c440d6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194197248 1250 194195998 194196011
    0x210031b092d0b0c0703050709021c061d0a09142a060306240720041422050a0b06010905090f0a0b040f14010501030506040e0a08071b06030903090504 66
    0x380c042c03a50030340907a820001d04507102c80700d50892030f04d00403003a040241240503d003000598041250050401007802c8800001600803040e03c01040b1041c5215055904130078031540c1c80410700180b401c42e000f001c64400814201410340ba140c4c800d00b0b80303800c501c1c06548032000c00d0210454403901c001042c2c4028621012149508001641d117001c06484a881088d0090002c001404030142402c0301c0494400f01d5500c030026030402030b50001c3c083c00785204103000400125081d00c1e141c0305681c20201d83c07501804d12504d0316071032041d01d00340800c0800b1203100d220b21030f400880d10411410040a20446030141145030590004005141d243d001c9405a400b0070284646241142030560740080505000522006412300080c0601110f00302201d0503071801c2d5801000c0e2051400582c182d90f801e8038103000ba03890310800e06c01101c1c00c2204004140d004400744030300044040c0010205603006051001040c040200101000003065004101080d61680d082c0101034102d80840024413044900300700e02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194198498 1250 194197248 194197319
    0xb120103021203070b040506060103050c044b0503010b0405090307060b010c0c030602070b0903041a0c07050406330507020405090a150b0310090f0210031b09 69
    0x104006000091040c81c042c0b4600c014400c00b00140d9a526811101003a62814179003885920348105079085030009007407c00144088220a08890440e48e001c8401203140b00154803c0c441408ac901442115510400c1032900300d05491414443c503140c1d807000c4a540520301405c05003191500011640540d082104200b0203520100a40311400c0d0002c00104002d07040000403985528400390007010700349000c03004414403a00398043e008883c810280c2d4507003070322400421650b0f4011407040800e0986408240d40015038000054680741c4020000c1301da203241c03518009800d54041d60481001382d21141442e40c241301e51440e245403900400c040603401812443c000038410302c5800000303405540c031a804503c04603420040c0e80200c0342c011200d01e045004032030384c0320040c00014504078801d03c260710007645032420300c0c4200d44c00150b1052211314810380c030303500780b00d0515200c15504003890b0756401d401201c401c0d808400b91714941a80d941540140c01c001c116005101c0105070059024a81c1104852 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194199748 1250 194198498 194198527
    0xc0e030609060c1b07060c0501050702010b031c09090f0b0306010906050f0609010e0904080a020c030c060406031d0313150c0c09020c0a0203011a0a060f021507050f03070206010e010b 80
    0x40150000b000f0680c1c40905200280ca03048030002404824890110b001908950041c0300694240c4200000c0c000d40c0c0390f04500305d0903200c098660940c160040da2010300e400f004103800b003c0e00700715410003201d8a41d859803420126100b410b5002e1201b034503114a900c1c0c074038041c88018050240450108181400d0801141c1044200700300300b030007002c00282c500b0302c81e0b000e81808010100004d0a0384642d251a1410910f150401811000588241a0003620a15002c2007a20381003901a02641c01d042c076140d021409007042060140c50303a0035180c2c0d01004001c0138002000145505046203110307500e4095804241c2101200c10010019000221800a0030802c1c8040c200d4850303a10158482c6000030003070381030907800781c8000d52540c03070603445050700981d016480038500c50407510100090b548160a0720310080f410a40c4005810180043c00380d544542d51061b0021a5450300d182081401d605503c141e41c0155521005a8007440040203134013215030165004d460740310364035414589843e42c0f411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194200998 1250 194199748 194199751
    0x6161409040917031504050c040315020d1b05130e0606070209070e060d0509060109152c010314070f050321130f0905060d1e0c080f010c0e03060906 65
    0x20700c07403600ca000c0c2206100400c07041100000c42849100c4d982d00f0910442d00c401d100a9484d103006e81e051000050702c5c054010107480c2241c0c2c206000010034200401e4001c004d5010482c09850107030740301e100c0850010014251501e0a4250316a2030b507441111361010b89404207680302a0302d9060030420007006880c0c0d2400d440c1c00c1036040d1a80c07003490301c0b03864064641c410360024142e0800310110341c00c079610500c0e0300601d008280500940c1c0307569880381c1000341541c581d024104541d0413a20720030455900080e021115010380c00e10081c0c0715014068607c0d02a1034282d1069a0341c001410310081030b01c60602c1003030300902500c4224a00e5603c1d090100380c03104002d962104000c0ca082c1040c10074917442c8400c44850030126044089425121202c071034006003c0d00940b500f01d4500800118142014601c1c03012058114071118400007a04106036002501d5140860750104d141078001008541003052403464189000003007100e02e00c0d0711000f4202510541128401c0e4003040034003502c0080850400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194202248 1250 194200998 194201017
    0x20f06060d06151e03030305090601030f080309030717040617010e01060e01030b040e0106032607080906070204060f060e150307030e0a0c03030c060b030d020d0e0102010914061614 79
    0x100783c825402ca00400a155240c0c80b26000080f10403610090b00c003108425820369100e0b482c100b00710340301c02c00b2643d640d8100740402130020301000c951501248000000d103503c690400c04032868102c059031010702d0b206400d89010082280424107014081c6c1001511020a1081c1501c1850390b2510b03030b40b005102c070b042c0720741c100344200c10442c84c2003030344280c00c406181d80f130145c0107002e09105000c10764001d100c41d200c00c3c2c54040d4500e48440f400d21080d0030241ca00c10000c0c005604140041d2145000e075071000d048a640200208034410058413a07006140003082c807041c11003025403400c07a000d42611020482c0718400c980354984105500b01c540103494000015140010300180c02c290810f00e04480700e00054041d1031403002c004105540105c06035081880755000340700141140060554540802d07400202507001641c2c2c80950a219100c243c10701e0005200218000d011910744602d844404801602207800060800171001000104c524042140e440e02d00344107048050a00041d00481c42c22 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194203498 1250 194202248 194202251
    0x30a05070b0a0902011d010c1406100501050a020c0415090f1d0a1505060609060d050601090501090b090409020406050a0906050f030303011d090109150b040e03090a17032503020f06060d06 82
    0x4501592141001c50745ca191702c040780079003075480c00b0501c99440b00129240450bc1200d10701c040ba06500c90310035900c0c02c4100340c005021071483d00c01000040c043c02d010491540e41140400183c0e1102800b40c00803082d110640010010b030300210240d841c180d0031421810981c030001c05034000842c80c581191820344294000104c0c0c1d11072800241c41c034407031561180d0b130011000c10560800c01c1c4540c401401407000741c0b600200e190303a03040152851001c030711581c05010418428640b0505041d0001071010780b004000060142d07d690010301010821b80040c1c0102c2c1da0750505011038141000a000104405c0f0010350039585055200d02071010a001014114242d440c04901a54400d4001c0c0e114030b544144002030030395003000304500608814842c980300e070342040052180e6982c04006c840180c00040c0c0f20030681424050010300c00d0034101c00300d0340f4900c820041081c0541964007400040c400094944040309030504001786403070f42401403080c041c2c00400510103141c0d03503240c46444981c1e11040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194204748 1250 194203498 194203547
    0x50a120e0304120b010602160308030f0a06050a060323060f0d0303090804031a0a09210c0209130b16080130030503010602011103100620030a05070b0a090201 69
    0x100a401d60146920515030440461515001c01c0f6107000018107807081c6900b101c409042164020059140f5840080d01c01e0702d040002c102c2c483c640c1810036030b11000070701011918907942c0700442c00642c2c003644a103000036652020a090000020111891012964056042420440005841c008a0381451442400342c641030004250103500036051464000c7c80e003d48a6640b030402c2000e0a5007490b402e04d4040303840c40003c0c0d0010292140e0f424090700310b0b00108035003400f0116154801100c03020300d030030300500420202c01607a45885035441809204120101c80d004e9151200741c003900a00510800f1040c40758000010f50700a07100b50449111100c00b00f800c81c5461006100b200c0c24183c580d01d1f040f0040e02d404141a00000214100d4816038001c016142890f01c0c0d01400d4082a242001c207400f04003030400407030f0300c60b03e4605200480b11515801c0e5400c03440c9000c1c0381d544114455004508003207050f40134032080f010038a81c0190346170424400d00c405a40024185000707030951078044c000502 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194205998 1250 194204748 194204771
    0x1a060903280618050705091816050406060903030e0103050a02091905010813020a03230d080106140a08040b18010905030c0d02010b0102030d091a13020f01050a12 71
    0x100444030350010498880c4070a560030500000c01d800c10340e80c0380e00f01007018540800b45904100f040382c0141c0980340013820304003081a507180c0545182e000d040e00814020030b10409021591102000942c135156061404040c40265040c9034001003e01100120030800301e078000025500a003005d10300000d40c2e03074481072160f009014003441d0743c0e000080300c441c05456022209111065840903203d4805a41d100f1075103203c900f248600003504810032500400000b503c2d45079079020032180340030b20307107111942d00300040ca030006206801c0c000800385070042205540040b031520904001c050300318900120240081d0003200b014200900c010a6100082c1d00111030441080c03980004034000c0c0300800c40e50a245641f90002074030400703280685868003900034014401d121046c40180c0241d41004000480709004280682040c0c1d0520540c400c0103402a4640c0002c5100b1590181540c204108074018405516107180b0032905018007002201565a04100c42034540540200045100c00000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194207248 1250 194205998 194206003
    0x160c020108070f02101a090a021e0705010e010509071a0f180301150801140f160804060906110307120e031b0708030f0405100806090c03041407061101060602011a060903 74
    0x807100d900ca51400003071b45886411200102c450140817076007100c0c0758440000800480c071801c50580e61041940d40c01c0e021031184440038000690150000082c1656444006c1703003900e90880701070020340c0000c04107102c0d41c4d01400001c0d084c6040342d035205003024589502d021070382c8a610401400041c51207004189079409411a4104055080e2107156050b0703210700d024040e2a034900d85403049414907000821448590750b519100d0a86951703c0c00032552055030aa40015010304107803000b54070380c00181c02107a850b0045032445403080003101d50302e10300064010f0540764021840303424039003814031018030a40e000054030140613400100d0b08040c48400b00365498500c86511030101804041010328001c54114041e20899a054a101150b0002c1210031070b1558000ca4121382e0182c40b000c0030031062040e00019591051207025101e00489a050b00701d443c040e0507a020b03000081305004616032903038017802588004c0403e80003e010350015087c0c902000142c0d904024040c0c080403e000d106540e04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194208498 1250 194207248 194207263
    0x703050409050c0d060e0907060c1203021c0612020f04050f070807050d110705010b0603160e0609030604240911060a0e100e19121203060503010f0203160c020108070f02 74
    0x10802004002e41c3c030002503042d15000c0707c03568810b0055840c00101c4901440405400759448904440c440c10142c80c190000d40044100c4101c207040303030b000b010318a05188201000751042c0200002803401502c108005024054040e034022030508040c400d07030031240070580d40c02244500348072180741e840b02030450302c5001d0002c051440b9411300c41008250b01400000740304480c0168024801408118180645840140c0c1c2c60000c50f0050710203102543c5c801c09440341064002070800d45044903400002c2d00c2c0c02d0084d41e042c1d03048407218540d058001109002401003d0052005100004460b03c1d90300080050056081c0512000100c0200c080d02c9817500100314003004000385079440586000806846c14044410f0040e500002d811003014586804881210790303411080c1c804c052540c9d120129803242600030414951a8000410141d8085c0108100031400300001a01c82c40c2c064080342400b46d07a1f0940c401403000301007010700543d03409079000b60700640500302841c4c07914002500b01c1c0381181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194209748 1250 194208498 194208517
    0xc06070e0303090a1d0106261306060e061206060d030e06090a030b040b150d03030b030c061605070509070507020d0c080d0c03030b100203040603230906011503020703050409050c 78
    0x130010804598032606031509a000300d0340d4400841070b80c0c1c07a107200341c1e100c1168140b61600501c00d1b1128410510b20f02c04050343c01074003840c0007803007074110b5562041035800a80080345942d400c841041250304250b004109400700d000010091424010040f508280e441040601040400f840500d0292900401c0340d02c52400a0401a0420380d43c2c180040031000c00d07541211a60244000704000080c617109120440000500355074824071140d4054005010b103031452605030090500800175903540001810320824030000382c1c03d00c00414a0042e04081e49a08400d10505100c0c0a03c00f02a0340072003550012a81a0750f8010100d0081c00e1401500446503c281b00134813450000c8426144e001c81d10441c1d051080e102809070448110800210f06402400580181d00031302c41040028420f400c002c1022102c0b005441402c22600c2c0c4050069604894a014550004004000001c190000f8501706181442c0c1142440c202c0e58006105106503c1501c3d09203446101007191004000c04541d01c3d003c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194210998 1250 194209748 194209759
    0xc1e0e030d02030301051008060f01050304150c090f0b070f030c1a0c0702010f1706060a03020f0408070305070816050d0303020d0c020105060103050601021504060c021603030c060506060c06070e030309 88
    0xc81c081009550707a02c24054035024070980164828814002c1c100d450103100001d0400603c13048140c011071b425003004000b607404d80c507180e0702c818462004e40720301c0c00400025610080320505040c1926503848456010381c9040404001000c0890103800e03814043c9503162502001e102510b017050b07686a403141c00c0344021007640d034043c006464001c400401449100780c0300d10540c51014001610480480d130300300585070300d5000000d00d1910b40f100040c900200c16050043c1004103c03c0c0300350b0b503034105411900d90b5611580c8244184482003100d02c00a20f810030007000c0481c00340c5c0c0503c110050900c00c49002d040c0941c01901003500940581d014191107810801840e400944001e020b0f01080e41c02c2c41c04680b0300300104803d075201191f89180e45440300c22010403526240d84403c002c01c0702d8915141180501045500d090031003112010041d4000d9440d003010001c2804c100e01100c9001d0700e860b1058030108000c1000d9500400c6159104645c1d003000d682d00d4004502003402c40c4550303490b096201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194212248 1250 194210998 194211013
    0x40315021803150604050a0507050304031107170a0c091104090c0201020d09080909090d0512101d0a06090b0d0602090a03060204090225020625020d0b15040c1e0e03 72
    0x161251142e075104d114111018045902c07440314404c212081640e100000030410030002d004240280d81040800c111002250100b690310b40d12001a0388241c0000c942303e401c003480340014800c1040b001c0c0003805c8044000c0124607016034035419684035910418003403a40329500555050f00030b5041d203111040c03c120900000d0b540e4074100005512011030325100d8580b0031f0100b1403548000407060441080c17901c6881c030788000840b030000f1825008005808025040201003620300505a0b40007481d4074002c03040c1054141141c40c00107585654016115441c50b0006200c0142d4409100d001c48542000380140ea4407075100115821040b80d80001d4a40c070700018002a207001c80798001c240c4240078102030b5001c4080a1114000b0859080c0043d500080c18480d03517000302024401004010700300e20b0919001003455001c00c004813407004041d82ea039842c0c0020031110440314244030340c0b40c030405c550402c2030b4000301074060040c4207501e905d50510542c214800c00c14a00400005502c17160040413a500c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194213498 1250 194212248 194212273
    0x803040906031b0612110f0d050f0106140703050c0102090d080c12030112080903070905090a0303180c0b090607050304080604030230072301060f05010203040315021803 74
    0x41c218a100840b08001c00907841c01200480803403a200b9507000390f403083c403c00ca45001100c09032a00ca25031160b1040300f04094404416210000c1c45642440c0c1008582458200201401103034141d0213441072098a003d001000345404d02115600c0e13515080c03403615512551281802402400c0000c0e40018494030b4110a110005002d090a90481c10850b00c0d40d840348041a080c60000f8450200d4800900300008001400c07000944a0300c0400b50880748440d50b16070304041662010780741d04c141d40d007200040c0e200303040c1c3c58003804c011888101c030301205120096032085074200d01c40c860484c00000128800c0718942c1c4400884030750503080400c8985650f1500e8000351a283c0640b4220058131581020700c00000d512128007903c5603402c05040c00d05980ca00581e8005e511580c801c407000140c0c14464240302c215502d4005034560500000a82da03801c004080510002a0704581d0565000340001c00014034039000006400650300400b41e165403980000c3d130001c20081d040d00f94075024802c4954031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194214748 1250 194213498 194213501
    0x70b0711030105190c030606020c1309050a030302030a061d130501180b1005030a170309120301270509031b0705040606180f0b032701020307020705130527030408030409 74
    0x40351350807400c1083c2d0300d0748082074003158007034480c0c91f01503081a0740c0d040380c0e841c1c981d91141e004044140007040c20032281d42d46508220400f00210042903000c0244800e01e20b05109600c090804064040b140d9690507072401e48141d802468860070703003000c0c8001001c000003034001001182d003000409401220301e15101244070000c0300e000c14110015000042e50340f85c00640c02c104a50803080044524000c100440a1a840213251100381c1c810000b51074881d0303040a0043d0700926800400143c441103442c65210f00e40c8031400c40d801e4560920741405035105001c0200c841070420702e008248160012000e04d410a07203643d00c4030360700914100300010580e400072000929002101d5020700160b49031300105000304114010f00d10031050600004075404034080c1101e6400a41600004075110404182800c0e680125009401a0003404c1c08000b5410003540c2005584e030040014403181c0b41a184034016550214410b50700002d48079003c0341049018011035000c0d22102090765a15034580c02e9000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194215998 1250 194214748 194214781
    0x2040b0d05060306070801050d210c05151b21070503101a04060305090f1c0f110318130501030b06090a0c08060402090109050607050114010e09070b0711030105 70
    0x18038641401d001032014500420700ba8410761280d103407141c05900707210030302c420080010021102150800f00c00b0740c01020301641c000c01c0003035650302c4244240c040d1030040d06000b05500113800d0002480d0a01c04840301c00400328212030f0700c4417540d689401008200102059050140110b40350045080c45402c90f409401117205070485c560300c040b9103542c0c0105100c000542003407410044014001485014401e03000f44e50401e002130115081c03506140c030b400382409150001030541d5a0002816107581e0381043e446900030207070b13040c01da00c1d00c05801404ca0300d9104a44011001103000e400c5c00300b140c1d4880741d03000103404505008105941c1c40c1c8c9040242e80c0c4080e51058410941640015200b40075805001d14030342081e565000c658407050180700194120325500360600a14200100b85529602d003d00b51060040c0000700d4400301c1000e0600700740310113030841c4000e10918410804013100008401d4219480049601e80e0780c00a0305103682c010700702d2000c003641035080800b8051107501104038807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194217248 1250 194215998 194216017
    0xb0f04090c080d02030f071203060b0d0603050706140f070302012c0c0d050d0c290604060503010e03310602030a030b011107050f040f020a050c070f03150209030f0102040b 75
    0x10380004150304020b9175a4050198458074082d820020900003e01405801b0b40c0c240b09418040380796922a0700c040312540001c03220f0503440395100c1c801c0041c050b04004000003862a030800d00109200f04000c03004c1441004940e0404070400191401014401d60104c51f041d001d22041e02c84002c0526000868040035801d250440d00c076200030348030b131b074030b880008442d00650140052001807890501900c0403000030100f0359003400010f018a003003072003400404608201c500105e00c003e16085c0100070445042e50051406030707240400c1440c204500108807000c1c9080ca40340c4160040d544282d80c8000d14074240310f602180c1e184880003030615000805807913020500e4030140f0880000c44011aa250200006080194403000c1c08021034103110300c0b59035848501a101141c02c88038200c2060a030381c000000750340015000a42150a4081440f1000141894a0f8075100c05c0346540c88070300c400141c00307441888042c0e0002d1040402e5404100d1180382118050003951544d49d075000360703400c0d5003101020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194218498 1250 194217248 194217253
    0x70c050118051215092b1e030b060a0c020301060f0815101802092706040207030203070c0f030c12050d0807020102120a0518060c310f06120507080a0b0f04090c08 71
    0xa140c111000c1040604c4001342a900c40b01425402e4100000140040e4009000d15503114270020f07641e1070780c00c000d190091682c0c54544210000303205040c03c41e80c0da9800f42e41d88084000041c0407101c00803034140c8207014420f082c04415100e8a00c11222a1843e80c07009001c01c2c0100346c440b030540c58a4001c0d085810046030b510701112a4080b0201042d6007040101c45451203c1000030742500c2c1075030141619500a10469040c880705583e000c0341c06905810052078030320592410010008440c0c90040076103580c6414644030301e03265a40e01e07541c80810490318244802c150024403401c0c802d41c140c0b000004031040880702803d01c00206030060200b555002480b921030042000c11500004400d40500f003007a140f50300d042d64408244004c094000300c0c0341078403d0b800001c0c1046002c44180d00024288400400784203600d000c0d00603000c840103510781680a8204800c2000c115004001c213940402d01c482c001c1802c00010300051650141c14424990140c500350908050141c203da030300080c0d0b20312004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194219748 1250 194218498 194218543
    0x260406091404090f0b13020409060207020405070c0b040303090311011b02060603010b0915180406021c140415150909020307060912080904061a070c05011805121509 72
    0x5002c01d980c408800a0714810180c08104005580c820480d0341c0050909190700d5007104507030002d815582070b01030550310140c001c02d0010540c40e0900c522901b011781c03405e1280040b126a0350342046058014000740030b0541c6c0b003c015040c58020744905424076609002080304400d82d500c0c9202140c100d090800040c03141000291041c101403040740d00c3c5140c000d01c203110a561b80d4140e075040524000c1c2c103540000140d001c821202c9000b082c6140194480c12006d41c40352602046c2a0360032243c80300101f04282030050030740800420151180d00281c004526042e0441c44440c2507018220004140c60743c95604800054034401d03580c06030f59400d10031415146110b075100e00803140c5807418050f00400321050b41e050400288c080000300300c20140034201080b001d41e140121102083c1d00d0054072210100090400200410f0b480030a01400b82400c0001660503074406196240d2984d0044c01d0181241c48110105080104070500c41140b42001018035868107049940e02c0b040081c0e505541414881e9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194220998 1250 194219748 194219789
    0x120e01140a2d3510030f05030a030b04090b1501031118090108030a02031b0106080a0606180e060612070305010c0906021605060d1a0301090303051b0c0a26040609 71
    0x506201d07144512250b410107000388083d40000b2a0070141c410613141c03002010000025101c4120b60340c40c00c2c0144003864540d1243c0001400340e401c2075810340d11445c6407055180010340350b2001e0542103a03641c1c0315004d50384105070050b402465454986185210041444100040c214854440d100d0050319690000d903070701c089550f075a0059050710710140c1c0040c07201200e081034090320075140d8101d207400442c2040d91101c00b241440d036810415104251a6441846046000c0010300010f591040003008004c26504000b5284e21029210702d00c01d100e03c040c1c0805900080180101440e0020001c1105842011014092405a11566003d03000e0042d80c18400300f6a00708900071608060701986c684a4000060030081c030f0030340308006482015038454800d0f51424072890780380d207100e91400941c41c00e1800c1003400000c00e040a03c840b844c0104100c184421000ca0103004980e48441c052480342e40b00d2604441d2400701800d00418140c01040c0043c48640c4205980c00b2600c034003018204100604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194222248 1250 194220998 194221037
    0x501140901051009140a0504020312030a0c0815100e0a0f0b0a021203071e05120a050103050c040b01121503020d030f0806120a150608070b0403120e01140a2d 69
    0x5c84030081d6400303c0000268110b4402d801c0964071a100400360303100742c0e034101000380e20340d001039400009582e40e401e007031442103400422054002c000003a6040d00440d03450001010641d1a01d4018104100c403809000c5940b125060780d03018004c402028900f5640b5900030364a1608210016401841820a0407544403444002c03030303009030b109070748180c40f0403144c2c02c2e10760f4001292004178040100401c46104d01c0505501000c0c0541d05407440414654510700700076291544920003d0703c02c5251660302e181c50307038202c403058081c0e4804483c040f8105102d01544500041e407a0b00c041c0d00141c045080c40c040652000050034985c0e10703912440200c0d02c2c0c06062100303103110701608020642c007024540700815514940d41154501103000400d020703444a100c1400c0001035801043c500c800860301f4802c22030b4004591340c2208091510b108072160345c3c4002003101c083c1c5070440d0b11110f00021803108242c0b056000c000011031503142080540414035080000c600300008102c00106040e11900034246d04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194223498 1250 194222248 194222261
    0xa0204110405030a0609020f130506030c060415030b0a030f030f140a080609040f0203070f030203060f0c1c020d060b0d0e0106030803191401060305070801080606060d05040501140901051009 83
    0x5001072082c0b000c142c2e05c0100030001d808040e42e210100b4090b0f1061070340c40041c1411a024134031008140760500d141810b25100c11184154850300381400305002e401d01d40400002c00070001d1401003488000440411000b21841e000a4103082640340c141041c150410b1101d90f40d454660f9801e403440752028040029800390019000000300c8400102e02e982c40c2ca01034180d00503008003280c0050030020b60000740703804032036400003000350780d010010415441c00f40001c40c5c0c00000608064407525244000b4a0944500084680b170120a80b200003541e030000d41c16a01901c0c103038141004116210001088560801080115901d060030a1043c0280040c0140e0046079807003500b4a00319255040b00407100c00c069944c40c00c0080d41e5408086944108400030b500134075480e1800244c0e0b05204500401d503c505820004546c0d0200c818000b4030b4803600d04031114541c0c10040000c90b40c0b00ca00c0c049001d09083c001c0c09015100c08420700c0007400040d4480c5004143c550380030fa40c015036071a404400d4920 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194224748 1250 194223498 194223509
    0x406080a0c0815040e06010e070f090e0f0c040b0f0315030a0b220605131b06020a030302030c090d03120e0d1b060e1b03010506010c02030d140f0c0a02041104 69
    0x101d10000c142032407801050f900007408000d201181d202400c00c1e4952419409a01503040c3d10041020320203ea1b030403610307400d00e20001e0302d4195680b500300403c46e001000098003855001d00940b00195550600800f40c0300542101103210b0758034010640c19038050381064545114001148802d014036150004d4107002055001d0008074583c0e8403000301e0041100c040740c000d00120703001800324000a00600ca218400c500211120010300c0003410590609251b0190582000540c114207125090b00040c0c6901c2455140c0780240e0ba0713030344851107055039000b01115107810152095103078040603000569001590300c22202000502c10510041d555920446c00c08400304810780e80081c81c1c9810155a0a0396500424021905103c54509145061008407008032414005418078269103000e00071150018024a482d030701d101c55030b40001f03485001c0030114100740301400c0b01108074000d1000c02c1e140c40042a2503e140c9407500074100700c0d00c2d1050068220311461424019154000030343c800e94050b40d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194225998 1250 194224748 194224757
    0x303120903081506040906030c09061203020a0f060204031703091005070f26040b0f06030c060904020a181e12030509010c060b0a0b04090b0906031b010c0212030406080a0c 75
    0x8990035803c10480c1000003034241c000c08208000300340741c1510b01440004600c02c05c081c841d050301e024610300864103140c100200203003841c5403500109500080000015802c8855011001601e24000d03000748902d0b4001460844401c40c6d007264543c030070000d14483e20f114800d071000c0c61401e140c4101112022901c071401f244040320360fa00d0851042e10460f038900c910300c00d01c03440a14043e2800e00d2000d4100c5084030b40c50083e4080107d01800182d0b11034100c00d0980c024520342c403004e030000d1224023801c96800e0065a0101312644514800d0b0f40016000003803036081c803c51070b1a1410b03030b20780011050702d0904403050407100041003214980018030154059607040d0900e001d2a00449110458410035200e840d12080b5001c841c2c0ea50391246002002440b0039555240c0c5862844000e030303442c0181440c030030b007180401c00005403400304107e504400022529690044480c0040c0c076041825080a5084000a8100308400400000801c10360700c1b242c82d010300a1303032442c040000341e071151a0141c0000c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194227248 1250 194225998 194226001
    0x503010506030106032003031b010b1914121905061012120507080c0f0705090603011514130f0b0414130615033914060c120d06030312090308 62
    0x1071b90548901c410010b0003400d4a2414801500368240d00784042d02c13045060f50f64003502c105503c0c2c004080e200c5903200d454900602c620f080d003040708488985000d140603200628803001400010300000e6002500c42e0281071b59843d4034240a681c485080315a0103242d40c00c441c01140c0e460007030400000c40d07903118480086c0b61142c15000c56568120440842c0c01a10a00c00d0f0205490305000248090700c5410062803150302d00000c201c40301601a04c00b83c0244d03d0400c0715244544110941d0090390007503c403241c009002000880c0f010414000a505814039004040c2800401900302203c1000b00b01d900f40510403008035081c254a83c2a00c11a00103040d48400ea400545550010070064100c40c0c0c003038440554944892807800040d05206407850118104000040340c01000c041a508600e01301000341403e100c0c4803450b2814811003548a607502180340c101d010b204001c01201500300100482c4c940c85484a003174080c00e0a070004070041074a040b0340a0400d8001d1041032001c54069440c118079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194228498 1250 194227248 194227283
    0xa020f040209040605031b0112020c0a030e0102030d0f05010e07020607350406090317150f1302040f060201060602030a051206190f051509030a080d02070b01090204050301050603010603 81
    0x942c4840d81d01608507494020005050303405001c43d0030315a8945041080680010000426030301e0980c2c3c030f4000d100d00c10300405d24861800100512020360606000f00c3d08100341005034a18000d140c120010135040903010502030b052034024904903010b0407500345050710b602c3e0040c1e0700c400301150800001440600e400010b203070b5002c0c0e650101d06500c2200f08400204e50b01e071480320f0208440a0720b4454a45080034101030303200035110355045044492896506216181041c24061888602e00c90a4a54280081030303682070316070044e401480da41150f442d40c0e200030440030250703203105403c0594030304240007403114001300880700c49140b60703958107280c90423000c43d05807810805009a600308010712a407510550034100c0d00710240400900c254051440d040400c8180d42c9804000c6211240901402e507040d02c001504001d401e900840c503c1c0c55000642c13086009001d507940151109185000000c1d120110303600a1007529002c0e0003c0c8401d96800091600340d03980c40c440200300c219003040c050403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194229748 1250 194228498 194228501
    0x60c020d14031312020717010c0827010501120203061f06051b060702010b2403010e0a090b0703020d111303030f020a1505060f06031506030a1d0c1009150305070c0b04030f09080a020f04 81
    0x68000c00c1d0100b2f0b0344801602010030f03007110001d80103442552018010382d801d42c6030070080254800d80c52066158041084c001c144445032141c401c42041c80004a14011801141009032100c2c100c114215041e9145c0060b000703000e00485c0c958039008055a1046103040706030a0444d00d541c88050110358656443c08141c208841001480120381d0b0307a0790610640042c10b862a040d00400c1d1990300962a2101687c14204840c1582d40540d040b8408000e108075503200711006004a1b40c00d820102c40f040c06030078040e81401c00a59009000340502c10712490040003640c0654040da02c1695814800600d10040c0310041c4402c0e280000e1110180c078440d00346280440080d680f2400101c0e0100e510840f81d024500c10028074990b40f0695041b00e200c40f0710904000f081c0051100351880c0010100745081c01c0c850082401c41e90301030806444030001146640181010301510f42c3c40b803c10b448610306410004d0001c80900f10003400680700100001d103185001800b00c000d180c004250344039400c00f1108120 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194230998 1250 194229748 194229781
    0x20d03030207020d1110050c0c040203040501060b040611010c0806030c040504110a080a06050604090f06110403210909060b04210c12060c020d14031312020717010c08 73
    0x50400d90200540001030700e0320300006202911030486010100343c20b20070404c03c10b91514a680400109005030120442e0015114520800c20303640141d0340e885030b05090340540815000842038040000d400685140e0121201c0c60040c0c0c25002005105010070003240d048406035001175141d44412101e2030310b071070f09a00940c1c001c0d110341030000d19900e114000c141da0342c2d4150310144460300704500b4801441414007990750711a1080701d0800c60710080c2c0d913030006103a02d9040080c002558600315411480a203030100c0340078680201e49c1c0c050045c610b41c007042e50603000c1d10210b40001d07448600050f04421b40e001e0203081d6041410440d041506060500350480b0500c2e42807400e031200103004002080b15514004064103000307071070b200711f01d009062410655100c01041011507220750014050a5804036240300c0f01d81d04018450b55030385506040140c04c900200c006040c030300c031280d100c400c16a00006c0c0442100c0711040289001c030341d09001c407401c8500f000caa03100407804000c00140e0101d89108d201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194232248 1250 194230998 194231003
    0x1060305091011040305061605030f191a040b0f010f12020417030c070b090f0409061b1e030618090201050714030a031109031b0319150501060203030f04020d 69
    0x40722061918450b64041c0c400b40c0845181c0c0000005081c01170000610031243d114580800080c900000140018040c1c48014007026500c02c002000c120320f54a480a0b80c200c03904060345c1403224111240146040e0000c203510a03100310b1034818441100d00b02101c180f00385080584a426041e11034280c10381d146659040729582256003003002107002070002e09001808110b0f0001591148102035000745032014941016254840900502140e0b40d506600308441220a031804a00d40040e4940b0001510002c69488201600f02c0c19010301d580e030082158003c410f04600102c5141c107011000c1e41252024010001c10f00641d0440503640403a68111011107481850302c1440d010194071590241c0101180c2c500741504001140000581e040c000c0f99008040c03094010315003c01340001230b0b070310f841c100031101c1080c0c2803644141640c2d41c02e104184060310319000381c08401d522854104240c0c10703400c1040d100c0518000000c5002440002560300c109061092904a911640c080160940001104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194233498 1250 194232248 194232253
    0x8190b0f01231605010c0903080405011206030f05161509050405060f0d03020705032103070e0f0301090317070c0203071202150c030c010e01021c0902120124050f01080106030509 78
    0xc809116404005103c2030008000c241c46a00c030764942682503440140d04401004600041030000c43c40d0482220101c44003401c02450f86000701034180301a19103940301030445804a5900b80030701c03a02060103511480c840840c5180c03140c40300301c0d507655080109058800991b03c040144100d083c07030350006d43c010390004d180c01c1a20a442c800540d01d041380f1a001c07801a0040c0310104000d0604220b5218001580000710040c0c104083e41049a0b0000501e80380400049010034540d82d00d42c01040d01c05100d0180091054003158100645004451000d6210100c8200d0006109600c11600d07184c400d90f005002c0d00c3d08520341911203128140205042c0c0e401610300200080b00c4034044001d043d010400c001854032041c1c10140d030f5084402a17000070a4590040000b14031100c04135414105210000c0b90028034100d060010422020502c2c0400c0e07600e40c82c1003081c8688060b40c022451841c6501804103a01a44840c1400012446c490010340031489600041c802d01e0b0180d0071040d8400300403804c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194234748 1250 194233498 194233547
    0x70f0306050c040b03040c060e0117040b280c180f050904030e030a0b060102300a020309030102040906050901080c0904021309060903180801060e040f0f0c0608190b0f01 74
    0x526851302d41c001c1d50226800071204008001c8a0713080142c1c18407104007402d20900302006000c08100740e07a0300510061000710f034000003400304503001c0348001d4151903032958440200c40100c8564001c0148d0861000402c019402982c5d142840550450a0368086880800600c1ca00000d01040e4040604210b0a102d107032560802070741c500700600e031841070103008410510705112002a05229885001c3c2a48405460320000c1c14104130300324500044150040ca5a81c0e2034181041f42180038040344241e0650000400180032a40f507001903054510031552290701d40d0740e5800e456038420710514244c1c1c1107012100010301503d40340071943c0018440900201c0c40300540d985203c11100c860400f10081303a00c5250b910b14004103410100054804400204403080c201a80e80d07001d501c006000074035804003c8607540410950030707031a50748198405100b40da807580780c0d200901009001c40d18022a0f29408501400881c0c0d5800b800c071007030b038001c0d0250815041d240011105080c0c00c50300c25514290b41c18 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194235998 1250 194234748 194234759
    0xa0f0b0a0c140102030a1a0102250905090f0609030c0a120905042a0f020c060724020304050d090506090f03010216030305060f04090206120403031506020d11070f0306050c04 76
    0x8080414101402c0010f9503490804400400c55103406042e402007250b2501d40101030b60002069407402c0001003280c004460120303980b450280d6240c100e10441800c21b4140440300070b0001d00c50f01c000660109841d125170342d444c550740c0d580c000c05080b880c00d58403841c0000045805001d0a01d20500c440c600301200c00d4481d80030501f07413801000342a520302035480e440100001030350107181e400441c600d070445407171000c400003d41d505400905244200710000c2c542081005a811491802c10a80c0100fa29031a07010701c2c0c840290021501a160760090322a00070040344108420740079584000d002c281440042400e0100d1940040c2d011501907608005011044070590803c5240c280320b560045000c3c9420404d100880802049180c02542813412650041e07070349800351280c10380620483c4e002941d076810b003140a8240600507030a500b00401003c40c40690210300da5403910042d44460f01808aa19a03090783c0f50080d1042a4140e4800b035024400101190410754201010802c11402d284c0c840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194237248 1250 194235998 194236013
    0x3081503031b1c050c03040308030a02090d0506010311150f0c0708010e03041d0103020102070302060d0204090603082d030a09050f16180b0306130519030f020c0a0f0b0a0c 75
    0xc0c02949541c0b04400c0600c119200d020f00c0a229041d5242c02c2e82400c20348000341b40e0381c0c01107000040074000003000007580c1c95450b40c1a9001420014249100020755051090300c0340c0302070005451840c40070600300302c0707070821044007002c0203401d4501c9480c0c8071011640d2001600300f41d0740c20701c0500980b5000200c0600900850f403596081001031640c0f05c1c036000000d05550460030b01600303222041001080540e0f00441d5100440390196861541c469010188600030f1003107801250b030003458246e0101c00d1043c0f841c040c140d207143c4110383d031180c1c40c0f04144045100f09100303031140d9100010000111130145580107103485920500c200c2d034801c142c40c103199080900807450150480c80320a8100000d454911420000051151017048040380d4040803c4c1c980078014000398150709000c4d19003080220801400c11440e0580e13000495641c560b01c0c0013005028110101001449011809155031801c544a4400c54000e9080490014941100450190000481c50003807003e80c18448002c100301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194238498 1250 194237248 194237287
    0x801170c090405190c05130b0904031b0503032401030513030f02010603061d010b01080411060f1213050708070f05100302090901090221040f0b06040b06070c0509070c0308150303 78
    0xb5404400017503007401d00f806440301d07280c0d5600807944e0400d00030810356101c2c054443c1d002501440d14810142800c2e6503030240c407a8145009209110020411000a03c0103584041a400003c250b4482200020045050300d2068a8501401c0001844540020301a054400201c3c2c0140004102566a9112402101c01c2041656128250f1a520451945081c491a008007000742011111400d10780c5841c0122000c5c6800140a41d10009448003042c10507000d42d202d00b00b0b001503c8189240c40305180c0c150310a81202110385100743c20700460051000b01d0450b00780c07260560541401458001040031301c1c8a00300030b00c007e06900b04240011a03e601010b140600000000541e403001c4038401c80020074060f11038402440140b01c14480050041c40c1e4030320304241c101d10020020345508001800a190794a515640144001360300b50410808004070070480e0f5040301c502d0301c244c1ea201c03002d070769800d05090002d0008a03900000b4a40f9100210307a0404441c0c05001c0300d091010060000c001c0804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194239748 1250 194238498 194238503
    0x105010314090c0120010c0c11030d02071e12030e040e0708031210030b040b160509010e0111150109090b010806060609060d091209030b1b0d0908070602190801170c09040519 76
    0x1408888c0f030107220950103002209001500102100482484c0c02900d4201502407008102414601072440400d9951420f002c1c041659008525400d24070f4043c0c40000e4070342c00b05020758180340022200c140f006c0307004000c87d980c0c0b1000d03500d0400d4070f00c0c1c0c05280c2c80b0014026400031084840100119039014102ea20840c801c1941c400d860801d010403864040562000d0360402900b008280700590748401005e80038802030030003608038201c65480a0816000300420800c100c4690300014402c0540e4004c040b90074000c016500c0d00d0798a502046488035000c4a0031a040581002401d05508114004040704d11400400140000f042e5888070020780040c4c0703032400001c441420501c02d01262080140c1c0001d50b942c2d4030304103184a500e17030b81c1c031600400510300c030b9580d0784082400904c62392100700e42100d42c0c40702d41155140212941c090b214446008500001089400041040d5400707c8900a1000f410002450103a0715042040310000004004440c28040c421010710481c04a01200c0c0304c051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194240998 1250 194239748 194239757
    0x150a1803080c3c0a1b050f01050304020906060906120f040209090c0d06020a0324060206010e132402030a0525050d0b010908070b030105010314090c0120010c 69
    0x441990300346072000b00600011400b4003d4901c10b01d000345076040701c603c2590680306142d000d004590150503d000702030040d01400c901c810310000c44c4044500413007590001c90b80740c6085032402c001103819002c202c500075080741040c00400e4544c40c10300003505560300001c01d544d03d8540409003408401c0d1050301c9002ca40f0002c0024001140b42c0201c0143d403028552000b0040158000c0008542009070180070b0031481c1e0004600c0f0381d440c401e811510641c5011000c0c6102c2c03000380b00543d03c1d81d001d184505001405620008107040004640d101e028451035a0f0304884160245c030b40070b03441c017003007102c15005e12204203885054803114005075101c0c25040000103079070b10b0580320020301c5d80300420003900c0101c2e100c407022000302c3e044003e0b03d8884401440010b000440400140e4406806420414a17445100400a0350152100040d41070700c000380d07801e001791440d408040c5103003d001d9514025980144441c10100d5204101c000c40c2e996040c11751052040150f01c0042c01c40750704540328400035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194242248 1250 194240998 194241007
    0xe100603030914030303040222060b07020406060207080d050a0504030c0306050f0f090307081602030312100806040f080c0106380702010c12111606110a02150a180308 73
    0x5038200c00240018400d050814414404040019440741b00040009200d031030345950703500302d51128400c2c040c103a100160080240a0f102c05404040303410440040f4481d0342002000310700c06101140d071204031032117000144100c81224101b40c030240c128145203030400805000000208030070414000085010b6040020705082001d400c1e402400700404815071003400c9814807001903400000c480c0b0317154105d02042c1d212100b0102200c04014011000795062201150309800c6000c822030300d038001c4060000d80d031015a69500010340f140720803200a802045180c0c81580882d000800425000314032600020340700d500e80c8000d5500304042d1140580c00c004d0405141220400ca0444d4902c00161401c1d80e42000381d542d000814050580310700400032840921080005409024140300e80d040c200c2c1507954010000b03a504100f1100d070303c1203400203910118508880c200101c0c000f0241d070740280520440610248406c0c09951000340000200104a80c210860201d000b0110000c0c40c03042d015103540e13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194243498 1250 194242248 194242253
    0x30e01021206040e0a0b06010507060e03070803070f0306050f040f0e010f0b010e0904023d020c090c03090a0305090303090d050a020906061903090206070501182102060612010e100603 80
    0x1140d00d90b0182074001d500000000001c1b50111448071303070100c000d00c1d20a50b01c0c1c420f4680301000c0d108220089016202c049504000c000c03940c2c010718030502d016503078001b0704025050300b1810356003240f16858100214400701e03d014281074020580611190f640810040c0071180400c0c01c482940040280040c3d9904448002d983e000918031029042103038421200d0403d5000149219006040143c6000805501043d0002e00c9550a441c00110440c1b10f100b00c0001c40010707403600c81040c01c051250342d10320000b800040703100003500e001c0d01c250310081c8641030707aa0368103880303650080c060385038076110600c078080f100d503034a580e2003c04510641c007808203840544140007207010064242c5201c2c1e0800e00404002c00202449585d05882074a00880c600b00a400030660900c03c105028041c0c0d42030540d080d4503d0800c1406487d0075104107060b80d100c4c4075206404445803c1c400d032450041e042000440e142c1d1400301646140003002000004444030480c0e00c1d80e02d005c10340714501002584801c0204203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194244604 1106 194243498 194243501
    0x60405121312140d0c050601050a120b04021207030309150c02030a031b02090a020307020f0f030706051e04030207140d02010801051009180b032808030403030e0102120604 75
    0x10039484c007503001020500c030890145c0d807a01c215400003800c4e05126160500b201d000b4080059002d00e56035460455410240081c1ea01141f82c64001c1b440301406d00a03800214460384a40191600e8503900d80e4800840c040c4c540300f031000303e03003c2c40050788002ca0b40745046981450f08982d00c112001c0c80c101c0c50404020b00bc1d41106458007002000c080550003180195040d408840d02d20340c400304481d035a288000c3c2c840959801c144014000244140c0005070031200c00c043e1a560070410811103141d0403421601580180d000300001c1240c00400a03020045041c182d400440507085034001805c40401031003054007428184101d402098070501c4480041d10012030820581c10540b00304030b024180200c1381e144280181e81d900070881c200903500c0d10000c0222044041000c5454460150030703000100306600749a129515001e000c4420310007440000742424a21070a41003ca05020 = true := by decide +kernel

theorem cover : BRFrame.Cov 194064748 194244604 := by
  have h0 := BRFrame.cov_init 194064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194064748 ≤ n) (h2 : n < 194244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
