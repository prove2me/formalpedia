-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:09.416656+00:00
-- url     : https://prove2.me/submissions/ce7b52bd-1fe4-46fb-a1c2-a5b522aa19f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819064748 ≤ n < 819244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819065998 1250 819064748 819064789
    0x1110304060e01021e06070f110a03020607020d0c05070509060a03080d0603140118080a02070f0e0708100609140103020d0c0c02031b1f180801150e060303070b06 71
    0x25259100107000040354040c5a000d803080384581d109000340c00c104500b05044400042000e542c0f05402150020441c0d0414000d000301c18209c0450a00c003880850341440c0280c0041c0a06e080c0901c00a1402c0c1e00600004c081103904180c400010340702140c2c030821240101c1c1e25400f283c07144030000e60104e113607a00c018104c2c04000f820f12076105c081d410038400c036805245019050401c41c62418203890440d075400301b40540c2c0c103600740000b0300f100d800740000c0103041c81102d110b142c40380d090244c20500c0e03070001d0710362104407400c1191131503019458540c01a41c104074004031314940b0714080c0505101c0e0259200201c82c4c1c1c40d00c2c1d0b4807640f003079043d104040e000c40c0b2306100071060030030090103144a08605a00a001c2d4490301026040c81000340788101001800351808440100e80b41c0181a603085900710810000d440302420341c02004030301c40054041754000061600c1910725025030821254016001c0104e18010081d4655011080d2101160403082495040d031b01c078000030b295180f5105440d007001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819067248 1250 819065998 819066007
    0x3151c0c06080c04031a1801020417012f031b16050c100903111807050a080121020904031103270a030b1b09090a091a040b0a0209011103 60
    0x2891045440c12140e003900c8402064031002c0c421029486130780000752905501c403400a60103c2c009070001c0d840000d0200d480c035810800380380c4c1406da9000754440640300c00604044100e9000c02c4c4107590700c1c0d5503813800c3c0345554402e0054502044070401c0305002e1103040070000504d250031030b04800c0038201142c0d230101c0d912100f4a03600007070004121410755080c840c0d0003000c8941c1c05c0466500c1e90000303061f1200001c040c5180d59020340100200703002500200c0d40c07480304000c00c1009011500851041d1034840c3c82d80495440140814416408103161890a0f982d148610041c600c1c40718485405a42841c69683c0d24101540d42c44510038500185200c00070340010071800014682803c072051600d681e0601c02d40300104084d840007800081e28080c0c00c81c012460240340e2180e640b92040e046000d541c1002062800203c01d18011100c18001075241e5038003204208002021141c00c8080ca4004020360509445905a004005002030341c41c2d580001c1520761a80145e140c03421480f084812607569 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819068498 1250 819067248 819067253
    0x307120f0f0201090c0b0d1404050604021302030105240705120405194b050a150e010f0309082a0601030809010f051c0e060a0c020303151c 61
    0x904415800280001c42220104403920310600480c41510741116100500c01c0c10b100b085120350344900540500c5039968800c0c1f000c5030a0280c0e4441c420b6025101404c0d6510703240c01803200030302080980710f00c0584100014086951250083c00c2101032021118503c0211200780304030501c5100b03c0500075202e030f20311074600e50030320750020720940c2d00548540c2400303181c40e0300b02c80008155006d1840c8040483c40d80f142162101404145820590303000c0091174915440c181502d1030149044041682030f4583c14080c0d4241010b00800401100c0340d0011380b0000020001c0c000d100b0890500d0400c08404a80c0d10400c2c031a420055000c2c0d0002078590707403441809413243c940c4034005030031070490800e0644c0000c1190003140c403038101d81d04441490f10b0407059000440c5c0c402000301607402031120500880b02010000a032044527600712102c0040e946082810251801d00002c0000c02c2030383c00c1915030182c00394080180e07500001034882030000e134421040050031038103089414010964004411009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819069748 1250 819068498 819068507
    0xb0d110c07060212090904112e0f09060f0c0809040e030304021c120513170a050601291c09080a091a25050f030403050c0d050705010c05030712 63
    0x1150341076000c13140d081406104840c0d44c1d01a94a90030fa02082c540c0004021030340701c00d8003000050004054402d041c03c61a00300e02543d01c0306441001c10094100c0c1ca100141e0002c201c00c103441e54904240120601e0b04500800b820702d481002010007051141d20720800c040c10003034402c9102c1c000c0090020042c000000796503a003080b94140d220711140e8280701984203103003030b00360400c58102d2100c40200002c000c0c1954540c2c80304c0b08100e001180c10070009801003225505241c448040c00242021114a00b4814907200c01031708002400c00502140505410b040e000d031501c54281e1084090300c1d1011081108007440c40b03880c4071200c060500542c5c0d010401440024040640300703440704007820351030710101c841c0808840041203c00c0810050041d6001081f1400d0000040d00c81c00d0113821405540c0f042c4c06d0403120565a142507001103010700c1045002c0c48800e080d20801c0e074880d80c110b00681c4450356982018410a414003c4079510902404000e20440f6201c541010304160101300c907590090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819070998 1250 819069748 819069763
    0x11803030b0a050108011e030501050c0307021509100905010e0613050d050309031b010b10081008010b0a0302010f050d06030809091303020d0e27010503120c070b0d110c 74
    0xa00003498107500800c40c0c64070040300825608180e4170420540c1c20007880007a403a0103280800c0460381070310000400281c090042a00c124485100e0355201e0030001006803078400c680281d10141c0003014108080130500084a107806a815580031441000e00e0030443d00515244543e44d540d80503420401003036015015412200c1c0703110710700f1a20589001d01003100d10b0700054450101c19001080310300513112000d840700c1c4124102c80c00004402d00080c0010380300320781c1c85221b44042002c0c04200064580c080750120000e0144000030300030258103900041003051203001c000d05010b845030407080d100e4868000c3c0c0d0001542d941c420450301c0e480b400d1000c0285c110441d06ca214911542c0000c202c0000202d11000301c96050b00101020f03030301c1400960f440c1d102120841c1c0c001204204241002c02c13000010105a49107552882c219410b2030245403e02030b80c80041c144d0720404100d00b641d0344800285040444e5a030850311902c400801d204540644401308082081e00404180e07080031000201e240c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819072248 1250 819070998 819071003
    0x130617010501030c0605070b070518090f0f012903100b07200a06080f0a180602210601050a030c03060b041401021513020f030102090a0f0609050a0f14010207080118 72
    0x100e80f519031780d250072102e43c440c0482c000c04e140d00c05800300c1e503894003490142c81e14103a410b0400c0003131604140400c40d80c01d0129064109661070805129221502c46011409040d03101000121040950110002d03804034250555900000000142c002901c90038800701405202c8103a981d40e42c007030308006e564511003901c4e04a402000b0781610f50b507403400c01c407010101c1c0c100d51507441c0507607584288100901801000c68084940340c01680701c0003560549a03150b01071041c400140c481c41c2c1001c4201b6a211045c5000d04030740001c5050210356a0442d080d10605005c0c1e260100300d41d11144000c8000e44500d900c1880f002c9804140802e1404103141c405034500b000703074203c075079142140951500f1501c00b603d20103686051445001e0140c20204c4e070000c08441d01400240c42c0c1901040403501c0d900c0c2a600246145508000601400e64000104401072004850010302903081003407809a545c3d0600c14502400d0281303203a10901c2e4002d00101c001020b00a008005800c00000e20405c1420110002c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819073498 1250 819072248 819072263
    0x50f0a0e06070e01030b01020c0303042706062f070902120603010501060e040923030406020607020102181c021504050f01180303030522030228030c0213061701050103 73
    0x34840035090028000d44100c031035035900500c0e240500e00540041c403010a0b074034110b01034506c45501d180c0702000208002c1802060a06200790400b040c005c003d07188025820381c01d8286401040f4507a405030700721074140c9413000301c40440c0d00d2040751790808860546150301c0c14000c0c450700098154666024107446590740c0543ca03010b0381e0b0351003010b00f260700902601b804500f41c81c030410111300b0700e507008030303501e511400072005000c81d56242074403003505049a0000c1a8000101480750b681d042c04603030780040071400294144105034058038641c1ca0b61543e024010100e00f900381c0c0c0c802c940c403060702c0b01c0d0b990042c05004103590600c44070f40320303030b40940581030107000d0484040c0010752207908000111411482c513122a07905558085003c3d0201a14208043e101d110600c24002103000c40910958405e070000e081000000b05000c089810302c1d450888415400d201c0440402c1d0400088041c1940c122120b504070712104914000810b41d98001c1c0d400c00800401c2d0f44180c40781540444e05a03400798030b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819074748 1250 819073498 819073511
    0x207060606030b1f1103041203020d090b04150306030204140108010c0903050a08030702030f0a0903020405071103071205160b011a0307210b040c030b1806010c030e060c01050f0a 78
    0x2810b906a0301c1d042401c41d0420b81400c0c2c40c9800c2c03040092498200c4501e450101c0340b2481041c5104e145400c1500000c443c4040c40132820b003015010441c0d40e098050303908107081c14910b042e007152285d00451040d8062841c010758030302880d80c46a400340307003e190700510400c0700560710f8814450f0351109014900496103002160f170b4845e40a81e054200f10780d484001408501030a6541212540000d002c0406501c424000c50003c08824005041e01a81075501c1904031403460040100b560b80240401c2e044c45140980020901404000c440c1a0341d0071440e8081d02c40003180040b070b02072003944178980825900c0c204400411501110290480e01d180b020001d204680e45551007041c071041c0e480102003005944030100c0c603042402c0080398103044034000100c2c1c0c403188000c10244c0740045580d4000a90f10481d40c0d01e940340c01d02104400807405034241002c0e1400e140017803e40d40740783d04080c0511030301d402d45514680e1880210380d1300010f0203000740b000e420071b41110941104140d481d10042c600b8501c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819075998 1250 819074748 819074759
    0x70203060f090309190b040b0d0f05010609031b03170408010f020c0d08070207241803020306010b07020406050d1419020307060c03031b02060702101b08090a050105040602070606 78
    0x1d0800b809003a001d0040c515000c124003c10048140700d03045c89500d24100100094400f4150b0094002801d00b031103e40e0f034a8500703884010403103403801e504001c85442c0134014000c00760b0064645040e0b80d4400c0000c1450f5544094400698200fa440100f944240c3c0010616840d60315000c0d0040310341000092007410039914100d17040e030082d50540101640088510795410380329410131134000caa02d0041c2c400c1c990f1141c03072100e07031440c60130ba0300c81810000c00b1308004410b500c0320010382c4124070824030448131411540000d450309010302c10240003080c003180010075965180d1040c8004d2100401200c7d9050341032400008d104500420090907000e02c0e18035070800040c01050360380540e4010064441d0a040c0b00701540c54040f42c2034103808059594000107418a08142c460b0034090280d002040c5c1d07840c020304000e01e85008070b100c6041c540d04105908054100d0381c0b180c2c424801c0242045220b0b507079440011440c2081d1810090520343c246014441884040d81c020181a8040c9030140400341c2c840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819077248 1250 819075998 819076021
    0xf15041b0f030b15090604080a050604111804060f0e0102070606030302060123130209030d0c05120c07141f030b0112110706050a2c160b07330207020306 67
    0x40203440c0c00080d4468039130164402c280080c9050400201400d0405807550507507031a1071450b607021a041d0380484240700512400034200e02400c4001c44403461030f03600161b91004082c401400c018403442e1200e040504401250308005110364a40c002151902c61900b40880540014402500503024500011820342c4041c140d1030b002d80c0c00448211060700040f4144807081480c4101d090642c3d9007030100da2401e40d01805614450003040da2203003548042400c0413400d10490a5014440c144102700314000480302003240c204451041880002d29062035000c42d8050f086101902c491440800724080c5064140d4480c0d540c010080e039400d00701d81007140755a0226101040d880001031301c24005100041e03500e03040240d200050880101d50b415001491102080d04c82c0c00d41e44c01148200444517210004000d100754240310314030b5205000d40b404400d01e01c98070a0f44400b0301224401c0c2d07600c4045082c005540d00000030310280800c40b41c601e80241c40002d40107003000328070a0040d58003044413070b40c94 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819078498 1250 819077248 819077261
    0xb01030c05011112030703020403020409211e0311070501140a0506040b060d0b1f120b04060f050112150f240801140f12010509060f0f0f15041b0f03 65
    0x1054001c0c481d56613220710408440e0001068101016000c21002c001600d0314051607007210721454041640000440582d0001c0e190801140e04100e406815841e085411070700340d003880503c0742400074003611254428205480b4008014084e5800c101d00102c1c82026030099a03c00d0030041410040360f00c501e4104801d40d18141c1007198491400e00c5a099142d185078004900303070320300901060307440818004010303044443d0310b184008642c6810103c08250081d024a14058000b1107080100c5070a20885040c200311070b0040320704000e101c1000654050303240d4492800083c049192080c04c6945007002041402140101e03e000728251000040406021b02914500d12076521f0b0000305030308043c420440c203001c2240c4030380d02000c4c41c041c0000039281c0190101d0818142800410546480820585001006080c1042d13100c042020000352040c803440c4647c000c4801341c1000c0da59220aa800d414466000742681d038010b283c80e903020700c0e05410b02c030186100c001584a42034020800002902154003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819079748 1250 819078498 819078527
    0x160311120c032b0e01020c19080a051e04090501031217060114070b0a02030708010f031208040c0806090c03071707030809010309081620030d0c1e0b01030c0501 70
    0x7003406120101e200f0070030f09160040f03410069501e4080b00c14075440564100c200030810076540011410003680c0203100c184185000c814000c0e1400003076a0b540301240c0301f18005181040404155043c00313a00700c0050401114480f09016200c0c2d440307200c0900203210a1108031041c013504c0e450361081c2c5004030400303400ca00c40524002c0041d940c010065405021109000d00d00740b004000d0100061190050703140146008800141c8030714008502800c850810313081340d01da40341700180800019201700c80d641540742403850001c1880c4c49501d0220840b00c0070740c20034070890240000b00480d01c0310000b200c40c0304e03440803000c60760750b2540c4080d01c5109050030414600ca9402c225020320100c0c003040020200100180b5000502c08104d8441c0d68480e00100c040003001480010541c0c10701040c0e00f0740901409416011030791403007c5400007903a03041c94000300b038180280c81240c00180158102007942003030400e503c00d00220302525090454000c24003003290080056480030546504c11400001c4044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819080998 1250 819079748 819079753
    0xe280b0f070228020415230907020c1c06020d0501081b010e031e0f0d050409140c03040605041716060e0105011412032502091b1608160311120c 63
    0x1052a02404007800b4140504030460000100009404001c00d5901500c3c1f408554142e1901c3c01c0842004540d810185ca80021544159130000069903403082030004c449044045c80c01886941c507008019000c0d4404880040d442c24000203016400801c0306030140036050410040e034a92400151650780030881c0b030b41d80503801130001c4d50560b40d1101c034205020107004100e400ea12050706000346080900d28903500094000301d0108001b040324000d00794401d40c4400c000d081c501e40340c0880c100c02c0c000100082c0c00c0c2501e66010a00380404002030750300344200d140860356910701191008030740035600002210554500300a1002d01074040c441c0a0680c1e00071112861010311702d50406c002001c2c04043c410b01c0e40410084a204044046200001c12100700e00c00c01002d04079004016406800070034a01507180001a00341d0908070000898007001e084c0070140003400b6003800c0c551450f000701d00c14441100541e0307078103000749508421800b1401709030710101ea07680010384504440c1d078020300c40a201c2c0c0e81e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819082248 1250 819080998 819081073
    0x13034b0201150e070309050f06040c05130c14030403050d0501090617010b090c0f0d240e130611040806100305210306010e15031e07030e280b0f0702 65
    0x11722a130030442e0b405000740c040b2014078884030601b5080c840c0a0b07608845100004508110504103515201c0c0c00c3e4444442c10042c9003c1b001c0041c0091008842d01c90305124004002020540554159009243c05c000c081041e503031103891440080655025070380f0180d00c2048440c0c3d003501c0c14040c03070f4100080a82980030503124405e05086941003071250600300381c2d003405414059402d510400b880c210303030083c03500c0484043c5580e8490382c4815801c000300581d010402c001c500c20302544a0700c0d00030740c46800000c91050802c40c1400900482d04613444500a000502c11554500030364113094034043d009445004e0542c90503104802c0781e01e80c440b400c4820600c00546250300810250070814000303090449000b101c0c00c001c25030743d48203ca075030001e0800b07462035044a0992340d80040e032081841c2010402001c2d03070007000b41c4e51500303003500c6105426885804249845a8000002c1c89680070103241040d04150711407400e840c0c01215a400184140144204e410b031500f0300c443d000c00100ac8105640 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819083498 1250 819082248 819082261
    0x10020a0c08031e0a0b150405031e0304080f06010f050f030d03021c090336050d050c031f050a02041a09030a0803070e040513034b0201150e 61
    0x382d0002441e0706207622000c024400140141881c081c0300d28020600001c0d504400d600701b22050030b518164143c500341c180070502a41d2400204418000c1001d10710940e0140c00340e40061961149401000b03d80c024861408100000081c44505030384101429042090304d5100707110101d560640aa03a142c0d204004680c0842d01aa0081045170f00315800103081c1042080c8400580e007032a6003c1740020175040003e03109541e080e1100845281400340250007195420103940114124000c0c0d070300c103801020b140030401408128034590340e07602600b9503e0741c14101c61f01401c0309112211154180d410580050000b41c2203100311401d0b1500f501c1c000c80c00020100221246800175910035070035111703080040b07004c684240f0145101d8003181ea148030b5041811000d120543c0c0002d82410303d0a00301080000001c0d4015180016254694166642c03440c00d8900140800043d2481032045540c00b100034a041119010000c4542d00c0c103030000c0c88014000c45031092801450f00c1000494100d20010411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819084748 1250 819083498 819083513
    0x9031110022802030d0f201b01020102091036182003180a0215070512030f1806040f03110322141c020d030908060f060310020a0c 57
    0x71514140703100b008030b40ca2103901080c541415004100c0105026504030381c3c4290b48001340050070403010140c1000c03056403480103035031902401500c6404003a0f1820344c0b4032a034800d50540d100d00e58000c00c05a004c82c41d0340380c050074954803003094140808540783d00308c882c404010101c0c1c41c8542082c1c0b4040d01d00e4948030390b61ba12010f2400c01301140b29185d015007523180340761540344961400340540c181d41c4d90030b04100041c0e841d100c814030941c0c41d4010f03102000142c0d0322414162102c1008000741070761103010b490524200303d95008a50145e0f94080180000c0444a0812500c5035051298900303104550215060ba10442110000c00f00a081410907001030b125040c81e0409101810480b400e28a80c4500d00144a100362600104008901020005071000303076900c83c40b0300e80964000b0116401c0c0f83da035401c2052640e0f0041c0c098100c1c41307100000c0500c80c1d50400001c015240035984a82404a01c40c1c0c8182400c0d00e00900c82d1150703035044e40c1c981c602c030b00c221106802035440712006813042e0740d02c103072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819085998 1250 819084748 819084793
    0x9012a0803010b3f1e091f0603050304050d210e0a090902030606130209060c0102070204061508011e0302120102030406050c09010518040e0f03030405011a1309210903111002 76
    0x403900c1e0380c03a45c4c00b4800c4480c0381900c00c2c001c1445601512000a950140c0451200503400d050310b06814010700f04041100842254150b580c01e4488a8241c0300600700003294040064021100007480c55001035000d61000a810003c01c084400780a000e5460b190700c01500c00741803002e941030304000701091003032500c5004540c201d1030018002d401e109070000007813400d400000d0706005603500003c000b0210300d00352190201801c5c00c2100c9101d0349285a40c0148245014083e10f03140900009039050503403460302444000f075500501c1071102008481e015030107074205460884202c3e00f8200440e60043d80789058554403101a96810b0405003c42061564054900d040c40e0b007040d9201e4460405140502c03c003a00c2c220400300443d40c0741030624105085410000c1c2d43c00f0000485d000000d10b40d681c8040d6000c81c03030303955803011450b0402401c0c000740381040c2811150404500b1713041039841c0343d0420508001c40380600b0a149144064100380300c1e071035001c650701d0801a0484000805146d81101200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819087248 1250 819085998 819086011
    0x9010e0102100c020703050105090f0c1c080a0e03010e010c021b040e0a0f0b070c050307062c1b18040204050709080d09150509012a0803010b3f 63
    0x1100c1910014001d02d0484140800c00e40050300031050070300501809004460304003017a100207100241d00941441d440b007698085044c0300710003104181d01001d901061020020b47c00244069583c40c400401074031005202912500950034500e400032200310601c1061002032403900036184d15450b01c08139000d5960b03410000da034030a50b03840c02900d41d40300c204512403203244200c880390b0400d01d1a0400d01806140240381c0410400c0003400340000031008015a015540d01401c0400c3c1d003806020b00440009000c4000c0007130120051203070180020002e034151500c50465440094400080d05003e41c4140180d8004288904107000c28018207003a4442d0394030000910340028030b81d450b14280ca0134022001c13501000610554010300c0032081503000d03080c804507603040103031034140701e4800a403400b01c80d08211481205200c00a10590310a812010079082c0e106170059075940c0c4070b1290036404d0b0018022a4852058040d010324075144800401c0740307400c00c081c408507444210700030001d4901d1005116 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819088498 1250 819087248 819087253
    0x3060b18011403100501090b0a0f060c0303050703061205100b010201022701050f1306030513020d141e0319051303150b0603070c02030f1b04200a17090304030809010e0102 75
    0x811000101c0d03c119801f030b00c04040b010907020010420000e00c800e542c1c105220003e6009010441103030001c0445d1080c40d4141400b18060343c038428203600521940c0c3c07191416002500030700d020080040f46800340f640550504001516aa0004900f08d00585c010802d10000745050400740e00c6886d803a07510307410f00525105151a0751003140400704e0f085590041c0010300020028000c460305406107990044040c00c0c1d40b40d2009403600080e211520502c0060001c401c802e9106400c2942070141d0312141c40d000c1c00080901480740462603a83e44882d410000302604080d40381c2e030f138a100d0400c40300050f181c202c40300f4410713041d500c40c600003200b0341400070103166981c2d120910540720007000d03500c9400291520060b41019005042c10900b009002d0003454000003c4219000b4040040513840c44043c1d03000a01d000545280721501c00c08cd0f070040c007030f20300041190702e4580d6101ca210049031284000c00d210b2502c800070025501c2c003590100070700d01c020610144015520600d0350b6120030405104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819089748 1250 819088498 819088513
    0x50405060c12041e150c060f0617070303231207020a0f0b0108060a0e0d030b0d0b160f020c0105070204020a050d0606080108150f041707120903060b18011403 69
    0x3940651080e4002c1c41c9801d4a44c1c1048022015100308000510959806a52514000d80c004003901c0c0f04400c001d00280da600b040000b40c141940c81000580340c0710419006e924520100c0f590755024038442100010068155820307240242107007030b54500c0c19643c845091483c040100b86110384001c0115085102d460880070100d120501202601e81c00f420400d00b10b0350519480f2410320a00409541601c0c0c104844607040e000001803020001c407452400140c650b03900710001d10b400f502c50401901d4101d5003000c0c02440d407015200c02e00751140544a60701807d0b0040380698481808525950116000344024030150405400404101d0340610f801c0b40b4151700c1200d030314200e8056400100005071202c0c014040b0a6041211440440907a03039402d0740c529103c01c1c900b24000c00280f00070610394107030707060207400c58021050380c03c6280d022400c039071084281100105444404d00c001da901c9410101180004d0a000d186036100e004000c0034584c0342c1c5e090426140c1c1c0d01000b2880550184120701 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819090998 1250 819089748 819089773
    0x1050a0203190513080607120203100e0c091018030611042106050a09230a080a0f08070801080607030b030708010f0b0a0b030906040f020609041103180607050405060c 73
    0x200101420703105440d01c3d5140c1c04100c4001100c400d040c0c1110040c1e6000c1c4060003001d0b81c0111410b505100c0d40480507a903035550b040043c206d6005a40f00a00e164005001e01030071103810760250442c03140c05e44180541c50014842140d40d10b42101c4100c41c100100c0c0c900b80003242c2da50700820a444075405c0260320f00390359502e168881507105402c944400d524514040100800c42c0101500040d02c40024428111542c4840340c0860011407840c055088851030116075140501540d540140c0100c400760311030145540184c2825a03610400b03000402d140005824a4050004070b03060328221401000c407544c80a070103400030516090030b168140300700f240c00516508240101e00b181840072501041c800b125205001a145180c1c201030200d43c41031040002d50480041c00945c03203a0020b64001c40c14407180086419071040d42c0d03a060f002400c0411400c4a03004a00085005100c0c40e50902da48000b00c51009460320819110380000602c20002080180b070000081d1000d03030054803d80c1c400d1103210 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819092248 1250 819090998 819091027
    0x2070b0a020f06011e140f15070b07020d05180120150105150a0f1107030c150201092a0b040f0611030a090e040609060504030302131d0601050a0203 65
    0x8101100180e002d42002c18102c0810b001c05801082071503034004003446401d1141aa046440c01885151844944180710507a01c5107070407078035410080e18500704120152115a010f50000d04c1c16a0940c0c1543d000c20442440000c04140e202e1141e07848034100310044170311103071440000c091541089000021108140d000700301e0046d00804c120b0003401108248a0004c503e81c0c1c05910031032068102e41302111003a9080310869404911915000d4003540e41100c05841e1414000d007492240d00c10700f0b201000b00b240d0000780130261801e2086640c2003a240320822401d039802500c0081c4000b56880303940607200aa600358100c0b48840880c2e00c59140c1c1c0311407014500e40c20175801035846d1710135103404001d5603811000f8540d410b485038018602d0700d40c3c1010094161622445132108400010000034280b06184d801103400c15806441440740742003900b4000c011750049203240c45902c5040340c000804403e8030310711118081c002d015903082036030346200643d03658115441540540c00200046407041161 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819093498 1250 819092248 819092257
    0x608071e050d0f0506211c12090807020906040e0c090a0b031015050d11060f0d0e0c12150c03060a0f0f0e1e180c0312030f0c030415050702070b 63
    0x40400000340c0786005d204022600d03140c01c55194100c4c0e10f280b9280009a00400c48194031500c01c881c241c4000001041200e0080000c0302682c0d10743d190401050030404024000c1c0059402203580078001d40b100001c100459206903c007442d2035000e01c00f0000c03a8205045800d900c031080b05800103aa642d04400320b420510340c00310301c9400c15514901c0b042070708500d05100c0040d18041e280008071510030303645d030481d401d0201e48892064001044000c80382c00d400301103c4414000350800e024407120704461179510000411000c2c070890116484100c0c03402c00060720b00700400c480c030100d521a294a51850700c181d001034821a0040c1d0140300225507041d4143c4183d0003004281c104403050303807034406080c81400c0042e0000c02c4160b50050b120780c0c00c01840004030703000b80c00c0e0000b054401035406000d604d0024586947c9405011380c108000d4120310309406140705030841d26505405990701c0b41c0744041444100c0c1c1c01070141d0010510300003c2002c1d90b10a5602160318012034800320303211001c910b01a0031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819094748 1250 819093498 819093521
    0xc0d15020d02040306050a0b01050301030b1314030d0608030a050906070c031b08060f060f0f0a0317130909020603045a021c03050d020a0c05070608071e050d 69
    0x2c001808004010175031041562190700064104840380035400003c1c214131040c40081e102d44c0c0504041001c400408044094195025401d111060011b6500f1900ca0b002034010a0216280100c009a104008070480e00d02604958a041c0f90020490400001d03400001e81a6075244102c04040001419601826014464203007250140740c944441c60380307880002001452100301c0c00c41804203070348440c0f0b121700c0340c04401c071250009580810040384542c01c4a0380040d003410511440301001d20032050043c4042c0d105089017601064417001c6c40710940c0d0851000941280f400c00004020900d00f07a07441e21014894200641200d001c0742d520121140007402441e5400305030003071505a81c400030b0140b40c6021030300ba0004141061500003a808001c131040f0044695003807641041050300c500304a415103070040758219121034016900501c4090039075070803206403060101c045401401101c02d0340c400c50003542c5103000322404040176080c1252014a20b0f091003824082100c00043d0f0f80a14030034000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819095998 1250 819094748 819094751
    0x4080601030c0603091203230a0509160f140a15031a041e020d06080a05070303030c020633090f090105180c0906030c030303090a051e0c0d15020d 64
    0x1410750521122400d4550720003001e0500e044410000110071030304c07520a9803014100081d1015089002d00c0300c290700511010b001c119914104a0703400b1990707101c1d41c010502c0c4811556004100a0311b030b29500100d001d0903000c81c00c5401c04100d0a814580c44210012018054090981c3e80381c404004044030200c0c6c09010903220444460500c0016032200c2d5002e20440f0103200d480c03450350304c0c0300e10f10850940258940e42c00042408a90710b107900448001c00740d2004880c41900107091042d191051800101c0000b030074100c2e0b403150680300280040c054130b60900070200c065000002d180d0000d6146802040a082c015034001c0150340d0289418424107024080b11828507110720742ca03007111030052070070229041c8a5046250500300141500038000d040c0c0c1c401440c3e0b150319001034505003820514540c5444008200080c4900200352561058824030403600030480301d040039173700d000011110707565039402400505024a8600004003c0501603060a1100c0f0303100400c400603030b40030180c141c036500e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819097248 1250 819095998 819096001
    0x80c0301110703120c0e0d15050c030103020108070509012303070f0f020a0204050a0f0207050f071212031d010203100f09020a08040b072601030201030b09010b0a12060506040806 78
    0x90a0038010500345100c0715010358905040303994080c24613411060152042d03580c64110110840c05551010b80c1220014038003050440c0502d02080e02d50f02400302da8030b105042030f0104104030419420b0f6410303a5030503102d4840350394886208603a6500521021030400121054003040c8071840ca43e00040e01d61104152035503417030040800f40940d0701e5405034408121564800058990703000c10711010050b412207005c1450303112103851802501d0310130f8407540a28400510789041200020b2501a40744401058496955444502d000c003840c2d500009401000e0300380c4825a8240700740e12103840d0b00c030411341a140004502091a00b260411202d0030442c85c00d159051100c450042c4c1c04000400e6000829864811007810080606001400041007060010003007125030707028598501884005d2141c502295284040840c80802c081c841030707001c40d03e82800952507040106190381625042c06405203000400c0408035040d03010400e00301e185654600003c9059030380d00d4002c100610f1a900200300c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819098498 1250 819097248 819097273
    0x501080415090308222004090501020c0c0a0803031e250819020f0a0e0111010903090509090d0c080d061a0d0b010f090b160b0a090b0702010b01051e070c08 68
    0x15040da15030b1403001a0b16242c4401c00941001070f205846d038440d0022100c0c101402d00414084c00c20104002c100303500100d0642103140001418102c075090407691100841d0b90340d0f850a4991006641c4000c0c44402c41d42019000c090f40c4c1001e80e08003441c22401c0c000221001513952005035403107070540009084000303000c1d074180e03044218070384c03400c140030304500d40348444440134694440d40240a062146200e003013807040e070141200708040407051000340400c200c603190041698265014107442007000a000c100c2c60a400100500500d1080d2145c840c8401c2c15190290181c000340f4884e80f0407500c8007404030b001e4011710340c0c0c03202c80012503200507183d05001d5400001d03144114206410031038111103580945900980d9901250340070340a4a80e05d40941300b0700680e0310306881000d0f05417a140c105001b4000381035400041d03d41d0081d4000222616030b648100d00380c49403415081c0c001902442240c0b100f060210018100c2c035600d405540c60040d80b03940347c03084221b2960105160327030014401c4141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819099748 1250 819098498 819098521
    0x250803100501271e0b161b0605181c14010e010b1c1109010816050306010501090b030907030b04050d0e010203090105040303050328090203070504020403020a0501080415090308 77
    0xf80203500100c1100102c1c1c440c0218407552110b8419103641d910443c001c0010310f528030107090041c04246078510f6507207001a0348880b0031034100e84211407021441211348805542c01d000740741a21003694526140071440300705088800c030300c210002c0d400504090219511004003040381d404512a0440a400074144082242101c41c6800b42222990529699190a03611090080341c0300100382c0c601185a1401e05102c0154104800407681200780c1e039002140a00340091141d066200382540600b00c0c94568080c5a203604003031084334041f621340c10007441514616405107030310020810446d01d800d99692901c2442800658041e00c890b040301c9150440c1c1340d030007500070518480c00c2c0000c61030401140d00003440361140b40700150410001101140e1280300c280354580108004202e002c883c0d0404003004401401d650701c04903c81d20402c003002410b41000c0c02500c0031a130b001801c42d80e84519150041d03a49040c0200121000013102d504800345034503600c0740a040c24000d940d003510503e4582400d02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 819100998 1250 819099748 819099767
    0xe0d031505040903080f070201140c0304150606091202040e0703081306030e1b0d0506040b0a0c081b07260d06080102090a17030d02030c090103180305250803100501 72
    0x1d002c0e50400b107202d00807940190a540e0040900480b0309400e0f900d12408038014084940e041141208200500c03604204900195020b075005400d9202c9403e413429810040340d5045c45200e01144840c4401c00522000d0940070841d18000781012491006201c501703420301d11a40c10842d091040480c00c0c504150703e00a1880c060089810200903400901881542d140c814500711020320744060f0a800c103946940f290b00320070030b43c0042119610b040510b4030340100700044a170381e111503103408104c000c5907104c4d00b84140140b40708034031504203260502021500707a2021f0800d54266a4048000c06001e40b4a41c07000c184c05649010180c032a56000320300c41c2510055407180e0080d0703005200265084d920b50305031a0868041300220b5501c002c0c1d441405085001c3c1a5010f4402ca1006c07042046560070300004085c00c2000341d030100001b404a2600200d08229080043e00040e000d2040703a20032500030860b40c04085075200d6415001d24540d40b1280e06134011100b2041070b0f079004030200301d996080300084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 819102248 1250 819100998 819101009
    0x106030606090203182e0612120e03190b0411030a08040305010609020a210b030a0305120f09060c030c090a091b050f0a08130804080d020f0a03090504020a030e0d0315 73
    0x82c06e41c080e084800002c1c18104400b200e25120f6006d0440d503541266920881c018404103503540b540726114286005040d24000403c0c010900c00c1803010100d103001300700141982185510440c1940640e2512040c000d0010012145103055440080c02075501308071102100b8841e071100c0c2d540b00e06602d0f100c1d080d103030142c0c4481c1d0054018442d01400c15000203ea410700310710000d17816020300c0e42042c14800b40041191031034050280007074000c24554405c00034050311044e50340342180e68450356610045200121045429174000c1e00101d0903101c140e00c02503401044500282d07007000d044500040550b210355006d600000d642c1d1081c1d044184481c0032030b50701565141051410300031030000703940701881400009010000300500141c0d00030404014000810303007280d042c9488a46450415945440802e8085e016116810494020041c006509603a503685541e030300c030f039092400e01484065040720510509043d00d80c50f06080840041008456855255501082403111a06081c0c0001150b0700701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 819103498 1250 819102248 819102253
    0x30304050f030a0f110c130b1c080f0a0c02030607090305011514010f0c200307090203060a03030e0d0b090318120303221e120201050720010603060609020318 69
    0x340e10420340c01000c4513505602c54203044104240340b06145080c103218110140d4002c2c03916410401503005a440b02c030310950141d49103015844014002c9102c941244802095210b04020624a4241c1100a0302e0b6410750760a081a403415540e00080c1010000c41c2c0c0700300002c00c505000c006110702401941218402c003e00950010f0501c00c2503403c60003145805418401c1000444450b50700c602004102e441c1c10042c090f181d003628610300c003503161280107007520a200c3e902020032440d03910310860f8019803004159843d010300e1a501956105988003100750301543c2860114081380ca00300d01c1c140715800f04009550703184c014088200c00160f00d071071210f001d40d031022984800f400300041100e410103103503010004c400051000c0c071a5410901074000782203400028440804d00c003400000e009052298049081a04084100320700300c2c1c10444d070240018101c140f101000c1040505485034030080000042174281d04d82d16110180c500d00da103c0c24a00340e00004100c030042c562042d05004041e035101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 819104748 1250 819103498 819103507
    0xf0602121312200105180f1506040b04020c0105040f211413050a090f05070507120c03030e0f06040b2a0d0902150702040b04060b1204061d030304050f03 67
    0x494246481514048506000c141041403c0303074011180d801c1080b1a2a8000784002d15042c0340c1115804030945070f8050f148960040300310501004a001c164107159041d0059055407200c04201c0039000c0b110085820aa00300081407a0400c00c0c0116489240a0303205048191b8003807800d4900c4022140800b40701c0c02002c603100c0380b0140c1c0403002e000d098401801140d168a84800c01c203028041030762013543c0c009a9030b20f0004502e101c81d002008801501075041141d6503c03244159260310a000e80200400714845444003040c0c0140c40715040e290084c540040c2025603141a03c0c40e0080741042081079900000400041120805810354000b40000c10320940d019098554880c0c0c0302d00c0d03000b1402000740465024040403680d070040c19019001081d6044000200d0f440440c182d004103401c3e4003640c00c2015a00ba01e0405019220403105000b0f03001d031800c49400303c0d240c90210003600840e22643c442d05155640080307240b21010000400c009950780b03007001c0c90284d15051020142a990380c00c00d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 819105998 1250 819104748 819104753
    0x612060f1002031209071d0916050d02060d060915050411120f191a03010f0b061c020903031315090311060304150e060702100204030206030c0f070f06021213 69
    0x650707140e1344441681c12a80e854901140b41083c0058004201c5134800d140c60340500300f0303160b50301d9000d80d40c9982650f21802d005a0305612a031683c3c010550004d60410000005082c010014080c001034088001261a11f030030843c03050303076040098038042440e50341080c0070624140c4150604001641140c51174014044030b40d0741c0310007005019050000c1c140c2d001030644600001c0c4018401040e45003086502c1102c0d5490003a00b2406803014001e40c41c0244292118a02d44100d0b82801c1d001005181450600c5c01403504c000c100a40c1e00c11115024445d040c0c03d61010400351100d1284054035007416400c4c40a82f99189245542490401c40c0c60442080400c03002e13284c402c0481c80a6690a42e40d0ba0341c2e0815a54124550840a00540c54140744044014001c03401e640680819402e4810b15201c3c2901c0806a00803800b010f0750100d01040480c01d00c950510090001004c4c012815007018031a850b00f669018812605a03003254000504c045c40380c149468403540051244040c0c03603000b1581c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 819107248 1250 819105998 819106003
    0x80c030304210c030503071a0903072f0a090504060b061c020a3f060f0509061206070c021507080304060b06040f060e0910050102060a090804050612060f1002 69
    0x20703003248503031911480c0c14020f40030100400ba507008011285d40e86040e1400c0349041890442c4208802c400c0004035595450100894844039001003011100c4030140c40300300b2041c0b59503041807185c010481d030b034a941511030000703400040012045c00240340c5028100307441a40c84910145100d14400c00896600c006034203003602009103101d10050b2591340c0d21000743c415104918806000004100c58140c280c0084070884000c04010000103894003120071030182900e285000c0c40f000c0d29072414041c0110b041408006a100740010031005100d1038002c001d90800c0c20503a00d200008207020b2000d020740c00c016803420742850080c20410714000c002c0e100c480c00c50201501c004c0440791140340342a12581ca0400355070103040e100d001e0100540e519100604845106450980610354010014104140a0074000f0465006030085c00c1960b071800c0180c401001d032a81d045440700e00521020481d62102c401920160404a05a4207581001c108200940a070b1400003403150b245900782d0101258003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 819108498 1250 819107248 819107279
    0x50601030608031606020904090b040c0602030f0a180e04031d15031512012d05061507031206150215041101050c0c030f150a05070905130e0610080c030304 68
    0x3904c1e914040a00b8501d4000041c0c842d02c101c0741d5000e4103241c10801400200c00020740107070301c103000e6010110ba65070340c06d0b6280d0044440c800c0080d882403045c1814240102c10a40300300c810a0b10035402c154680681c0d852524050310141c0000f01692034070505c0143d0900300d940c041e04102c4508002d181441c2d800c100c24030004140e514501c1d00c0c41405105500c0e114014107030940e16a0081c002e0901304106000c010b0012203d4860740801d15425203000840b030b200d200d0013188080c180340203081c000c000a1210fa4001c64046003000200200c29000e09114822000903003500501e40c2e4064008100c024500b07500c02d00080140c040c1e0754140800150b46101c0320290700004e0078129181e0100e03158850410b00c019403803d4150041c0d003500c800301d6034042100005403000400e40c903500e880d035081c0c0f0300c11138000b16003c501213001c0e11410700080c80d1a40400b285e212a005011914403030505020b410f00c28140d6502e00440e849213404d0002003400d100080400c00b06400640c102440d02018170b080c40785 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 819109748 1250 819108498 819108517
    0xf05160e01050918010e0d1805010305160c0f0503210a0e0c0f180108060a0e151b07140d02060a151502010e0322060c03020307020f280905060103060803 67
    0xd03213810030031181000e40068600351b5141d8240c48030f0550007030001d017150b283e889070456405030300040400c09602910078140a568020200092240e402005031568401d03940305036052980009200005182000181415043c1264205c40007002140c40030341500040d00c0d100f5007604043d070081c0809400030b11103035a10000c880d5041420a028040344146914a014032089040c0c2400800e5065000072401c1c0a25021101040a4204a003140b81c482140304030000000c4900f101095215448020554107001c0d94401107141c41015503d4000e80402400b000304240c00030081000d00c030340c05004885c0c1c0240800d4041c004c0903128404d000380035186009821449480c20700a8400910035407150f600c4e25030070340c1107e5640d00980301410054140d0751a00d151600c43c51800309885100d01d11615006500d40c0046007480081d9003044880b851480303a1942001241200004d24100030480d80b921040c80300d032650341107042000b1f02d002d80c0c00080c000c505060810350304000c00c1c00d00000320340140a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 819110998 1250 819109748 819109771
    0x31f0b09030303061504120305180a0501090b031510083c0901020d02040b19090608010b0705010e1c030b03010903090e070912030f030b0a030c0b090d0f05160e010509 73
    0x70444000b0b034060041e40c029195250302030781c000b010160270000a20444100e070030741001807034114041160001a50003418006514104200140d41425001d1900070110002120740200f495005c503000c4820200c100002600120502030038583e4100c40003a035040040f900e501c04006212021801c00300fa40d29100041d0524000030401c55080d410b80710b0300c078828282035680d03070345d01c000e0b40045402c503619010040403c001202034807400303100d06d02d0458140c1c3d100c2520f280e18242040c0000e4000c81c1c0c0940306075481d120309802d00881800038034481543c01ca04100500c0d080b000c024101d0b503030000c9c0705000383c1c9440c0c11800802d82002000701207400ca181d45000750390350160304542c06011a400940740c0c0c002440e200040541182140ba140c2085a070b0810003181c1c3c40d402c12280455502c0041c1481d00d10741418060000075000500030384a0140c041c92019081d40c0e0707081b0802603845000c0d40d468000d801c0560051203610080f800604250980d68503075410b260000d0b11681002c4c00084161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 819112248 1250 819110998 819111019
    0x9230c0a050c060703050f10080d0c24020a1b0b0c09190e040210031b050c0313030b0411010c080d020d0b030a060c0f180e0406060506031f0b0903030306 67
    0x220712480882c2c560b41030200c251030b06810407010117400b924058404c03464403d0000001080712a442210004840c0d44030028400050000e1055841d02c85400003070341d03000021031079021103014640030500390001c564401a40c0703c3c61148010210078803a83d105d03a40800007640440400c40700202942c010f18010700065a0321401e400081081c6185142c80c0d115950403400042c4480210084a100324029210b118601081c403808400b00d80c4d06445000700403d01c80408a001840707903001d0458810003104803450a500034410300d8040c00b06030320465200d240e4030300700420084c0f01d42076103104400a0138880b83c1c0c10303800d80d1031403014009c4d00d00300c0c0202603001c81c503881d0200f4107800606c583c2c0b801a00303940f1010028141341014052003140c88020400b101007a01c1040d100b5010f4030001041e00203000802070400c0103042d41ca03000070340240c80c0c0ba03448510100c0e055071140000c44c09080a030601441ca80d540751070f82070300041c265110416103c01406004500e1301c010085a5108404a40240c0c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 819113498 1250 819112248 819112267
    0xf04090c031518050c09241308060907090207082221030f021b060f0f1603092705062803020103050108060105062704020f0409230c 58
    0x81920b480100c00c4464000400151042c4004080780c10b800d43d0007081c440c641d51000c18060703512440c05c400380c01101c0320f81c00c1c0d54203101034180980c0a44202c007403a0714010050201441d440d00c60340281c42076402400030301406075000c12541c00140711920056003030080548640d07100340120720146218244a00f04804510000e10058014055085401c2c0920803001040e078908805210103c3c003041d4101500d8501d58000906a044c2c1c24a000d01c1c10748035800301d414050b00e500059640030008d40c05106030303000040d800d03000d4841c0007082e101980b40303642e09080c01042c1c00e110b80d0080031201058030054001c000346502500614501c0000440c240d21290b0101c1d0310b00c14003005103c0c070071081c0340070200c00302d40c0d440004084238002d9030107102c140d80702c042154440301c0a2040c00e40c00942004000a05400611181009030580b036810802c030300e0740004241030364040701000c980312a0009040c04407241520130000724504072170030304510a107050700050307043c07038090105c000309400071400741e02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 819114748 1250 819113498 819113501
    0x8010e3c07080303040609200f0d030909060311190b03010504180c170d02010b0d1b0b0304061b361d09011b020a02010e010905030312060112020f04090c03 68
    0x4050384012203907a843c090410b070303000303043e195400c0311070414580c400200004d44041a03480c01c03600a003691009c1070420704111a41c40d0f0100120103200581d2000103e00c3d03160701c51840114060321403a40e018040000b002142941c4407281d610701c1078a0a014020100e02078103490548005880000d210380700d802090010764003110000b0000c0705105004254016524108a0a00c55a1045402d1000580c0050b4261030024203100c0d01316014002c0d55010546100f1032898010303480c4804c441c1c40740c42e0032008010750310445040c0c42003619850000343c0d032424040880798090305450580400114200400801a200c010b602030361224404841e040c5541503405200402d264240156244950310000728038290464072043c6a51900c2d400034100d500d5045d802802003070b55401342c00034020603801952401ca40b60f004904106540c08045050380b0100020034031050030b502e1909040ca4a00001001400b15001908415005200500301c08000e03070155020380d107407400040340c8068100701c200d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 819115998 1250 819114748 819114763
    0x1a040606150914030d0e04051003020d061e0c08190f0218030d0e130c1403070201050405062503020903031e0d060b070b0c0703021608010e3c 62
    0x108109001c0d00410703486422030811011503480681c0408201004410982c66880100c0d0980c04228201080806441c003a4805e5034404600c1414418003500d80e0045030100c54000700444400b940d0303809a8441100e9282c3c220b1601104582c10702c0420f1440e83c0081072070601420340303000002440c001034144c41c03d80c1c01081550a03011411503c6000c9288111800c080b11341d030150090040b40f030401c403004c0c4a80500b01340780c003010302464214404801035a00802d03040c0382d09010840441500c0380f01c0783c1001300640c0610000c1c0c2c000306150600b0308020342030403009001c4420f85000e6614442203030004c0b1000d4240401e4a0500603241c1e07003500c0100e419840f80384100c1900d9003a005900440313030310b214058007081c01d40c004200242521568684024410701c80c01a03d0301407200300042d804044040149461442441030750007030050038080d0b1441d49480d07049018565160010751200700d00812245c2c07401c1c42e50141020050705204000d0280004180c01544180f448981e03040d040181044032a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 819117248 1250 819115998 819116009
    0x3030b0306090d110c15070302010906050109021210260a05060a15140102070902160606091d0102030c160201021507020106052d01120e03030103060207110a031a040606 74
    0x3201c4500e0041031203602c603403e4046040104012401c09103001d4000030300d08141300800361036641800a0110141d029400c0520110219034070b0b5043c0c0030004105001d0326000304500c94000d81c03121200003115104d2031008004400d0f240350807030200f1001e42c48201132100c0d8400c0c1c600e071140b2000d11111050a1a10b200009041b80c41070000b03000340303aa000d50040150b42c0705851580141611026840d030301c800c4003800c0600503400020240201c3c800703076004014aa050007582c800203d25036944100b84e585903800401034543d1112900c0c8002e041100e2022445860ba000710301d0741c41c0072400c4510740c0c0103840204c0d2101d40e40c40000c40441e402080f04020348481c21010b05214600450024083e10b194013a060040310407900c06080ca000c600100551100d41080c458102d45818004417007a001c1c1e00d20211130b003504c901000c07200010620045001e03600811000d40d555800f421b003503c8281d1710301651805002845800c00100c0c0100c00e1068204c003248280c0c2c102c2d51684e0904201800158004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 819118498 1250 819117248 819117253
    0xa05180a12091205120307091211090a060302090c1b1b0a051002100e030d0c170f010b03070c0627030e011e180911040608010b0906040501080403030b03 67
    0x211024412200000c1c404074440340e88515101e9102c200e00c00c50a5200381c4010300c180c2c4a10300f088010f130011000342d80d02c003e4a00d0b080d840c660703030350014907248071002a0589030b03001c0035200c540c1e40341450084103604c08100b80040c4005072071517000c94403001000b03108085100d0046450f4a140d2003e07101740342c0000307040080b503201816505503603542c40c1502548078850344050b000004d1905003c20801d2821000d9000b500400e16440203403005040785441c0c02e00c003070004006e50310340c500c1c0c11b210301c04201c1c1003035880071005050054000d110309400381c81020301e0b001c41c1004010f41d501d440d04a90380003001d4540384011403003078078040c00035200500c040715400c600f900d40c00c171035440e0341000b40702858041c0da1f40310301003140c1200641c0e0329100596899900080c2e118041c41d418054a00f010f10f016680300000100c030f80d102c2d015402c48840b100014110301d80010200310055102062074058607959202c20714020090000442e58802c51141c42d060191a00008040c0b5000b64481801100302805 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 819119748 1250 819118498 819118513
    0x1407021c0c0305222d15050c1c0201060801050f01121205160f02040b011418060f03070206070914090402100c061d16080a022211030a0c0503040b0a0518 67
    0x40c8580c07841764401c400d080e0606940303000d8021595075040700d0641d01e10f41980640860116026404034601c203007544200038812222400c0b05203480d80c0f5558a80c000a8a2400c2c002d1050079a2005401114021750a00c01800900c1d120402e05600680c40b0808000003c0d04210aa480f030041c06107294544800d0496441400f00000e40da0300d4691080b6010801250030b000103464010f0800041c24001205101e46107141254909424565100800881c2000420b00000b802540300706c0e040001038000307006001080d50090311a00c00b410307aa010100d4292029008140e0306000208007910a1800d00c0c1c01a61440c081e0126100142d044035060100f0004c1000d40c0700035081c0414022600d00c10020400d008040c58003044050781c1c03110015101202140e000c10070302100c0c80c440141e10400800660a41d00301e1403207402124900c0e0204580c881c41c0042c0d0981c00c444d58888008103100003001088002504010690381c813020041e4001900c2d11490707425042500d0708410544076128190 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 819120998 1250 819119748 819119759
    0x10c05070f1508010501021615020304030b090a02010f050705030703120605030109050a03020c1503010314011407080609070c0b06010c08040f120c081c03110d1407021c0c030522 78
    0x20519102c0c107100361180354140c0da841c0012681c42c075000f9040074403405011414040741d00a45001c2c03040820b40c3c8102c07410a510b0740c890014922080d240c404450b4401032142e011960002c0e180078110002d030501da410f01d0280e4030340c00d80b40e109442000f420040e070001c6600d0501d02c0c5078410006004003400030081240c0c40d1400e036a46005003107098000d4801c0111000c1c81c0d2500200030b042403680c80010a085901c1c41e030f9480e4030401e4000c1c800c401035484040c140c43d207100260a40c2c4c07046072160340e90f68440c00c184060100710400500a6000c00c01c4500c409004a40d08106a58010a0038a014185d40805040c404460f000b20b4001001c4210840000110521030b0542d24205034052624140704956884140b41d9598400e00c07200c2c0c1080300b501402e4403040c066440806400f000d0b2010350318202c040c1541034211030180740600712804640041c020500c0d07040081e500700150807a1514004217550101900306e0455800082c1004000034065017000d101207030034540d050401c040003400da40c4a8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 819122248 1250 819120998 819121019
    0xb040303110703020f1e0a080c010b15121f210605180c030312061e04090305030a0f090201230c0d051e2106190311010e041505010c05070f 61
    0x440918910558620b2031130400d56070041400010350500610302000d465503242d04a4002d43d4403c55203540cbc44010340c0c2c0c5601d52030b44010742c0500590401d5540c2c1c01c2d1260032010880e02500d0684042840303c0f0310300303014140a01100c00c0d6101500c540360b207009001c0c2c06040e6450440c0b401006a0f00f4041842180c501107413a5a0706100e1010660701550710b51814543e481c00b81003c0d01888080007004144541415070303124500c3c001020527688a0008140460240e5900d030400302d000a00000800041040da841102c3c0c0150084d5000c1c42100c0d41c2d500000e004601c0e4903281102012240c541d40d800680404c1214421040582927400214000d00082c0082e0419001180d85d0401c039880321000303405220407134201810041ca07800151303003840c04560340c01d04020001e9030000e8112200241e400188020701d0021446010300c01e60a07a50304000500049101421368051400c0080345568503118003011025140c0c2803074000c3c1c00c00100e0401d285084c006078000c200b1100c1405005c03030320b407509 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 819123498 1250 819122248 819122263
    0x7080d0c050912060415020f0c07060206061e0a060e0102031b0a0308010602060c16020604050d060b130606091403071a0304020102120903060402280e06090604050105010203070b04030311070302 85
    0x11102e00003c0204200e0180d1202c00865004110450800311803481408075170280056105518070581050f2550070744524080184d0401000740e03001c2420006a40f50100602e420004000100051400140c020808010142c00b0308000e008000c034a2014030b91003041500d54a0307808a42160f840c0300d0089110f0740395400d100c3c0a40010b6501b8001240090000035518012007174074804034a0b10158910f0b201d400600b010040b81c2c001c10401c000103e650302c28840c014154000c550000d40605240c3c1040004c1c1060300b01e41e60701d68100b0208008040d0005001c608891600095030804411080080d0501c04582c00c4031049610703036003802c00c0c81560030000d10311403131003038081320200d181c0801d0800305030280e1118254154000c5000030018108500d01064490844100d0051301401d00b40c04071807841c007a00042170003a811000c2150519002c480b064004d42e041e81e00300300c0d650402000075140e10031035201034400442c2c032020508042c801c2d4000000e0541c101c1600f901c44026160003500d9502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 819124748 1250 819123498 819123517
    0x102160b0103110910060c0812010b0a0332060d02180106030c0201021306050706110c0102070303150e0c0f04050628020c01050901302403080f07080d0c05 68
    0xf07080e5854040390600025070f60042c650040103890003840c02404840c0390b0b18003402294407803000e019510408a2580c8060b002c2d0103441403103600c0d4909510010102d81207072412100304e803125070081d01482034070b0521a072409842c2c0c0e4800225a42c6502140300595180002034022030300311a00c3d0820500c0c05a0740c2e05a03407445c0d0b4203115035111503800303e00342c0c00740c00c1c40000c2c001003002c010084140190010b06c1214400e440c0800e0078880e5400d294696040540c49880994001071208101903252044c400b030341c0c9005c9042d98100e405c0042c3c201103288001d000380102c003000071320481415084c05c265001800e0061070940c1d03e40b08204120181c030000042c102c51180071220110300c0300d0011985640041c1c060b9076007802c040c225001102c0044000340f00c0c240c014601c0e40000c907000c7c02d0800540100760b0361040401c0d04030790008c035072042000e102011415075444c41e409100041d06c03e0200c3ea0b02403000b200300364a407001410146a148030b0481c1c0940305e1494a210320700c0fa190480003820030f455 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 819125998 1250 819124748 819124763
    0x1b10180b0a05070b1b16021207080601050a12080a030209280e011202010c0b151503161701140a0504050a0b040b0f06091309020918011820030102160b0103 68
    0x48070702c40d501d00c0c1440140c031703c110106802e0284051407480c038565a100b0500080020b440028003c08090a0104903000400c03240c0180c0014010360074151407220050000811040c2005401e45610901e130082e05840406c0540003d1000340c540d9507150240a2000800c018540070840100ba401d0307446094030a0f0b01a0080110000402960011190304031503011384404030286c3d503d90382c07008984c1c40109200d80f8042d6803860414980c40b90700f41d0106c8200100380e150baa0342000c4220035402c5000b40004c1007008148941103a60011a4440c1d50454011510b01d0a100d480b501c00140701d00200e400c0f81e5001813070030007000107104c1ca6410030103078854255402c00070301040f04140000c1d41012400590482010001c00d0340c2400c0c80052031906080e400000540c484c1c080e030004031000b401303031400c82d640c1c0107029021000040a200710560311065001015441031155131351014901c2500c0011010903190501c00c0700d5450a4045600e08254050385822102351823401c8240300400b0300040d034000c0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 819127248 1250 819125998 819126001
    0x203071b0614090f010305040311010903260601092c0f040c05040506010c02130f020c03070605010617040f14160305060f060607150f1d1b10180b0a05070b 68
    0x1100781c400b1201c03d490050300c400b92540142005502416004d48201c041101408584420500030f104135400540300795903ea62040740c0c2e111000d01c900306500c1040355040c4800074041039a07000049131044030311032010030840c0185401801e04001c6040e049111140144040040034a08030848600c078a21554070001817646603010f0104403201128003502050160b40c8060240c0303058030b070080a409502202180518075030385502d0998010108a0f011603101080c840100006030051038007404140c9444000341c05007840c0031411307150160025243c0881540e4040c01e000000c100084c406004a01b06e40b0314075100c80060310202c0c5188030a40701402050007050401403e080c03c00e000e4400105030904042503900c1d111540c40c400f03001c280d250f50b075400e00b9858000380b80c09507000300280d10602e03044803913240901c2400c1403107a0716000c000005401e8004d00c0c5d070f0b882c4030010780000002c0c50000c480842c611846d01401c80f007600402c002d0308010400082d401d60040050510b644a00c036040242d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 819128498 1250 819127248 819127277
    0x403030e100908100b030c0a0323010e0a0f0614070504090f05191119050301090e0609060a0506030a021210060b0c19020616050c03010608030a090302100203071b06 72
    0x34110034042c140081e045505203013604003868108445d07124006043c0c60090030b040300010481c06041d0b0088940c1000c03418050381500d00130350030309820543c100080c020340a440c054591980c0c00035a0080442802401200078002c65500c5000401d0850541c2407040c105050b01400d81d4101e031183c110321074180b40880c5c1d00c081d020b00440303010300d040c020f6844000812060907005801c10082000d0080014049501648400d481e02e0031030ba0528bc551607929410310080f242034a0f54a1201400741c0c0c004000d1104842d000130358141e000b0421100000d160300da0800007414106901c00295118401c003040250741c440206000c00707c0c4200364000c06c040f9a9550111416002d010352000854010a52140300b0745100300d000341310244000d158501c4c1040c2c903400981000940b24096803a50b1062066a81c50700b000d101c0c44c00a4101e1900440c03c0c01d0303000301c00604907012800003c1c080c41e034912550690f41d0003002a959051383c0700c4035041039185030b003465034011401881039400007401003100065 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 819129748 1250 819128498 819128507
    0x1030b0a0e120c0114010e06010e01031406090408040f1815030203030a08190204080c0a06022805070909030c030f080615160c080102040302010e09013002060403030e10 74
    0x150080c20019060351291110881c20796089102d03450265500c170000319000840001c81a0701070080d048502c54642090000107120b501d825141505140c6821302030607102d240d600b40e060788660f0445507400186e980d85032104a60141c0e50003100740910500300461701036010342004040222381c032410441000c803e55502c0740e0307404a01c00070390903030410450740450f03034419100184c4c4030b0b040850b220002c00703c00400100300e80c025401055140c220380c0740c04103a80f401050000081c1580e10080c5249066540e180038203482c520301060300c03910703a010302c203041110505c10703100148a915010404400941005045506110340480005100c2212106454001c040841c0114009003071070510480007880455181d1119801e8844242c1d8000c610001404065054026103031410025886d0b034510304c00900030464001c80b03944110324100c01070210602264140700f80300b001540b840001000700f01c0704100180144406508181700003804030a043c4c20003800b000742c140c2903502c81000c581801d030440c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 819130998 1250 819129748 819129761
    0x90308090a0803010b0a0215010e09210d0b040b04050a150b04080604030302090103140c18031207170d090506011706040c03060e15041505070f0215151801030b0a 71
    0x51020b18140014041c0740b64010252814295a0040728241680300e070079a10301c1503099009503c01c0402b182085500c88051003810358050b49602e4014844102036124a201d0168000500c8610795403100780281303036200d0304040b0b14464080e01c1003140d0700b0104600d001810180d01089441881007000090b210810307400c8804031107521001d0b104a895176517046001e0f41c0f010345510304041c3c540c0030701042070801d06092401480d01c40740b0182e540000c090482e05842c00b0001451007038000e206000c90a0788900121607580e5400311322015602003000d1201801d00824449002d018900700e071250800200003050340c181c58100d00809010104001640c0c4c1d00e00e03040701c0c01060300c00842001c000041d82034200d8000181341e003090b0380910914051203d4500400c031015100c800c00e10985035400d44481c4112038000415141c4190070052241000c0d41c0c2d00902000a10300982050000302014540552180302a0000308201c0c9008044409c01a008030b080c0000c2d118002202e0210b0300b115424402c90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 819132248 1250 819130998 819131003
    0x5120d05040909170a020a06050601020c15030a1509061e12021002120d06090b01020d02030a180504020c0c09010b041d06150a0f020c040c1409030f060109090308090a 73
    0x20701d001d007484001070142c003054004981203039101300008029200740c0003800f0345e19103690090903c1812410042c0c00c0e902e01600c0c413410740d04000c000b0b0980d6150210040c041c5031080c08410b1340c0c0e44850701c2150003043e05484001600d40c0440000c40d030041d10f500107104603520358205404404005543e5840c1c21038510600f90311070013048010006041c071500090000c4100d006552620b098054030303503c07507071184142c1c0c6a100d640e24000d21151089204042d41911700b8401004050348202e0041d60b01d11603180203105000c20b0710b4220780f8034a80300c0c0614029081c003030030540d00c840c070b14007403d035480c0303114040c6500c54910030001051a08041040d941240c0c65050800d0001c2481c2e88141c15280303000c0c2203550041c0220959010554000e0300800305090340e9034425024900d00d0700000c0c14504803004d42c601c91400c2485148100d54400ba5605544484a00c040c1c1d40d00d15100c0064904a030128104140d409000000146102154012403481c1c0c000d88440100e50340c0c00c162a500c50b220b02200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 819133498 1250 819132248 819132257
    0x201051f05040f09120507020a14010203030601083c090a031e0203042610050601050d11070203010c020c0a170601030330020a1b020a0312050d05010f05120d 69
    0x300620b10306a0040e030f0214890040024000c451600c0d0f11102e980543d01c904080748000800700214200303004101c00409248881100301d4a019000070344030720000e4030050410036108003249032034000580083c00b821031201d80240e140264009a001e4905551068007120008000a04011400306d10002c4447d4981c1d1081c1c0940e1101003940b2044254a2540c421440144070100c0c0120b40b4a0041064070442d0000003820b0b00b200c6c04462401c0241d03648890481c1c284028000c0d141d8200c1c3c16942100b101500200d0044100000d52515015025000e9455070a142c8d001c2c0e0142d4010030341000c010015a503c1d800242c4540c0803900a030b50100d030181890340b1400040011904c01d007203d68a4580348203100340400300d140301c640d0640c0c01e2510f20400c0254000b40e600d05070780d00b201f14640384180580000c098030a41d600000c8480d40d45100c00307031002c808142c000d11958820030031507580c017034044001c0120356111005034019041501526000b0400000b41150034500064002c40113101a81c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 819134748 1250 819133498 819133561
    0x61b11060a020a0905220b0621180d0c02010917070308030c0405061c05060a030b07201b120604080d020a021c05120c0316030e07090501060807020105 66
    0x1e15030025400a164442084041c80d0003040903510401d0000000a00610b5400440e00000d80c450440d20101c4505110780c00401200903040b030148244005106040f10070141d95844024500300200c0c8414104184c2c014211410155908140c01180701c0d4002c1c0d03111300505465189030585003040c83d103a07400662041a042001840718001164466821103a0307604061f92031000c690316400020180320010002881c000070340700f60b4030485500035000c03508a80c020740341d03803150003540034080d02d00300400c034040740d45058480c1e009400c25048103e80088900010101000c50202101d00c032002d4841e030741000460020701e2000400600941c3c01512461411f070480300c481000703500c01d50062055006030b01e0501403801c101c60b607400f800d980d1911010764481c60074043d0310705248002e0000d00d000d1024001d2108201c1d0406243d03035580b2150800203410341c005200700e80b03041036662000041a00b41000819450b0344034540f0390003140709400074481515001c0707070b002948100951048001d00300c0c28 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 819135998 1250 819134748 819134761
    0x8310f050106060201060b09091e010803031609031a100b0408070602070e0f070f090b0d1a10020c1c02030616080f01030b0f0601120c030e0c01020705300a061b1106 72
    0x5426420100800307495500380d101081c0d82ca0002b40036840601c6940000c4108000d95441120415140b24680f4014185c5d5040d684e4000a82c03586507c00c26030ba08000c030003e1003040c002c18051307024000c20010162201d945e0b4205595441d00b500400005006603500011070b43d1003000864002d032000c240d4038030f80ea0b4072030600310b60310300c191036001c410000d6803440041d4424142c00107060903215802c020402c41c001100754400c8840c011800d038010140f904910422690101ea1a81114400c0310b4000c510301c82101001c0f2036286081c006503041c01104140440c0340c500301d00702c01c41d600e4562a014070710b40c1c1e0b03142c962005003401d100281586200c680020744030a009013100b41e02140c14102607107038054102a82088039190301740d00c00401d5a500308582240c80400500755120424801452210308120115a0b0010410bd41d0710007400c601462006c401994041c9005003c0d00200701c032059030003070070310101a103e4605a503c0c2c90780c021000b110860304c1014101c80f10710048004095546035034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 819137248 1250 819135998 819136009
    0x1006030c05060c0307060908040905060f1503090c130209032103071202120a05010f090621080f03280209060702130e0f030915090108310f050106060201060b09 70
    0xc10b0790f07600030b01040001c1400906070b07100d1202e90a00031000303d901c482c14480d08030100d0740c001d444c0511544403c06401329540d030300000c0c8620240030b18602502c94035140e1030744d85400d21080301c1c0e03903118411446414280c1d4240c0d0103004e0004040703040381c49100c001441042080c2c1105044508030004000149255010382003084080b000c0700401441c040400c000780884810a4a401c4941901ca900400c1120840fa030b010014280f00203007042880d02d0259a82d80307804082101425100502c00b000342409294000c2e290180400c031480380c7e403860400c02801021802e100c00003d501140003050320500114802d40d041407401429840c81c0030819000c05c81810814003608030340f5510307508031060b082c07030a100c01c182c22610721004540711a00e000c1000b0b4601e8100e580311405110070f206078025a0ba010310030359006607071540b60405800300000900c2184418421521018081d60071545c10032111091500c0d500340208000c000080e2035103003c900b070b210a84660401600d041c05843d00510b4503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 819138498 1250 819137248 819137257
    0xc050108130303051b0f1e030c0d09080c07080d0f020a0b060103090f060f020703080916030308071106010b0406020c0d02091815040501270804090507030f1b021006030c0506 76
    0x10420f2680c45c48054007514a07480d40081c0141c08052004150541c21411040b0401c20140074030382c0442c19440c000100e0750030b80c0200348007101c0d102e40700d031012000c0c85102d03021030700c101c2c400805a80c1080e440d44803013590340d62071070401d900061000d0000215144041104000c0d142d03c21040e4056844000044018001c405010748018581c1d2803654009145845440041049041d01580f9402e0a09002d403900400030304060351a00255005660760714403503001810b99070f050401c1c401039101d01008581100144d24040c1c041c0c400c0a00114440c8000c4e4080c2c02120055403c4852000d007850500041107840769009401010348800305802c0d00c0005a5006040b000b18221600882100c0c20079403081400d407415212659600ea5115000440400c210552590203420b00c1c44011590740b8201503104a10a00c07810a55500224210720b120350010b540800d9100c0060140f4040da000070360450755041d0134000540702e900200b05081440340140400c8a8124003555003051a00c1d05014040d0720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 819139748 1250 819138498 819138511
    0x809060408091314071b0f2301020a021b060703200a02060324100509100509120d0f0215040602070323070c0e13021e060703020a0c05010813030305 65
    0x16550030a0310f050303224803480d805007910541ca10301504045602805400300b0000ea01481d0800da00c628020a04944001e03000c1c03540038002c440e40c4810303080b401252020301240080c59500001d00c0860840d40050131111582d500c9070f070070400011140400545115481d0001e000c21243c11555035006103417001000c1001601056030050400c0c0d600052180d841110380da0030140710040b68040c45260215032801900d425501c0f03aa4140880101804138020b80c000c1c80c3c4110101800e00d107400c0c0c41001902d449a00c09009400700c50669014a51030350f0042e070046000030000000b00300d041c0d2000410300c0d500d840c60200341425458685810001c2c2d0300c070360419018058450400c0b03480c2c4076401d2003e41403e80c2071014a8980c011440c20004164803503120140300c0d0940701c140b0061700b1070b110000c3d403003560448481140c00504039803000b1440680440c1135000e000406d91100349a0040313120791040b4443e0b03595030342c920f0300e9038010350b158041902d8170010b0b1040d58403000d0003c0e000c0d42c4843e82191 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 819140998 1250 819139748 819139759
    0x209060907260a0501051c080f04120602031e070e060310030b010b0a09060c08040627091508010c020705011d03033103020f040b1f0519080906040809 66
    0x460209018200b420b044003070055201c1418104048048140b1035103015103402ca85051440e800d41100f00300000741c0c5400509068400540c91001d88461421103000b060b03030302d00109486207107041000c001e42040b0b9144881004402649840c0f2400d0035485100d141c1545030200010a200c042c0641d0380c000810515105924241c040045140803007201e0082000c200e18079550300c50440000c20030206544001d051241410050000920034000c1e2001e4441c1d82c80d044920b2801100410314076030301580b0511009407081000f18100003a071b004400030b07254041a038045140d490001e1800c961011201500503008139206004641c41040c0b50844100740c0008a402d18003040002070460340302800d0201e055400903094002200001c69105040114a04011115155030003262819800040c42c5108036078070f5862050541da121140d1805200c40301c0788221040502402800c6079001c42a0203510008480c0307180c1c5418450011103114100305c01c041c6c0402c4d21a13694030b01003030300815070700c59011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 819142248 1250 819140998 819141017
    0xf011401080c0f1c230d02070f030b07050c03120403091e0e072006070f03050109020309070611030f0d051008030f0d1d10051803040303090506070521040e010902070209060907 77
    0x520b104c80103107520605100a405640350488010382340105e140d00204070301c2883e100420110740021059548003400d420210380d98005448a14110f03c581c0000300400314003070003880701381a40301d40f8081c00e4400ba00d8401e040803001e804c00d1640b544080c4242c034510250200007452462003620300220b603200c9403200d80c0034a004054810b090000c100c66050000b01c1014400d12206d42c54040caa0040c05101c004501d0350074081c0403da1140c0b03483c0200b0042c401110b0301c1c841000e904108451480740140319082e15151410325542c041c00c02550f00c0382d1050300c1c020b030115801902004540114040000c007030701c0d0180ca28108005000b001040c01c508407900007440d003004d8800e2000f09480e210703030b210004591415003c8000300b00c1060024100a91080c001840001d812518170001e03203208803122602c48205181261412403494603044803441241c1402140b41d0000300948140c0b424500032100e540c3e00c1e0701a401c124068200040d51005000002c03e01c00e0918005c20764000c034075440c100e8441c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 819143498 1250 819142248 819142283
    0xb07080a090b0d1b2c01120614040b090702280c0608040507080c0109050105071103071203030b03240402010905030102180415030f030f020f011401080c0f1c 69
    0x341d8110740c0850f54055110103502c10710300b030100120130442241d401c0040c0d00d108800e8101112000b040c118024581805409807441c0c1e02a00c14070020402c44402030125540314025104040e50410013240110f0802683c5001c0349005c4440350f21030f038950fa0041c40028003a240003400d070000200c00f14400c0c01e000c4c0300c000100791034a20300b001600694803221564142031a25918000d096800710005402414503007a190f0703404010380741102d0302483c04e0703622003900d41803051125407540043d40e8135103d081b00001d61040d0070726001101e43e0003514200003a0001d4818192100c94519401e64003101c2004c40d40c819640502211b038005006140500103c0d4648000c00d007264448102d00d1580d0454400764215842d050144284014506480200b04ca2950f6503e04488801d00c070000d043c800040f0000400da4420421440030904140003886130641c40b00a907c2103a0003801003030020301844e40c9140460620240c02c0080b110094850124a07800d0030040c8207002081303004440600801c006c2629 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 819144748 1250 819143498 819143519
    0x20303070c06080a0c08130804091a010206070203030c09120f0703061b0c110105160f03170a0e100213030b1501020c0111060f0601050706020d050f010902040b07080a09 74
    0x5038184102060304009003050405004903000400f48074500f0706242c80c00b515594040c100582001580480c14610300491401070341720300407034005441c2c80d032130070301204900501c0801c031400791a0300782c0036207501d0b4540c031000726102d220403618a04080810080103189051420210702c1c1d0301440002d40d0369000c01da24800e828810980c3c000d681194039250240700c540d80341c4054141a142c1d5040050b0702d0300143c0d81e41850b0b0140c000d0004d0510201081b41c0c004c00014000400b040da0380240001022a080d1501802440320380304d041100700300050000303481d518a0300c640e140045003000140710410811010b540654812101340e05a1210070000000081442c3c0200303000d4951451090901d58010000901d80400d10200504100709006810030f03c180110709a90070001101c07048400c0d56800d07005940a00c40d024004100c20b10005ea036041d444c46a078442d034082c0090f0700d5500800d90743c414086050340114019820325007402c101000c00501224002c101306111400c1000c0d940781d44441001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 819145998 1250 819144748 819144757
    0x3091b150d0603060606020a030228050609030307020601050a08100e011b1e080f150103090b040323030606180301060302040615020c010c12030b01030f0608010e1c08130f020303 78
    0x41c0a031030300420b008006145c021800078040f948000c10450410303480c000d60322a6036409000402d0090440700200c200c40c20520761216402c441121618140486002e544e0b0f402103034100300501512001003058900384c500c2104881d841c100500502d603191501600900011202c030f00c00350350312070303595504484224038000a07100503150600d101d80b10070449041c40515145c1c203802c00035240d042180d14030000040300d07088041c2c40075008100000d180141c0040c004240d01404001a207401c2200301580540d00705a80d40b031051040000e481c6851902106010a560003503000400780101c9540d095080407580c40e230b1400034008104070b96290013040444003a40c010001e83e54101c2e80310b6132100d40403c406420035900f031130600ea0501c0a0f480303a040c10741e26407194a007015111a0400510f1f031007500245100500000208061543c0b190380034000d14881402030001d01900450300180004c0010446c0c0b4620751747c40d20052695081c41000ca68503801e8030442d44d6003048094071025072001c00141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 819147248 1250 819145998 819146017
    0xa0905070e2407080c0313030605090d022a1903210815060a031e020310140a05010c0819020309090a0b1e0d140312090303091b15 57
    0x301e25110280c0d0900125891004401c21429010b00e02c0850b6202040100e0b03c1554000c040c00d41c44006540c1401d0451240c010b400d008007002c0040881881603d46c00b0a00a0407040103c03070500c040c00c1007d91311900501844d4000c00c0d10b02030107183c4845c680d0304040d4060002170000c6042c84100c944c2c1070512100750015940300c082070ba5205c0c10144c4c507000c205500340c903d0900803014600104120700a0380c184408902412003c02c8400c0342900907001020075102803000e02881c0c0c03c0d44d400190094000b125121038a40c2c00785c4000885c506869031000030300401400c186030031420000155140702d140402229110f0301000750b42c02400c1c0000ba80c00c104041607002d10351711100e2a080060340d2101071321a840203858080c00f14800e585510349080303454500240c00c01da152802e0000703952203808020280461454001e5605180c001100500e284c140360b2a2081041d01c400d00b000e40c1d24002129860b600354415030707100341c105502904417034140800408410402030000c03404105038101d00c2c5007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 819148498 1250 819147248 819147257
    0x603030c060a090c0e090c150c0a060911042a0c020d05010c080105060f071202071e180e06130f200a050103020f09090a020c12031005041e05060a090507 67
    0x3044104140304c0c07030b044000d1142e01d080881c60b0811032001c2d45c0742c0741c40310004e62260105055950703540d03e42030b041d508115022011b4070300083c00d82c10080040c210f10300007194801a184400411842e04d8841c0c05002590389060124407034070401071188402141114509210440e81500016034490310240c5410384904004900c21000c0c2501030082001a0401c07882500180805c00d0b0002809059880341d5800c03c1c500350681000d10303c140d040c00303140d803c4000e041d640d0001c129034043c3c1918494041b2640c0b481c0e034800306c0300341c82e100008603584415056610b030829404505030710300a582ca18001ca000d0841303035132803540340c1c0d49500a03500018814aa180c00c0240800f0b12840d0540741440105428241585004a000f8000c82d041c07041c0854180704083d01c3d00800c004071281ea043d9807a480183c1d084a9040d01500c0260845c2c0e001110760084e400b02c901c0d0045010706190244070140311000c04000716100e040040070b0041c10004081c3c80c2c0103000031000144800644c0203260044080340ca4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 819149748 1250 819148498 819148511
    0xc030c0b0d0b030127110306010b13051002070303120b04020315240a140c010608070f0b0a09121a070f120b091f0b040608060a05270603030c060a 64
    0x440060302c9000248a200340d150180309070241c40d801040140c0403803030491a43c0c2e02c03602854542c450b1415410590f800d441240004a41205034100034200028044942502c0b01e5807001004003080c50a005500140c1000204000081c001c03002c0c04401d14500703a01041c01200c0101050407a00121501d4100302508100744440742052100d0000f9070390701e10110303c1400240f0289280c40d1182689810401c1045000d0460350007044041d190046403204c000d20a01c0e60707031080c6541c6c03030213240580c8400200342080081d6030300343c000403905007100c252034440201f0b02c0c080304000d81c00343e110400c6d10110000110b0310000001e8500300d502c101c1058607012991034032440014102001502e03020b5002c0d18002640010380d0741c0d004015401504016002c00c185416880d8040c60f82c2c1651143c1d081441c08074011851a400042d1180318000940b048500c055680c020050391030004c943d4000c0a00c008019040c10408141c04503501c80b101400b00c0303180144208c9900c3c0b415030304980c500d0229954a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 819150998 1250 819149748 819149767
    0xd080f0d0e0d0f0804030c020918030c07031712040305090d0204020705101503020f091b03040302061b030705120601031503060f0e0631061e05010e0912070c030c0b 72
    0x54504403c410a03240502c81ca15181c2d4000d005603590000191280c42c5000016035074903c005021042ca08503002900d841e842a8020140d4852042c00308440304a007040300400e03820303283c005545c00780300000708540c41601c840c0c070140c503191f010b0030b0004c0d0003802c0305420300c0144c1c80d203000034900148144000c14031044503151100c101c0344102c01d00c0300515400720040000d83d40c0c1c10b061191030082214420b445895040040c00b0b070f5140d0207440000d030800030003040180744c1c0201d0620301c1214401509001300e000e1032030020003440201d07a10004030300203200d80b070a882000d44003164001c606040015403010300c81001b0349146816801101d21588038964100218624060940284900d40c01401581080303d10010240b0083d50a064a1002c07034880310711642d45141e5400c46560020400c000d0341d20101000744912415034003241141d1b003050b00001d40d030705810b19154030503c800b601900c40310700c02c6050401168410130007540c00c02821032000c000f00e084a40440000e0003d0044c1903030741d16064 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 819152248 1250 819150998 819151007
    0x50405120324030105070509060f090d050d140702130b03100501090c0315050906090403050403020415031209081e07170109140c150c15270c0d080f0d0e0d 68
    0x2c081c15010f42d050005104500d03420070140c0d561200201c6840d40c079a0a680c102d18147e01a44140b03c0c0d01082c0304a03035000740700000c03808a00101305991002e0386282e0400401c106842200c2d8000c1d00121b03886805400c10046900c0400541e43c02810313079134000a40790001040d03440c281c100140c6035a550800304043c5415100d0000c11901c40004210301610b8140080d9048500800490141c440c0d200090105403162048a000d035a0042080055031049070200c4003042c1140001c03128100e0351141c285c525802800d908044070f000c40700070502c1901d541d401040010704012000320078810403901103a01d00079100c8660081c0c240400000c0c8615640c1403500c07068181d4074081c88203403c0880005000d40321152030301158005d1241c01581d80303c0c81d480c150703e0059140b151988004003042400424011003203100d14035620340c94041501040d4012648d22644085040c0e50301a04020794100000d00380400b030000380b00c9424002e410451120780e13500c02d40c0c000d114002c00e40d8224400b07219010303420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 819153498 1250 819152248 819152311
    0xa050906102109120807110c12030f04090509070f06050405043c2004050907030e1902090f0106050324100e09070e01120504051203 58
    0x125440041030410402203400761038014030316020081c69100102103410a0400b1030482825860108608606820401c00701070300c01e0fa195002031030880114014a12600a00054440b1000038207410401c41c000c22940d107121000c0c00140780814003d8605290744200900000c004e0010003003118540f5402c55820400c4540100040008241c4140075581d07020041c1c41c03d98600352000111030100c1312265103485540042000700301020400403541682c281d5040205249600c2c06211044500d046144406110741d10b64000020134403007009246010640b4607004103403800c0014501207042c6082d82000f101301c03039098451134003800c260210b007000100540c1c40068a0b0030703c4565410010001e04611024050030f840701060000400c802c40e280d1b002c00252034005284002c8840c031440c02500850000b180d1501c1246e58500240315240540b60308544404e0580d1610100c41021030b80b400208000760056449100308a48014800e44010046000c0d0039000b4203840c0c561a09540030f50281c15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 819154748 1250 819153498 819153509
    0x20301050a0504020a02100c120207050f0705011d0918030301170d080f193b07030c0302010507060e030711100309030927092f2d0d0804050a 62
    0x4100103181c0841c0d03000c600030f00803086054008c105000c520408031741c4000d0240d1861240c0d48005245400c001d000a030310000542448103485440340d842340190381d803405061508400c0c109200c041213003890882c0060b58412105288141170860405003545150802d820500c01d280e012010308602020802620420008a1500520901d020a0100c2d20554041d00621181803112184071912240b40c00602441504490549100e6021410a03c80140201c4080a221407140071888514070200b1803400b526080304515810300e1a5030300443d0181e1080c1015103445507a001c185051309418001440c1c01030042561260240c0b4a2007080b0040081d003080714141480c040ca03520020f900b08041c00700700c0d481c40c11210403c0b00c1d06c1d0082806401700485218050b45044a418200146201c2d01000342c15003110645101541e002e80805410741284801e511016844840c404100140e0080110301030002c2502d00081030b080100e4092000340e04102c4464401080038050b508081140f07130300801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 819155998 1250 819154748 819154751
    0x2100f09050d112803030b01030b033322170a0906080105030a110f0d050a050307051c1e09050d03080a0b01051e03060d0210020a05010b10120504150e01020301050a0504 74
    0x10f070001107445003d8013540007014545c94400d0a11168000c0d030141094001c00340946a180d161880c4c0502a010b19101124140a0f941c0070714030180181074441348100d00f540030050f8092201c1c018803116241e190b004075000b0704d034803c0403c1d0041100c0040c011600e0f0640f90000610b042103005040030f07405070041400317513001c0c0b4100c80206a0b05026401100c00a45843e0090410a0b000c2141c2e001e10190281444c81010f04220400000200400800d8020002d07280c8583c5010103540707494160500100006d40e42141038031404074000c0511503070102034104101566075a90100e81c008028207400e5001c0b490100411080c82503c1c003c0019039102480c08a1518070b8032071410004000c17940c0124900d082c04000550141c41e911a00c44855030020300c0c9203600014040020b590315203904c0d080701d407035007003c0ea0306001d410002120301502d41d0f20380b0350302d4a0104849159008000040041d19507000708040500e81c0c00562243ea00508030302000517035258100014061410310981c070140c001e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 819157248 1250 819155998 819156043
    0x10c0c030f08040305040503030403050304050f010509010f0809070e090d1205190b190b13060201060e13050c040203100801150e0f04111309020f1002100f09050d11 72
    0x3039880054400310344154102035001ea1a40d050840301d0b4040d54002c66098400050040b060160000280c411101c003150f2485002025400454803070181002403804684034004504040380140c0403c0d0344201180101c031041d6944050341100e11006030740e003d0507034122a803108001c03944505c690141c0694081c0a003c5801c00310603003903107500e92200c0911070715503c3c27490f03011540e24861134412881005c16092401074650841400c00ea00c0101d11803840f44100000040c0c1038018001e001c00c50700c0440500009036a001045025030f1030710002210fa038041c2c41c03440c40c02a40d6610103940564807a09104007654202420710b42184e0302450321001860400108224480048051a40c802003d8030324082d543c40740c0c6016000c003d0070007a56580054903039048030542004c3e505c201c103041c1c000c5681c41c102d0780c411000d110007815000a8040142c1080707282d4505c1d40f0386600f0103030040b0204c510009030b081c40c1e51581e50900440305100b0000502c495200c80ba000c1003040184c154400c13040064000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 819158498 1250 819157248 819157253
    0xb2d03040803071b0f1b261c200703031709100e0f0706080906010303030b0303070602120a0b01080421090506040806071e0903022403130c06020a08070b1003051e010c0c 74
    0x4241400c40d60081400101020b40900c01f824859001c14180314500c8000f102005080641500c1c248801c50380784240b160840c2c4405400062124100ca8058a07004c400400c0b09207404880d00f002011800640701e016042004c03c075852140207075110f444d102415226040c0f2031920f05106503a40448100714501d4180040200045400f904695040c20b002440d4020107000c6800e40c00f0306000500090710108a0080c00e161202d030480c841c1c0c1c40352400f000100320541c0199003000c015100944000e00c11042d000c6244d010415540079600d06050001e41607913660000b98199100c0c2e0404480798020100340650560002551681d002851320780319107000c030f1008018a8500540b00183c0b00d1081060315016008583c3c0120394080c8882c4030072581e9241004c91008011000b540850f16403864a8000901c01c0c8080352058041d41d0103d4440d02c0d00800e511100c42501c0054038804070074207800000030005408010f4004039408180e144004415920303080340c211000c44c3c00d600d0a000303012211a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 819159748 1250 819158498 819158519
    0xb010f02061501090e07020d1403090c0118180b033d060f03050a02100e240d1d011a0a0b0a02010b03070b2d03040803071b0f1b 56
    0x180152031010b403034040d51201c401201d100d5400d40c80b44041c030301004c05001c0c6846e804100e10107680070365251003264600401e064811880202d03040d03189500448410303181e0350300c110a038000480f010049003401c2c603122142280c5030744c0c10a54011009555109104c02c6040a122014040d498014210070b800b690001d9041c1d0940b5010040d0001c06041c83c81c032002c4801c0741d008070041c0c41440b01403043c0035202e1038515941c405a84050744602444c014680100b845007c50107882071011303001250070340301b2811240781c5078000d22b0b03c0002c03400107100c5840114400c0c0f00b0382c42c1c610b4042e01146c0e003141b014207406c0d086070020010742d080c0103c911203107242503e8044281c0304603480301303800c16175404a150040703005102500c14140c1c03501403a84002000302d01c543c0640900101e00c41c06204043c0f4400ba00004c910341410701c1c0d484c8403024000140070130f0019001e0340e4824031509001031080c501c800b041d1a03011701a101150a624030742241d406001d0b07210b503650324403904806903200050900c0050403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 819160998 1250 819159748 819159751
    0x21120f0b1f141b0604030824060a0f020307020d24060e06092707060318050a020d1502040909290402120c03030712030e070f1a12070e03010b010f0206 66
    0x640b00c440010b2050140c10180ca01028200c01d01040c4c2d0400d04141c0b400420803402911031482185001c515040030301d0b207810194400202c018055460306204001c01e440316040044a0015804103218103000360b164000510022841620000e01140420340f503003600c1d005282e40c95150610701002800b080c400a41d00a401000031541c1c031045d561200c1c030203c00b005c1401880d420101e0b100d4015269400300086010942d100c6407000d02011401e0008284c5100112034058030703550150044802506010810b121a180624003120404144455006c1a82d000341e000000325030b9036601100c14420034000b02e01c0e241410f6240410601400802a00c6680000c1d0001c4e00c140ca00c118007100c010f00c03c1244110060015054948510082c00d2a4018000300c03412403010030f0414510010303061000c07440c04241d03480142007000c50713800c1c00c940075907690408038003d403800f130104100b020780760045041310301c10b030b015a44046c40d1009050500d425038403400d4180341031041e459042c0380290340100d40340c2e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 819162248 1250 819160998 819161027
    0x1011071b0e040f2301050f15130908041e0f091e0e031b0321010b0a110c131a01110a030507060b040c082221120f0b1f 52
    0x2000160b4941001100c01886504d4404411074200c040c0d0301001041d04110310403010043e0540740c035618401c2c44480142e0040c466a40710b0400880d01c210f01c0b403254060445c071405045040e0501d910342081000d20705070144d1502031502da2001c200803050740003d000e0090020b40609105084d01d030101c00000c0c489081000242e43c2d02ca5210200001c4100300f910070705900340e0250000d120100f24616142c1d80860b20425030108503180391002890308520180c100c500c4601e142d031601807440411558106d04d00c1c1280054050303480304c201c583d039403407102d03030440416984c00048281d15a100c000c1a10688401d01d4144180801d41094043d00420381c1c601440d010300f00a552014940b405000510740c04040704c1d841440e0865003000150700048540c46002144241c101d41e524007000641c42d022001d07001008104c800d81441c1c0316805080c103c41040e40c00c1e08010402c02a00380c5080141c44412103c018010f035a80103458a84c1760203d10728100044011034502c0035114a40b0051004001c4c0a45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 819163498 1250 819162248 819162263
    0x2062e1403010e030a120b03010b01020d0503070908100f0b031204050f0402090a0e0103050d0804020d200a03063204030c02130509010f0b301011071b0e04 68
    0x160306501c003074202c401c0c00078071401503030384d05d440100001e81004403140d4030780e4004d880d20701060100d040520480c1c1c1066416001048180c502d48021110395000420342d10400c00d01c43c00019184e1806c05c03500056854500010540602c0e0700100000c90b11082c0e9a1446a0300c040200c0606042c004119800d07154281c1e91140c03808409808a40a0720130400c94a4001c50180343c00290220942e1405068a110f9000d40f040520001000c0710016029580039520118030000840001e040d003020140c4804000d407403194001c080340024410000e00d07030084d0341c0a82c440c4c440041501115054803c10045001c62015032403900d030030458042e4006000809000c80148448290754819021001e0100c5005051115103400b0a45601804c42c880c03508490509000c4000240c0c03420248201109041e002807034004000a9500d0210303600c01030300000680120300c0700d615400c80c80e01524000c0001034400701c0d07a41c09949010400c03411000c2a00421100d08141130020030740140a558101c2d030010036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819164748 1250 819163498 819163529
    0x71d010f090f080c011b03050d02130315090311070305060f180a0809090105010804020d0f08090604030b040c0e040c1a121e180d0c0f0209040302062e 66
    0x2419101051260404120a0302900e0300085102002a45005080081c1d03103511b80608100324801075400038140003000f2440500c01c45058103103c0d40070f07040c4e180244c5070701007146541e501c0e0f0480c11000042c010305241d8880e403030740d41032603001703006c0c803005004c800c0042c8401032558949a40320380020701101401040140840e410310001e014190740c0e46045010f4070000604c6280c007000c55808201054003544a44000183d15805102c810b41f2840d006068141c203051541c0d15003101500d0038108860b6041c01f07100c0c1d0681c6845900141001e103204481d00c034400d0a01e810b005500b41007581c003403d00301a4034000c02c400103807104504030854094002c07961070342c0300c0c1001c400300f14011180c425120388203400401512a1208030500031481c1d4454444489840e5460944007031518000000140da01c01c400c40b8402c14401e10084e448940120300045d1268110360029008410945090340181d10200078450000c1c1540510107a0b1080602c420515800044e00040d61a1191080491709608900b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 819165998 1250 819164748 819164777
    0x12030507060e030a12180c0b0a091707030302100b010e12030d02031e0603010902060405220509030a08100806190f050a0f0f020705070b0313050d03050f071d01 70
    0x4224011201840040d65210028042c00406105e040c0e600c00143c6800c0003070ba101c1241080d60403c04260304615440035080c242070780081c0d1a4024000348041042600000520350070103070740c0480b00b4001c01c0c003070800700340346041c028a45044814918000ca141076028801c91380c00544c1042c09610035a581c2030400345030240c0c80c0c114001d142c01d034510755000000b004410712407123011f404106c9042414612944840c07090500f00c071100720000350003040030013060003207280c000c00130307800c8a1418840302000d528094006080d540c1c01c1e00c1d092131541c808192180e515070030480c102c1c1c4c04096641e180c00394a1424510590712200603004519070b2416141d6100e65029540100c1e6510040c03d01c24052030525080003070082520a00c050309061600d1921040182e1a000300c801840d00003000349149400c11090035100d42c0301814810301804100310340000144180038100f034000311a100060b491410558014050000800c400104902c01009a4079600b034081d030001c1c510b50a00c1c0003079122442d00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 819167248 1250 819165998 819166001
    0x60b19140d1d03030405010c1b050a060b030c030304171e100504020d020904050606031c0206060603090f0a030e040614030312190603140114060d06020a0e0d0303020c0601050603011203050706 84
    0x59111482e14040081044203001c4150400220b1140c260b4540c084441c03204410140510141c0000700030790070248070780000ca85140c100c40c00001008041d58450004a40082d181d42d100b5807109180c0a98039034a5810620140180e90003102c0c030a00c035002d01c2081103542501d0710349014901c0001551100400c00b0b549800c012841c1d2070380c3c06821041641030a080a42c0d03201002c407115031103849014009601d4a10030321003c003038180240c004083c29150401081521b400003013941500b841041d05000c0410700401010aa141c020703165003c1004203001408107072000d039080152034041c03903100c40465440000481c0d000c00c40100e0101103588a0007507103004842000004580c95040c5000402405100c185000b00400603100070451602400800300605008071643c0754003844242c035107808150a0b800601078070b0211302d42521580b4882d400100181d013154000e500183e40490b01803514101000024058401100c125040d58501815800d032126544001001c208000c00e0300b0342000400e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 819168498 1250 819167248 819167291
    0x20313081c0207060e010e010b060412151407030b0607080d020a0c0b07030f0e06090d08091219110f060705070f0c03111804050a02012001060b19140d 66
    0x44503040d03681d16410b044c02c0019064068041145528180032034401038414414000e0003580905000d00b418a060308023611080e00600646408441a40c0d480107091944100e1703120844c40020801c8071b0a00e04001000c445441c0d015a01506c070422050f0b001c41c5805041d199814204100541e545804243c1158103501d0700c18010240c0324a04c05101ca042d816400007011821030140c200041d0580c908001c0e90740b801074480107070079004441c1d046c00301841080d040394819041c00464207101c11079100d404851340a08a05040f10300310307400b0030541c25802920a604000d00200404940100a46454491501034442c0c010301500183c103800300030258071249451a00081c1001c0030760759074104041800484454207100e840040241008401210f071402d01039078100300200341d640c80c0d590042d100211150240c900840e9502901200d0700b9090148001400f4080302860700c0303a1342070740c41c841260803440e040d105202203051008000d010403c00d03611402d6800201060140303190f801025200030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 819169748 1250 819168498 819168547
    0x10f0501080a02090d02101d1c060c1b0c06080105091915030203070f05040e07030507050d0c092c34330f050a030f06050315010f0902031308 62
    0x581704140b24100d900510450809452582c23504207440b4020100720100c40d40504603a6150b02c4c02d11554085041a40b09805404044c00d185409038654040c2000301513a01c01e086074009502d18050203887e41c0200c0103030040c501a40d0303410240c1071a0b1310005038881405180d0b046259120030514999440b020b00b90300854018047d9540d146d2580c42c040c240d106c0074040d22f400749081200403040744000142d000e08894112000d000d02c64103020800100d0070180d0307800d5a0740701160001040903031041c81150501e91f40119841c00014101c800b40c40f0701c540401c2c250b4003a400c00c1c55030010a5008101286650060f9581e907a10403900340780407620401207422200c0b10000c244405110301c40310403103403e0300488091003c0c4c29100002c6084801118000c1c00c07600180081c420035028034029000b00c0644d25090b0303404030307081e0303100c03001300b4a0300ca10f5a1a481e80d011814004002400c41c40b0600000f404640c0c2d4158034ad4545a8403403030107103a4507d40100312403000a40c80128800b6030503c40c54a04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 819170998 1250 819169748 819169759
    0x30604020f070b0403030b012c0f0a09020309161d040303110c1c030612030c0f060e07030302010b060906040909061d0a06050105030d2705041d1603021e0a050d0803040308010f0501080a02090d02 85
    0x2e4078cc4040000a410132240410306100701c47c40710b00c41100b813040000032951101c40400555a403402130940200002d08224180b5480e45102d81e00191460302509409409100801c50700440400d0307917a0764400c103c140b200349441c041c0305000e103101000811842c02d0300f50800100f00042d5181c0035400d0180f90340082d00051500c5460424007002040300c0c000c1301c0c041d40c002e1007000819010410302e40304c0c0703203242540040100010000d191003904020216800f582c80010388481944400719007101c1c0c0b0a00e00c40d00e42294124604101452040c1400340800754000c0418059000002c2c0c030007100880080a030181c5070005103848988003001c4000391802500034081310318000710403c0038818410010300b41c0c1c040c20700c1c1020702000785003c040403a5002406403080030140340d0310700f4804080000e600c0d00703d00c0380c0300c000c07030f0341d4403107041007082580304203d607550320f15041c1170042400c001030b0000085024004010082c2c1d81e400103d05070000a03c42c00140e488028100188203812844002034016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 819172248 1250 819170998 819171019
    0xc100507020d0c2916030c0c0b0a140f04050f190608070f0e0d11060f030c090301060e010305120a0908060907031b1208030604020f070b0403030b012c0f 67
    0x640c02d2240c122440214540407850144010b408134152605110949400c14420010100b01444807004050700178101110520342944540500da45603410000e20b0003000284601c030264409040c018088403148941d041c0f14008100d1400c0f40f00d1403180b00e02c294102e0354050010381c0d0300c0501007034040d15994070341d44440c2c1d107682c060b182c80c0b01200c021000c5540385090451b120300520741a68284801406545110065030b10a065101d50b001441e4200b0000e2064801008503d0025806284104c2c5581e4480c2801c3c01014250341d0302e50409615404c083c0d004100007030b000510f94282c000010015901c45481c0d000440300700365158041d078414403880c01130140e00400440c0c1310042d0703802840d500880d00c2d908070381a0403090b05446800d2040c4d11129091000c505040040c0d40c000b0401070016281c00341c43c000c0c000568000d10300c192801e140d04e005000406401d4859018090400e0a250810011222540c100c04420900c01442d480003041c50000301e9440103a04400000000c0c40400007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 819173498 1250 819172248 819172253
    0x180109050a031a0c03090627010c0e15070308040b0916031110021b0103050414010e100f05070801030605100e0717060604030b0106050c032710080103050c100507020d 73
    0x16070301c0a0200c820048643d030114084603c000300f120322a50444000f480940c4561121a2004220b01c2041412114100020804810078090352001200703da847c00600c21401042080041d440c5a9048071044200130310400a40c0200f4202d030f0064001c0c018001ba0395864039038a040c81004964030040d400c0048001c01040140f400c0803080c0748094481e00700586214070305907514009441e01c983c000704507401284e03281d072098221a501510a61081e0000c01e0311407140c50035100307411035588640d04210f898000e40c2d1200e201e00780071038080b1482401079090a01d0050000d45041c0009070030180c81c0c4000400d4581d01c6500c41c001455001010380d418076060800500c504200d8080140d000750f00c0000c03403c545030032410344d03040c1c03904040d0136041a464140c1c1607846034441004100c06010500c1100c0c29441c82003028400d2250480e031108046400d0b44c2080004080b040c1080284002040140049000018402043d44040d1403002c03440101120984460040703840007036001c00980149401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 819174748 1250 819173498 819173513
    0x603070207090528061a07032a120801150327110f060414060306150f040e061906080702160906030b070f23070807030906020c0f06180109050a03 64
    0x1030b1450b2158100480c04e2180c83c1481c180c0c0d40d00d01c0b40c9800b1003088200c401e002d801c40f00c01000307518800d042c41240c00707a02007211001c41c4400030160402d400c0c90f0340800c0500031079907600c2000d00e84d18900440c2070b40c1801601c860458002440f0410195135940c1440e003003107000398808042c0c40008240d1041a0240740001640b03e800107000e004038203054018500741401c01c01d48041d20a22140403018060032014030540d6000149100d034000700c01c180d080c1c010f0745044024011203441d504000e0340c41d803c01d0382006900b071010b0440c50180707000c42404002a120804401e05480321460444501c4e250543c0c00ca00d4094010000b40001d1061000001d4951040c1c0c020002c60741303e115403020313590b01c1c00410b907000044010360401003100000b0410401e0280c1d0b6030184401c80820644d4102081c5465800c41070b000804100d01045251380144a610f030100050000d0440844601048002071300c0031400d10b0269000c00e10401d2281200c42c00b00e13a0044035000301520740501aa1001e655034144000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 819175998 1250 819174748 819174781
    0x41d061f030c0b311e120b060301090c060305041e05030316211b02010c080c090423040c0e09030d0b0a092f07081603020a080408071d01080c06030702070905 69
    0x10340681000003101c1d900c00500c003804101e86c3d0310350b42d0b1005660141c03902e900380340c401464079626540c1d4020560018030b501c40140060b0801c2c1c2d80c0043c9a24051620843c126006282202c071404485400d1000400000440394050b80701d01c21a446003040d544159900282d04111000c02e04445512a90070801c0760300a541300040744050304507107014024180d003287c001000031000a03940c0c0340041c0c01c81c0810001002e402c1c00280001410030700e203940d08165000c4601c2d01c0c0003545150703c280400d102031940000007400d4004018000343c103100c81d1083da00e106906203070400d81e07120b489069685ea1686042c00c01402800414802d04020011304003e6090501440030783e11200c100d00c1c1c800c01521001d0350140d45e031011413140b5080c924480400743c0003884004804501c5400b901500045010740540000c1003080300420110381803503404001c10300301b100b044c00c0c1c0e101640010001c9610010b50407000c80c00030340d0103598035241c07501d040b418009540c002202c01410201400140130001890740d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 819177248 1250 819175998 819176009
    0x11010216020f011e051e0c1c140304082703101d0d030c110105060f0405150a0902130b07080a0c0213050103030f110f07050f041d061f030c0b31 63
    0x5500c0c041820304a141b082c0914840b140b010f6000d02e01c1c840c4a00e60704292985804814100306160b40028031246c580756200b2182121400c0c0701090075125100d00e40355040440e45814400922113800c5000b00b56030700c86980c404030109032609420000c5091086107400704000800648646004089001d8098015142000b000859000b01d0031107021040c410940181c0303004050f500e0389050101000040c1901814080b0341400c00b4070203004c5075652030003c1000b040301c45c3d0050303212040d1038460100c142c4586c1c402d61540400300800c10000d50294101c86d02040c40d818250454401c0f800030030004201000810605480d1030000310901d03800c02445640b58a4655419408100d54102c06032503080b840700f00d000c9540681c2c002c0c012443d101249500b580d10281001500e01d2500d081c0d94240c0000d02501101078002005101500c00242c603100030351280d101d000030415140d80e4407103490b821144a01045000c001c207a0091b4420701c0300d4101002e850f070100c3c107454030b0000b03842d24900704c1551084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 819178498 1250 819177248 819177277
    0x31801080a090828090b0706110c03161205090f190305030f123727060c0c02030a030c030e0901140306181e070b0403030c0311010216020f011e05 64
    0x1d04c06842c4030b0f12101003900d00040f00c071130a004080d43c542020f49100150410b014500b4800c0c00b4903068204003829110880c03204109800400e400c3c410045942c6a1a010800404001040c007540b200718014a20400c1a1021000307030042e144a10390b40c5495400c02000b5010010f020000080c134480a080e003500217858260b45030703c031796149114040712081c0c048030110f1414800316000200da8820300c841e00ca14000822182c802c28a48844181188080341d00701218080071000e1025174410140d4034101411f00250021440e0002507880c0210035009081000d10006401010b1103481104924a0301034882040347d61204070300c05021188180260080c41140700080c561060900b0011500343c0e44bc014013001c00112100684944a6017050310f400c2c41400800600c20700c5402c010801180281d54115516a1900c2c1c0201824003c59405010760f0050060300a60310726500361110043c2e040321091400c0781e0000040e641a0030b007100b4480d03519010034100407450b03041002070180700a00b020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 819179748 1250 819178498 819178567
    0x90424080105060a0311010f090321021c020723090a020c060609101502070e010801060e07020705013c02011d0303040b1b0712020717031801080a0908 66
    0x1400940744c0e080c480540b07040d0040f1100e02241d4003c000c0700003466243e14000e1505601c9454800d80308103074402852800c4800c0fa220300e4101d605008000122034000554074840c1c0302080000c4d640c100501502030550006000100c0d9082581010346440d54040c3c06c0d51410301d070071030b4910000c7d0800405490340e401840001400d074600010000c0c440d101024180740740608000349403421350900d80c1020194030403110042742035210319039200d00031b100070000800d00609040d41e140c0903410141c85a005d541c0051b5082c407041e070308a040d082032280c100388150040c00501a030203896048602c80600304000c01c0c40c41c51001907042d00030340700ea1144910183c84110300450b0680d980e00c000c0350040d01404411020401e166422203100294038102240789082441a0300e07400080c00403000c40501607841a0010403c1c11114040b521041c51004040e6003001d00803020711f942c0368418520f042c10000c060f400600c501925a1090190342d40180015448007669000c031841804140340c0e6503008450b080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819180998 1250 819179748 819179761
    0x61005090c130b1b0109110a0509070522051002010506031b030601140f1903021f08070c0213020d06090b04110a0c030e1f11031905090424080105 64
    0x450342c204002c04070001005140c001c1000d07041e00300b40040c102609807000e084010034024054445401e004600f801240d0f40307d901000303240012944442c0c022503080c010409025005825900805802160020780d0050322683c5e01100d42c017900850341c065039180700400f00c1c0d07034150710092144109030100c0307405000c00c1c0008072100e0800c0d0421940365005030b005003c60201c1e048032034a02c000103000d4804070084400080d6112040c03818064004c8101c560810070f61400f000c0c900d40d058410301401c900900c1c20b1f0701c01000308100604950a00118100400071510b42d400c0b12840c840009034115128a4581352001c00342049101d4040301a0600e02c01c9001031078035216030300070780305001c14a034600640001d040d154a035035410b040e810b1000d0590303420715a40b00c0d0700d9440b6102050200000c144010003601500e00c490a180c002c14036402809110150302d04201c5002ca07103419400c144d6210320b140c400003006000110718103003110089035030118500260703d01060503504031074002d001558981c4c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819182248 1250 819180998 819181021
    0x702011b0b0411120705040f0b0d051c0305040308040f030210060b13050301060506041a0909340e011404080d1e1b03032a050c070905130303050c0c06100509 69
    0x145100013194105000c2001646015031040c40c21031928036021600180c04000180a2420f06005071890b8001503a09250b150980140b4021680c82d41010080c0d410242c40052148400a00c0100076002d000c14900605000308211074800701d512005102581e11405440025000007408040008c640c4202150728038041c014802500d1000e000b441c1014a00b0440c00c00000c80046e105034810400c006002d60b031f4039040002407080d8041040004400d80340032120f1590340d9001440c8a89039002e1640420f41e581c0f01c0c1c3d00382880b100034641010740c03a0f942e00c42c140c03003841240c1c0441c1103881482c0303030398020a03000900800d40e4003100011038406c00801c08196079044070801c409440040c9114601c0c0000d00035800012a0240295404c03200c286d540e140c400f804441540f000c005c92400315500b40880c1040103643d016204681c002c7c091401c001c1601280e20b04091401014540c40b030000a4101150340290780103a032144044681c40d0800ca9002d40d482d601e980543c90194014000062200411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819183498 1250 819182248 819182269
    0x20307060504080904140c030723070c052d100314040c210b07140c0303070201150b0a0509040f02070b0118060b030c19030605040903030b03071a0f0702011b0b0411 72
    0x1441f81c108e103103170789651040b100c96502114154400139203400c4c001d078100040d0003a1030f00301c0c4a80903403a00320381080308019807109080440304030480d0340c0203051401803060034043c1c02c0c00c1003502c09202807c044c0c1c8055001d412019162410440f0200c10001448038081103401140c0000807242105076403200182c40c1e5480c820f80c05445000160003003400e2602c200081980042c0b544000381c20116440c0c178543c215403060352b001d80140e444400c3c401c490340c0280c0d01c0350002e280404d01203181011002000d4514000d4032089131140c1d680d000c4122550040c0c1d011510f8960b40681c1c491400d68442008002c1e84083c3c0d02080700316454408007181000c5070b14212402914800001414005100c842100c1201e914644804054071028005100e84950280702d100038460744010444041c12014103103000301542c1f00300b0403600303054103400c141410b40c4219880c060b070880040c0c2d0345004900051303134040c2c2e180c202926106203600c2c55609000d140c010b0103029510a0180404603984d41080010f0481c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819184748 1250 819183498 819183511
    0x11040f2928150203090d060b010206070e030a0f0f021009060807030506010c020d050f01062d060813050a020a090e0613020a050d1b0605040509160c08030702030706050408090414 78
    0x210054240b08401440c07404519842e428411039280680c0301020031350a0411030800c0320b0a07901c8004040c0c0560f0103204850b4032812a207084041440c50030300082d039848074001301600c2c1c2c8000500340c00510403c49000c0320b005802400b82c1a10440007240141003624500c28400000e0faa103000c19035041c4240070b19405980165101c02c1204c021303408008031a500414115910308c6824280d407900c030b5080c01040001c0104403000181c840300d0b4060700d0f90901e4480790804a00c06900406c2c081d85421103511368200070741c0114007072215400d240c45881c050101e00084c1d8400070176500050036564640290303402c40010001e950729a2110f658103000e1118030a402988040440c0b0103003c0da00780000801c4030140a007401d541d000c0030210410b100809150402c0d4000307800003805110504080b0394180e00150b1520329813022203030012008040c508040e6000701100d00020104001901c20000d032861540c00c0304e410441030a003440c06d48a261700400c5110700860824440c0d504030a00c0c01d0740c545c030464 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819185998 1250 819184748 819184819
    0x3090a091a040f020705010f060501111609050702190b0103020a15020a11060d0501140a0e070c030c38090102040608040609050106030b040c0f0f0311040f29 69
    0x401c0441044041d0164000b000d010b03d0303003405103102040d42400341d00c080c008103040006c3d000382032270001040c480741f181004c01642d001c18004000003003a00241e000b11110440c0008030350311010001c074140b1a01084500d49860314401240900c10485075803412a803003142d08038500ca41c5e804011241d501550b00020158101e062450041811002500041e68005240c1450099020700d00b00c101c41c0e0070703040202c0c40714602c62a010320b4288200c6076005014840300710f01c40341c40c0101c0d000f401c0440d05a0700034200700c00b2054020400001c0c4142c644042d0442d07c03681c1050a15003006105030f11101040c032b620f00341c450049004800c06100300c2e410341e030080e6505c0c0125a502d44503800030341003a8808550303e6580b40000408a504000104d002ea482404180481880c20b0100804000c05400911308051090020400181048a040b400c1d031026500440c0b8100500d0200c001420080852488044a84503034800308100c0112104801802c8650728403141600b03400044540f1500c0c2601000d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819187248 1250 819185998 819186041
    0x60d171b1c120b0f130b031212010611070e01090f0b19270c08042f01110f010e030c190c0314030d02070803010503010c080912091f0203090a09 63
    0x500d83d411000122401803c0001c1c1c184a1340c02084420320b0448008400036512070340c100c1d252400344030199680780000202c9041c8210103580050121042c8610418070804c2ca01c00d0b00c0300030051054a00900d00701290704000d40c0c0d1469002c01801c04810b49005c00303483c0410484c0b052402150700c0e130031441c42038283c1849905201c0b0580c01e5030748606218001c03c3c20340020b0054a915401508880780c5544c1d00d01c911400c16141c00f2900c42d400d100300c280054110400c014450701d00c60001400d4a01c2480e000c41e04a59910400d42004040d1030200c0c0d041d404c00c1a48070420f50700000410505101000300d6544056190300000900100c010040014070001c0b001c0010840e102c4000150020340001d5901e0100920321b80c02c12a032145500301d0707042c20b022004002c5482c080c82604201d81880c1081440f41c603080040c0c9071109031000c5511b20300c1d400461038044c10344508204d44002079205002c1c0c3c018441505000e590717600400c1c040c6200d8240e00300040703060815401381e041c00c181c120300c000035071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819188498 1250 819187248 819187277
    0x2030d020a08180d0c06030914150f13050601030506161422080d090906141503091e03070606120512030406230103020301061d060d171b1c 61
    0x100109141070584c0f01d800c1d201031201003040492484000e01d40d40e20001840505032509085001405121b840150030140e14a22038214500c401c5922100b405441d03001070303a44d2240109406d50380342002c1c006110b403070000b208024002680310302425540440304060b104050044402c0d43e040310b6452560102403080761645080b003650350b149050000303000c3d4902a2250422807504443c030501c403001501c080003c01550002d4400c1c4805401322207140015002807001082c10000003200801c40d040380080043c800202c00e12410540401c5d0380c15403451a51803203001560785e0084641a01c0c0d1078a4030710001205041032000c001d040790702a02030f011202d1200c03048a22030b000203106a034410f444950b039283d010341c186440c141400200120042950542c0180740c215071031504903281e182103040d000d4605542c3c01408c241d01517811140301048000c2c40c07401008244540028050302c280100d035004928184100c00108070414004850409480d102e12807040500e01140b40041291165002807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819189748 1250 819188498 819188527
    0x3081803040f0b16050f250605090d15060803070203101e020304060b0411122805040203190c03032d0e0406050a090c090906030c06080a0e1902030d020a08 68
    0x4d003a40350407a5003040303840e0b0f03160079080c48004039100003503030001500c01e0340080c0d600c2c18401c0f04000005004608500340b107006040703442103114651080c00343d0401c110400c44900f01600d601c4140c52400d200c01e541d80c842150b40c0b5040440101d10030b0061010300748181d8458800c8800c21040344241c502c01025425024009600c041d000343ca01c0c03921220f041c0102d03180c1e0301030412140300d0313415103503542c01401500c610500e101070012080c3c1a003001c400c040f422913481c40d00700c1c80008507400155644403440060301e41703c4500c0a01d810110110070710001d100010b81244101c80c0207031100c0041d40c10920400401080c20716071070280e40c1521150418051040c451285e00348030140c80001c62648803c001600e407509580884c3c0c3c081d450384c480d0100a6400030940005042022050010b6820741d55108122641030040320300704440b001c00240744074030640158485004901c1518041c1140104030089000c0010041c2d00034800d041d90070361901d20000e501000e0035001002607060601c00902e010f0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819190998 1250 819189748 819189757
    0xb130c080115030b0447190e0103210206011503050426041a09030c090601020304030b0c190e090610020304030204020d060e1e010504052203081803040f0b 68
    0x3410155100c504a030980c80b54496030340010b81c05004030f9011036103000071a00001080c52100000030303000046c114580100c12802e02c0689040300d10000302e81426850b0182c0b40c850760f010b80d4803008010000414007842c01407070b00c01e001d0307161051894450009000daa031001c0c20701c610140c3d40c000b0003d900000e48280e110341c0d0040d11455018410b02c06242d0003283c0904c1041c0084400c501c009010040036461081c00c0344001240205103050807003041c0000e0711000b0259400c2d0003180d0040000342d046e8402e0084030b02456015030314010505003000b00110380e0700320352038407102e0f2003116210071303495805a240e0940400c002440b8150070b56400051160610700c02441c0010340c80103110202c01aa00c40c00906524480a01c0c0011080c0c0b81000750742a05a018003100a060300c0340505d051280d0748603a10505465040ea00484d031074545145c442103011040301815070801958850b14100350f44202840c0c0a115480340307030300701112107100860b213034480d500c40c4545034014210b003001300d0140e16001d003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819192248 1250 819190998 819191039
    0x30306010c0609020612060a08010b030601150318050102130b040509041203060510020f01180305070b0601120c0c15061215020906031f08060417030603010906020a030b130c0801 78
    0x3c20700804950210701c4d1380d045441140ca0028000d402c10225003012810007008043c448000c1c01030202c0000420307100c24040c0140d04110b1043c0564520050290300011540300b42c0c1414605515618100a8001e402c201c101038440d5614000004100c005101a0340581d04001c0c9000760030b44440d40d5002c00f421007522200c05041e2070300400a0b0a40c0c90b1200c03125914820703000f0300340300164500b020342140c0503000324003200d0340c0c81c41d031007030200f44c6c0401900c459a0b4409580b411070b0311220300580d0002003c05501020600f000031049025500006400105210300b4804659500752402d0b00c4c144d401ca4040d2a030050001c0b090300d0007089402103090400701c054000107161181150116101d80d10885e9024080419118054a0740d0923a1301d010004010981c0a0200340c01c040da1a0710036201000009400840044003151980d07800394451b401030355000004558440c0c2c01d282c0a000f5200c1040054890401c5980c000c81d40c1446010b043c070200101da42d0f0044680c00c244c66420114001c80d401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819193498 1250 819192248 819192251
    0xc0b1006050a210c09210308040f141e060a05010501050f090411040e04020307060f0509010815120d09060e0603040f140304030b011518170102131e0e09030306010c06 73
    0x2c4680c2043d640c40703546041195a0703500920581000c40c0c001c408914800d0100040c464000e00d0070109134001200f9401c81d038080441620080541404100d900402e82c002e84603024041401ca1613500b54450440584018429078100350784441d4404110342003442002e002c24001c0118034039003041d903002802c942c20001d0000901004105100c1000c0c0c10940111607415010018041546010060500244607601d4408084000c201e00100a07001d19030301e0078180704010000c1200c4085811b00710f2140c20010708403c0c00b80803100b003141d507110107400d0300320081075520001280d11840f80305104607000000c1c2c1024034684403561209040e400b2000c058611055159080f4107409043c002800114010a1401c01550406104a0241a8001c0c80c0010701c28400d0302c1d414400410000442240c622078a01549800c060707003406d01920840ca2552400e020001000c114003400a00401ca600d40304002c41084c00d484040f005900d00302520041c145d80e0003400080c109610074007031000c5007413140f4030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819194748 1250 819193498 819193547
    0x3261603140903130816030206070c03060e01060f050a03031e02031902030306040f1406130f020705010e0c100221040e0103030e010809070501050703050705031204030c0b1006050a 79
    0x482214542058810701441d8000084c032031440c80351810042c02a203407001c05042c03c0300130013080801000c164480207001e80c201141c11002d01c00000c46e560029a0401d20a0054400c0a10628020b040c50302400740c0f5074400d00c3d0040b5007828404045800d0701d50646440322800b280b884000e0b011001c01040c803046100c02c10004042e0342c1171100f10780ea943c000b50025912400c01c0020403080d12005136040490f1031a010141020741039072000c16400800c26152616000c001145a0b8042c119045006052500005440040102c1540041001c89a401c00e0741c00071034244d410086580200c0e0016801130740680d040c28100740307030312040040040c105800c1d107141c13a50743c0900004815099200343d021412504401c6050b580102503154850360400103020190300340350000e8141d02845801800304440480c1d1385040010400c12202c2d114144182e01e0607a26251174002d0404642e10001c98001c01075101141401515510801c00e40b00380d41c494600700416a80f04442e00c2041030030010410481c0704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819195998 1250 819194748 819194771
    0x70b0a1803113f07020a0e040f0605090a03021b180c040909061b0207151805120106080f0a020a0302010f0302130608060f06070503040e190e0a03261603 67
    0x3034201800c45003080c903809800e66003040d10f8041c4002c520108160b004000c094016513541c0180c40560358001903101c003546460600c40400f101c922402403c0920340010f0100800c1c00045c107804282c441d030308503000b81c80010b401e200d500800400a40c1c201c50801b041d02803511201c801903a0001400500c1c6090541e43e000000c191001060155420b46d510030503204003400e60710101a07a1009800108081880c0801066204204c02c04140800680d90341840c4044440d00c404001040300500d03030114800000702143c000c03c41d5215080f114400c00c5524001940d02007014900b1940082440c2556891a0010350344001c8040d43c0c1000c0503801c004039400403600c0911380002d045542e50386c0c0654605038080c400e0340c007180000b0354484c1c0360600c0840000b9200100310303001c0e40c082d4045d401d0151280342a42c0070440c00920380c0e58405080920403a210203001a1070082c42d8042c0c0d440038206072034403a4841c0c010080c040d01344c62802c0154005801d0324012402c001c07240245150000e95220001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819197248 1250 819195998 819196033
    0x14030105090606070b0718060c150f0f0207050f1603080a0c0f0b0a1b050f0d0c030207080c0d120501050303030615040807140901080c030a060c030b04050408070b0a180311 75
    0x80391aa00821f00400d005690710b00100e090714058a03581c03e292408141b00d84907040e50006401e2416020341d210031070302004550b9a0861904e41c4203501d001c0d529401d044c40d1960f10382d042c035490600580b0444803d4407001d0524008035040f00d0300001d8107442c040c00c0c10340c1160b0400c0b642100b03032291a0a8006e2000241c0c400140b42e204440c1070000051142d24018000c0d481002c80600e5400c000c0203000c20b0000854082c00c8558092103c0c9001a08004005003a4081c4c02560800740000d2000700d0380e01e1901d00c01081415074803503d661458480d0021080d50000c5a80038010f654040e44280005140340c10700d8290b2107400762860020504055586c0c803050b01e010040d4020300701804100746448000d0604581042c090724600c0f000d4244a01d400c80403995580d00a0740140a9584400750003503000e0290303021824900b800f41c4103000e036181c20300f4a4086613005203c1140d02ca00c120700001d0301080c452094101d907150114004034600d0322502c0890301140e038100b40242a00415000040c1076454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819198498 1250 819197248 819197251
    0x20c010c110114160b06011d0d0f21020705030706050d0b0112063f0b040f0b1006180f1e0f080f060a1134050102130614030105090606070b 61
    0x80e440b0400128016203450030440c05d018040034140142401611031004002d0b01212044400751144034074400c240c1480c81340c0c42c0c1490000380c44418034800c643c14804a181c80082c6008068086030055680d0b8010f00d0f5541c00b00340f18480000f0300078804918046885d800a0800e0036052400b01c210f1020100c14108503001d40d840303003062554095081c18101601500080514109506c0d586025424062814400c0001100030710700c45003000000c1c01c004501c1c4802101c140c0202c45000f4510b06400300c0c0b142c01c0001d0203400c021820308081c0f41d609040303410000c0280c8171401c4901003413510703210107490311480703c0b4044003a200c841200412a0703021031851b03000821015000780050001c1d40c2c1c0342030411401904894819082007d5030122022901c11980600440c0304500d22a0380c140104003c0c08940c90102c410100102c24a80280030054000d002e201c00c108203901c290a80d140400e4600034404013240760100000d0004011b0b52400b4201031b680304c80702030700041c54040d045d503e00084160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819199748 1250 819198498 819198517
    0x3181b0f0e09060a0b031002040905071e2109050f10180f021005090d0c03020103050c2d040807061e050a0507021e150d0c020c010c110114 61
    0x10014810050a11058548402440181100d40d118248074078500c0d110000240600b040c692030700180503840d01d04118201d42408942400c540325503c0e288820040d01043e030303000002818103050300c10313070311100d403c4c0c4c012036003190b210340e801d84441d0600d5028000c98003640b03402e055901d09001c40400c1e424400c03494030b00440c40141c60300f900b601128808642008041400100c103001c840d100282c10062540c54094044864580010005204403424412300503030a42295420070702608020f00c4005941c20380703100744c030305101561325181e202d0113174094544503d4a0501141448840341007603030040e10651030009400d480d10b074980c02c805241c0700712a4001700c002a51041100d0800004000000340c92290f850042e10b0000016001040c0b0300454101038410500c0c6901c09000302c0100514107145c45000d4070620410307149054146482d00269428503001c1d090102460050f480440d8406010405031901141d91402e6120b500320403202c00040c606001409141c500f5445ca00005440c0020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819200998 1250 819199748 819199793
    0x10f11030c0717160f060507060207150203090d08070e0111120f130e070e010516050601140406050f060301150311190f0215010b0c0a0f0b01050108010b0702030303070318 75
    0x1450f002501e1401d02c003c1032030740d028070b1380c2e020a20510000c0c284403012a01685002c40c1c1300e104c5401d2a10080c0f061050003050b84820981c2d88900c2c02540d00079500c20401c1c1003e44581c40422217040d02c2c00c030300c1141c4460025240b090351030311541c0038480c120103048250086600c4980c880c040da2a1941c000c00c5103035070f080300c040750300341c0d04134050001c217009040c100c2001c9455003030400018200c0000b10100c14103004002c41c0c003201a1010700c2c186180607410108450072035a5821100026101d0300e02d425016a05007000401c090504080743c0700031080150900c0d1940e8a40000180d0008032107002d841015114504118070010f81405894a8280c203c2650307001c0500ea88080c100341c142c00b64a40c155008250fa04039130740070803030b038060440b00a03002d1655100b1814195500303110f442480141031401c40e07144501884070b1910414140c41013038039080da050740c90300c0d0105802d025901000b5415842080040e80b81440798200307410341c2a008100d0b40340400d003036890b20407581c1d00061041840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819202248 1250 819200998 819201029
    0xa0804030b0118020705071202131e06050910030803190504030807121404142112091f09110315070e010c0512090f060309010605100509010f11030c07 66
    0x4080d0f1030f0707031800c0405440c142140ba01413103a85907a2914164802c021691446042001c00d40d1141c81c0c01c0041c060106004200200204407908080f00500c18108142440d11380c02150506061070b4440c0582c844210306502c061856492660584c8010410100d0744c4441541c400c600b411401814080c034031940f81c4140a00c0c00c1c80006110021542c04020440d060020340c0c1807030f02c0364540c1c150300180c120360745805a00f00c0b010210f1414503150b8015100180b8111401031900c03803080940000c100d00320024159450f201d039945d9580040d4140e1180c5143d805103004420900d40c1c0c81685148c2c0f20f80b40d8000600004c000103424480c8090500e54519012020008003a90010700481c4510342402d00182044c0b15413109680d80640c54040c80c0908000030b100465991410f8010707421b984020011076803441c00c07503c1140a812140b194034000d44048050b440b19500401c02c0e41c203c2c040694903480e030030300c882c5800c64100e0b250714030041c0380b40020050380d900c50034188100303030103091000410807a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819203498 1250 819202248 819202259
    0x1c1e0b090d03090b16030608120417010204030822171b01090b04031401021e0c0c1804060203041a07090f051f110106081c02060a0e10020a020a0804030b01 68
    0x20401e9031030303110003014604030620700002c0403a00d5103a01328240407190f00480d00390610a4000705134a1304240c03018030402e60703000c1840b90388000074400d40320245c80741c144140310810314501703034025800001c00c4294240a4000202c0003c01c2c448003c02110743d442049950700c0c84103a000d004150084551740c2c000c1d008020740d0911502000c07002d07200a10341145114a040d90030210340c00b9034040105500199a86055400ea007501a211030034004c2c00140e22803000708604286e2a80150f0116405010b04421348000345000000e071004140e45583c0340d08a551182d940c04000e40c002030013100c8000c03e00f0189481901844e150501c5005a42c85111969040c188034040034400c0d40d12081c8149158203580d000c2e811007c128203000304c09810081400014070070703514003420f21074000c0d041512031202c00300b140203441c14119201080c19000e940072915401540000d80740703481e8603400d281d0f00c21640c0004008840e8010120143d0f60320546010a103c0c2d640c0011550140c1e0007030f240d030198000144030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819204748 1250 819203498 819203503
    0x70503040201260a0c120507020f0f010c021f020705070f0504060b0301050d03030c14210a180825080a0e06180d03110f010f0b0f1c1e0b09 61
    0x103030300c000401d5031511030f03203004124403200014115490603440314100740032a80106030940106104c032505000c10707c0c0c580390080d0345400d10034450704548a5940c0c480b46400c2d040c440e0180703444640c4d0103080349074045083c0c4804d240307400d500c8107200c030390811481020500a1000c013000e06003800c00786100e00e103841c0411040c0d414a411070500c004040004000725591140050115641800c011039402000b49003521499991001031014510008a8401c41104181d500340f1380da010210755000d03615002124030031501541c8002000d265200d0001020a4040c0d016105d802c41025487c000e800020420081070403558008441076040031802c110318030307008064001007003015105c99080c1249020301e601c2650008101c140503000450110043c18031034140380d18003c0720801110007107a8200d2081d402010500c070804482c5241c9512400f50f450501074110300a500101400240c0440503c148484082280100d402307012940041c3c207140024158400028080c2500210134030705010342a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819205998 1250 819204748 819204767
    0x30a02100c020f060609040602070f0b100f1d0907150201091a040b010b0d0b1c03111204090b0f0406030503041503050c04060c030c050708010911030a0c050d060b09070503040201 78
    0x8080d500208003d18841400050642d0300c207800302c0c1c000c2010b07100c07400c1640080c410180d02070a0300d08080e82c20805e01844245050140080030031440450380d95494241840b044c0d4007844032200c6100100101c0d030300c1003c42d0360307400c4103568050791102a03441808c0d51401e60004070b42c0c001f50351107001200a000c8400f2203900b402160a210381c00a1030540e5910150110500420000c170002140700e0444e541103600100ca40c81018041c0081402005102d06000710140b80840000d200d0218604c61511b000c603158003150340b0903000a0615060004000c058003542101c1a00402c4400301c008250340c81d402010011070107100076695407420009001310be03860b04001501458140030500040d010108101c07011a4418605100f02035483c0c07800321941e20360108007400c036100b042000319000806600c540c24492040d040307201120030b24400c2c161622080d01000e4046003040900300078030f00380a5010300c00c5601c2240e00061a2243d080003034640181a9110340000310044204011960800250b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819207248 1250 819205998 819206021
    0xf03140708120d0603060204030b04021201271b091d0303041203180629010e0a0e10090e0607090603020903101107210f050408060423030a0210 63
    0x5240c8241000d054564468200000504401e000107900b03000680b03c2c0e0140c4051584130304259521a542e04082d10742500948040c0d00c01d4207602c039010082101481448040c6400303c2064a14141c0d20043c0071011450745000d03501d0a6001445003a041e01d95030a25014011448000522404003ca862025680d4100d0b040302035000700107000c00b1501c80605212690024540807501c001e080130128019444410000d10240c100400d01490017800804542c51424181141c0808100c84004480c5100d0302c80d0040c1e0000780c00708017841a44c1c40b81d4005640950002184140c00d0b03510344000003111b0f11507505240d1074011400748604640d010018030010f0109250a5090076003840005c0e480d840000002c81c1c032195108e041e1800013540360152a42c0d9900401c2c40e10003034900048424140c2e400c10000e000107918008510301003801402600c05813020000204895502c40d510014440c812079a14171040d241c2104688010700100700a0410303211340c1d0b014026842c14075050704151409031104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819208498 1250 819207248 819207253
    0x21b07030302151e0a061e0302010c060b010c051002031e0106080a0f0e030a0305010e0604020309030d0209030a060509010c0807020d0e09060a0b0c031305090f04150b0a0f0314 77
    0x100042940050390940072000401014500c4d12a482800501c44040500500c444119000c000c041e00c580e50000c81150f16001e8200880d040030701e1000601200c50100902140c1d0303036480c1c035010900a41c082c00c00700b001810030741c000d01880e07124549801031040101c250580c0000800c0030503030b01e2010100c20540a01049500c075418008041c07e00c40303004007600411580d84c4180e84031054a41c01c40f884920b82902600e41d1120343d203070000c000d490240612954841c400300414542d0a01c1e208403442100124051400d0240d6400105d0181d8450b40c105581032240c02e403070801080c558480c6c580228060ba000107520111703040f0180034018024840c0c070a41d000f11007951032407034104014165100045501d102d81d9034580000510091154004014591001ca0101113003900000285801242a424440d10310350b44c80402013403d208036190100e2011010200d000503c4002641003004070b04080854001044004161601026800011114010242042030024602e010816420200701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819209748 1250 819208498 819208513
    0x4080f0303010e0c03090703080c010606080c070c06121e0203070e10020c04090c090603050705150406090302090c1c0c030b180f190e1c18060509060715021b 69
    0x39500c1d10f0080c5101c1040ea00040060b0b1034917820700c0240091b5600548040d00c640c24030613054024a80ea020307010119005002082584140905441340305a000341c0c0d8920340360030080c0c1107030b4100202c03240c00c0800d5240d04008a03020090400700310b00706411800140c881c540108000e09071001410032a001e0f0281c0b1401c045011f03030206100280640645020401c0003242c0751000c2e411009510012100340ba00901004025011541d2811510110764103030049a002e044c903000e5128520410b000715401e8141000141090080f05034440010f543c0f10742080040400311040b8151010002c071007642d0781e0b00d5803480b150980300b05640e9120a42d151140000e00320f203820382448010341102c0c0d06c22040320009150410030340324002090311407503090240351603c2c44a691f030b81e8a00c03443d0f18a00c0e000a0086c4905500c03507021115110b4000b04403600f06845c0440940703896000c00103082c0c1024040000d000812003566603c0050407804d1401681c658144089145080300040c20240f41d03001440d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819210998 1250 819209748 819209759
    0x80d03110304210e120607020c030d081f0816030204110f1803010915060e060405040b06041e0c17090c090a05060105040512030306010305071806120608070b04080f030301 75
    0xb41c03000c1c0000d10310300301080c4050304800b003514110402601c4079800440c4a154017a0b122000c100a4040e010340c2e0216291040c1d10381c20162110100c402c4000040c1c8004006840880e142c030382060022640c00c0c0e00400d16481d14030150070b100c2c0c0341d03141075449041c141e401c2045041c24403440003039660440312a4200481e15116003041c2c89036402c3c0c0d00c00c140c044051403400d41c4d005c1d0300100000c0d0303014000c2c034030407031720264094054120340c4600a40b0344001000500c081c100f40c001c2070312603035008144c4c9002c1e603031710400c2100610f02c1041c000c0422903090001c0d01000980d00c564580302d05107031181c860b1032148489280c101d040080401c0c804d900302220003901c9403030302072420b9004800380310003090f10307922040101c4040c002e591040e58482c0c800ca10000400002200550042c002a6003d000583e00c2c104280e4803640c15414004103800224000c1069501c581014807a04c151504003240490b56440c0c1e041c83d0206541040944000000d010030500004000407540030345100301850a66143c0f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819212248 1250 819210998 819211013
    0x3181a120c2a100528020f1236060105040e070302090703021207030b01110a11010507080f030a06080709050903070b06060c0109031e080103020303072406080d03110304 74
    0x1103480640c1100940d41801d080607051203400065a80f2000801581c03514203404400541c1d03129650804284a05a044079048203000b04c03400940d980408600d00b00c00c0c00c03143c100c0120014003569400001c5803021080040c3c2040101440480382c020385a00b8106083c11410080103034080c2d407007140b0b45071116001c1d01c00496030b802100d030129840f07050366542c10f01c00c1e0302a20540c00810101a0410b04210903150140e2183e50044000e0b80d5031400c0141a201d802c0c2d485498110240010420f1081003400c1d41c4038400410342d99108100045c1044511140743c07080e42c01c152442d2109035200d01050020400c100207910090022080a0102d4109100c26030703103e214a120180c1560140c00024605859400485404d40c2c2c100008100104103402d008242981d40d040304498140c1818100c10034a1107844441d040c2e070b40090245180030202e40c0d803045181c0000030138005a02810804450340d0740d09120b00c2c4014254800500030741000340700000c0440701c415100313106c0e0302000d005010124082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819213498 1250 819212248 819212287
    0x31e010f090c02190c0e013812090105090d050703090b130509150901050607020616031e08070305010b03070e0d06020c010c0c0c0504061203181a120c 66
    0xc4200151000c510b020482c00c0c6168249600000649181404200000d0f10703400e0b0100c6500e2000c1d6101640c89400d2584203d010500001401c01c07400e868580d105020005100407240c051642482c0c1200c0c141c0000c0c42030021604003070580d56030341c200140d14405010fa0382035a502881d24030300d008900c1d40c000d411740e138280c000c0b020804404100d18149106113001e0f280034200092200e02d882c40c105010343d840046041c01c1d83e000303c20070000098142880350503241800d90042031103040c045a40100802c40d160208180e04100840b9a041d1022412820740702094040f80e03075206441c41c10510140640c1c106903c41041040d0400400038010f5205524685040088848584810190900c00e0180c0204542100380354a411009002e031768100c4c0001c40c03501e00c40c2d12000d08141e42d030700c1001b0840340741d0303c01c90219140d10f10000000a110340c01c980345400000c0000000c02c0d448050030022412045100c00d4240000100406010303030f040d178040d40c000c032903404035458640004009a0ba02a8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819214748 1250 819213498 819213509
    0xe0a030804170c0d1e0209090d0212090f091003021801030515100b071406150310020a0509120a0f0605060f030f250503010c0309031701061d01020a1205031e010f 71
    0x107110000007071045980c09a50798080c6c00506a96050a103907984035290781c2c4540d08003001d0b00c1402ca500d8481c014070001c1c0c4200c07400081c40f41441500d52414000c600c42e0081070014400046100800160f40300f800b00d000888448034600d0340c941c1580340c080d150121050b0b103800c3c1000180c00b001182c00c0b440c40a00280c818040146460300f0861414070070040900080c00054042c001c1005000d03400d80800c03c4070084100c0c2140e0341c0d4440408201e04034418030202e000042c02c108182c49807070400107882d04007091400111078880c00103468034079412000c800211400c41c1c035041072101502c0c119032100c440c407a0450140910346905281542c1c0c4803454a00607100020340000c0160301c1840c3d000140c020070b0054000e0104080500009009081c0c070442140810b0404600e941864259034016059403050b40300c0c40b416036378101220401300c094551045c11031142208100001e240026460f00c01e8000344c441c281c403030600503141c40d440710a210040c0f21402100b0010451000c1c00b80c1e112003140d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819215998 1250 819214748 819214763
    0x3090b03190929150a030c0e0405210d05090d0206070e18090303090706140921010906141506070b090c10110d09031208070e0a030804170c0d 62
    0x160b00b8039041d008044070303c0000080808a0180c030602c03040c101800d910400804d06120f114410714402c111800308640800703468400075100501c80751003620000303504a07002d201194600e41161900724a90203810220315129400480d0441c9405240c1c01640c0d00865440e000e40032080310136000960301e01c4000c00c040d00b086002c00100c0c0b07041e180c04d44111041c4000e0031280000b0728103408829521741c010f5030224210b1188450000740c1502c140c1c10038080311a04003d0b075160240c20313404c00c140c030256034400700d02040640803140c030820001d00c0b654048511440000c03401d20f41818614141c1c0c0c0008004a079091546414040a0342e036140c2183d000c0d07a40316094000680391758080500c0c140d03440d0b213090b0700604030507103902070f60380c00c041058000030b800c00850b00c0c0031204d010100c4058a0340e1200900c55600000c0005149000e00343c0c13181c0c010050f2501c001c18254002c002161000150300075280080001800c0c1700741140d2503603541c000d1720004010300c8450400c1c40030450320a840301d005445036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819217248 1250 819215998 819216011
    0x120b06070203100b01140f031f0f0b090406091812090602070b070c03050a0318050d030816120609060501020606030303010303050f0705010e060a0209040c0806011218051903090b0319 80
    0x1768054000303400a0950081801c4d1980204610101503a005888408003212540512824010b5501b8041e040da51902d8000d00100e203000708081c4a034114030b2041d50b005031510004140c1c55128450904c1c0000104034000352031050f4100303c000401030b64505000c01100c198103010207a00082c0340700807201e45011440e03480c90542404a45010a50401002c90040004440500d41d228102d070304180e9021036072280c2c1650f07850400c007201d40c64190080100b41c0103070005102c0c1945894441c3c5800407410206c001d10302c9070009004817511070304a2210a540c0300c205001c10b50f4100000c6a1011040c1c000311320710350664402030300a00600c0342d1481d554100191034002c00400b900302c040c00f444284220381a03401c0100380900039401c91a580e902030307441c180e17105228038401c180582c020501070b1507620103401c407421400b000d00302660311308641d40c0420070080001207040000c40f0b80c690310418002c11040030343c0b400802030380c03255002c1000c0410500900c0000010a066035402c00311405001900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819218498 1250 819217248 819217271
    0x110a083c03130512030a1401150206060603090a050d0f0306060809030d020a050f0406050d0c030b01080703150e0408070b060603220c0b0715050115051602010509090106120b0607020310 81
    0xc00c03e00782181010100080f01b44503c2c0c8090340c0107440000d03a0090b0100c0d0503030725003288a071000005085200181d11a0000c81d01e6403e12000940d0000300c4101903030301801c12900e456192003041040701c1c00040b010003514084507850f108402c050f184600d02400380307003000f841156481c0a100e0003454080d030300040700f4403c940200201d55200041c400d016807500c1e9103c1c07020f0203c0c0c201948840f001400c2c8407450181500c20710940402c0c02c016101e12505849025048008240303520000342c10f0f020550340461950f550304001c6108034490106135648030f460386000d2840754809001140500300a10500070000c0c009007036460b01018600807500c40710182e0819a081003582e6014044642001a4450a0050f03040600764902c484800500c12640e035113030146d2a03101d2100d06a000907400b4031040d140106268440041207005140880c01c1c140c1401c0060804002a4019404646010b8074130140104500580703620000444003241010041e0700800d0300c8004110381034480c0d076a1000407402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819219748 1250 819218498 819218503
    0x14152b110d120903051006030b073203150d08042c04050102070b07080105130b0303040e070c061b120216141b091006110a083c031305 59
    0x4190b003244080c669104540310280c031096142c00162086d000f03807201c40615192078011502104e034401288003082c1d9800f201203035002580d010f800030801c0110b413401d0200404d040340e4122046401102036581c10101c00749400c121400322518019145204500c010030440d400762400c8850308103820503402d0118040b0a01d00c02041400311001484c9001e101c00d0200542c00f800c40e640c403402001559445110090300c0305e0301d00f4803556034801321440851003403102d907030450075044a0280460b4201611103407914180f200413038a520000707141e07460302d0f01444490b014420a42c0d50314170070b801c510051824014000b81190400c1e0b00e05940010340000c3c90701e803901c5004642e0703400a4801d11005501c81e45142c49214403010011203a40d2014621414604090350034010004855020310151030018251441e042240044110f0f0203140341c2480807a40c2d6400a11030444044540030219403201c684924213403035448060880c5061007412001e6041400440c0e412039200c072030180c014445440d1462 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819220998 1250 819219748 819219769
    0x206030109140f0402090106050d090c0f2309160207180209091012080a23130503060603030a0e0a0308030a0605130504151d030d0204090b0111070302011214152b11 72
    0xcd0241840420006451a45602da01c00741c580303e0004403d928603200350414660340d020812544028804042801c60b00100350340d03500c00300540117850f056641c440d01d000c4044140c03d0b881c0d070b0054002620f035a807850246c090702e500080303442d004c030909818001c02c00065181c141000704807410000b540c441490003804500340320460100c17407060000c400107031000d10750046140301d141060280e40c04605494081207030791081c131000d80110302700749000000310b420441d400c1602c0d4003c1e01020011020800900086d40300b0075200b0780202d01c0701e02d46000d001d40303418041c40122801d442e18007440001103085440420407030440d040441e99a41d24415081c02303510070103081019100000c4d141c100e1302c039690090000c58560840030840c040d10352005449603803103032603103002c0798015050520040d805040150251403003050005640d054482000070b0304401501d1000880b0b0b004080d00d9458034000350b00d210401d860003c0c00d01801c1103448045403418040000811b04a00b18101107816212030f070654 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819222248 1250 819220998 819221003
    0x602070812040317280c0e03070f05090141040f1a0d0203031207050f0a120b1e040221041a090102191b0206030109140f0402090106050d09 61
    0x1081c4074141403801901e00c40801103003150000010700062040300203c0d1001000010f96141c1e62200c8040c400100020500140e0307042c140300c03d200d000b80301c07501c0801c0ba03800038000807002030050f01e00b40410002040e005900a103201040c20203042c250120b8105080010040c1c00d1400e10000702c0820a000b4008820b25040d400c1072034005d2810b1391071029084291003102c1022107081d075850403c188003480f2464080a501a8810000c2040c101241d428403a40003001c1d150840c10142240103c17206640702e4910070000948107124401c200341140b18500280200310785802074040c200c2c210381d003442980c003241449030b6400f05030141540c001d50800b040010340f41d07980010500d0107140018115944004c100200007a80001a141c030205108680c0041210b10041001500c5200110f40c014500110340703c0c0031016141200050f19107901441c041d15181001085140e90b4001400381c24134000c0c03140480c40d110b201400050f88464044034113540c400c0c80c10070364230001400c1000c007408048100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819223498 1250 819222248 819222277
    0x807141002010f1a09060907080606161b0801050a09030f111f0504030f0804080d0c02030912010e0f0a0f0204051b040f06120b2b051614010f080406020708 68
    0x1590355400b0403200551208125401d2485d074072000140300b0802812074601e0302061060001c181c01e4507006001d8902045000030301e0801c4c0100e640c403115000301100221550070310440d0700b4001d10f0f0702801081c0d4428810002000001001d8900520035814003210740140800400c02119146060110700f15801004001000c0400c840001030010001214150700050f0410b00c2c0000e8144165106405a60800d08031804c101c6490000e034018202c08222200b03601c010807465a003a2120038003644c400c0170b03020000400700202d200322801c022031200b84403640d402034031880b00055030713445001303002540580300041e01d0780d0764040c9900c60f004981c800380c08500c40410700151904c041607102003a5400c55032030601c4070b03a19202070015074200c030364541d91194002d80d0514442051000c3c1d17003c0c0365080840450f1900c400c0d2501e500340769440000002d07003851021b09020031070260304803c044100a10b08916240402c6000800040b0b000e480109121b8000640741d092141c0c06044d100c02ca15107134003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819224748 1250 819223498 819223511
    0x1f050307031b060503040f021009090e06090609150a0b1c080c01110f03150f0a0f03111f03050403020307080d0c090803130b160506010b0d05010807141002010f 70
    0x504800d00c415500c2c6460381c8100807040412007500c40d00a81740030704d520201d22120729200d6400c00c901c24840d040d0003000c00100c1c0c40700040311243c9001710306414803600042d10007070808106981c18210300505100250340008000b00c0f40150202d299070340480500350009071145031700c0000c0e03030048101e5821040020389041400500c078100d0001c0107803440200080000541480c500e043e86e010f5140360540c0d03500203000013a420145011080f40070741006180344103081d9601c00042140c100361700300b07281d40f180440c0c0a100300954605031075062841290150700054540003080310185460802c0710030507403540081010107008006450400307600055035034039a003d280800c0010720341c948810000070080800040c0d0005c000c000c80349a041110215100e4030704207418180c507640441c128034248960004c0e0780010070030510031103010f0465000c1d06980d84008200c41c1c0c060b00c1c81a005071030150440101000784002040344030803514403d407500000010406400c2e4010210414009100341c141203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819225998 1250 819224748 819224753
    0x140325020d0f02011a040915050c040806060415120302070b030f2a030705090f03060a09050d05030f01050d0f0c0b03061507020306060103240b09010305090d081f05030703 75
    0x1030003144004950b9140100c01010a03012426548024515459010090002207984c1000e40007180300d94000c01454841c1005030309442c040303c500301ca4410000740040b034148405a4244202e640200c0221014046041403190048003c120303071044111a400d84d8083e0b0b002c041c0280081742c02881c1424469449240c60204900000ba08440c01070040300007100e002039010484c0303d000a0480851091820740d9107050054940b5405071082c598001d200c03049010300c42e5010094584641540440030800400a103041c602c2d00151114900c18000244108040040d090300e040e411240120b9508000c604603041c418034105c41c2c424090100e5810300c8000c1203030005600258040d4038180d84c05184000c002e01d40c84a0381c0a500c10080d0b06404c000c2c0450081c1d84a17070449860110a00c11812510144100440740008aa40038020030100800c0309081d0790b03010703c20194010000c0e4058a0f00486050000f0b1050a0080050400076883c0c41c500c8065440d4801400c0502009803c41d96441d8890 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819227248 1250 819225998 819226003
    0xe0405100e06180f06100513061116030609020f0a1805040611030906040302161406030405010213030302010606090b0a0e0909071208040905150102060a1808030708040b0105060a14032502 82
    0x41794400c0c040d0b4411034041071144c4c4a1412255410402d1001614890914030111010303c0320141d000060300c610010700b020406882c01c1400218840c03c00081d6003429403040c440303140e003d103c0c0076118101010342007000e07070415940941c00000040000401e542c582c9450b2004044110710030b1000c14020007040f014030400590540500c0c025002c072583d1110030b2107001c480012902030b55010811282605405040074009190824841c1d4005402d00c041d00d008400760019580c810760041c8c1d1900400c1103d00e0300403480f034000d0010401c8452600c0c2d103084000e400300c9a42c0c520035010301040e40000e040000244035410140c4210200b040d1118a01d040c6503010340c1060180e8001c80d4035200104059040e0010f0104440f0410b801800c85943c412002000505506541708400022284200001140ea10003540306589640313030802541003a00380241c0b4001e050b00083c0c000c01e000c014049860b900301001030303880c9030f0315541559039584943c00c1924a200c0c004905010111030100608001e401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819228498 1250 819227248 819227251
    0x21020c0a0605010323010b06090405061c050d09080102130302130e060a020d11030103031b03030e0d09090b1e04092105070218010b0304080f090901060f0e0405100e06180f 75
    0x3010f00c200204a1748100107805c0b0f0302840182640028100300b1089103013015007013660306c60802011000310b90420041c0800c803000010040316150061440f107110150407009220140003648000c5003495411601d0340d0f2410010b00001e4840d41c500c070036000d481d00072a08220840f40403041902c0c40c078184040c080c03000c0d400141400c2442420b01004031110314001054a04980d0155038015210f01282c485404c3c007840803a080d0105922045d40038003526003045000103504c0342d81c0e18030300c0c1075103030122140840b060015218491030001c00034810501960300b0484400c40308840004411460780380c03405890001d11132000a1001c40d910402000340c100c3c01130959580203a6902610b40c90340c0d40c8184080703009010f0748020f0301081c000708001c1014035010740351b02030019850b10702d04072964000401d00042603000740001400c849100c9100f030360180c400e1a0506080c1c400340558200030f030b00310840e41401d004003034285991200040680c4d0b0b54802201c0100b0305441d18084a04151504d80d404160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819229748 1250 819228498 819228533
    0x90a0c140a0b1603050a02030d06031109090a12111e030d0b12060103150b0925050f0301050d1703240d11040c09150503100621020c0a06050103 63
    0x2688040010601e030b12034215071100e00351100c1d045807440c06640541d000c0d0000f100c1d20013184030034080300300d0203e210720038040a58024111141c0d070120080c20012510070084c10b85010703810440b91100000d07122428141c001249083c10001c1c006900e030072500c0d0241c404400300c040018080340b06d22110001c001400308100c000c0c2c050080c40403031801d000e0304891000b451176081c0d00103801003020900700c600400301244c00c16004500d2100150000310980d60640d08054000b40e60042c1c00202e40180320710138461480d5042c13050400450005031449800144110340c0a54488459102001030050b00500c800c4405880075407a4148800b44002d0281c1100001107103a1200782a52030380e150443c428002d45620a940420754440d100900003d0042c3d140108288001c07090089080d10820080b810304801d1070380c519480345400380c0701d000c0f40713034141d40014240300b03103440071800c20b8003c0d0380d51105850143c4009070f42d92141c05910b0380340c4014042c028050510303101c0048100210708a82e0303030b00d520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819230998 1250 819229748 819229759
    0x2b050a06050c0a0c03031d031206040e0d02070614040b07140c010e0307120512120a11031003020f0f0310020a020705150703050a020f01020a0e010f080106050d0e030702130b09090d08010608090a0c14 87
    0x304001001030340d0702150559037000d603000c5001004071703910801c0001c2c16408a01c001500745a0f880c12007070241d0300500c10844001030940f02078003220804000c0045100400d00c1c04201c204203071310100b501c401450083c511b10010003a000c5040c44030400a4900f81c03041e0015403941e803540c0301910b03264441c05441c120107407400e000ca80843c0c400340e4004c0c1c0e40541241e031030752410b052443d420003d101c21088081500182d00c54501c5196660512884107010039070f51015980701030421000f410002c4a07007103984141c24000011092102100135181c3d1540e06003003a90741d40b00b000400781d29080280c0c041104d550300000c1c05201c465803001e1070740318072502a2038070300490b004003805072401d403400d0140da4000381d800d01000c46a1980d64020b4210001594152850b00d12645c0100340e00c6404490f0170118941c841c81c0000c000d007400911141c0c460399500150076007903142207000340010740602c00d41e010041c01c6004201505003c0c0001c0081c180c1c403145501c1a20358644c880c091400100e2000703072254 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819232248 1250 819230998 819231011
    0x1a040b22090c0813321b12010c09090509100c08070e040e0a081323100e030a03050f0903060a15080604080a0320070c030c232b050a06050c0a0c03031d03120604 70
    0x344414000e9409a927002d80f0b5820402c1d04241c040d80003020001d0002c420b62142400142e280001c0b4421100342c1134071030b50b42c004c90f80361000c1c0240405903c1c0d0213080c040e900c0c11548007252400424490802d50344050744650350f0464143d0601141d650b0b412036200c80b0303000ba01d40a50b00403040040400701d03100382d07030038800350181310030a9900b40c99860106806801800340e10001074410401060f80702080420141000c40ca14042460320000301c0d016000303540d440c0e100c0441a41d43c080814000c0903440b004204501d07040c0c0d140206405400c0c014800c0c142c85040580442c0d6840781c0100d5030751813102800c1d84650207810f007a0001e454502c000d90348546c0c5003201082d4a00c40d08a0112aa000600c2e4160710b03001c48403d1000781c4890740d0500e1100115100b051002044032007150030518050303401000c10b1862070915000b10760010b06100da81f020304020100d4115000b1601000041e010b00b0700055128a102c1140c9010711090300c121224080090f03c200520314269401b4000d61027170f5400c1140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819233498 1250 819232248 819232279
    0xb07080f0c06090d020c3001020d0e0102040f05030c061e1204030215010e010b042607080a050105060d0c09050603010615020f071a040b22090c0813321b 67
    0xa42c18500158244581202e00c2055a03003240110342d107e03203081400040c03820100804580445010f9044c200c21a50006020405100c01001543c0034000460180000c050b140d00000c03414814881e02c0d40000b0310250b40d02d00001215804d884007848001e1503180b10b40303041d250007501c90441c0354041e44c3c5204448008294060b003c003842c1e060760801c90180b0304e0a4200a44030b01002c4007990701c0201016640b00028001106112803002030008500509421006252182c2034507002004140030b1034103142814085503024100354210b441c4c90130b00244503100c85000c00d000d491690003400c9042503810610344105e42c002503403464000303118251801c10b51110954401c550583c4e081e1266803d080c0b2080c0f03d8401110001e003000c2c000c5070340034044031400d00401e020803040c59120001c03965540da0004079003038000443e01c0e4030401040041900d45111369404003401c041c00442100032030099410403842d11003001000403414260129840344140c804c40400810614896a0060040c0369003105e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819234748 1250 819233498 819233509
    0xd090b09060f130615060e030d08090d0e0315040b0a060b18010f090e041214030603100c020309132a0f030b13020d0c0306050a0b07080f0c06090d020c 66
    0x10349400300392900d07192141d0300340300c4182c3c2982c4000d995007030366020310181c5040300b025084024840f5032503074140000d07001c0c201400c000c000805841486505800c1050007400400d40310401006403c20401e84510303000840c4ca0300f4074004407004988600c03420300060007842c140640c810041000240b22183d210003038941c4a01403003090010800022000545544c005c0c200310a44a00c5841c116030754990350680b00c0540081900d09442c41900b003547c18000d0b0350b010190441320701c0c0d4106024030f1400e089001c01d540300c01c01076001105555801c9003241d881e10034001c541d4005030080c0300104240180d1a084018084603103010b481c40459401503680820004001c200c6540c035840d402c3c001d540b20175080e8050201440c410380d0000050b03000e80802c1d0b400d072002c1d200000c009a000035203060700201c003030116069030b088644903922501003003009a80c40801c0303641540e441390300700d900e640c40070742e0f440501c0c041d0800c0810903028407810041e6000000440800030060340d8202d4580500c000705001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819235998 1250 819234748 819234751
    0x822170d050610030c05071502091f03060f0b03070807050d0608031201080c1807050403140a17040f17070f170105060105090f220c030b180f060d060608030d090b0906 73
    0x801b183c0300b8001346000c01c060304c013080022041d400001d85400340d02c0c400103030100f0a820800540c440411000b0300c05960520469015000403c88100382d0b40c201000b0741d0681c0801080d000070040d00c9000260703540d2085040d107882a440c100c1c14086e09468440c0c070703a1a83c00040d91395500021460000550005c00111844849009409841c1900c110f004441040d44028071500500c0b05c200400000104022030040265050a01804001c2c034140703050104024054074041098205010500c02200d824a600d800c86007400d100400c86ca0001c041141400c085900110f00941d000c9070000c0e15041501c0c082080300031000080006a5881c030040d551806284411900300c03044080d1114203007800c001d40c030711240800c201800c00d119201c003110300341c90b006000040000c0c2c5405d8020f401d4205006e08401d01068410003840c00d00c0d01106941d49440b0045c242403082d0701d40340061090182035440303000039009100940366110801c09280c005050804012622040d41c00300080710f001000c507015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819237248 1250 819235998 819236021
    0x405090118021009080601170d111009050a0206030c0a180b0f0c16091b1d090709030605071d010518041104080a061b0822170d05061003 60
    0x801403000c076502442001e01c4107040c85030601c40c020301c002c81c0252080003024028205025a00a004a4440d045080440003e203003404e10000f855042032241d00400c034400fa41c8141c4200252030b0a86040251414200040183d00040000180300351014050002d0164100035181d1920a1484c0990700180031581c0c801d20810f01c10900100f40b62908141c02090a121080101e036084001c50410281250195004880306959031010034000110603d02109590396402c00358011244a6031100750103141000c05803082e801c12001036041405282404059074001c0c0c03007049645802000906048040014106007050300c1802060300e61044085400c004021444015800c07202014040606050081010221801d020204901d003040080ca440d6a00410002c2518040400c5088e99021440080800c01041c54100020200a1011646803140038010800c8011180c20520251803000b00790302d030001400035041001c403500313030041402070304200c4e880c4c00c0c5209a803509804880e07090301117 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819238498 1250 819237248 819237281
    0xb0411090f0c070c09020307020c01080705090108041401061d0604051b120912180a060c02030d11030913150e160c02120102030f01030c05040203060a050618120c04050901 75
    0x14003040e10400262110520800b130300f030320140e254a0901c0c00c1e40c10444580300140e2140080725a5580c0c403003603660b003004090400501e0030804500003800078600900191503521401071800008209610440082541c051240020805041c40e9000a4825140e442c491410706020960040307030310070340503000c1c031100e08a540390400c45000781d1140c000c010064200383c0941000d040c040c4030110020026107940031003054a4003000c00c20449207200319009032082060015036000103840008090a100d1940d0074190892201301d01c2c8d039482c41c4503060000760410510440a4110351260f004244965203d104c020521a2203524100d103901c0120366804002d090a40c60401d079600031001d0b5032070b807030024188801c00c01110a20600b641c2c4252212200e110409004005003d0f0340079214000c1c0c4411501945581415170003d60140c0890054510070440011540d60700104079240210400004d05000c01005107030704072540700d03203204002c14000c50402000403085041842002d04807441d10301c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819239748 1250 819238498 819238501
    0x50d11030d0908011431021314011a0708030a0f0f0504050c030f030301050d05030409140105030607050403050309100e041b12020c12160506250507021e060f03040b0411090f 76
    0x2001a009450862048031b042450807400003603212025240c003a142001000310304512005003603501c0c44c00503403010780003040c204240302c00302d20b1000841d008550080d107850b8481c0c80b02240c41d401401c0c0c6019680c50342c0e207802a0082c00000d41d41269210724000c0081d24401d483c88030500d0380310701520700111115003081006001c5846c0403054881e2140c06541101d0801d0303100c0003040100c900e505021796084105000403c054541004083d50040861500c10b003814075603942e5980c3c030701032600003d10415103440310540091040600d0154040300030b10074401e1076040c05d40520035a07104018400000c002c1f81c600f0300fa03c44203000319500f0121050090045205040b0001b0140c0c1113060b003581c4148590804901040041061501559004204030540300c1c08002c0d03807c0321244210b000e03050050511049016980d002601382d4084054403c04940c4445400080c0c0c1d41c1c0710328a0825003861010041c0000d02022040b11445035106181144da102d00035410043c0005080b510508445400b00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819240998 1250 819239748 819239791
    0x9170a030e09070e040e0313120314160609140606010302070213180b0a05010609050109030312050a0608160e220609150603030519030510050d11030d09080114 70
    0xe04080c1d000d081443e1038151044130a001606580c900200707070311141e0011036030b02001c0344401604130082103008040110008a030347c002e4160705103e509400d0703415010840200350b0005001c07040409a01500800100e4500d140003018820841c0700c80c000e921078074000440310350192003158213560300109108107440343e0390803000107080803050100c03114100084000000e11030441290181d40882030101d8990304000300144484043c0c2c0c0a141009030b15070701000070070340040d106102541381703035408a80c40da46c0040d104060007180e44400c840e441001d041410414240304441c058420f10b0801205646507190307da05d14440642d5120a1103460b1003046002403c0395025071505480f880180b400710440320207020031101190300a402140c030000300143c0100200100d012420f002c2c0c06e04200c2400c0480c0c1c081100300c2180201c030b01501a40400100b0b01a40200d9580e0b0500d00800300d03001081c04610040c5003c04921400031503609000113412652950b5500030300c21000c68646090500f00107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819242248 1250 819240998 819241009
    0x2a05030a060e0735100314120306040b12030f0c0f0d0206010e04061104060801090e010c09060f1107270204080309040b1c03030e0c0102061303051b01050709170a030e 73
    0x15004d51342e0000d1300000c510410402030394440c40c602003110700410714509051066410305240c0d030744560403030811440345501a500752600000192000907801504102007040346001c060311101030310000c280600c00709051001080f0301c0c40300c00e0541f00f9501503a07503d10b583d040003800040160b0008801400400328444900341c0c0035001d5200481d420f00390031141c0d00c0940c03094100b0070011b40e03150014420858640200d003c1d2460b01e4008020002d440c0000a10286450103004201308c0100304141000740b141091004100103d000e4030f0700c2e0340c0c3e40d004059910072203142c03c00100c42342c4a1940d120811602c00d80e0304507402080034601d401c6003941008001c100c0c2d6000d036036001100ca00540a1420010884809144617440014100048000a42c5404003110859045500450030002002d8042c14031000171989820704686078882846410300c50410719090416644c0380c4010084402d80c00902402202c0700703889250b0680f00c04541e00c545806001c0e101030007090013084042503600f0321 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819243498 1250 819242248 819242297
    0xc0c12030a2d180618180b040203010801050402120d021b01050c06040c06270b0a030b0d031e11030a1d0301020d02180108010e04062a05030a060e07 65
    0x108020303400d050010202c8141d0950b251812a80000c4082807241d00c0040800242c8001c1c00300c03410141d020200107244c28149580c10b00602d040d404840d4505074403901150040340440800410640d100d41c1c407000f846000303200481d030903440342420b40b26074141c0b8040844c1d160610300080d13000c2e100421a08030080d20b4046007103855410840d0420940c03106030014404640503510074107006201174648540140007031011007100b17140003d0a0001200841c81403030810480d00c0c51a486502c039151100c00ba001811000405500006400079040c1090303480300c481002003d058601404070000b100c03080b070f04002c0540c4068003d60040241d00c40c09401101d80c06440104240b4100c06114508042030030fa800c500074585145402140198001030941100c40c0d030703000c0c20300e806802517240c64001ba007131080141c00940016030303c60101e00001d05c080c0745036490401940014030b050411200080c0954000c40d10b42840b9860001d010a8000d049c0c5902e500030b0182d651580042410308150302d0b4007418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819244604 1106 819243498 819243527
    0xb061306122402040b042c011707090608070311090402010e0d05031e220f1503140403090f1a07060504020d02090c0c0c12030a 56
    0x1c03001a00322620340c02800703075809491590306003440711015002e41c0042c00d00000b0081a00301011004200f200c01c940640e04510f003204086086081c514050f0f50032244201d00100f0500b400c955031440f00c4001d05040c0c5240301da40301d9a000c00c8030741c1c60340b089000350805c400c200103000d0382c0381d00c0c0503241c42c0c151600a018a0903500090400d04c0c1c1c241114445c5240900302c0090002c1001038844802c40e070306003080c0074044a0800c9900380c1001e00f1001441641c5808031701c1250000d8401d0040b036000b0a01e95180c1410a103540c044482400410810540d81c0c00204907501003011410b409203000f81ca44441d018101840d11141010940086a01e50080500c0d552489a504102c4070600d400420004003512684000386142d074500c080039500c1103002051004460300000140b004070741c0724044071440441c44040c410314000e0a2001032041d0000d00c81c510806010b4200c5020194 = true := by decide +kernel

theorem cover : BRFrame.Cov 819064748 819244604 := by
  have h0 := BRFrame.cov_init 819064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819064748 ≤ n) (h2 : n < 819244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
