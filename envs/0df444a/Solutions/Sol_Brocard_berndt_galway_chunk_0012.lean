-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:21:23.807977+00:00
-- url     : https://prove2.me/submissions/fa030021-005a-465b-9e6d-297b9c5a0ee4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1978425 ≤ n < 2158281 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1979675 1250 1978425 1978429
    0x30c04060303020c0321040e04050a021008010810020c0706080603030408010207060506040509030901090303030b0102010605090c0403030201061502061b07020904030c0215040e040b070908030705010f1103010b0d05040813030b010302 102
    0x2003100109400c13807188011b9000000c190202c0c01a13109041c00602000045024040c086c0702d1000f100d600581450180d050040300941141428411003007903210720740c000c1c000021284241c0b44100d0f1030344040c04d4042e203861400c17299004003074044daa15020030000001ca81c2c100b4402804082e00c01d07030005c41c040c40c0220811085410050a11a09800c10042c200642e81e00808481c15a0380c1820000f40b00022000100d0040c0443d030821a042044401481a07112061028104880c071990007806600c0c0c849011b00c070040c040c8800c0001590000780451040c000c42550502e42d00c0b802c540796410103803142c00048003004140c0f005e60204000403403890542c1007288070806010b5a0780c503143d00e001d28043c42c90406180003000a40414140004207030fa0901c0b4078203083c014100f0f442100e84a14031418001e00810007450440421840c1060408500820700241d90496907280d2051341081440c0742580c0181000800460780440c0400008035401d81517021400654010b50804026605500c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1980925 1250 1979675 1979683
    0x10306050402040b070213020409090501020403120201020c06010b030c0d021803010f0b0d0609020402070602030405030a08060301060308070201030f0b1c050106050303070b0103020d17030f06010201200a0e030c04060303020c03 99
    0x49140203500402c001d006110713540d0100c502c0c0035415140c0a466150306803c083c02409240c00a100301824480e5542c14410150007030410b49002d141d84403402002c3c2882613080f4464504204169000b000042000d124008007540e44a0640c040c12454020040700350b108030382c003000403070508140140c21600541400d204400100c891170070204100860100054200d003600070b0028511600c0b02580d1046442d150103641c3e456610142c10b5483c0d0404d40313082520303600405480000182c40100194262505001c0c920489400c446128685841500110050004410f110302110384500b614690381c1c4583d201c1500100e8a18034117040030300145495402e450880e80128400ea00501100c0c2c081400c240c44281140d90403513512501800500d00324081d090010f8000300441d001200b0001001940c21092344142130980c002c000f03a91021400c440040040d4520840740c90b02807198508180c0505820041400c1c020212000f05014100040550385581c0088005802c81d0a01c032440d810100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1982175 1250 1980925 1980929
    0x203160602060907030c0909030203040504090605071107050901090504020607140d11070e06040209010207090203010605040312020a03020a030503070e06040305100606140a050a05120a0605030615030616170411010306 95
    0x7a01070607203a032950321707111101c9480d80a614140382c8c1c0c402c08801014001c00442c0c0c0104009403091200600b9814488000d16003220581d01003148440040c08046002c240303002034600c000c0441c1d03410313400d042c0d003640205402801241c00039020007a49020803111a00b02180c4001c0c28010001c00c810200300810080b1403184e104a030303a00400c0103001d6001082d00080d40104161401a100d507540c00040385000380e56800540c40034030003c004a4007a44c01002401030748e00030b800c5c0040744440007408a0340c40000c01d1000c4d005070040006000000d00c991300568101c2200c0c0b506860b503030700c1400021481d07446903008640550007004542046422030003180001d080358181184d071561074902400103442040d106904000d000038444544074015400c0d20000303112501c4250280c5003140d5400020306e15801740501c80e11421001130b80b11b00182030744820100b0301034041c120355150004c60042075800f601311a428050701e03e0880441c00c00358560507218a0003038010380c40d005003080024085550b00e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1983425 1250 1982175 1982191
    0x50106080c010507020a030209070201090b16020c010f1b1103030a08041103060402010906030f020409020301030602070201020c03030913090510050f0103030801050604030308070806040f020a02030a080a0527010207020316060206 100
    0x40c013503040540d0b00c40518608880d01034a065225075258901240107145a6200501801c1c80900b0302401407a40c00304460091b9444d000c940d0b0001c5220019580300c017480d69880c00042c807600805840340f42800301901018420a1000c41c541c1c0031f40006811600b09000b504001a5200300f0481803059445d10400b00c540198017502290030641c0008041d022540130700010300d5114034500c441001d5641c1120010460381e0421910b84d6120b00c2c24202079131018000340c2c01449040c84290b2a407074003104803604401c7c000c080034078603082050544050624070310243c403103000c1c04e810040c000655000b03040c440d0881e410300790100d605614000e0104c6506070801400b0340d03024001030000a0700031a6054102d07840b8281481280d40340b00001e40504100c14207400218004210380d22038a8001003e401c04c80c10a0b1901100c0340da0f0700082c941103440465000f080c8050a410b006c542c0c4d542940010f40c220340310400541340c184142c020a180800304480a081c134006210204991a03050007201c0c1c004d10701c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1984675 1250 1983425 1983427
    0x9010801150905220507050d140601020c0f01110105040303020405130501061205090109020a03050304090605040207020d030509061201080c04050603010921020703060f02041401021501060c02120a050106080c0105 93
    0x101000203080b03041d1405040d016400c030f14401440401c40c0b05415000002d01c0307030184614688910000c0c00c98216440e510071072400d01e107008565008040c0c4840c4104010fa000308503100501042104400c80c000d102d0b03050121101041298010038098a8401d60190314056900d61511040c8011694409441c1e00c2d950b20389001882625440801814400304914003c10b482d292050041c4c010111242c0095100545210000801402001500c02c44038545000c00125650b801132000764400c01c05c00035481890a00349400290003a0f0191854102c00750005007040c00440030521169400c0c0c10500542e4001c054102991500f13000d140e60014040d0700a000e20060b40c3d849074050190262403207000040130852461080c420070544001356004a170078000ba4480358040d80003540b181c001c070070389031109503c040502e500000f060081542e80c151504c02c56843d0000495500081c40030480c0d10140b80209070091410421000d12007501810000494520303000c10940390108144900b814020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1985925 1250 1984675 1984709
    0x40e060118120305070c1706060406080106080c06070c080f0102070605070c0209040609060b060f0717070503040b09010504030c03082d0a0302030c070605011d070302030c0405040c02070305030c0309010801 90
    0x400341d039a0000b10381c541071a9440d1401480c1c1403200c980590025107000c0790481c513656242c03030b00040c1d83d4050380b415201003059075100c4024034242c03109802070941941c011b8602da41c0500b00701300201611800740502c083c0c0c02c0d03114144542858070381c0c2941a901ea4002ca07810041c03241c14802c4580042c403904041c1c6d0000299404920390220003040945219a20896081808860b8011010211004181596610a490035403440742c21124041e100310400080000c0868221400c660a0a421000a6041c18505500809240d010b1643c050400030140030000000705000c0c0079401a51190940035150b21f03544803080c0d60440340c9201880c403a5802518110b41c01e4100702114048a4249009a030b2591a036514001910803c1002040185400f00001c0c8251405c44901c200c40210f114103c49929495012016800161441c0b603040e442048108954a0a1b5210302d01c0c800c0180103841a183d643c0c0c80e002e0560b040000c0c1d82c445030b0400100e1200c0c541c0c3c08501107024048100e442c1003000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1987175 1250 1985925 1985939
    0x7030507080610030c02010b040507050403060e0303010b090d0507030209010f080d0801050604120c030218010e0a020c030301060e01120903080a0e070b0706050402060c0a0503090f010f020606060d02070503040e060118 95
    0xf4114450181691081101d4000e8400e40002003281c0001d4030a210a050503c1c008126a210b40710640380c951400f01222000d41011040b241242c0d848107c660a209074041004070613041d03071310100d40e1403240d0080000140c0301c001c0c24034020449003d00d070b20500d107000e0405052543c0700c0c1e029030070018100c005000f184e031600c0685042d2061071a0b4015024000d142072940032509400203580300494000e100d10b940740c607080c0141aa070312544ca10105460713900700c2c4400e034003401d003184095800a0005108852007200f1448880e00b0500d03200c0d80c441100030007003003140c14802050740090705001c00c11440c182ca0340200c8202c0b000c420004d058007882c0010451080c060070000410032030303c4401040c1175659600603079000903118800c1d1010090503290030782c0c0c1c80d40083e00990083c0300e400300241480d80034291103600700015070081d0000e40d64030010010b0741d41c884024010655424466100400c5080002e807001c0d044c50030103031142c3c1c2000c1000ad0002040f201000700c04100982c0180040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1988425 1250 1987175 1987189
    0x10915090f061d030301080c010306060203030103030503010b0703140c0606010f0c05060a0203060f0a0905010302030c0406050f280303020601030c0e01150e010203070209090102030a0605091311030a0203060708070305070806 98
    0x15001200041d6100d90a00e03d00d07218040621209624880072001184810000c55506200746c400d8904000721551010b09a840380000d110143c046003062004114245d00b480c002c00c502c41c031034607204074801c66802c40c024040d08208404881540054100521540c00c518545410f042909080300c220b100c075560759a44000050008207401c0d00030010800030345a4004071400e03502c0041c801e130000c1d078a400320303e4010b040c241b20a80c1300c4e220b5900b5840a13410540302c7c00d8252107004d8030181c040e940000a101d5148920201e0442c59014076808440344a401c54280002d1842980070300081e51442c244850b584107240c22002c42c90148000401c244040340b1840d94107a00f160030840503501c1190300503425405628006500070703031a10104a1600c1e03040d0300a42c0b080741480420085691900280301d42d4800803035405c01c064010085c03450118224080750384a00f84002c0c200c0d9014880d6130302003402c01006507444400300e044070007840300d02030301b6009459001c10289000046440e29100203099 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1989675 1250 1988425 1988453
    0x9181302040e0c030f0604050111090a1e03061806060b0f07020904080705100509010c030c0207050f0604120b04120302120402010f0302130f0f0503060105030a0b06060408010501060201091509 84
    0x1045955940d41c09100000f809401c0c0c000900900f501c81c06402d84003001d440340c40448003280e855181a107a00306000078901030303440641d0301800361402a81088945c0030852180e0040c0090103100010002c0050f0490045840010400c2c0d003042183d1228039014003556025006940d49450902566014004a00a0362403140d01181e13080040e40729410300a43c0b902c030b8444041c02c140580d0807801c9080c0d006402040c0101d1010b00200084400c2c104200c00321a0f5038105103005800c005003c0115141c101ea6901d00484001d02080c640b03031b914a1000c0d5011038400003107030010b0741c110401c018440051101c0054100ca42230a510f00f40c075441c0e207540f44100003031000341030090b0642340910003442a4141c2c2c038540f508211005001d030711600340311440c9180b803049242100b12083c0c0800e07507040205d01541203510140080582a82c140c0e640703103a0604c0102074a8100805000015804000f40500c038000d00f6140c000080c0d61905003882080d1003070342582680c500f0306002228000903503c08072050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1990925 1250 1989675 1989679
    0x402060306060a09030602120103120e031e01060902070b070e0109030507030807030309050303041a01090c0503011401020a0203030403060b010806040203040506040b060f03010c0905030601060e0a0b07081204060209181302 97
    0x20f0358052098058807a03161a41014250394804a14240c1e20614401c22606030390140b60304010705404c207601100d400d50f012510365010303004800e0100b040c0880022445184640074004252a40c6070605981242c00590f025034031105c10301c1c28010542d8105840c00b0000e0740a2a182a80f28115100c4035130b42e041034400107101c0440040d00c4010315110354444a5020760003015265241400d08100721004145010701480b00000000024030501c00d115840c5907082688805007980c1c64203040002c84900c4060250540c0101c0b59403100581d0240020005944503600c00540c00040c20001001307964000c1c50140100d01c10000d00c00442c41c00900650721582c890b2452503550741707140210310300c1e80055455070f805608280680c0621500071140d0342c103841c000d400b105c000d682c0c0c545d400c4030000043d4815541000b04d400e000d20000010b64001e02200c3e025944203454034410b5114949107031812201a100a6408114480c1c203150041410129224100c600d12190601c1c8014010510f40000000c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1992175 1250 1990925 1990927
    0xc030807020c0a090b030c04051003020d02060702040509060108010606090b0909040c03080d020c0609030403030c0b0c04080601060806030f0c010e01031d06010608040219060c0305030408090904080a1403040206030606 95
    0x40d0a144200000c5541001c042d0007070107400e90710a00c4c4005000d45a006621074000c0400900d03807406c0501c6003620400e050314901c1492413543c5c003070203089003240d002680c100f6001c2040c94050384590041c680144140341c0108005d40c50a0303409400c40710749400503007c00ca0401010048400c981e811b4801e2164121040c1c07406845500e4514802011580014524140401c1213400b444851b80036196036000d14081d5011030740c030500095200c0c499400004c02060700f220f0903c01040c40e0803800f56000030f1030000a8a0107440d95942d500e0b050342640b1600008800108001c2c140c10240646000840300200505410101a001030a02c0003604c02d1241095076a500e0383c11061514000d03c22040c5030301c01516510351b154040100f4080c403c680980c0035442c0c29205148200310041c130340c01110f005540d40600005c03039030f800703d4a41c0c0c0090b10644034620f051281030219030b10b05030032034000c92056100568030260f900020748004d11410809035407060600410001d6107440040f41d602400845403d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1993425 1250 1992175 1992181
    0x5030a080c19020304050a06090806010603020306010c0f060c090b0a0e0103180609080901030b030312010b0703090503010e07030b090f030304060b030a08070305040806060f01020c01110f030f040f05010305070c0308 94
    0x80c0a2400b84094085980ca010404800010f802100030810794100369500501903442e4032098a11030038070300c01c4010340ea01c400010040030740f0950103140c00900514008070440e0300354417070b02c9191040300010780f40d40303030f41f04035003004280c110060b0310003003850308440e038100b84402501400300603059000c2811325031034032b0007030584050600000f0821540315604000034080c0c0e0414522503001441458003291421b2022000340c42c1c000250b9040b0440003005e40c1d0300380e08140d03044c24036030000c803411420b000d01040f01146d150f9080c080d0070700801d0f090008100d06481c43c2080041c01c078001e1304040564014141c1194072200c08800c880d03105402c1440480e14508803800320f454804294006401031502061850030513900000420490f200f14041700d0306c0d502c6407400c114035000c040b02c2c3c0c00d0140e80050300b29026540a03541e2a07a6000824040e106c0400f0180d420030f0841d40705820038a4601c0300010184103000c2d840d00a413010302420b2070104000d00d020100030b021400881400345c2800102000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1994675 1250 1993425 1993441
    0x110d030c090504020c010b0f010c0b010902070201030204090204080d030c050301060e240a0206180c090403030b0301091203090203070801051608102102010e090601050301090207030201020c01050f040b0108030705030a08 96
    0x20703803401448007034001c5545003191402c81c0c0c020500900303890f10420546801c02c0440d0b02c52105c80b0802604040001440e92030090640001d511800d03080703040c03540902000501e41441d202800003804500080d03d0a85940400242103c03642040034091200501c01171100c1a4410300c070700458401502e0041089115800d081075540065544001402c0c00040308400f0740e03408035126000d05403441c42c20034141c0c0c51500d46074441c022020020340103a8403900040c04680b10703400c0000109400350001031003204d81d07144d520150150340c98030350200362941903500071424100004801858088000c011604050510210090302015180300700000035022130410300b02da00c0602c0081c42a100110034040e0a241081d0000b610b9260590211322003481d02d02c06803c2a01c0d001d4030850050b50b960349168286460031009420030708087e02190350900035280f0010342403050314080d82c41596140c6071450180340c4016110b030140c1142c2c209400c04d004c030100142c0008190748000071941007824841d40d074a95 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1995925 1250 1994675 1994687
    0x1050103020a050c0f070608070f0503061507020901030308060a09020c12030402010512040c09050f100302060a03090209041401050c16020906010c05060f0405010b0303090303120709050d05030a0e01110d030c 91
    0x8003a001d021741d490030010b0b0070b40010f01100300c4036941c0f034100080d900d8910649424041c607074080080392007003000419a24200c00d4001c002c015052a140c1080c43c940c003c034088640907081100400e0364481070051502c0c01c180030000804141b541986130154440840740c0701c0f981c0102d0980c5003440070010508680c066400c1c0e030104403d0304541e00041c1303454102600848407900c6841c4d6201d280201150b54031840b01c3c02c1a104050900c455400c0314595802d21900343d001700603110800d543d408000c030042e51388901c014040c43c001d41e42c801c21046040d0b4203501f12003020748000d112580405c1881c882c1c20545c4143d81d100e54040719000301750354811005891400d070b021002445401020b0070403024240071040726000714080c2001b04200400e64090564a1180440090381580184508410422102105540a05140b4298070407680d00d4001c41c60f00c44c680c12084032290800301d014070718140d00a00749600e451003442d100c44809901030580c0e031180c84154840381010b03140d81c50fa15005010b81d1f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1997175 1250 1995925 1995937
    0xc030203060a02040504050601030b01020c0d0c0f06020f010b0604050a060c06020702040608010203070810050d020d050705030706050a0305060307060503040605090a0506090102040302011404030201050f03150a060302030a15030b01050103020a05 107
    0x140c281d440501d860040d10000350702c036000700342c0320b985044007040e5654421b200d800f0010340184c000704006038202c404c106820210b0700d8121039207640c4c140c012444005500082c1c2c01001180c0080450300140035246007034a054211950058409001c200540d5a550300704808641c0c05080c0400c1c0c4000d01d0800c980a07210304100a900541411400030305140150700840c801c10090307075070340f803152a0b00030308824522840c410158400001006940907140010071011810b104004039000390359917002190030035034a0391010010480c0420b041041582500400b03a21042c100c01034201c0038144100030706103000281c4090181541c0300006070018008001a402c480e0b00403044922516042c08214040d610500080380000e103500c03030456080c03051000f0785041e01d174141c46490600742e480002d94829040104000403504012003034000c0303500d990101d100600410f80d40560b07280b9285040005070b4007a200c41c0706d81454104000c00210f0030004809065500910340542c0c1c41d880d035102107074240540 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1998425 1250 1997175 1997179
    0x30602070809040b03010501050906060a03090501060e061203040501090605090409020a0f0f09050402060a0804050a14010903080603030304050a03050f0904020f0702040c020f0304090506061c05010905090c01050706090c0302 98
    0x34081040c006900301402c1d110310300719410700107445107500f80350030f07584288110b507040900c49001c134440f890030303001901d0382403100c1c9000100d8010700c3c1c55440c2960110b0348440c0000c0000010301c110303800c08901440034030091134000c52030b051805000900400e00d61091a0401ca40468000c003143d4840d00034020164004004209268481c10004d03440c800502c0780001c00e00d8a41c80001e01c18803540160391050f07800828140c10070b84404d4054660480082c030454440c000c45172220006500101707044e2011410100005412800d07150107081084098103040c07282e402482000300050300020000300c1c007545403078155100c0030000420f6170a400b400789100da005001040070800301d10000007800b00e0764000c0782c4c01c4c010f40c21600001d0781c84da0150403510503990000c00041c8144d881d1500711035001640505040d1616940780d01455044004000c50080e141d10b031001000810303418010300d50000d14071400341140400f0341d00041d0941c4030752030009140c80d4680322a00148444121204019600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1999675 1250 1998425 1998427
    0x90605070305090106060212030105060c01060e0f0916080a02040c0201020c0d020a02040c0507150504020f04090506070807080601020a03121506050c100b060d0203061201020a030b010905090403050a0c0804030602 93
    0x12550181c0940780849506074158a4a5070004200e4400a06111407903019a80da62542e42000148445540f007554081c0081d0340f64440060f0b2101d40201e450b1050343c007500344507101d0403d15150340c100f221020312154190003d100a00c45482c0121380201300030f40c1240c0002d64003000c41002d0740603014200c03800c2d119004043d82c2c2d103041600030403109215842144d08001d0303094640c01c1940d21303000d0070134007034448131a981801120040b45da0005402c680010000c400001c00f500003d400d43e6650300b01201c00d50804820f004002d41c114000302d4203c01c03907050141c028034090000035501d240c042400790800c0b46184480b603181030350b03038442200d001c04e91301b17584c900a8903440c000c0d10541c441c4000103050311a4021541c2c100d2014400e48412200040c02d0a1406801d410034034042c1d0005000242c0c0520803007044c1000072002d1006140c0301c0c0c02074501290f039960080000d0301c0d41801d41e1109028840440402000950050803188619000e0a200c1d281c0a003e04008280340555040200021301c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2000925 1250 1999675 1999681
    0xa0302030601060c14190314070b07090302090603070302100c110901080319090303020a0201030509010b0406030501050604060b0306100c03020f0307050115050d050705062101090204031101090e1306090605 90
    0x44c1c068030f00d0402c1c900581c0321106001450340202c0d0341e1440d07441c40c4004054900309044c0000d100e079040280b03860382e0419039410102c49440d00341404206464560114184600030011410007420f00d60f030240c0110094030440d031540d008241601207801010040056a1099004006001044500424000d04541d15568482403220340d0b80d44086000904188030401d2150441e12900303507003003500d5041e8040c203a00610f607030054001e020090a5a550345d500c503985041c2d5038031035215071001140078070004620341c10a20240003ca6215800480b426801001006000d0303c0709035840c01020f000f8646410016003e0504900340b1160686a441a01000680307200740001500411400c00003c0320010005540310200700c41154041d00041c0903070000e5a081009180a4028003a031007182e0180b210341c0003140c80ba0003040b9009030130001000c0c1e80400c09009100000c0040007840c030742800e14001e41804c148020507402001041c00f956a00e0940480f0b0800c0f05982104d15000e90101c3c040c407140c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2002175 1250 2000925 2000927
    0x90a030602041401031d0709150504020a0c110420070c050303120a0506060307020a060b01030e010e030301030b010b03060306010e040201050d050403080910060b090906040608120d0b03030906180a030203060106 92
    0x10306000c0f400360000f400c00e40404548000a8034070034100d07013800000c040c0d2900e80851070000d01001d03c6410b450350103103031000035030b52100c2c0014650b010490340c4054241740140b800c0e006162404281b00c0c06180341c86007080c11842c015840804013802c01d050380303072615881e18001204543d550451501800301243c9000004c0354106214003400e15020103004980da0070080c402240000c6403c600140c2c041e040034000308001c1d500c0840207010614010030300104000eaa03e09544110074120741c96400000100240b088048049002d0200c102d400351460611500007644c1d2a01030292418000c0010089011a8010002c80b156100090402d100929050034064000c1b8401c4a40c0002c500a84094042c810200d100f02ca0540b28010155820f040c00441440801030000302a640c0003552024003240c5500200301c0c4268190801c0700c601d0b990207051201382d044d508844030f85400390380140b1441401c1c3e50340c2c009451040442c1101891444071800000e0014940d66001035058080c1100104840e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2003425 1250 2002175 2002199
    0x30507020111180607060606120c0309020f040b0a0302060a0c06051003020f1002010f0906050106020c010e010504060c0305070606030804081204081504020103090b0403020c010f08041a0603120a050706060501020102070302070b090a03060204 105
    0x649c60045040040b005030810a506446040300d000754014004a600301a0b440c2c81d500c401d40851016003001b207400e88036030218500e40e20901481f8042a0a02030103020454030b40241681301c01c5084890304000d145a000c80c180080070b59409102d101544d0100b01080d1003584510048e80c1961400e21181c106410241d004100a009050041c000e9900b2040d8950043c10f001c0c11001c0180e4509261914203041120221851a001c84c10418104a42d1011458500070200910700448650360b40c1ca241047e170b98901121402e1052043c04144010008108081011140802c4c80c4015440c1c5a031035200407070003003080b1800100304040e05000c1c40145580010403a4041c2d00a03210700003018038113681600c00b40c608440042c5a8050741d1910000380c2011b14205401034030140c101e030703903c102d408100d038159000b03a60120000f8101003209014443d076402107000a090a000842c6842c0e0310742c40003511100c1d50300507402e13010720000f2154425103c1b50511320045801100031500c4a4030b8943c04808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2004675 1250 2003425 2003447
    0x603060b090703050f040803060a05091008010e0613030e01030e0a0b01090c092402010b060304050c0307060503010e06040c0513080102090a080111030406091506030503030403030507020111180607060606 89
    0x2001c5030070000301d105000e403081074000c24842800c00d119566a544035000c560009105c203403c4080c060000456442d141b4030a8041c0304004c0010042d6818800403a084071a02080703000c0d11741c0600300703001c079247c602001d1004064041c0303400300904640d0001a000f41c010f10800010501c0b038070406c1410700c000400b5160503624110020311410104c10400c9420840a00400307060703013454500100b82d195001518050328000780004500c03284180005200394004603829140c0790801c01c5d0340d1045160502245002d0192402e0182c21541130448016080070020102030240d44d440d6607002c2c4040c003903400d4132590720400540e502d50548454542e40030390002130b03405002c0c03216100e01069041c810700600020541620ba59401d50b0755070786400c0003030002010151904882000b040800800e2405400083c0d40504001d5580b428a450001c048600050208046924010f0304000c06000a4100e80020050b2448504204884c50000d8414403e002004208601d888800199940c0228443c54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2005925 1250 2004675 2004679
    0x60e0c07030306080c010207090510050604030804080f030304031b11040204060e0a050f0303030601050a0507020d060615080609010b070203010f0609090c09020901020303010905040f05060703050a0f0603020603010306020705030d0603060b 104
    0x24541c0e0744c40700a9807403080504082c056003108506110b0f825640e80001d41c020038003400c1d0380c0c102d59a040881c40d654007d07002583c0b101c00006060110160400c80e82106245540003585149810384008028000706000702500c102989501c0c01071084c075041e038228a0200800455466542d1100a4081e5230b541c201240a071401e910002802d140100d1600f07188d2202401071840c1d40d540c8401110720741d000c5401e04041c8031082c40090050703183d034424404901e03c0346100082003410180502202c030800090310003081604402c020a41c1c4400400a04440342e42c1170303240d229145480080d01500099016800d41c6180c880c2c0020b000095800c64420136020340c1102248a03207e1482d070080c6e01ca100a4240940d004200402043c0c0155001c00d0f88076010b5414104038904c583d9600e41051030075550080080d44650501140350424861114414200c0e04200225803640c0e01240385030005200142a143d40402c180c41031000610031200c100d50301c10010400e280d102d01d4614010410103090178 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2007175 1250 2005925 2005931
    0xc0905031501080d0503060105070507080105150f030a0201030b13090b0402240906030601030e06040c030c15020601030b0702010204120305040806010b0901050711040f0204030c090f0903081306060e0c070303 91
    0x200701c00c2032050140e4160381026001e45a50304540c902640c843e0f02c040c2072241002810032900c0b000c2042800b03441c01502031800007240c2810280840021000701c03210072445603800aa2002c6140c0e800100442455030a00300800e00418030310011b800304294240802030503090140000c01c02078248021841035200321141000424038401c989420880074540980c8c5c8a0f00b0401454207207084000303590701c07010503d13012410001102415051040075a41100e201304d88200900c2040400740c40200505a0300d032504641140031a0000d580342c20610003d4500c245040101d24013034804c0d01120050100f081260f442ca02c8240f03130042c099030003803080b02c020703005400006c95580000d400725007031000143d5034542443c1b001e07200d442c01d81003044c424a5206582c1e16075032170320040074000342004500036021b055050340f400500d9016102091000c5090500e409000c1340002c0d00840c1d0290015585e10181803c600d032403901c00020481900140d410f891442e007000382d42c440403001012418465a018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2008425 1250 2007175 2007193
    0x1060309050703030c0203030702060406030c030506030c1302030a090b010602060103050f0c0901050f0102010608010501090c0210090201020d080901020909010e04020102010b10020706050703020102120702010e06010f0303090b030c0702040c090503 108
    0x85088940102009003036800418003007001c24403441c50303404014002825245030481960005185501036441080443d840384028010b440c1c1512405034004002d03005030a20203004c2c0001403034248041c0c00601c0031a03000c00420354840c4039501c24050345074001400d04855031200e03c00f0b540c40000340700407203161040c1c4000d40112800440d160702c41403c080c0000303906900307000811582d01e400001050442d961307800001503401c82400ba0030f00804102c0c800080c414000040281400812050010f1003400c1801520050740c0c000f642c00508000e602d02060b403920783e840914068410340c06465441011a000401c2020003504424000c0f4400d800802064080201703000009108005400140c0c0000404002042c000c400a2910038401c0c8001860300500646010f4500029290f80c80141e6407822121a42041000031a01420808a002c0c0310300785140d8000385004102e001c0c1c00850000440803e070350044540036102c005600a10a000f4018964401400b2140c18841c4511a105200396 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2009675 1250 2008425 2008427
    0x60605030603160b04120519030e03070b030c0f070305130306020306180402030705090901021b030705070f0e130606050310090204180305070602070c05060406030603050d0819090c12050102040e0106 87
    0xb50049803001d101c032a0600703191100101b45504810320549150203090004030744102800501401d091098899004008400c4141840c0c5921600040c101c40710403c18080c805001000b51b500d121800024580c0d62051443c04035414010020942008040c004010080002903000380d03114120540300e41100261002107003001d4001503902941503040b2000502050038004c0069900905010000d0715080525107120046102d80340c00400540000c100401041802d0003c1001484034500142200742403080c0001007050242508640c1a00e1070f55141c1002940d8101c0170041c0001425918922004c032560000b9000200040f403250703180c55a08150450b01e140d040701c4d2550103580301ca091055a07990ba80096009100c150342050001c0000615035a50704028005010300d60343c080785284c51407130014980b1200e118044c00748904802007203046810b003101080311101110000c51807001c9411704030320700f50700c1d6080740c00c0040346441fa880030301405400400c00c95480c0300364600e2503a03950350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2010925 1250 2009675 2009713
    0x1080d020115030b0403034a0303090706050703120509010506030d180608060409060204081006060306051807030f020a030b011107030b040803040309050301020307110105070801030201050d020a090306060605030603 94
    0x8000c2103075540b2800b16001c43d1080c0c0c01a800180c2300f0969a03461b130302e00c151200c02413903142c1181991204e000c64901c403000c030040d8140c1e525042240154154207050800030746924190069500704440407807102c1c285849400318803400d49401c0d20420960070304405507400381c04103d803102c1c040e2240030f010529483c844e808091040c0d6803840d5200e80141040804c86109001900f081e42c816100c007a160b0100c1c0c95031000b4401403214900821004801860700b40035150305501c0001450300d449010032075030311a4100c0391204d0040b07042c450056528220154010551240e445038401c4c030200b45040156055400082611400d89681c0c02c0c4101c560100c586c1c2d10381c64040205019014404240003d40300030203140c11a1290400e1510302d502d440105c0d0072600111003600018000300f1b50fa0480101c00c0c42003075081000361900700c0040d811500040c041c0e100320301d004100d030f5034000f0768504400c2c41018060091039003c081401010b0b1740e0000200582c00c19160a40720340103801c2d40c030b031403e44181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2012175 1250 2010925 2010929
    0x90708030301060c050a050d05070308010b070803060d030203120910060f080a0f02010c080a030906050906090607050c15010b04080105090f0c09070504090f05010305060c0901020606090402060c030301080d020115 93
    0x1001149076070f0030090122040d61501804580318030404100c41300040040c4510355034084580e4901d40c848800d414010020340d01030340081d6070040c081060300d0106006400b01c99019100b911f00b4003944200d46022840c620440994480010900703043c020324500118a0852401840070203002864413100058007468240c45180081d600c94049280051192203003030441c540141810032028007d52117901240c0d200700c1d030f0304002940d108030200030070409200c2d41d03800281d120000d240c10b10380ba80322140c2d40c240242540052103008501010b412a040080d68036200005d0000355140d65554503250540c2c000c0d0183c68000e5003000d00148050800145007042d000b5640010407140050314140000380b00060903002c00c01100301b0020a20904500941300149a0700200040030361460414a007404006000340d51b105d4010402c20745030360b90000d805504204100ca061116403100e100140c800c0c8141c0e03103c251030380800300001440344004142c03110310300e580b6002072003041205280c07405411070754 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2013425 1250 2012175 2012189
    0x6040b0a11090f090703020408030408030301050112020306010f08040203120403060902040b030a0203060f07031508160506030106090b0c010b0301090803040308010e07200106180b01090506030906040f050309061603080907 97
    0x104400700101d10b49503444c0d03600100181001840e05440d4010207046900940000003140d000100400c141c2d41d11005200030302811141c1181141082070009103100c100f0100c41d41049040001314041d03640901035006c17000144031289590395683e10341040580b49000081e4032840c6004c03403805c850b04022442070900755009016265695075500c0164000f14081c040340d04155992098820050a050811001c1e1031900010011600412445501c01c803598006c40e0280c27200380010004141c100d00745406440104c0c12890312031440208581c0103010324450751b649903090500b003030140300c1c00000450286001c1d0395160b0443c1c0c1c0b5045c40b10b86904040c1c0f4440002442e0340101c0c0000c6840e59494000501340800100759981c1d58040441031164800040002640e5800080035a60b00316110a00130131040e0380150840ca0034104051b110355000b000900807807409408802044801d100b110740b0f480d402440c171034030b410581184000302c05015000f240407507201800704401c3c00002032400126049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2014675 1250 2013425 2013439
    0x307060f0503041103060c040302130606080601110f070b03090f01020703050f030601020a050d0302030106030b0108060a090207020a03080d020706060506090d061104090203010308030601020c0a0311010c021206040b0a1109 97
    0xc0e04404660a510082080da00c1803406215060255000d0014a0040740303641184c98030780c3e0450041180c007141440c61402c43c245042c40800141d03400441c0e155100c1400d0901449020034045114186002406080e50a014a010129020a40c1d0000d036004072060000c0b0740613008101ca10360708038414104041d000c03607010b1201400703401001d0000d5601840c184144c510400242d0303100d5280040c400200c070086034000c00184041513251044100e8201e003460f1005e403034144040481c2e0b0b036804078040c9024094002801030103640350481510015988041e1490765000c82d0f900312070003500800c004135240360a0900010321481c00c00260f42402a0050800ca13001d113803592240006c052140ca00183c152041c4000901900f99101660080d805400c42942c1c03854400300080c105208541c80f14440c10040000744081000c521007030003500820f0910850b21000c50002449440c090150f81d0f5842c443c2c40100410000b038034082031300880058406100c208180940030169004040505400c401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2015925 1250 2014675 2014697
    0xe0106090b0f03040615030203010509010f050601030903080f0c0412030306050a0605071109090f01090303090b0606040b04030809011b050109020108060411090103050408070605070906080609010b0406050304110301050112020a05030706 103
    0x105c13580490003000e1810300019101d50380f80e000c6820f580d000c5501802a0f5950440190b01240da409501d40c00340b02442c041190703805a585c041d2400178050880d80e400d00054000030902c0340150122006418442504d01e203c44603468014040c00b582d0107081d00400f102c1a00040c111f002e881600c003100d0384440210762846100090054003000140003640300d00c1507a00002c0c0c409802e101e49054103000382d8010944181604020f240181d0182006004100070042041441070000036036003034a034001d100395601d51680c801225200b503215008658005220320306c4d4104481507000301d49580c800c1c2c075040300954400c000c00040f10001a0501d003034150402403135007650700c00e40c03080d507009108010395410241141c5030740048078800c4070050302203001701707206100c0c1c160040d460a03440801140c00c03009a60414511080d24002d500c221400d200b00800070a04200743c0d46c50314004114003030001c200301e43e036540e8614080c03a0207000030785c004c80e840b110104d202d003404286030040d01c0543d02c8541c4422 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2017175 1250 2015925 2015933
    0xa0903030e1207030c0312020d0e01051606060f0317040503030a050c0a0213020a02010509011118031203090109170703020309040506060c1006050a05010201020c0303010509040f0602040b040e060102061501050a03150e0106090b0f0304 102
    0x8dc1c044c0411602918481d0f8a020008110b40f03d40e1018220004030f0f000040c0c25407034136407800280e007880303003000700070501c801c000c9aa400822681801e4451820a0f01c860506610919006902e40000c1d800300d000d141440000020341d0240c040d00e115540240096210880c42a080342c0c000d41e055030ac1842d00b00075004908041907135600d0100000390460304d40f0b00910b0036a8003107070070550341c2c00d03070a945900310a07040c020314444000d4900c0e4070703038070840c9403240c80c0c0c1c0c001c3d61364410701444502841d1900c0c005421995404c00b600c500501500c141d030000c0c203810099000410761805035510580a64a01040c9948144262580b07101c5007001903285908040030070a19000003803084805081c0e150300b980004005001600080020082c890340700e03403c24026030800345004050604541c01002040103549031040c0481070100d0a0070020b5440c014540218003a0006984409540d41110030000f100b0102d415098102d42140c1c0d684000d25848220401c0c9501c2072076a5880044d0080c40428041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2018425 1250 2017175 2017177
    0xc0c0f03050c030c0106120c0506030f01210501020712020111120a0f020c030d060504061703030403030507020f010c0206010806060d0305030a0b06090a080a02090105060a0903030e1207030c0312020d0e0105 90
    0x5a4604011281800c000703031344480c00e5030340ca60040844000b1000c2040200000702d600079001d084100d601e9419440d022841400040051140106070710004140c83e0940c002c0081301c2000c990000001e66945001d4280080640f03641e022140040d8a41015042080c032500250b80c5000e034402c81420890b100c40c02c2400191018280301040994200b0902c10091820001005104074a042c0859001e240404004c11103500d50b02c000312100d209516440507040100480b81e0259143c140060152105d0030128170300050011100035030b600e8050081c80c40c5400103001130495109504a0761560b03076510500c1503001c0c14250080114000f8800b198080c1d101c1e8208400c0c1c410081c051604000051b0005070240c003407544400c1554100006803000d6081440026014000c2500c5952901c031580300010004401c1e4800501040003c1d240480d080d51045000401040d1050840c1c00035516400c00007010400c0d8801260940c0c490302d14030259a001107103441220303056031140c21721006000015511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2019675 1250 2018425 2018437
    0xd02010e0a1205070609120f080a02011508011409030a0e09071103030a0516020106030c06030c03020403020301050403030c020d0e010c0b0403051b06060103060812030406020702030f0105040609060c0c0f0305 91
    0x400007071541c01144000c8a40541c0500900500060550030316140000c0c2080d03125402c03100c80640d0a11450004c244042c203d2204507a0003142240d41d420098812070041000c18680ca40d03803940d0781000030b441201500540300741525244040091f88035400b00701d56a2103110701d01c80201d441240450400d00e0036640b034983c0728a107403c02521104200504c203007107a104131103443c000b581d0340707050011164480154262038030f110300007082281d085460705000140369100e89010180c030340420b441014801d4046e6002180e001d0300074026070509180c0540544481c81c0c0e0800140705000400304501c1c07007a8200424924181c4501140380281d131142d0951220041080d402e0090801903030040c40706910702c0460b465401030281003e81003003400141070b100c02d98494100c0c1d501158a003410103055134104c035003060740032000580d00d1f040d92000c2800c1c111019500c103a076510b440d04210500c207683e0013142d001445440700b0019002034503400c0c0c0d00d1010142c000b5001c4021414140c1c0040d000d07800a0039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2020925 1250 2019675 2019679
    0x90b030a0b040308040b06010c0209150102010e0304080102120606030f07050d020702060304030e0306010801022104020f090403020604150509031c061203050408010c0203040e0a020d060504020a050304020f010305060d02010e 98
    0x10005500d071003070600000d4400300c00150f400d908010070300c18082a4030f40c000d0402d03e040c01e0f0224258000400280380035262410322602440e005007182e000b584a0460100c0e0803003940d4440d5078800b11036000f50030142d030304880400b0000004038149004800c6911418031680c1c0d8501644402904407507680000701a001840d03402c21141c0301503505c51000d14421403080d0b41d010300025004062500705401a40402002e82c01400b19a16881202901002d006003020300d80405a40d1030000420300c1c50301c001e034039410140d09000d120a242c0c2c041050707841680101c0724079a602c000170000310200c60084520f0707219a0001d000b00303a6a007085403030481c44500c010402091b52a152a003220380c50010607800c0b404248002003c0102c214280100346d4a4207190024505241c90251a64010400100211420b607800070b90b000c000300190344404c001e040098421511091000d4000d0719903071064074180d109400070064581e003503200c1d01411f803080380d010341450b2102d01c5503801580c401c47d0b0411825 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2022175 1250 2020925 2020933
    0x80d020f0417010c05090102070501031a0d03120608070302010f030902011103040906030b060301020405010905010c03020708030406030204091419021303060f1407090803030402060c03090a0801020c0c060403020a090b03 96
    0x1905030003558094070241c00c070014900e425000301414542182c2081c03200300103020b414016400b640c1c0e00404c6e0321044410078200030595030501c3c0000e0044901000c00a9803021504071144141540141458541510482d040060b540ca0316070091f680c80c45448020b000070801a000710701d40c4d200380c014070240c41c418100900306000504000e400e41e0456040503e1a9a603280d04009124803520344c43d0f0042000e600071071419044c80700082c42c1800ca40961814000750078003d104051082240307100801d40350017a60f403940e0701c1c2c8100030040c1d8828411400c106c2c3c100007038488101c0c132601402340900985142c0f0760074002483c0e01c40029401c004007598148034001d02c00400b09000d07000700814811034640008220400810403c1c1181001d4008420003200c60020722405400008036500306404445003926261a05041440c610030b209175240c006e110a8400aa220015005808036009900664001068107002d0108900407840040e501002d843e80030850b07920306600801d00b17003101070107072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2023425 1250 2022175 2022187
    0x3180307060e0c0307060c08070803130602030906040201080a020a020607030f020403020405010927050304030b1306090308010303030c03140105040b01020f161503020306180901060f0e010e0603010504050703080d02 94
    0x40e00329854082c0081254124128800c0d052030306000c010f015050b01c0c20702c1c100101458a440c1014011210700403d030305800030105058241c01e000100c00d85034416003d55803071804214030340d1100c4042d1012400300701154041940000c050081c0e96107401c0690007014507030b0700c1100403800fa02ca03409802c03d04950800c000700240e100c07400f45601030902d40d83c3c00b00e51070311000204802c0c1100c00c10200006941c1c0d00d140400078101208642c01c80741c010300480c095464401210094004522000346041d140903003503002c068000c01402c1c100ca020762400c10102d811500c0030343c00d40300d0b050445003804000300f00500162400d5400b6020640c2c041c41242d5050940e040c070b4900c0c2c050b4811030500c41071803001081104030600d041802c2800c0d2585070660450034844042031102c480d2015020058056070300040141d5402d511040c0140240410300400315501c0022000d10102805a441c400c001e490010b00582414080c2500440e84580107200003440c6480b61001c68008000d460b1600341c0802003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2024675 1250 2023425 2023433
    0x5011a06121515040e060103020703080a0f06091a01020d02060106090501200106060503010311010507030f030203040f230609060f0403081005030102030106030e0f06071e030b0907020309010f0206010b03180307 92
    0x900e034240c405100043d070368034140b1170108071a800042c4074504141c01000490002980910100e4000109080c00708011007240c00d0503000e01310981240984900d010400d1518881004902e011031f1707002c0c0c081c2c03180c03842803000c12621610240690004100480c2c001c001c0c0d03510400b86a544440d5507140329046030f26000302c15003516032990000c00018000700c010300038812080d20080c3c0c2d03008242003191502c19155000b03410992016000c209241d804400941800a02110b11450641c0301d48580c0d034036204180518014003c0c030b0108141441030f1400251584c0001030f449006203e482c0c1c070201d16075115035040320100002001c405240c1c038900030003e01602c0c00d001650181440343c80c00714a401496408030726058082c038545003075910140c20f0042d055042424050740405014481c42c110320742d040700390702400040140940110198080082e4180c1c040060084844c007680c42c1203a2645502040303940d07a07000e000e11041d981081020903500b02441022a40c00e03000203054a09003581511 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2025925 1250 2024675 2024689
    0x150f0a0303080106091203120c0e0306010b040906050301020301030f02060a02070e0403020304060f0503061005090103110d0b0301050c030403050306130b031905071a1608040e0405010905011a061215 87
    0x4421030210b000b06005200c0c15410848900c041c00d00104645003003012510b00030112400c2c804106002641c1e007646070100d82c0304520304845100b0180c2120300e02c0d691003020305880d60052042512440c40c00001044519040c02124102da4108070000000d520301d03003c10500760b10440d44042907100301c9000042001d0035014903445240a0b401440d2641c2ca01407010b00282a0700b4000d01c2000010030400110340e40300e0301d250440c08460318007075032100740300001680140383c4043d041d4507140300410340310700072006078110303a00c0c0c3c46050b00240450f4803a02410300050106407801030100d541800018500d003829124185e0f0300b003042c10b000c1141d00100303000c42d04228814030104038071240d1003422014842c0030404000148044060b0250140724404070888500901403111840c0910504840500c60703104150b074003406401c104d03c02c107400e10f40b4090b0300800741c1c03450448080d400c0c03000840d81c012003103080d169000c501400d90307481d0860903900b135038001e84000c0400e115808002c030079103003580300d6007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2027175 1250 2025925 2025929
    0x609010509100801060f03050103030f0c0501110f0d06050a06120506030304050a030605040201030c0905030c040207170f07030f0801030305190201090605090309031b0a031202010905010f06050405060414150f0a 92
    0xa141e00f030f01541000402041e01c486100850103050814004100080d403241c00300011803030b07030310702200c4000325842d180b40035146c0c0d040d00740750410002c6003504452070440001c0a100c0c080e40d004011203661a820b100543c100c9110f60300105074212100220403049800403503128600500b0303a0304d019280d1000070a8590f075600f0a0314950ba40310304010442d6090f1060107010029401c10107800c520f40070000b0780d07072080c08070200e001e90b4001c200c0a04120002c0b01805620208105450b1140c58012042c503054101184c1a0002952030383c001066600030a296410389415948644c5400c03903113504182904054112001107640e100c85a001294091040600484012024641c0d860001003058030701194030b100154805203c007426540f590f9480000812690311201d10201d00c40410f034141c0c018490180054455400c190418078015029400001070307880489080045445040078441100c80f0804520174801c0c03114003094008207412044040140700510780e0030513402000c045810310701c00e9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2028425 1250 2027175 2027177
    0x5030d09060906050901060f050d0602070b0106020307020109140108010501030c020a121d0301140402010c020d0b07030204030c06080402031002090a03020a0b09010306060c0302031206010c060504050606120304060e060901050910 100
    0xb9a0038001082020300841c2c1c1c100c00108003d000560401030880c410030a04d114070707803080146400c42010401241c0603204010b400015414140d030350307a000039450303900824040b400103011380750224040c04801e040144802045c1c2d90343c81141c0c02c1c440190024030344402502d0a603c5200400000101c440c04880b89031046982c030544e89040d0837001c0c4003842d001c031781c40710303c00c0c0d050441001c440400169043d50281c0c0928240203180c00c0303400464081c040c0c049000c0c0c42c3d0044501080350140d0545c0081049a11982c40d405040d641d0700c0d000c664402040d24004d40c560070840841c2c0503190310b6000303400681130040c928280070742d0300d90010340c05120300d911200000c90302182020640d038040c4940b80082003181000c07000181c0d65174000391030b0b21402805801885031040483c0041e48506c12004215902c402c1c104014242801e1041d9a50411941148101c40b039200e41c0500c24130100a42d0100c2d5019161003d00f103071a4010000302d13810240038141040410309c207809056540070300e003900202039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2029675 1250 2028425 2028431
    0x307090501030608120f091801080d0206010e0402060702090a0f0903030b03011104050607080c010f020304050609060106020f0d03050c0d090803100e01030804120302010b060a0207060806041b05030405030d0906 92
    0x2900300003405540d0705501c01c90603604003070340d1010281c2d1000103e41c600700b44602e90f587d5540c003540000d15004d00c40c1c600b24000300300c408004180d140c1d0010b502101c02410740c084621f50703030365040c1c0d180040004603030094126400740841c0d401818049900c80c0c00140c1d030600450f01c95140d02c0441d046450340e003410b40000b0f4807424512082d040030301c140521125804d00c000c0c0741c6410003000c144513116010f402402c0150005200c0704a14080d807121b99403680c04a0103640d03e041c41d0508995070f007820341d03250754070780249000000d0042c0001180c070010704120019010782041e01c001076000389401840303000034003401c000e1058042550f01c1980c03d130030301c01d034040d9842c0d0400e42d4a4400e85d6401d6000100d8080e400e02c010f00200d43c100090b90225500818040745880725403600300d01400001100c02d0300700e800401d0800740c5540200b2480d080d03c04c075a54082d0381d0341d502000c2000381c47d0200e14644150b0060000060414414001540c0c403e008900f140d02d009a060b9588080340c4202c0750581d02c0c659 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2030925 1250 2029675 2029679
    0x70c090e030d05010e012d0f06050306040e070501020d050d09050f03070c090203010b0904090203010917030105040c0503040f020d05120a08010906080115060305070e090f010503010e06010806010311120102030709 93
    0x1000b4841c00340540040c1c0d0008006605101da00160155001d02c1d00600d072840c117408100e105e8460b900500070b4800460344c2e46408e90b540c000504150003c1d92900c0c0306505058440000120020342d0b64201c900590040c50a89101d034005e45a41c0e100340c04e861581600c40300d0100104000708901c11001c6506401596104040d081c100c50501d41a00070000303060040004010300e4050b0003d85441945c1140e00254692152001a004100c20714008000140b1017410305154120000618100ca0041e00e041c000d0740310341d003c2200d4510088500600a080000450002d800e000d1201e001891054085803061503004052040c1c0307400500310342001428505c0107000c04481801548001d18800300213101c24102c1d41c10828103424540107090070107036503100292000b481100b040d0403004010b41b41c2c071160700b04880900c1604030240200c501075828070950360b02d800030008a0504884101c0301600441e401c5985800b103960707545201651102120b620b1089800c000e1005601803003858990641040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2032175 1250 2030925 2030947
    0x6020c030706050601020a0b010312050909040f0201080c0f070f06060e0a0606091205060a1e060303050301030b180307030507060b060313110907020706030b03030f0406020d08090d05040308070c090e03 88
    0x2500108545e04540200240c000003412a04980f030540b5480222040d4590303251508480d1401030402140c0d00a1500003800180304405048503440307030003a80c40c0c070180e6886041032081803103840107204924200308030340004615940d4840074054402d12010840d030380d84040302101c41c00d099540c0348440d65507005c10000d0075082200c040040150041c42070f5481155142c031603c505c40107003003607121922880781d116540614000c030441c162020340e00f04545901c0c0d040040c89500300740002c41b10b10805a0214000242810303a051046510400a51600742241d4044409420080084803040e44900028600f80d0b03902c0051882958448d440140010960504a03c000d020310030042c001d2030428244103070150f000c13901c4819280e0700d05000c03810b602c007000468694411a0094164800049404150154042115075061029644480c916112140842d4440301c91a007400b0200d07004010810024400602404490380510780e012a815601c0d150f440c20b6842020400d038094100103030710a404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2033425 1250 2032175 2032181
    0x12010801060e06060702010f0905060301080307050609010605060418090206030406050a0b04090201080601030b0f030601030602090a06020304050d06050a020c010501030302030301061106010305070506090d0c0b0403110301020304020d03030e010906020c030706 113
    0x8090741c24602c0c001c2e080032408140c0d02c3c4240d9101038100140e003e090101d031130003143e081c0000e00014040550b2503a444441c81e40307a410284040703601d402a070010078030410050280780c0940d407008024516041c500980b00600040c1c3d07103000e103091a110514140540e48002c080c500c5680580404a2685401e001910403103080e081e1040c49240b41000d90000350740d00c118504c4d4041d1007801c0014010300c0850000e503501184415242d450320a0a002108001540e0050014a5003e40b0049822074403a5000ea03120b0187d8017070160460202c2c807030403000c200d85421080d0000d912000c0140f908508041060030740d00c00340c1099000d6800040100102e9034007080440348501c000000c0d041030b505540d0f40355210f80481c820a031003000040307240f2400d41d480301e10a1044941c0600f07008003203035a413544a0350a811601c4207407841c500448c8480034508060080b139100f954000d008900d150b450ba64154000c201c0e010f8140129941c0341035180014206100070200ea20b1281c00a688400142c0b130304900ba = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2034675 1250 2033425 2033429
    0x30b0a090515130609050a02070501050c040803031b0408030a11070609030803010905040602091215070309030e09090106050d0b0402040b030d02030304140c040606050a090e010b04030f0501020c031201080106 91
    0x1028070300707010410150140d02400d00403000864240380b03114003a01401c000b40200760410081d00c0c1ca01342c14030a81036071a9000340f84140c85180280710b159180e80703050368140258030400c1c2c202c1d00100000f60454103920410040d000c54041d20900f06500d40c03840a1841c1c105a0003200465024003945125100420401c001081e2900e05004030320309550301d89010f0f00061042902544d100c0e03021404004d05601030f5180c0704c0c0054104510003d00e012050b44c0d8002c01c8521307102e01c2c0c091002246030540309009180c4620380584a80405003081c03424040031010082c02c00a055680d01d00200d1303942d4400d01d010302c00c02c1c020a503d02c2e00b8240390040000315000481007a209901682401070300b2600802901e5206821a5030760142415407210141891850130038103034440e01c1c108000c00c0d525000000f0b44600301c0d5507a188000702c3c0d2500400d00340890203000d06024110140420400104880c107403c601c903120714000b40c18003104000961454110f40030043c11400d01c2030052141900034070503800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2035925 1250 2034675 2034689
    0x309090204140607050102070816030e03120306010e03150c090909010207170708070204060306060314010608120c01090c0905070f020606010c02040902040209030d03020c0d090e010605030702070902040303030b0a 93
    0x714092600c002d50030504100000c1a000b4400450050140903082d07061300c183c0b40d0071450850b901e42e00079282041d0800012411800300d4003da2072400c1c23906001070030f01c0071500744d030031194515181c0d01c0064036a040a0600198144103402d507004501c00f0242495001e45d49a2041c1c40d03c0c3c0f2080010811881c030000c004212580c410302c0304d5004222155a150303005e060401f80302d56210328a090800082c032070444081c0d041410302000000b082155406501203c1c0541e0041c002d050100514a0903916030b4418408180d00c840544080b01c00e00c40020312081d03011500000301c0348001d036544503642c4800e9001c50713501d555900400104940281c0c00601000c268800380405142c120006000754041440180c085c950b03c1c0307030074030454490368101c81d45804020121000c481203100c00601940c04140c000801c1e0140c1848240d50358042c2801405840310341c41d40800980c280001228076401c02424072045100c3c00030300058140b018401070014600a94000c605c0e44e02140038044820050b44c0880 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2037175 1250 2035925 2035927
    0xc071406030109180501020c03040302010f05070b01050909010b03010e010b010206161205040305071406040309050f030307060b0307050d0f030f0801080c0d02030313090f050903030103051002030a11041203090902 93
    0x41503640e44101c0e41550f1a85000150000c028091401001901036005010703620025000c10f2000001020780100c0f4400da8901c0074480720048115214020428002d040d40350304001130010345070a65004c0d0741324800400000d034080b0084002800d6600c2145c1c2280c060b55a40b008102a507414041e00b5030180d41459040c0540703803444d0000f04242400c04d400d040546e40d40c0041001c1620980498203000e0b08030642d000524895007000740c55501c1a20f04030003082c5003500001d424140200342c10700b0680020040c6080803a1500c070840984442001640c2c0760207100804a00e607a6402c0e03030a845036000304041d8420500c035280207018080701c00e284009008030348004201d00000022048606101524210034101407840881c2c61402002014030448070400008980443c0c64ae005c40a1014807103c244120f894200d5413948900c0207000c040e005070018a18a01c120300030f81c0046421120900c0f00003810403202e00c10a2150f00b25070460742d507184405440c03a0078194080c45540203048040421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2038425 1250 2037175 2037209
    0x3150b010503040f020316030305030a06060f1407020a03050307200402030114220f0c02010b0406030203030f03100302060406110c04270507080111040609060806010c02040f020705010e01020c07 85
    0x81d145000007400201001c81d0013a54000b15141030142c00300c408800c0703141c400040d48901d4003400302d40080307485001c0d1034605040000c1d940e1080c11950781203007098076520100000c0308110310031a4081c0100b07a0300300c100c0042c00400030780100002c0c04218041c005540720100304c8641000381c0c604107240d25202d60300500041c08110407959079803060803011100000c201d4401c0305417141195520010401031881d202c181703456800c02d500880c1400748198020030880403c10204001c0b684a404065099030081c02640540c1d80004004c64000c148001048040c586e66030000d850386c0d02c9030b0040c1380010403000e25440b0008040051441c800d101719410710030103241e02e2042007901c0b440b585200c0000c81400315201440402d01c03900d005000400001d00c42850b002681c147c80c1d903c60b100d110f00143d4016000540113128680d12402000141d481c000d28008540030072014001800070307490f44990030002ea800080091103000c1c1038210410015840c1d00c60f1241d5203042c92a168002107031300c02e58040d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2039675 1250 2038425 2038427
    0x9061e0a020304020301090c0603061404050c030c0703050c0d02010609110a020a0b0c09030105090606030f06070f18050603040b0114060702090609090703080d020705100b010f0e01020c0607080403150b01 89
    0x4410340c000301040c001601c03640c513400000d014202c001d0b000b40001b03d0340c20300460ba40394190010420ba6400d0203210003850410300500084030811a940c000310302050021600509404009090b0346000c1d1405030f00b881580c440542c100400031000c0800b50b9176680d01040344081034000c04840c00f084070802420700b4088035010b0b44031002d08000408031060900080c0c1207003218429100d0014001c1c0c0200070760314004412580e514000d6032030510a109000140040810004500b4407441103640d07002e142c0050701000f50f0f500c2040480c0c00342d081169110124441e291003000d14400c90145a4407040d070b51400c4410b03881d00607034064050003910100000d1015840da1405141c2240c003d440e40310951386c8098445042c144603800081a8400000d07400858a00640103400200d000e142a41c0101d19440105400c0b0b802c0c8640031804510500c50203000300f03003c5c0b03000c000402c0040c01502c0c05241a0400258190320043d01110000c07808102803003030101036480420a42403200c010840c40d288080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2040925 1250 2039675 2039731
    0x90204080c01210c0c0605060a030c140d061103041101030501150804060204030501020a020d080f060d03030905010b09090109030801080a0201050412030306050d06020307030b01080103020a06050a02070b040603050906 95
    0x1c00107051291032510b10900d07451a40f940c045043c02114208903082d04c81600900c1c1001d08031040c0d4500f4146800701d40d2078501509105e0849e03901034041e402d030078176258007889801c050101da554440032090709034021441078002d030b1600c075226001e41907803480c040c5482414807403800c01442c10145040c00500c098241584c6140d0014100c2c1840304032590340e49459406445943c00c010310a50000c600440c0843c1c0000c0c520340c40044c00d4990101681e0303190203a54160100f180d02d150b1122900c0101c5020901a901112085005500108510314460081204144180d511029580d5540f2010040c10340c41312000f030140240c1d40c0a8082405181c00081440c0110300071301c40000d1038032f801d03001014081d9026900600004d000b450345036001d4103041c070094004480b21800b10307003043c1301c040741c940c840d05000d4141c960003040a1800c5090040481c1c0175004000e055080d81304140380811403a5440010380000c01e00c0b59404606803420040d0340d403c185025003582c80c20217010180010b0851503103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2042175 1250 2040925 2040943
    0x20604030207050409020a0306020c03090a09020a0f0302070302150c04051003020c0d0e0a0305060a09020406090902090408090f0303040902070303110c1c05071a0f0108030906091009080609030d0609020408 90
    0x56010072003030035a00000e04120b0307660384009d140a04c005240e54038280040050820108100d030a40310082e03030364903100b0580c032640300342200042454180050340ba01039409801560301030310496a00201d900400c40082c40151406c00f803054002c00c0c1008185010702054410503a01c1c074041d0f00f81803183d8061a0786641444001c0240b00c0d100107400d280c1d4681c400d03901d0040d9001400c4503a00d042031038440005010010050340558101100801c50303011a0180c000940e6000c1c0200310640d030b42c1d13101e418050f0000400150321556610689016590410140010301110341005a03603049a03d0044e00301d9080c000340003401007050041541a02c404074003440041c2d00703482d5100e04624400c5040f101d501c1103003402403041200d401d0200320344c1c1070f00201c1445200e818101032601e0b62503500250392070160a8803903900000401c00e08105003001c0c1d5000e01d80191034184503101e42c0e141c054917800c0c880d0440340705001da84081482c2040c0d11b01c2e030040034005c15100d6400c6182500708555651180449d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2043425 1250 2042175 2042179
    0x20406090e040204021c020403050c060405011d0301020903070e0604050f04030507030302030901061205100e0303010f03020607080702100f030c050a090303030203100915030309050a05090103021002030c0307030804050d02060403020705 103
    0x1040c001015512590125203009100e0b01c854800c81c51314106d540000c0d00b10380410b407a68820140c111a89051401c11642640c4058480300301c0d1448145031508101c45003811580c0554080c01140d800c1c0e20304104040c09000100041801d92404909000450303100400b420761040c910818400404d030003074115140340340c0528000d40d480d030f10006401d0141c05141e02c003029a100c10380e803003010f1060102c1c0d2124814080001841120300d0048220b03a240802c5c020880c130010409420001881d00340020110345100e2440c99080251070340002c0d50715a108081c500215902801812a056140c403444150700303e0340c20118204034043d14000c10a9145000007401d040e400408118604510041c5c2801024111818849006802c000c24081480707480308030042003c0040c003090503d400400101074036800380c4500c510b40e296400300601e021a2007940c8095010030000f607100c0307000620007440107034080d860301621400d10303241c001c1c50411b54002c0c28085402003000e100000381e011622000311041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2044675 1250 2043425 2043449
    0x31208040606080616080a0b060405010c15050a0e060a051501030b03150709090b0108060f01030903050708040906030b0a021309050c0c0708010501050901080f0d0503070905090f010806070302040609 87
    0x451074420300400e01600006102e110380020484001210020381c80b0801c8a59134110329900d8088440081d24007200c0c08981c40842407000f80a02c0d4807402c00d00c1510342c01010804541e0641c0c142041c121801901c00c00c02d0316423161603140c49039004010311a000340d40b0700710400491400450120094000e1a88a810181c40d2024901c1590301044081401d204c3d810140190b801c0c01c40d0081d25180c03031840784845aa040c07400d1203181d507000c0d002c5580310756805841c80c1800070f001c1c0c004400070504190304400744002408008049172420f4040c0c000f42000410004440381141050b13548000002c0c40f00d002c1d2401001074407040c0d1004c5266104882203c0801305540c1c0341e2000d400f065001d802030030002c1d0b214042c800500780702c0541101c0e0407594103030344140c101e076219100c00351a0355507052006000d501c500c0c80d00c1c411600c0740700299407052007840e050615545644c00552014020f9503428000380d0101e0051050020512410342c00500c5400c0c02c500e010710302803014103120a14405c540c0350360a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2045925 1250 2044675 2044681
    0x7060c110a0306050f060102070f080601030b09070b0408010209090105040209010507020f031f021e030402010504030803310b0106181202060c030c06010f05030a030801050409050c03010515010e0307031208 90
    0xa90240c0030001c2e5a1001007802685422050440480422160a0300611500b032001400c1c402400c0e8540603906a200940003507030960725840f00309100a0b08140139885444000207220a81c0405007024200882c005613440c6111810494a24410303080107114a20410144009a0700300003100c0d4130b250306642960025400c00000390429003140b01c1ea41c1d4113024118480003444041e40182040805280c05074003412200d01e50706580c1c00100c07002408284200018400301e00c50300d003c1c55109283d0403900c1841140c5201c08214481444803120140448003001020040300070b204a000d0000c526007002c1c4602c80c0c01481c2840c40d035912680d4103042c2c0c0d45019400f951580c0341100d04a21000707048a40e9180b034070401556880c802d10603406191020785000c9400c4c500401d00c1c5543e19090340d0344c0310300b0380d00b01002c0000500f203004007104c40e4821313200700c80c8040c1c90a01410f88a00801e01c4281000d102c8003002420b60105520b841c5e100303401c44101400003440000c4414400300c110f24090382155 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2047175 1250 2045925 2045929
    0x714060901030e010902090a0e010e01060302011b0501060503031204060507020a0201020c06070f0204020301080a031202030c1b1e03040503070603060b03010909020d050106030b180a050c0603090304090e0705010207060207060c11 100
    0x4480021f5001580b010402c400ca00c401d821803000d00b419400200030441c2e8030301c141400c860305404020300240d03500303140300400c5d900342d885071003254014000029210740d1000003914651141e2941765480f42204200b0080c03007014402c559225080780040d00032205c00d40d00003501d402007500c0851040d40081041c40a00451508038180250702030000c5560f540c40c0c1131016526400030030b088000503440004440298018005c1e20301172906801c44605082d6500654407820004209180c024401c1c2e1454900c0c03403172000040040c1211030301c080d613520780c140b00915040c031030f903904031005050074248100144907040781140d0446107080c000203050740f40c5200280119a1225002d0b1103503081441c08000d1068010b00e882c080c0c0e101b0107910000328106281940c6807003505d000a45180c00c019207460150400c6002960301140e28025203142030f8540c031040049400e49002c1001590011209000c5940c04100401c05002540010f040461400e0030060103c2d200900041444070242c0c4c4000641e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2048425 1250 2047175 2047181
    0x13021305031605030705011b0204050402040e1006030204050702031612030207050d050a02071202130b03010f1404020f18070507080d02040303030903080a0510120503090901170714060901030e01 85
    0x2409009007554000042e4441c0c2c9403800c000b900803907102e800707415400209580100c18510402070103c3c101c5c0700c1502580c080000030700340203000b0b81e04640c90b1510381c1d030000000d2007a281c0401030000c00158440c02c43c0184011208014110015540100807a04202d15101d10040486500c01000454820b030600214061700401e0f400400e14400c8205e0489110f4014014241090056085030740039940e807400040440000f15020f5005011048401c16000068010004100c805000850039104400c44102116030003805100444c00d007000781301c21481c003881d032141000b80031594010031820014610954640152404051020002e42841000003c02c00d032006911690411502c490307803410040d000e4200100110000b480c0308000408031074061240e10f01a22040042d80b41e681d092807914440c08500c42000d803581e10046c020107096136211810107000e0861402c00b82c020010001542e03150070004c0c0c1000380c071800180c04d03210840d1a4841a10042c3c1c000346004606840810141401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2049675 1250 2048425 2048429
    0x90c06040602070602010b06040b07060e0114010902040501170601080f04030903240c03060303050301060c0303020c011d0d0207030b07050a030905070b090f0d0c0b03040c090e060610020606130213 86
    0x21a0015081c1d4020414100703c8000c0d03002805001108002c0101d41e20890048104080040c40203001241d00ea9019580c441e405400000d07403042c0e000300901070040268048036440383c00107024130180d40c0c03041c03182040c07a1902d040c6504500380200042c217015002003007a280171203898006020300d84034140803c01141c00c4442005008503071020500d44000c01e00b1101103c9044c56402c1c0e1045200344220707001c4a030180e50b964156400d00004075240408030006071304064084c0040c00007650284a108207480284400d441c4a413000c3c50717082e04004440100005540100320108007140f809088560f001c0c420f894000c0d5211140700e41034000b000032480c050f16070b01c41d004001c49d151801800810758050300301c030b80d0400030441e1010002a5901f1040080072076248090820208840801541c1c000d0300c81c2d00e21920050322080107000312400c01d800b2030f41580c00a010301c003d80c2009240000340b003103248050f00c0030733151840c0840e11340e251006402031aa5400685201581c040b0f6681d0300c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2050925 1250 2049675 2049679
    0x702030304170703030e0306040201020d0503100306021314091005040207031101020703030b1507031202090102010219020604060501050409020603040b10050a08030c0105070807020604060b0d0f080c010c03021e03090c 95
    0x1505040c07000700d03070303554003d030740022804180c11500190042c40d000440034400c6905a00402407d07070810022165500041c29081595040d00c0340400004d507d40094802e0105940001d402a807401c20700104107584082014007814021060140403000b480c088825940107a4002d6a111901e29040b500c9990b02d80e5182059480400c414080540c0340c0c004054020080f1a4500e00c102c00710003040741d501c20001c00401161051a0441308054507802400707102c3c005000060818080c86c41c0d1141007001000c012006030811408c1008004041c440c0354054901500c04101c900d041d075002c07410310b22010304054442050540019041c03040070302d030003000d440c0250a5042c0c0a585502803a503d030840150801207508040008843c20310441c1c03400d20079002c5500402d829112603c52400504403034003140c1d00030a08405010104520f082003020b400d02c1400d030b45554054a401e003600311600da95081e81003600402c425146242103c544811409200100e140e5039202c50132501d00e00820303040380903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2052175 1250 2050925 2050949
    0x6032f090402030108030a09050613050103090c0f03080c0f01021206090a0e0304080c09060909060601050c03190f0e0108010803040501110c0904030201050f010602060108070e0901021605010c0e04051b0702030304 93
    0x310745d080d8044080c1c0280c000da41c48800100341c4820411420703026008502c442551040b004105c3c075031207a0421491540200c1e50300c21050b441c1c4074504e08952003074100f03480c913000010f40a10003000030006d00205441c100000c40c10f002030002d03200d01503000a441c4a11034200c2c81d0201d0541402580035000e00010001140c2c2d4480d601c0f40c2441c1c48040c82c0519038403c0314030070b000640c00e06211150320b1040840b1005810640d039900300555030761300645000c2607148400d11910302e08009410010074416029152505e1146e211070009041340007820407203042005003401041001070000035201541e800b4240f038510110180d1165107041010422030754000c100d407050205068040d0320040c010b84210b01e50540c180c1c0c036034801b6680d0f624207200306c40311a0f01c42030080201a03044138105811405020015240200c8502051210501e01000703617242c3e55982549002c2d030b90801550170070724405540074400351500d002c46441c85010100003180c81e00000440b14110b40e014401c6401601c6281000c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2053425 1250 2052175 2052179
    0x180a0602010507120209030a030813080c0105061f080109020901021005040606030309080a030504050609011209050606090106030b060415090e070504050310020304050a11040b130e060106032f0904020301 89
    0x740a80000d84548001c100c8007040e950403510760b8002c03601c00c11806802000d080a950f0750444c0ca005d4000c040c47c41c0006582188000610078074000d0140000300701c0049014104042085009112904011640c603810320500d08465041300e680d138119520114010303211302e002c0380180d0809221408032542149450100001c02c80c030b0750300c080e0607a8020340d101d100d07103601c420180b640c518450b48040c021a00501c401c02c82480e04c070000744101c075010300d00b0a00c54680b032750207101600c00c7d45a04a5886e0000010465941481d240150061007186070910203081c40384081038041c0311303034001c10300040c052032030481840e40201d18110041400501c0e40c00146000360f002440d81d0428090a80701e400380404031a5021030701d0081c2c0780500d402001502c6001380356501d100316807420940050b002511024840400e60b202030007084c2e1000d603180302240d401030a03480c1c10b00f400c2c030503001041894544116070b0018030040082c440b20780e13001d84558903e0600528000554000c6000070b5902ca4000000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2054675 1250 2053425 2053427
    0x20a0503030a180501020304060206011203090e04060b03250b0306061e030108010c0504050a0509090c060406050a020105010f0e0403050c030c010606030209040b030601061209020d060906020301080f0a0c0605180a06 94
    0x12503c0c0c10f100509602400d29152001280c40b80f00790b10078440181c0c4803400500c640614000501d042d07a104c2c0c10818030fa640c0d14030110302044011070382954060744e104e81310655801c040c84180e9103100800c580c070b80306001a600f06c55a140080c06669040c40e80800000d031280c44520860310580c009481c0303815160b00440c880401d9500900808099508085c10300007054050010380f07040c0e0320014461008036040c0000d21146a10017400a0414441d15160500a882d584000c1020b0714250b65000e6546182032006401d4520690104541c03c840801c200806417001d540c29420540c14904241d440c4012810343c0d2450050102c40d44c503a501c0d00400140382d0b0740590081510380f0040d41c044c44000000b80c2090b031100800d214241c04268000340785602600b3f83d900c091a007510042c40e40c50489255100c08088440b441021266a0760004c0140203210007000110480102e0700024140c040e00e96a0307c0301d00d1182c0384035400a1040c04254003943e07560707540c0d00740703900c000c041d2441d050303250303a500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2055925 1250 2054675 2054687
    0x3021f03140412200309041a090c0405010905030c060d1509050f0103030801060f0e060f0d020d0204170307050307020103021b03030702010609050a02090a05090a02040308070b0406050105090f0a0504020a0503030a 93
    0x11080d01048600340c0e00c03045082e480580c0182c4e8580d6070040c60a05440034280320285c208100700010388080e4040b081041d03562800c0d103600542d000001142c0b120b00704400500b03803070650380205100342e0008001c003115075594012180c48045500c80403070641d90304030700746034051510740190501b5070502c1c0c1004225856040d0035412240280d0f914007050f66194001c1da9000030005e4043c00044500d10151100d05140c0014a00c403030300c0c0043d071072030b14850003401004c1740c000310105003000707800190030084403241100c040c001092103009185005500d41c2c465550f13204001340241030540100700d8002c4018039060715500300c103d90090741c0c0d503031410401c0240200005c1c050303101582d2801001c1200e003d52442900c140380d602030030780c2c6222402e120070030102100051940311026000c20010000400103000f400080d8442c20311581c4504003468014243d400581100c0d0160340c440c4200203140ca00350031082c5e00700345401d40c0020b6586503400031440c0c442c0b00d03030400780d0503110000b5816503050340b00b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2057175 1250 2055925 2055953
    0x1d030c0309010f03020c0d11030c01060803040305010e0304050102061305010615050702030105070f050406030f020c030406020a030f08060d02090a060302090903070203070f05010c0312020712030203010e0f0103021f031404 97
    0x6616901d42e41c010100a0b002c900421428030a90750064000404040c0980040c002c40c1148c401164100300100318501e0950f00c00303030000002c40c1c001040070404c001090040d9010841c0d000042e50a10b814200001e6807180000e2408401e840b03107403204000c0c48400e51024020f4805418446144240c400020381243e0101c1d6080340030350f107050000350300d803407007188080b5452006554243c07820b407030071204070003602c501c001e03c02c4819401c00040303004c0ca100304010801845a6006800c0650180c14003811400d8800401d2090040e000c04018960742e0b108540e9500c641d04036000d80341030304c039017206400500294000a400035000c009001c0214030000140c00740c288200e0454401d02c3d292008160341c65400d11500d80890543d01c0c114001078010000d034100c03c2103030300005052807000d407640c240c0840c0121224011030360002c018001d4410342d042d100c1d40280001c098407819450741e4045540301801000c50310303080c0050f154948100d8400d4001c600b48100204a0504904007803c1140001c4985 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2058425 1250 2057175 2057177
    0x108220807020f0406030203100f061707030203060702010605030307060e1c03050603010606030e0a06020a020f03041203080601080709030605060307050a030b0105010e0d031b020112050a050106020105090a08040302041d030c030901 101
    0x38859101513140c903008601c04d13203030301601914070681b40c00c40c0100a0503184074440e5641340c0350103001c01d0f10442c071490500b1f80744043c03005000f400d00e1401490708100f0040c00060844e41040d006029646000044a103a194000c2d40003800104a04000303043c10a00200c01c02400d40d41e1030102030880e415003009005400c00c070001c210bc07544e5001e06070700319882c1c00e902d42e0940d00008400740105020741d025007800e02043c01a17442d0a10411071042c21644603800840d200100c0c28080f10a065200242c154010350a00746888030b418504805001c170039451000520b62500c500024003e9242841a20003d10002d040c004030fa40e121701c1d0400400100b4020b09002a4038604044034a1420644140c01e8541549a48440c240050040847c400c0201d10503414012401c1d40c0c0c0da00c09a0511906d842550f009100207840c3d4149a0001d00b92480074184604d10f0b07004d0308200001c01d80ca40120b40c06c030380e4111000182c2031031850f83c28501c0b000460b9035505600021600308819000480244080502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2059675 1250 2058425 2058439
    0x50106120606080414120a03050a0605090705030f070e04020c030705010b03060403050d0c020a12020f0c030c15090f0a03080301060305010506040e0403030c0c050102030703090c050402040b0306010822080702 91
    0x90100c00034121480c41c840d6400182921000c5000b046204c0d0040700381700c51074070541e0346030080c0b642c41c0003039030f40a40101800a44e803442000702a9015108000103440122107044003400d05010045c40d502014104d5080b103c0c0400104084a018001e140300c0e10360f010b40b0941d140c41d5000c40d2030741c90750040141518070394280018801d00c0d213000325807140f08a80c0342d00c81500300045215840010189140da05043d0301c03440000e40d01141030300d1040038108605500404268506209045c14505c020840a010b64443e01802113203542e05202500c041000005c060f0312484180d001850f0400000c0d1616001104a44007209210040c00154160780c02038409010990343d40b07061162078030880c07141103c0d0074861004100040d219400402090100d40b400c1c026199160300c8040c2268016541880400d130740301e62110400105c480500c0040804440c00c40c01c003441d01040c0d005903c0001c00380c0307040100007030004802c0d80300a6603c078101103031f200f0170f4110000c00b85840e0795a5445404280d103e802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2060925 1250 2059675 2059697
    0x40e120715060e0106050714011107021f08070e010905090108010504120207080a020103020f0913020a140705060103060e100501090204060801050d021315030f05010203040b060901080a020105070804030602030901050106 96
    0x72060041d04121110306007089440e81ca060780c200c0b050f80242c0340c1184d140309480c81402c40c40340c00340568000a003420790340c00d55a040f14810080301c1450202d010b00400d07512101881099005034100c0e600c00038508050b4000015a00100c417110760b180c0189038092100d10001c5240d1605500803449079200707044048801d2140d1000b640c0d2051035220f1f07480c50740e210170349002c01548640c020340300c20f480e5002c0f140d052010800001ea40031050419005070b00c1e0380864640b0200c0c1e0b11200c0d10080c904040c01440c034280c0c00341c0b245602c5030720500014200d40e4441400d01e10700740c02000008101c0920b048200480d584410f900e10181d0b11a100740c0000550f00070002c5990b1403e4048040965070080500c1442d0581038050300107051031104404600b03031b14590001c00300e0408903590301c019128100040c2c0d24902844c00301c0c000200900303a180911204001400b81050002d0307403480b01502400e245440b502113103080042c7d4030550300000e11590000c424404007140540020381a100309488000340b5030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2062175 1250 2060925 2060963
    0x30c06040308010609080309130b0301020703020c0102010f021602060a0203040b1b120c15060303090a03050601050310090f061e0204030b0402090a05090c0105030c040b0403030503010306060b07020f010509040e1207 94
    0x140542c01011b176241c0040191030b1a929081418080b081c10035032001c90304000c6803001900f2601b201d43c054025801c1600640da8960342032041c0584515050320440c00c004400f040c3c1511551000c2000340101c0d00021003185581c000c0007500c00500c41c824a85584065414a10f081c0b00741c040c103401c0b550b20401801d4161203000c6019111034051600080004c0030303e0b1102c1e00e501d050301500a86d05030000b00f2002c60246c403140001405036000d50006c0595514080038945410041c8600102c5546440041400105207426681c40542c1200f4041161000c84c08a020000600f00b103122080b0b100240c004100200817403c80d01c224000c0714100706503500c044481d03090720012a0000c10741e81118906540d990b0103900a503800804c000c039010704240e210021031800c4e504c0342d0802d80c003094000c0010020840c260240901405501900c00d0030708003d5800f14081901806940f81884808071b064004d50b12640e01954803079580c07204603840d8407201c0460305241c1e402058251b5058119a6501c8024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2063425 1250 2062175 2062187
    0xb010f030f0206090406080f01060e011211060d06090218010e040902030712030c020306010305010608070b090f01050d09050604080307140c06040305030601020a05031813050f0612030408030c060403080106 90
    0x1660003042501600440b0303420031591354000c089143e401603890601161800c0c1c104a9814071844800000035154109407546010f440140c0c080c075580341556a03400300191001c1601034039024103545603a11907140c918003001070419a0000c07002c461001c074418026440c00440d43c0690340003a2070f0641c050200109010941e1900440607401d680049000c00013a020101a90302c150b00910302071100c00003176800071381090000e034426680d90b034441e41c0500452006120044c018030a00d0a42450064484040b542c000b03510500103061050209004c84803d850b50000c6041c598010300f5036030507180a10b0500c43c41e800a0f030700240080c0c9042c0c10384034101244001c42d101803141070001c000d1503486513000c640d2644014901c1d4110302440b40e04100003142040580780003403032420f0130b1031141125400c1c00010303041246d40b20801c0f82403402344160241e2a04003035030010000c0c0d980f00b00740030200107202c0c039501c944d82c0218524800060b51035200f400100c0c0340ea0103180b00780e4500b92617998a0400b2254 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2064675 1250 2063425 2063429
    0x10c110c0d020f040b0301050a02090102060c13030303020310050301090507030302070b070803060f06090901030b040210030203070813051603060204030b090102090303040605090102010f05010b0703080a0c0507030507050102040302090705070b010f 108
    0x110040341c00740000b6250050880345180c4004101090301c881c2c07440030030700b035950698119290300e4012880b25010740e018412b02ea032040360040040d04182c401261081500190302c8080c0a01d035000000c04c40c0d04104040c1c0401610018000b4056420303140b8005907103002c00c3c0300c258010b000764103000c200d0b01c4c070070012112504c0d00303d004141140c403900200000e5000544d50694443c108011801050300c0788010180214090801c0200c0b624090043c0910610780245520070140704000300310006410608441c0c000e40955480d0300394011501d4101d10f40840c4005154040e918100c0002c00c002e07440c0c0080c410f0740e00c40c0100c05082c0d240c40090500380c0c0624290564141c1090106011081c031440103441998014400400c85200103070600040b9039007a005007403152030002d441414190020071941e04101049020041c00050f01e000415034018000010104940000c0c1c560504c9000d4050720083c5400404c4c8030043d007000d04000e840b40d8008001150107002040000a1465201304100c0c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2065925 1250 2064675 2064679
    0xd080a030c030c0f050913060b03010f050409020105031501020c03030f0901020106120b04021e060307050405031b150d0e0d03060303021002030408070f06180605060102070503070b0a05070c08060702010c110c 91
    0x2c450494500588032500900100351f006808013450407141e80e5180100c0c8000c00d05943c0103641da5040100808442c1c0c0250080c900a40c10500b0400060341e1100841b80d0005408405800b90b501c0038004174108248280300561512010070308a10602140b00107291004003600204840c03960b4101890b0b01d001d60b118081c0c031400c1d2200008025041c2440d01100c140f20006010140c000c4940000c0c140380c205450002c00943c0101381401241401c01403442c080c292660103090820300b8a0000701c0301082d4010b0200003080105140515000c2904901030136460902502d841070b54002c00100101228802030f4014800c84543d81c44020003442103d0245400c140607503e0900941c40b0900620006141181c01c0355807542c0c005441d15a8001041c1c0981c0b02d0f003004102410484002403411070305400484c80394003c00c1c0200100800c1030201c0d5003e403524184640c49070901d0504c001500c1c0907912090450107410b00300141e60f5410f43c1f2000f044171181d121300b84100700720a035080d599a00d07081c040f5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2067175 1250 2065925 2065937
    0x1e040815010b190909090501050a0b0603040209010303030b030a02030304171204060503011203090305010e061005060408060105090601030e06070203090a23040e030f040f0503010b010206040206070605090106050d080a030c030c 99
    0x54540c190000002d1032000d0181082246203039a50170940403100008020744045e5035a1080c00000f40403401050741c1801c040b02d1b101d0860400c2c0e0005201d00c1d9043c400201495035900c81c014503a2010b1103452030080c2c000b8184c0c1e4507a40d03110640e004075400100f049101d4000d00f000300c000080f9040c00e0320140c0b040c5582d61400d684c01d002e4a054034000c43c0c1c505500703001c465100000058003d00500c4542c000301d5003d881d880c20072900180c03501906800c441c0c460031082c481844881c2000800c42d04449003251141140d84503000182c004120355440040c041c05940100140070750000b00802801100351400000103070380c0c001c0c4914008414201c0034191b25520200e2000c1c0c545508410425914081940d2502604500082c4aa0302c6548105003080b1086070070440ca00c4d0a102d0f51a2000003800900b22520709540010001e1045010041029a6a03070104101840035402a40a403401403d410a6202c460500d0809600300c80c01e0000000e06100815800521034090303c034290050362198 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2068425 1250 2067175 2067187
    0x405070603090203030d06081506030309130519020403050304140301090201140a1404090c020f010e060601081509010b030609070c030f03110906030a060e07030207030c020f061e040815010b 83
    0x101d0180c1680365041c2d81c1071009110424950f191440b806c00100031201c020188802c1c0c205958005510080005209410a010361980b075159403002400c0c203002084002401d41e1000b016001d00c1d00d014017080489440800c1c04010003000100420a40304c7d0100c1c45070310b00840b0010035090340e440440003400a50440780f038858150034a0045d1003254514240000214965400c01c4c001ea0020b6000401040e15600c1d0109455010f212096919000c1002400740201141d5900d94420010300715504011000d4001941c280e0510382d010004180240f0300d043c1740d41e60f100200d003035070400d4544d6481601d400b00800c69072409006a10b280c20346c5519000c15200c50142e0a0300100314111406c0ea007208100320b2282107036104d1004521501d03400c0c000088460070680145040e843c020000c800b814410403071070001c2a004030321a4070050f030481e0011015030040d800701c3c8403800742a05080400055843d0101da460114010780b080c2e600b140100c585c1c083d071610309101002000e00c40c00c0c441d14010404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2069675 1250 2068425 2068427
    0x30a03050705090d0b060a08010608030414030f07060201020d05061f0305060607020904150608061009020906040504090c03020909030a120903020115030302010510050904030e010f09050d0c050306010501050304050706 95
    0x1030354000280d040250404040501040c04010010401c546403c0c0c00810001e50b49040b41c41603000e00000002000418180881190b803445a40102d80da00c41c000005d50140799030400000f001080c511042d0b440d070b9a82c13450040c4c040d41014501480c20360604001070b80a0800900c004816001c0083c6083c14681070501900204000b034085900a24204800000750720780c1c0304000e000e0742c450b100707100e40c400c9051340c040708a607017507007146030706030851400d0045440482c2182026034148030001682c0d0121303040014158030075607010641050401c0014000e00c1100070707440c0100c134000d5542c2c42c03c1c0e648a080302c80e2203104928070a0f0101da11181881052800d55000c9242d031403190000050704441c0c42d0718141d0b100c0c07050344120b00613074544040085000c100341c10131004060660704494941459540076103e13a400ca10b1040c10082001e500c1c83e840f500c1259040002e00002d01101036640040c02d20729070310714490283c07a0003446650300018040d44a03004880c820794005018048403401c0c07000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2070925 1250 2069675 2069681
    0x1c050c0a03080a020c03070c0305060601020610060e1809010b03010c030605030a03051303020301050405030319150302010503070215010b070b011203170406020c01150501020c010206060306010b0d0207080406050705060c040305030a03 102
    0xd00c00b8a15400e100b00c01c038900701040180300c01f600503001c61208030300c3d518002d407034140010140da046400c10750900c2607910168000d0020760f0a1801e01c05030070140103011400d8005003010020059008106000c40d40b6810340c07100d00d241f4415002800070780e84003441a0305640251080d990181e10286880b001b1a120304064035840c1840e0101c1c003421550b980004e42500d0054070b00b505d058000009200540e00b83e001d040c010f00d6450182800780c8103250300c0100b180302e6103100103410f1210000011300d05901c20700446480e8032001c0c0c00000517503150555141103401590044030341107404e20003c69031420480076180301603416035620401103a428480b450204000d0801c880390394082c002d10302244000e0180315a04259161480c2c0201d2606000901d00749035030100c581950411400d000640d1008122941985c02c0f14036840d5650f0124904d00d0000d11036550090300041000c2400318095902c00020190035026800311003070394451b1070510203144114413005001e41e104004c04103410f40030360 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2072175 1250 2070925 2070931
    0xd1d01030b0d0b010303080711070302030a020103090602090904080903070b090901090b030a0501050c0306040609090b04020909120706050403020c010807020703030804020a0e0a0501170a020a05121207051c050c0a0308 95
    0x601110300d0b04038141d546004981083c2c000b200412148004c01c011194400c1e4400800c81103100140603031840c41c3c0120781c4480304030901904054980c2680f0b024464180c04499100201812840c102d1625042c841c506802c450729551180c01040000105035822a040e5400d0f02c800504c0500035920700341046c00200325500a10b90117025083c02080414028410b26100d0142c1c403014a07a45d251030010002182d015400c46041d540c5040401000f050384040e4150348103505840380c1a00e038035000881407034440743d4501c1c0c5010f9071000074080c040000581005004612039001c481c445001c40c40151024030701180d0642c0184d00284081000c04c4c424140300b80c00038000383c1540a0a5140c85500c0d40030501158600001e58543c0c0041245000840c05d41c84055290300c090b0458218036400103242c6c42031803003011f01c0343c400200401032141d030503c001e94030307903c810f030b940303030f940e20301450720340e0f140e20760401c101c550001d070a07c04100c1280103804031109c515201014141b05a8a998150ba0048e009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2073425 1250 2072175 2072179
    0x13151406061b060106050301030201020d0c0503070605040c05030a050a060501060201060b030a0f1104080a030f020c0f0405060406080f060f0106020a080f13030203070902120105060f0301030f050a12030e0d1d01030b 94
    0x10b00300b0700d00406041c88014060f0200d961065a40d40c114000a49040c80321400501003201c2408201d000c01c1d404402c0e01e6440750301140c0803e1030f40380d900b45203611200e150070603a858040c8185070800c000d00000d5145d070f001d01c00d10043c84141ea032100242d00700c1d15030b481400f8010b00100001110443c803540200085016400c0020344030016464254041d000b64000c09025440040440241500301c00700e0048240c1610040004403c100c01007400e5021401e440c40c021a01c41010842d19580c41c2c1014003c0e001d940129000b400c200803d45540c1c0740b040c1c07600003102c4e07a42c80001c10308620116234004050340154010b49840880c000c00040d5902c603a10013549508201004401658148884802802d281c8400358407075035a43c10031950020188d220610550082201c840880c07040c00a81341125000100e8032075a03003d07400c1c13032400d1541040000b01310000b00d007502000c5581540c44a411501c0c0b410417282d249070802016220900c048203241a498500508402c0c0e0790312a40028208c0c00c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2074675 1250 2073425 2073457
    0x903030518070614130311040f0c02070501050a02010908070602031905010503030315030f0a030503010f050901050d06050c0d110406030f02070b0411030f06010b2206140306010e0303031315140606 86
    0x441e4607800c5c1c0c40821504100c4000444041400580c5841e005400015042000c00c028130700d0128000b80d519130035840380d1818481d02107880310109000b1743c070040540750842c9405a403000c0b2460504000d41c0b08481d40446d00041100c4600c2500301881468141c0b080a0021407943e1515007011040e12a00303540710354944a2440020410001400514804c611a4503615202e5051680660b01001507410a6024460040040085035100d0407902000b03074110100188503100c42e034409070325200300d148810702641080c0b0340001c0407450300d0081048401d44d83c1d08000b80c030642d41302c0c007040e4480ca14014101d480c2d40780c0850b011400c0a0202801d894000302121421991209410705011090380007000581e17002c91102d40b1800c0b507203015048004c801060301611400c1c204060300d03042034000c041a012801000151890340101c81400849500504a80d1213150544052040c251a44411070790034011801c1d410503402c4900840c0e0450304406100c001d81e279a940300348401d90b000760450f078000c040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2075925 1250 2074675 2074687
    0x30908090607050c010e0102010902030c04020309010e070b040501080a05040206070b06011b08070c060c030c140c0a030501020d0b040204050609130f02070b09060906070503010909050708010f0903030518070614 92
    0x10301c81005008691203280a00b0b44500100000740100e4000503102d419641010802001680d011600345100c49040300c005850b0f882d02001940104000310210395075104ea0782c40868410100c1002c1c10072104242d039080072503911111040241d600607207001f50014000d0100400280449040b0350340510306250100407003101c003031950151b0240d080c050b10440e00001e2041c082c44942603441014102c07a043c6003c040040b81da00800b48161818080c101100c0c2d8600365001c20801e204041c81a2001031409030203e4032418980d000703610800e509a5000d150201050072070a05009440899800030001c504007a0440f0030300001458221135200720640e6401110340702c0d40e282c07000d40001805030303178054800d180c403035501450f141380a003149509070b00035000c2048656200007124190b601d40d800200d2001c126180c41840d003411138000c90740e03a509020f84562503400320340c42425014001d9a05000d540c5600b400070380d40030706840c142c03503440d007100e0020311085010f060a001d640018a114600e405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2077175 1250 2075925 2075929
    0x4021e040f060302040f050412050307030e0313060206060406140d03030f0f09020a060c020a050103180c23040603050601050108040812070504030209060f0a18090516060306081203010603090809 85
    0x704214910304505a54030403d2080d8100344c41428004441e2810811450a040d00c1d400b100c0045101440308010b80080003445040c03107a013001201520f0102225214212181c1040311461940596001841810002181807820380155800c90340210010bc0717052012106010550004da2419800d050329049903100c2820070384904248081c104030002801e040c83d10401080c0c60241e44100c08210103112003002580d50f03442284122a0242000175484000707904800222400000151840c0001c1d41d001a00f4801040c42a01524080900041c100040d000300400c035505404041c005500c00801170001c2d500903a00310350418040c4009030704000b0080c802c1f41702d03c00b04842d0345e4006140850100214201011b41c4c0f07400280c00c03216140c0c108440c0010071600c00052081400c0c03022681c0c054041300e40b15500269000d83c01c2810360309850a441ca04024115851240700d000034a03020002031203407008a1041c041e0b0511221f110b145901c0c1c104128050122800284d0303003201e0400101c03841d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2078425 1250 2077175 2077181
    0x201050c0c0306100509070503010b03010b160b0708070801050d030507060b0415060203090a050a0302090f0402040e01020d0501081501030506070e011205040303050619082505040c080405060108031204021e04 91
    0x200c904040d02d84616040801b0302280c0c000217000301050010920051080c0c640c1c503800c0e641500c2d60f2046071070726400c09010200900000d0240941407905040512205540c00050303203100b0041510b640e50180d984500740012115648009000030f002400b110000424a8020102034540208046035050a0800c644500112680554003503400000ca004e9541892600c100085c0001c80f80042c9081c91a008110505c4000305814261201c1d20700050855440d6803002e03d04603030342e20085440308001c9080d10024603080c00703559070601c120b954950305428503210143c142c2c1d920401a2209442d1110300751260907094000c281440320304d01c88070004510a10a00d4800e601a56011400d401d1a00174000078410030081310902c840381c1c501c14071032100b000442e05000ba14440c005003c201e020119101600e019402141d409420081d098940795400b0b52568001c6000328290b8100c0d0340e0310600d0650f03034454101d4408512505100240152528400300c10407084102111142e0260202c002021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2079675 1250 2078425 2078431
    0x90a03021c03030501060801060507030c02150309010e07080118030c0c03080a03020301050f01020109020102070b090f03010903030b0102120304020a030201050f120a020d06050a030b0402040207080d020a030504020414070c0201050c0c0306 104
    0x50301541c685071405040c0c2c103002c0d041c01407159050000c010b505241e00109184503000c005014082490354040854691800c0445510032510b280d548908111546a010345410005004075101e00c00313001c40e0808041c41508074245074840d5010420901d990142c03943c100d4003c0c2a2110400c00700004081685030004140c160155540165a98101000c01c4031400950302058110380c90408140c00607600000d0080590308100c2c14141c68284840000d084042140d07550764065003818001810907801da08107009141090702031302c600e0105240001c0141c002103901a44c4400c3c5040100091350142d801051203220095003030f813420920444e060802e110945080314450703800210400c010030705108a401508048400c0d503540da2450f200c84060400203840030f4400c0c0c3e40040c0f401c003009003501c101c80d1540e42140066450b44030131030018004100440c1c0c164050b50820f10481080d11101011612400f41d5880310b90000040c3c0d0011101a00440c03580682340c07141c0b5191111a0343c007008941c0c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2080925 1250 2079675 2079709
    0x1908011103040309060e0114030c0702120303060a0605031506030703020c01050f180102040305100e0304030209100603050c03040203030316030b0414100b030603031b010207021507020a0803030c090402090a0302 92
    0x9624142840c0c0213212029030ba2004003000110b0100b800d00d40ea2040c0c1c402d18001e15211b400ea180e45038496403102d1031252640080d807001c19501417580d45000130014512458003152100040b940d940000d541c14802207810a0b807148440c1f2840f2010324024001d940c1184662500500382810007001c0c608448090320a11011144041084404401305400741502c242c20002075040510710381d00e16076181e080300e0950075066121024810580701c1017064800842c0c0088c400190b504040d407161490500781c0c00340c980024141000219004c48034000c036800380b070b80680158a55070b11000034031030031500c12103094101621600c5240c081c2d681c9019082924030b8501c0f001d81e290600101c074401200c115400054104000d0003080f4065401000313907059101451014035034003c0b000c1d40c0da8024071803144001d500c100c0c006d100b0b580c41005d55014012580c426a60484580d440708070141c0d0305c1c0421522100380d40c504001992403402c050f000f52a6140c000707022104000d45983c0041c03d60b00c000c0660381 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2082175 1250 2080925 2080927
    0x2031b0303090f01020a05090405060609191502010603030c06050406090204020a0e0f10080c0a0504030b0a060617040203030f07080c030408010e06070305040308010621050106090f1a04030219080111 87
    0x40b1002c501809004030600c0200021031134006c2c0030401400b0b03801010f1019224964503000111141c8600b0216070312200010803070800015020181c103113120950162620307a240c201307168540f00b80140314000a4035010f4880220740d400c29079039080034040040c01141c3c06c5880b403150b030f0010b8031140050f00b41c03941c0315103075008200440c46c18130800a4aa181c010710505048010801980e08a410560002003e0190a984114092050303601c0d1041d84c2c801452480403000f004094140355200300300b074030000d5881140301c2505000d101e036030310b030180e074082e40c940c10420115080701c02240040210310322a58130203013000500c446072811a04140d10000c0c040e5100e41c940c070400c1d10f040c080e10b5800282d9050070429800c0586005120003c14010b031424040c0c1e107101c0d1441081d105204034000d000c01d003000d100c50340c1c407000c0060650042e84914424010b503c28003194151050070482040c1c01d0101d9a14240740c40c5400704a501c0481483c41c0360800305d000c0011420110038081c0c0401190b0b80314060f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2083425 1250 2082175 2082181
    0x11d01050702010b060f030402090c070803070207050a0611070603020d0603080c060105040b0306070f050702010903050109030c05070b0405010507020d02060405090c04030203070f060c02010e030c0d0b191e0c02031b0303 96
    0x10f820346100e0403202d440780100304000740000313903800e007641d0708242c040d9541b82c00765650110030340840c4105600500440c0001c410040c059070700242e00029101c2c00c0e50600343d41076495070250f501110011115056800070102800340510a0b40a014040060b4401007100c0d44ea9440b10501944168800c0080b40c01690043c03119003064081c4403c0010160007c0016291075600203010b1407401302039a04129000480c1d40a43e84180c0e0310a0103150050001c004042e82d620f0007801e6141c040c10700321098069110002101601402a90b0403680c041c4c550600e0008103508000782d5014030301c170890717000d0010f204c00b0440341c4520300364030701c58850810700580e10f50860040610300745099000182110800b04140001c03a4041d031129015582800c00c6c20b8101031540c00603003000010803680b42c120301c003520030f80180082c21600783d00900b0100c401000400c211107244056520b07009011507001065096102c8400b280e03070004034041403c1c0705890070060008008014200080c050141c154404018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2084675 1250 2083425 2083427
    0x15040305091e0909070e011401030f0c02010b0f0102010b030a020f0d0b070507050708010204050f130906020319050907030b0403050a140403080405010e03070e01120602040806131a04050a0b060102011d010507 91
    0x3002c0c0d0042e49132001401040e20303050400e003819030705000b8024480983d00d003220391640030781c10440a42280d001d00303000000403450000e0080c40c40038001e6200b003040e00c4c140e04230b5500622a1064124001d03002d002411110780a2040190b000c0c4a100d80100306220030001140b03503040241e02500142e90b03903a0799074030f05007800c0d0314100c0c5039007082546034810442044580c0e5440300103180038000f1340b80b1162588180203142c008002440c4080c0c8420300000801424900c0140b01c85500c4031491800c00541e00c1d816242c940e601e40500004003003900c3c3c000410003003809030001c1c110003c0c3c20704d80a13074880070101007000d00d81c1203544200c41500c0003040a2101750f1308012189a10201076000702007a901d000c8000d10201c1c0b0604c070b281103050049103004140714150b0110f401401c41e07003088038024100303400110440440402c0c1507030401e40d554052940700702d000340e0207130050b9040801000b4941080d11411580136010700014159036135465000c1052403904405c031408008000006514607000b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2085925 1250 2084675 2084689
    0x3030c0206010f0f060804050a020a0b0901030e0102030903041208040f0f0e090303061e0f06070b06040605010f020307020103020a03140405010510060903020607060207020301020f0d0207022115040305091e 90
    0x103001c8190282d40034002c072180f1601310811500c452511040710748a0707041403410b24942803c003175040b5040701d43c0440c00c5080311000303016143c800e80c2c0030000c403000070f0700715400c074007080da48200c168000308002c1221078003d40180c5510783c02200c4a81c030f403a50b105445d8101c661964000960081c5000c81041010b8001d602d241c2d001d20201301551440c44c2540c0010820320300d50341e44c0d44c600d40518021601c00e0b10f400410320000351000d024103035103a217581028502c8030f004541d501c0c4581d00b000c6000c80c0c6548983c1c407659039002d1f1a0015420301546600540182d006409007004240c0d841040c0c4000d0324180750f4050103140100000140f90074250380d00ba840c0700341608100b05004024030f0030001610b4550803640c1a582000f00161151220300c0020b0184c820052003481070701c004030304c1c5080092643d005101503442100c01100a1120811150641804c0116081c2540084044800b40c00c407544e034041c0d00c10701c2403500c140b81042c4030300000c00e040902107000f80210348401c411105d07400c00403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2087175 1250 2085925 2085929
    0x1b01050103050c0603070c15020409020a030515060405030d030b0d06050103030c03030b010906020d0804080909100602010b01020c060304060b01090305010c110105010509090d110f0106060e090708010e0112030c0203070303030c020601 102
    0xc0c2e10304d4070310f00c4c2450f800303801190703241c5005098200041c8000200304140d41654084d013032440056540b8014214000c2c017811050700d1103080b00740c441004000914140045604540010f005070190604009040d0020300508220582101d9081e0107000000d45510405010714801d07100d071002e4014900340207040340c20742201d49042c422221002e02c81240c001960700034100062a215800d66100c0c60142203d020300c500c42070b00300d0803407400e100781c10055208903000d03100d05500030401c5402545c01280d60b5031510806a40160f02000400c1c089015a042809550010705214010964a80d80c1172b0071221102c1030200024149290b2044c6000c080c011280105000c8800c1062400c000007460f454a03c0c0c5150003080c805012011400c03204140605c0c100300d6a048001c0114a90362803018200396250744807140320f94210800210001d0040710b4283c103a80c55500900401d0303003048210059804800300c2641840f00c2c250349040103030b8080150360042c620039503003c607401e07207040c001a140c180c0603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2088425 1250 2087175 2087179
    0xa05010302010212090301060e040305040509070302091e03010b030d081801060305150709030c09020a030b0103050907090c02010b090115110f0303040204110403080304050c0a05010201020a0203041203051b01050103050c 96
    0x10004002503a8005010920200e0758480155504407203000030b1b00400f485d0740112150700c100c00400c0b040c150031001500c200d8105031084d0040307640f410b10880403881018407403544076415142c441580287c00144001c192400b40000988450210000380381808110132140080c40780f0301000881a0220201105001040001d000039410743d80d41c69140c0311110300d91400d48901c1000144120300c02c4100400644e00700078071155007601ca01c1c0f000081e60054400310042030a20343c40b01c030705510030f104203803245041901502003e42071810303030300151808007013140441d92140d0200509642e1100314900a150381c56070354106220100010b4007041014400c498a600812a000e0290101000b12079001d54101e9000803106041c01c4a01158010340e04064401d2201100300003c0090011b000e40b17218404440e905201a41e0750012030a030300c11042a038005130002c1c8000c110780156540421902131003810820b0074500107a6161001030300314100180b036a91640d0040081c014207015500400c982 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2089675 1250 2088425 2088431
    0xc0f020a0209040803040f080408010903030b100503130302010609021b0f0102070b04061104090509030c0114010501120b030109021203030a05010b0702060f1b010501080a0209090105040b010501050a050f0304030504030b0a 97
    0x303900010306202c0010b0000c0c01c05000000000e04120526415031505584a40c00d0358803692214200d9000300180b410440200b1b00e400c4054a003441c0c02c818810f0a414151746d441c1c0b4541da00205502c041c441507a04505543d203c400104c2c443c000b600240010341411488181c170982c0402c9900d00d08030010314140c110380d1040041c4800308114003009944582c00880114070f400c0c8000e6103401c54401c81d0700500140e450b041c10301001c01030210041050003a154000e1020010003c1c02400c180b400381320340fa02240704400c1c20007900a16030080300804400600015410f030150f000b09500784e508021003080e40c1c100000708030304489240700c1c0781d0240c20310f15581c900300401c41d4003041c603d104244804155001c04240351100840317043c8020040074a140c000e000c5540c0d2011f195655410780e540491242450310005030600b82c05106040c0314580214510000c1d92a220040d00e5541c8410b22200402004011100b007a100c204000c5004a10980e140750342c482c51f5051441ea4090702909421030242 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2090925 1250 2089675 2089693
    0x105151620130e1905070306020307080a0b0f010e040f09050a03020a031d060406080a1e0c02010b010512010e06060403050303070207060806040b09010b030a0204030c0e0603120408070303080c0d0f0c0f02 89
    0x44107213403040700e0361310301401c1c0241d4100030f860100e0a90008103058000010000c1165001079040e01460310b0390000e120241540040011800c0301008083c0003034810f0303c0c4910a4030306604081208500305500050011003078403414144040c3d8032054000d6444200c10004141c1c2c4035034070818440300d010750302c102400c0d0340c00003da4900c210b10458042000c400082407651026900099500080000e040000781e800283d0314041c0c2120344403140554079141e01142c1c03070350050045a04a000210482a40c0da00740580c00b81c1c49071002c0c10954110505010205c00100f0400c000c500030003160700208800d80c44c0160050482d000280101d001d10300300005843c4907141c034100c485c10b4070040c032400c5441e5941d880003400240900d90014240701042e500008035110243d003202d0182a050b0295140c0e4003501c15010b005101c1e03841949a02d500c00001017002c81d101c0c4a940d6088042c90080900d000302420000c0e01741d510a00100c88010707641c1101070b04075500100b05141e584200d00141420755 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2092175 1250 2090925 2090951
    0x7060f0203070f11030a0c030209010b070c030b07020c0603040602040f060c02030d0e01021002040b030402030706030e1009030507060603030305060a0509070203090108040501060902030106080a14010515162013 92
    0x1002e254801400c0c07020246006040120109a13919074603405400c4400d01000340c20b100c0030340798251005070b004000d07120001c203000c104802240c3c000d68210790f588080307501c2e5030b442d815038071001010003046014000c4891a16a2038400560003180145000358480e07090008481e80554154012018008601040c5006840214001c0110040303400c0000c0c41104820050742020068100942c00da80700207400b1130502039090240d0300480c0240c048400058458900750b08070313001c8482d58001e0781d100c2180240551034540080c0c00480c031a1500504203a200d03550441991400d070000c4000c252900100006401c001c04800020402281d10380d5541c1041d81020352a48655855941000003010005040c04000d400403030007003002610841d500d41e0f5400f8000e10b03141c02555a0112103003010b060a186440d15051281030310700042c5082c0c0c440144a00c00c40b0954008001c0041000382940d91102150400002c010704052441c00d01e41c4100101041000008000514070185854445603030068 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2093425 1250 2092175 2092177
    0x70210030207020f060406020102070303060b03040309120609020405040b0a050f060f010309050a0c0b030f010609030308010b03060d05010e030a02010c08040b010e060303040e0a0c0905010c030806090c040806090c0307060f0203 99
    0x490242801a91500540007084a08a0b04034485400100c0041c001480303540c15401419068017a9404100c007584562203d001880140c80103400a0b003142c0050003e90010110400c102d40325500009500c8526804901500ea084506851062000c3e0030054940850301503107a014421030300c0c610140c80d0440024081118044e0980c0c100740c1d56091020820808101c00000380750403c0e00c0c4440295034440c504c01c6548219890302c0d1141d000d40001902500a5000109482e4141c0351140340340c3c07d000006030103420041195034171420a400762004180b0a00c1003013074018200020f10799480006001a00707450400c0080010402c0030010440421031030107949040d01c0200c4041182034480c0e4001a1940c050340e0024041e0010303901c00d00c170701044240d01c4042a6a095214040c0c1d882da103034015030b40500c1c0080c0c0580802d48001c0003030352a2400000c0207a00926035101281400d44035a581031030f1003c02c841c0c00c1a2540942c03040c01081c03904100040080620b460101a1100100e00094072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2094675 1250 2093425 2093449
    0x8010605030708041205070b10090e07060804110d1202060108010507140313030309080a0e0f01030509030d0504060f0e0c120606030d050304030306030b1e0117070b070f080a05070506010b0702 84
    0x100b170562400117882440382d002c90328840c2d000303417004400341009400f446048080d84950400700349000030703c48180201082d810b0403a00d00e600c40c45000e0340c842e1200180c0d107005050859100e0031303005284000542c0d0b12039601c26004980d00070b000f29810041c2d6542107400285c01c0005100d0080c42a012940030841102c0e40558200100015070032245401e502401031041c00404118010401501c8154040440310400300c0440740000c01007000320055046800030380707004a43d60420400129068078540201d9007180c49040d000841d0080c2030b0712202241c144000c44811a00a40f0b1284424500b40e0740c80015215140e0213032005003041d0700000d56401048421405111000c000602494001d501260041d9000101c00348280b404140d81c055000d4280c0c0e00005d000d091800110f9500410b0382480f20b0880d9190080c0203882c10500384402c907400c00c00b001c0f185140440840400a51200c01402036500c00d130316000e481c0d80c810b1811a003046030507017103003002240c10b000c51000f503910041c004034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2095925 1250 2094675 2094683
    0x203090d06021e07080304050c0906060703030b01090b0307090504050a0c0c030c0303090204060f0501030c02010504110d0f08040603050402130c050405090a0212070806030f0729120103030504060801060503070804 93
    0x3942d00c040c010420304010780d0102c0d80210322008240078085c401800000d5100e18421000d54103502c610100b004500c3c801628625044401448494002406940b100e0307024541410001e0b012656598840083e5000704d81c8000003070356040c0700700664103003406100c2e00b1038500340080c061251102c030010142c640900c80501000f6603071100100f0302d40690721030003045401030001c1c4555500c5001081402240b48559400a442c10480d05003035481845400c1c001c5622041f0500300420b103030200014011014401c0e5210301c4003480310800141c084c4000e000900c43c0341c5020078a407a0a00400100d1110700e1902c0c400c42d03050109807040c2c80e90001c00c940070340d001119004640d45800701250000d009a155040661550600740500c803904000401d101d403504904840c01004144c50454680c0200d1181203031000701e402941c41039a150250402c0081c111400e040c0c02d0084a60310960075020030391064002c01c1000505011040c0e10051640c007500300d0703040161542c00d183c400140b41d110010000740c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2097175 1250 2095925 2095927
    0x10e0306150d050111030412030504050a03080601050c06010806040308070f080106080a020c0a03031505040b010e0f0319110901090203010b0a2109060e0105060904120c060b09040303021201060203090d0602 90
    0xc80d80c0d07060282e000090b00031000b007000c1e03d02e60500161503442a50107403200d003c00d004c00007410b0712a000d21070ac11503010001d4000c4088a6400351081c43d800b4000e03a041c444c0921540b190910100041030007415840000c001e507040c1800c3c081e01d4807401a0441d01041200100000381075048440c1904603100c80c507050301315035103284800d0002c1c0502e548082e16406955005000e140c0c2c5500542c02d61212503204a40c6181e843c410482114540920309001c50903104032805107203004500d01070018805070a4400108205107560341d6200402c0044031040c482d4118240f031420003102050141043c58011455541000c0a0940754090194400d08001d40c03222040182e41d2941d50b40050003180c43c0040c01500c100d0b240c403002800c00854608019842d11002511500c1e10a52040c041c03508003a032549036078001d0004032041007207402d054902c1d6031201c803411003d444514580b4400c600a90340141c070307450b460021440807007041e4032030400c540c0240604a107556818240c02c80b0654400001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2098425 1250 2097175 2097211
    0x3060b04140f07020a060e0607081005010c02040f09050601080a1208010e0c090a030804090c030e0c010c020d0804050303070807020f0301090507060309110a030503070209010905010b030a0207050c10030b010e010e0306 95
    0x12407800c3c1840f91700a01050030f00e902c2c09030744c91001600c2c500880144e11900307000c1da43c0000e0006407640503c113060010750190359074070150800303a0203080a501004004280c072000c640710145022001c2c0c1c0050741650042402c1814020310401400c0321581d1403500c601c0652411006c80c06034400500035900843c00000c011800d40e981c0b041d164019680181115229075543c6c09000c014001e4204440100c0d041010710121040040341c407081c1d210f0141c642e50100d42d482e8091081848614000b1a4000401c1002140540e01000601030306403252030703610707914016841400303010780c0303514486400f9a0400c03d0450000c0c50100d981c0068034091710700000d240d846810016071082d0726001c1d403038001c00c844101006018011005110590007030b5511081741c0d985091180484009100c1da215000c818401f00c0c0d02814150000c040c50b5010340122181083c08100140d00002072107400070100c2d55400780c20301a941c00005102610300d003403c21112003003030b01022036100d040c000d040c85009040d200790 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2099675 1250 2098425 2098427
    0x3020f09090702060916030b07050901050706050a0903090509070905060c070e01030503030610091202040b0d0602120a0c03020a02030708030a0e060901020703080105060306010203070b060f120703060b04140f07 92
    0x25500054001494040107040401001e034132000305039103440103030050b010070035001100001d444084952094440407142d403500000c45c0c15400ca41850390410004000950100d40c1600555024205000c0d00090380301041c07501070079035170081d804a800b032002c5404108900340c02c6007843d0226903050750312913035074484a03500c2030804803503401c62559000700304004801d002c400005075110324402d0b207910940c11a400d406803447c1c0c00f82e04c10f4071581d5140c40c2c00c034030050829400c0002c18040c0030b08800d42c29036456075104c00b40c0c3c0211603140c094841d0082002005645800351903003c0f1810300f4210702d07010346041c009440744a2081d02a201827800008a503440070719520180c200c1280c441610064184505558040e500440c401d80c0080c2108001066618141041304d0203aa0141c00440c0f414002c0e584209040ba001000036922040c2c2c402041900d85a0226212800d0483c02c06010440c2c1103103450001c5076465076000d40614a4a24506003054070ba00c8a107400c0100981402a15902c0c420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 2100925 1250 2099675 2099677
    0x3040f06060807030c05090a0905061303020304030b0f060a0b0901090302040504050f030705061501020d0c141204060203040501030e0105040317040809040906050a05130b0106030e030c0d0503061302030603060703020f 95
    0xc04107500b03103e892800001e02c4a1100280141c910450301201581c41c0c040d80001a030b005030501501a0300f021000c211b4503481010348994542c8240156820240e4a488036402c403182164229281040703c01000840e02c1d04260180c0030300590700400d03040041c894002040b000b01804001c3c0195582e402040c20b002c0c1c10031030040c41c0400042200e130b6501061070011348615007a00e0201801e045000984520340c0082100d50480c0c00d259960b268021007915441014404015000c52038090680711801c55901400108054051900110350751440c1000060440700b101a041c031050b490b100078000040d60003000c0551142c2e824421001070b484508002c01e40f407054a2403107920038940f248001c100080f83d04150704c58803e0f080100a03940e41c51610030500b8041c00c8000300802d4903200184000390107070303101c441400c056800f01c030300f0039605400c21880c0946145c08840851404010050185061803000d1007024060406604506004000c04e40c2d640000d441e180c240758021a40350f01d00c00480b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 2102175 1250 2100925 2100929
    0x303050301120303090501020c030a09080706121e1a01020f010209030a0303020913050406090b060105030f04031b02090906010801050c04030510110f070f03080105010203070203030405040c0905030609010c03051006020303040f0606 101
    0x6c02190703180d0b04030402c2580d0380d0100c0c054001090b00c1c1000081e40c1e000c0400d400c02181c0080d210341c080c1000c01c6065400504800c0c0d807a802c02e491070600c0400d01d0440d80f2800c050340080c003000c0a5441d05a0001a2408900e59415032450303004024000e103d0b200842c400c02c00360b502d400c01503200c12551000889040300000040160f9150104200c103000d5203411101c00e00e80100100d450300c6e120440110341c0d40c130084074040e5800340c00a0108001034030440e0304c031109242c008c0019a204925074006086030303100780c601c9100c1e036203d4001030055007428820a608006401011844e03c0c3c916030315207440b0785000441c840202d64031712904150b0150302c0116031f08000382da040d07190784040904c0d0244142c0c040320340540004d14210000300d507a50002045a02c03540c4c00074011800d00d407030001000054121460004100f0046100016080e01e080200b54091140768001244181c02c074a002812100018108140c0c9203400074100305107500030007140d4100390490320103490883c1741d04000018005035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 2103425 1250 2102175 2102183
    0x6030f0f0a0f0c15020703031e05031f0512030306030601050a06020a080d060902041d070f050403080306040b04020304030903060c0c03120209030f07060302040801060b04050603010e07030e150603060a06030305030112030309 98
    0x440c4d02c1071a12540428180140c900c207480718440b030b20442408102d010302c000501030106030100301291002420440105296808843d80003469480d1404200084180c00c0e000105600101c00d02a25280500145025107c15220032085503c1d0050081d07a60580580c017a004000004000d1010309943e04188054045004113640d81d40d52425100512907000255000301003686002c52005407088148040000484e078a8600342410750702c580d20743d5030019010652003070790b551130041103844d140091442070303000c2c2d01c1c0e10001c03c0c81c50400e0015201d01035461410040781c810310301d00280c4c100d001c0c000384400d108001601c9031281c202192400585803440c41d041d00c41da14001805d85da142c5c000740103440e1a00300900416584400c0b0182c00d011764000e007a84200103200600801002d444481d502222528011034141c1031500d1090074640016030400003003220b5401c000050408100e81a0801700070740e4204040da107152070082c8140010300410a01ea25002008414184241c010600350780e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 2104675 1250 2103425 2103449
    0x307020a030807050d03050c0a031104081504050d0305090307030c14060a0606021002040302060405090403050d02030a0501030c06020604110405070e0a09020307020105060a030c030f020402071202010506030f0f0a0f0c 95
    0x72800c01d040c00303801803e4204d03031a1089500309030507070f4800e000b0740d801007130700000040c01d00c0600130058019047c4131070180c1c40d6540038080003582e01010050942ca480c610704007043c0b00c0c00c01d4280030b03003001d803881d0100c1c00780341c00d01c070038030600031070000442d0015505450080701101c02071519800e030b625940d80403102c1d4480c850074000742480f10361040301191550740031071b915100c201c1c0014059004c0c6220107544400140010403107400c12504255000340f01c2c1c0350951900c004c0c00d421108076001034841c03001443c0d5a200600820900000e064080d003901e000a184501c2d06036a401c0304c09000f20500c5006548950200d601140969a02d24400340300404443d2490b0b210482e884c000c0d0400c59003c0015803c6c900401c0160401c0710b4540e06498101410111550958a0f0400d08144050003260081e07401c00c954804202c1c0c00e84101040401e0341d0000c985828074004261801c803078029891001c1c1c2117804520404040084c603c6039035030b48420502500030560500c8401e0010340e510250364110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 2105925 1250 2104675 2104679
    0x307030305070305090a030207030215040e0106090306060e0f0a0c050412030203071109060102030d0209010509060f070201080a0b030a11040b04140115090308090405090a02040f02040303030f1a01050307020307020a 94
    0x240540006202c1d0009903400c1080303689003200c0c41d1380d682114201801503040200c00340094149901401403402c540e00340c4c81e290035960188040076180c2640484006070421a06100300403150080c10000d10080050f4255403c124043c0884210040c060801d4142d5403c1c569684500480c00d880c01030035400140302c10380c1142c0c10065120352000c0c5c4212080071030300ea002d11a925045480718007030101039000f141030900300d074681002903000140417410301506002c072050030344d2900024529074580703840d15500c42c5040c1c400903207803210180c88130359001e092405585158500090801da01c50b000010300d0b5504405502081c02000568201c64101d81482c4104014442d0705451b14122880c1140040b41150302c05001c5544070406d001c010309503181000501034602d01600300f9504031045806031a40020f5a0380020304440700f0010301d14031250085010070034960035108400040341075480034090b800c0d003048100105410107003014180407011003c06c1c040d40c400c1040c0d40c0300560241034049104c4d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 2107175 1250 2105925 2105927
    0x15020a080409020c060c04030807020907020a050601030c0305060601030507050a0507020a0e01030c06021b01020a0b06011b060b0310060806070302030709030b04030201020409050604020a09050105090103090c15090f0f050d0c0305030703 103
    0x58000d0740b84c1c0742e181c859480402c1e0310112010032202101c1d0031064441c01c040c030581c2000040c10001d8000c20450ac182e43e15031010910a201e002d0003184289036a400301c1d0f02d140381043c24170000400d858145403400040050b502d0f040710440c0c3c81003410745042039a03250740c0d2000420405654000904a1558030008400c0104041c1c0030001d031030554084441290130700c01d9154105c407240c41c115005030002000c4500045001d0a8207407c1041410070365032401003800f10400003081e008040e12085c0c1c0310403d40b400c6040c180440c3c1450b00e91403c01f400f01c1340c00d1240321640d45001030030309010181d000000a00b51403084000201860b84403207082d940b4201401c0c024082c1d00300e80980e4401c2850440850217500d8a8401c45584c52504c2d01e454079014600001501c103608520301e07440c145174440e001040002c0484903c20042c105071802c1c079461041c0440c00030f00104558001c60142c0aa030441400380004401d2200216071003143c444101c0c2c0190301c1c041c000140264801809480041000002c01d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 2108425 1250 2107175 2107177
    0x204050a020c06040503040e0603070308040b09040e030304061b090b0711010302070206070c03020a06030b0d020d03020309060d140604020408030414010201110a02011d060127021605060a1103010f15020a08040902 93
    0x2a501036101d81815149c0c030302056101c40c40c0b444010080a400c0004124080400005d003800c0e800080000814001c03810409040d64000c43d803c680c52076a40343d202030b07400c034100c1c100f801522440c54140d440509082c4d07401818426070388081e1003c41d0110300e01d0b00c0381c0c0c8203030110340c000f41e8058030341c684420052520700004032035030100724403c0380381c8840801c401e8481d1081e072081a03c02408104002995000d00c0003a11407048103408500040114020607100e0308000c000747c980350a40000d21413407414507822681405041c1c584200c0c01004200460a03002003650103903906420104109110744006074010001e01688507890300d0041034190350641c06600001b9001c04e07400c10b411200304010000c588400b82400386c58803040900070500390103080e481106550140c001c41c014581601091004400101000100d03045c3d400b1030100500343c201c5000300c54107802b440c4403050441d410700c0c800c1c0d0840d01c010f0041c4104030001c1010f08415a1082083d5400c103038000685c03aa48680f01c0c0e00132000703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 2109675 1250 2108425 2108429
    0x90203030a050d0c030b0105070803090a060618060e09061f0909030504080f0a0c06031104050301020f04030212010903020d08060117010b090a0501110303010b070c0f0602030307030506011701030204050a020c0604050304 96
    0x4a1072070403541d1140540280201146c446050390340c41c1c03519600d070340c1e54501034002808030861882003800310760000d012841400c01400300442500860b206007044802961030541001c100b440001c400d010822200203910703504401140e524030615040c0362460719116100383c0c000c510340da080418000a240d0007600030401e4a150005684040302461245a034880901d0ba0007001c030250420b042010501c00da101a0388196203001c59440e05995000003826070b001200500060b010020f020011403900d017000c9140910f54200920400314240c40182d181c440e440c000790706004c0401d00003091607101d82405030300c440b83d5481c885400d5031149400c0c402038010003c2980210000980480c40358001d284240d0145898001549140e003003000c540040d801c0300404445100c4005408a20b01e05150b955001038055980299100c1c500014000c054550281c20320f4140040341c00542142d58090202e1030550741c0540c2d02180c20b0302c4c0c500340e00b40244115400b240c210f018036030900082200200051003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 2110925 1250 2109675 2109697
    0xb0109050609060108010303050d0f0603050115050a03080a0503150d03020601030215040807140414040308040b010b04060c030e0102030c0109050a02120d02030301090b030705040f0b090106081501030b04090203030a05 95
    0x950340d1881c040c011082815070351580858800401040002d00c204000c0c6140c40b6291004185404101e0948058404581040382e450751180c00600c034564503601600000d00c0300b1144030110620b03607140e05000c0c1c800c1491034000c00170f001000801c04c041e41d130102a1030138800340c5482c0041e08581002501c4032800e000072480b50b100c0d070795145d12058405042c0e80a403900500075042d4246001da807413201a1f00e0b03003a01034109031203107411805e80c0300041e11030748924080c0d11030460610b490324250000c010140c1010400040500c801c0c031500da80400d02c03260644d81030901614440c0d01304010307403a50041e8032194809608164807041009004650b40d86081e10076a02c4014485e811821103441d03228485080005074418401000030034100e812031120b40b40090142c41c0b01d29111000b180644400d0020454040d442c1e04821019050552855005110030724254459007460017001f058422040c1c40c40d07042548903040760076540d8842c1d002d9440c9581c028112130b5512041e0b0b5014003940c004203c164 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 2112175 1250 2110925 2110931
    0x8160c0b0c010b040506060a0e0d1202031201050307030804060c0609020a0801060302041103010812161209060e030109020105030a09050c04020a0c0201021005010312080a150605040f0b07020f0405060315040b0109 93
    0x21404c2c106070041c0c6000340d030002c0c4418200b0124450072181030200400302a4800394907451003000c02d0004400c8408840254051643c071046811807242081c0117078040d6000342c4c014041000481c0249068400f0794505250810311f600280c20f042c2d000c0c040740c40c0041c1d4401c40b10000012585815071291044a109a43c00d2007164180c005104a50209101e100040c0d001052404a0b044294005040359211000264140006520382e4205032103401c1001d0302088200c541488565040804014a004203c009012501e0755900003002400302401450f40303240c82d041001d0070400107015400a054001e0000c5440311361034800180080e00030b001c16030150195414009210b0028000d25040e80d030020840c0c15100e410003000c9030501e0000303080c411060341e522003130304080c10240401d400401117035907009c1d155410240c3c4842580c030564456045e0810030069480180c6450b840c02e5540078044a00148680d10540441d0030b080c00590320b6000d8100004c100402c0005c2139a201c0c0c1600d070300072020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 2113425 1250 2112175 2112191
    0x105040f02090307030204090302150103050c0a09020a0e06090a09021602011103040806040807020d0b040b040201030e0706080c0703020a1a0f070305010e040b06030c19031e0305040308160c0b0c01 86
    0x160040303214402c40759030941c02048052002d41000d4002200151091040b21582100102d244035010303020381080f102c03504000d04001c0070303242c40100e50000c0c00e8507000c21407400020f003201409512301254807d0044102240c01000b90391400c0d0003070010030301780c44150750300c0702c0e00c0e103a03c42001450071049012a50440d100403a41400106076000d968401d03000788001c1e112511850140e8000030b1b030483e03229144c1400c0400141c0c600914502451180c0b42d0302d4500d040501c00582510489180c9010070f0b440140100700309980461060f400c105400d19040d6641d4090600b02d007408010040a0700111006010441080100744c9483c4244122814100d00e034850b2182102074030420311440c8842d00c0c40401080c041940c401c070050b00705030011b085410742034402010450703000d0803680540b1310b0103920604105200d051041c0b03485455450700011203030f02c85a40c02401174029400080e01ca080c0c00302d00180c007a5100c801d034101c000c0e00f14884062840d552101c07801d99501946808103954208811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 2114675 1250 2113425 2113451
    0x2010e0106170d032408010b011403060a0b0706060306020a02030a0e090103080307050310090e0c01030b090106020a08070804050409060b030f0a0209060f01020304030f0b0105010815030a0816050114010504 90
    0x55000b4001e0740c800f4110301080e00008038081c0c034481c81c4c44045003140050800700e02c0b59002000c0300030002580040ba0b9809a00005050311008402c107082c2460100100009a40c80460b07800507143c04403201c070341f607414178142080245030b0368000400355407000030601d42c09900000501004055580c03241b000f50301e03090a001d6541000c0c48020040b0205201195006005038095035000c0349210342c0c110ba090303a40c1510801d81c2c0c80403124464a40051520104550740340c004c0074119081540c3c40e5555500d4032400a6070390300c664101401950000c20f82004001c0d140b0101d800405005006204941c038905156004000715800e0a129104915000c0710001002c5206410306800800a00403503461030281b20b88200c0c1ca5a90314111b010402010ac001a5960b04440c1f0950150340400403d40c18500058040b2030060314020b20100a5101c90600b03540c00201080c0c017546c040045a114440804c882c4480c0d42c1003a0018a1b5500304080810082c0c4201c10b07040c101c400841d0240910005c12031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 2115925 1250 2114675 2114699
    0x30112020909030717070503090310020a03060b03040507030303090c1d100602060603060604020a0201020f0d0e06060105030c16020103090503031801050703020702010207051002030f030103060912050307050a03090302030d0c02010e0106 103
    0x28000303060a201c0d011101d5045c4096000e821014080c170145c030300d03100e008000030303040c04101d5006003829a030115680f415246e0610130310700a46809038280e031440c10952200c603079a410600c0b00400f010384840c0c03c8020805448107180050203040043c2c200480c0b292140202c3c508121406010400300a0000841d03a02c0003034850b0141201501400e00ca40b034281c1404082c0d407200f9440300c00d40d03400b000b00e41d10502e81140180007048104030009074013030082c50b409084c00320150480c0e0401c00240309110705c9111240c1261020305640c20201103011680c40123a0181c00e12040162150102000f00030707071030072070200c014074202c0814001c03c603a5803002806e408a000f6820040e00592100300d0601060816126600700b10b8902d004807800d00311a206019107aa01c26082140e89a44844646040002080c14000d5981190074100e045283c030400c001e065024000000c4105501c1302d4081080c18020310407a083c1080c091402c0c025017070020b0000c2e01901c3c3c100d1402e9807540c0381c410001a40d01c1100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 2117175 1250 2115925 2115937
    0x71101021b1008060a0b0c010501150302030402010503010e0901110f0a02010501080d0509060c010605030609030a03050601020105010b0304020907030605060307020703030212030c0a082e06021b03030901110c0603011202090903 99
    0x1c0070b020480e0300c11081142c0480d0014040741c0c2141c50745801007040e0700a0406032410841900010620350705140c003180307030b8140c400c01c43c03000d0600600510006030707000b00c140e0f4103444011104945503a030b1170324042d024010016908007101d000060b0031031140881c00041c0301c0021580c000b1f001c2070741e8030390785030340d803100c00c21145000181c1c2070100084a03d007100081845070315160011401c5522103001030309000003900c03882e11551001480308907081c0c1500409501c10000d000070009585407014071801403000810082c480c032505c4001401d200d0082e0720001c05448060320142d120303e003420019659151034081a0090700c9458600328505000c002240d1050260500712402c1c0490814190fa086201420040020340b514803800036401701103020259041003000d030300080310728041002e428172a80d6a0f26002c214458241440552400000c8414000f001c0c078010400f0466100032508001c40b020701194800b10000c00019504048007507511100e0003100d041c4640e0b22422a00f69413403280c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 2118425 1250 2117175 2117179
    0x2070b0a030605030609060108070f0f0b0702031501030b01050a050303030103080f03091905030d06080604120f020703020405010b030405010e0607020604060b0d06020a080703050105040b0a090f020c03071101021b 93
    0x10100601515612401500d4045014100468010340f10b40010741030020442d0a100703280d100c8001004688400c011600c0201014026052400e040286440c1121030b2405640b081400016091046440130816020031320148000b41c00c10b56101e19080c0506002886100e1095499030404211442c002c400c6904895021420524020840f048400b980e00010b100301d40078001d80000081c0303070300c00190f40800284900055035661170320780c101c542280c00c550000c050a178001000c00c000600301c49880c040d458002d060000c4400071248049190810b141c100941240c100341c000200c0590150207140107030b114000a00015091301400c0359a1402110a000182e12002c0450082140d07070780205000440500080d00617030b07a680f00c03602664050501c200c00642c8917820820f2056041c8115400341004980134000c004022001a10b0605e250140180701c5603035041d0508109c066504464010b50a0810759413100814285094000300d202e9419025000c0d0040d43c40c40340a500c90000501840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 2119675 1250 2118425 2118433
    0xa06060b090904020904060207020303030108060f0a0903020a0f110a0602160501031103010e0a06050907050d0e030f0d1d0712030e06030f040b04020414090f070b0309070e070311030705070303150602 87
    0x43d03400700620504003810903a0100d50811a090151f2000c0c00194003034481d4100610882c00d00810712041c1001c014808801c5620306062100000e80c003145010140350003d0010000342124100304840e64042c40480d036000c2041c0c0c900044084e00416480407101c0c5104001e0314055503134006400340c13041c4040c0c100d1400800c200502203091912411038005640410003d0072503103034008903240c11410b03510030003c60701c0811a141c00c42c1107801900300701032108002d1400c121729050000064040d110402c0c84482d1501090303811031004402d0040b040d111f24044482e000d03070380e00070380c5450360b80e0b4501035000594072501e0350143e04112040b070303008407091407051031240d80716160303035442020140049130b020b9118981c05070780520480c07050b40100f810303002501083c450000e02902d42882d0b0b0b4800e083c10101801009a0341c580425018200c0d802c01142000340d5944a004500800841040b4141c034180441480080c80c0e00038040c080b1180300340c80801402008003409444004544220b0f801640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 2120925 1250 2119675 2119681
    0x20a050304080d020408060103080414040903081314070905100e01060c140a0c03060c020f010506060403030e030703060203040302100c020c0306010312030f020414010e01080103030e011404170a06060b0909 90
    0x2080c030081400f851407503001401c090700c9000e046e041071004c0c0d00c00d54204c0008038040c0512683c000d003070600e00708100c80401c0b01da040e40c0d4001e8580d55008102044540c50401d40005000364a4809100342030507800380ea1005841e15900340051401351140c100a0320315101c0070a00d11241a10755061302d10a0f101c800d41c00c501951040403074003100c0041d0300103014501030000001c0600d40c01c400039520810b0041403102070410700a1601c410055208042da0422007489480d071169400c65081d41e4041c60948484c911031000709241c44180d51006001500c00020881850f0380801c5800304481105000d1110b5407102c0012070755540c40744180c941c15000840104001170440400301041d240c00e0a011401410a800150491300103500c01e2003107589220980c4e0441da40100104820102404c044032194196140140484248071045042c40000c43c29001220054003c3d24000c0c488000307a50945107529035440e440702081030702282c0450520902180200e02041521a00030b406040c800d11a0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 2122175 1250 2120925 2120933
    0xe090a0204090606080a0c03050c0409020a05060c0111070602040806060a0303020607030506011b0803040b06060310140d0c0909050f070602030d020711090906011403010203070c06020327070303030f020a050304 92
    0x100c0128400c4541640e1a100000d00501c00d10452038428040c6041f02041071841c1442c90603e11616180c2e13208920341201c403401640c0d10119041500c400743c90032038407100f600042d10f00421609122200305980411002e0801865400401c1a9086001034448580b9404248030800f1224040100560000000071300e01d1482503001d1035104005245c03005904181540070035954544110035a400b01c000800c000901c002c1042894000c20190343c024918034150883c6804044223005010725907428810710001a501c41e10305180701074101d002e80c2070072a640c00c2c144000f07100c0e100703048a00e805210803005811102003142400c03551260041c500c0d00780703003070702800c000d502c4204100e46206441c201c4074010f480310300310326210b0120440206155410440103d90011501e40114420380c010030401014076844801124500d81c4075001584a031121040e1644d8803a881c0c0004026001403114200c5411000035000100c0f80240c40070800c040601041005030710a4a0f01c0c200803480400100e0005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 2123425 1250 2122175 2122181
    0xc210402091306110406020d090e0108030702010c0512030a0204031202010905030a180801020a08180703050307030c080c060901050106030c05040807170a0b09010204050a05040507090e060307080303090d090e090a0204 95
    0x8a8450500040c04031340c080c40341c040b160426040000140d2159200c0e240d0a41c100b0f078984043c202250007801103624003031940360b50780300f8090028100800380c00c0c8c91040240802003c044c00c1e8071040603980320f20340300311801c4c000c0d04148029219070680804001c0e119006104440150780c0003c0a1860898a1a400e80b134a0950702800d8082044512000414a60a1020b4501808190381c0c02c10b00d400d2900c1d0500c00c4003903000c1803452507042440c003040050400000c594030140e060038118042c04880c02c1420590040380760a407201e028400230451059010b5002d541a01c1268404002c4002e180c082120580250f0040440c1c96010308414428000c5810410249000d01000c82d090741c81c0715a15445148019a00c85c01d043c0e4020805100354585801e28501074182540c0421083c54420001080c00c0304601c6032410500080000c103c19860601292019000d4023003240d55a04040318002e5440c8130b055074007030002d60030010100b00c62810015041c00740304482e004200d02d030682d0f0208001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 2124675 1250 2123425 2123461
    0x30b04022706040e0f0609091204090b01050403060e010c080112020a05060c030702030d03090c05062703010209030102040806010f0b0406080106080a14040302030304030201050c0309070317070b0c21040209 90
    0x12002d0700303000000348100380946503403140d1820b924510782814030313038140145903202601c1181250007044807007403d00402e000790340490320380050208400e21040d0040c0d6540c816900042d088606003040788600c4075054016120b841829921690f10307030703038a1400c91200ba400000080d448003007460100160b01d0315602070080701d1880c40031340e441c5c00004c0c0d00080c40c11200c0e010314804a5180c00b82201444900301c02a0010001030707550920701441c001554a8280d910000103c00b0094440a0989620258107407503001c02c014000719903680d140d40543e940c460b001d1081e44200e1b040b02401040d19404039091341d045a4550300c0d500f204d6400c248c0e050f01c1c00a80141202140d55480400403151080101000c0c00f45000e600a15503030306140c10020f09407800141a40d92540c02042400701100300002c0c80400c0f2500840160210200d0540e000303034521400b0b00141889603000144403d180b806030080801e1603104469040ca0a4440b81c0e10283c00e004640c065484040c1800048800b200c1c0341c0c2d6080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 2125925 1250 2124675 2124679
    0xc03180303040f080d0305060306040b070305040f02030105010902040e09010b060403080304031403010303030b09090a11060714070b04051309030512060607020d030e040e0604050c100504080601090c030b040227 92
    0x200b05511419189400c14260b4805210750b446081c1c0d4a81d0140c0501c02c50f40c201d24250003138041303403a040d140d0321100740002e80707928105a40d0b44009018807a13260303022120198014002c0c031041d60b40710344c008041d4004e030091400000044003c9501c02d401442420400003001d41160f0905107180c483d003c16802c010810b80501c410285500b41d00401c840046010350310130384000030604180c40c1032111706a4004d1101189500811000020038442e2101100f84e880c00c0f529507607299040c1c501440344500404090610f44601c00011030b020030240090000d8034000d903080d5180296000c000000d8580c045405404142d04010440807148201940c0741d2203240a0409403400e1169070204032510005e00058000601c0081041180d260038012107200700c03421300081c105401c01b07403541070300d4000c480d6006105a0000c40600c171400c0c0a0780c00e440043c40301038151500d80d0783d901041400742400e540201d00180c980250b803005417505d4420f403441c1c008440d0f030552180048145904074581e940500302d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 2127175 1250 2125925 2125927
    0x5030135030403051c03020309070b1606090506040201020d020303010b09040504020402091f030b0a03030203030c070309051810060305010b0a03090606050607030c020a0b07050607030207020103060e070c0b010501050c03180303 99
    0x10003940c0c104001e01c002c6100704010003100190b000c0c0128903c501107040402c16004001b4403601103000944041907602c02000140d4412541002c280c0c0c0003104000100a070b41000f0003c000d00c031001c68941c0c0310b103000382c00351280901030500481e181d11090013881c03519002031180c0c961900b4a0703806264020f02c042c10061401950000241c0100d01044180000d0403007105a122282e03071500919811070300075282a88681c1c01d555000e52a400f0052400c510300c2e90114061090500c41c44900c40200f20151400011640b90022405030080445d40302e040b01c002e9020014000f4403a10070f4078101c82441c8021800e004855408030064402400d05580850704e4003c00300785a074441c001040e04074400d0b11109000040b61042c492144895484000d980800b03224000c04104049489503000c99945801070340c0d400144016030041c07201e90000660b010159041214141d0800c441c01e45150043e100c11001e40c0e62100111038910460f4891400340d04240050003003002001c80400c2100c100600796 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 2128425 1250 2127175 2127269
    0x503040f0306020318030405030a02060304061409030a021902100806040f020a0201020405010e0d03020d081308040902030603060f010506040501030c0519020c120d0c080306040902040c020105060a0501050301 91
    0x4800d5005a0410755589500200380012401c5a0124148480340c90002c0c506082c41d1100083d240d805504c000303401820000300160402850350f104d4004a03071007517000341c81800c007043d40e00d03640d1f007103161018050705c0f641c2407051b020380035004500240c66000304440183c1d4101c08040b9202c490152100b50015241e80808203540d5080c000b920006c0700982c001600c840c81d001c00108a0101034203440c2c0900c1ca102401d0f004241d0214030054000d00a041240c840e85495800301c02d01e0100d100c0103048401c0200f4040f0343c02e50550001c40c083c40c0c0890840e601907e074140511042d0740d0a216466101e00200003c100e154080c0c0c220203641c108504103581003190403100044529501d19100700141c0007422204068644900020740e07101c6c1c1e850050290708101c0b0b03c041c04003260000007070968400803000560942d11500682e179820307400317002803001850007c4040d02800040d143c440c4203c80c42d0300c000c5099441181036034102c03000d240104807005041c0c00344442500703569074504c02000d402101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 2129675 1250 2128425 2128439
    0xa02040b030c09160e0105040e01060503040201050c0d020604020901050907020a02040e0106080111030403020d05031302061309020a080405010e0f1509010b0603040c080106090207030f0e010207090e01050f010501080f04030309050304 102
    0x9154440d1000c4d416841101030716070002400700c48195100e80c148501070006014403806145030905549003800c0941e6203494034001660a03020b01c0080007a184180107414000c03650200c0e4070342c0140d100341d03410046643c030f80c0300300014a00c0884010300180d11401d15400540340c039802c5034943c03540e04030000070b08540b103507512030940d1481c42c85040501c07400014082059030402c1490b4281644c0e144c441c0c1541010f152125036010501d0b0082d105000115810320524120640390008010301c0390b04645c0c8150040c000340803004102c800b9101d035485c00c120089900c00101d460700c6120503100240c158410600212a401e240280500c50250f5803802d04c801ca94640c080298081c81c0658000007440b40381c01145400e54500c0e400c1401a035005208400c00031360080c43c0360050341c21900300000c4242c0c071040100e00c0c001459012071030305810100721f82d000030410361106004032800c1c8040c0003241c1c0c0740e20040d10a40d0042da404a2540e00c40c00000d0042071003a4810180244148242c2e407800383c0d5610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 2130925 1250 2129675 2129689
    0xa0b04060305160216031101050f0309010905011406010210021305030703050a060b0117040204020a020111130905010f1202121014070809060903030a1806020a0305010608010605030402030a02040b030c 88
    0x800100307948409101800983c41502c1442c1c0c2e481d07100a080000c18080644021041484020b04040b158001084180c1c040c405850b20984259076054491501400c0c06018114490003612035500e0841c0010154040508403031050406070020446160020690300003580078040e0100134400381c00d00860307141c1d01072050704003d600801c0100708210550905800b10b0f1960310302203050001d070360b0340072407105000c40d5029441501190b0068441040704802d0340500640d0f601c0d12044080003d01250b0104001022002d880001c0b0003000035130f8881c0c0054081403d80e02071418180400359030800103181c00684110020004016221070308041e1900d00151200c28040c00000d070380b403000300852240c0c00448540e11601d04801405581441c811080d04d0388805088a211b407074843e00404203a00c030754501c1c03041d030a51014003107680d2403501c04001d00500082c010070700090781413400040c00d6882078040c5c0e802260018080e052036102e0364200070080c9003580318180c2500070910401065034502d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 2132175 1250 2130925 2130929
    0x21003090309080316030c03020a0605010e070f1404030206070507030b190b03010209090c0903010e030409020307020f07030305090105090d0614010e0a0207030206040f1a0403090503061003020d110a0b04 89
    0x1490104034444a8940030740080d0305504020302c40e0303100380451070764204d600341c00da1015901420171204640701400d040303041400312200640354908020000030300305000c0b03181900c00c42860b80c1d0100124210b14085455283d428a6840086401d1105001501e4400003c009044c410008c45101c035540e681c1d6034001000450f509040900402c02103201540796015510445000700c00840c50050140002445040081c10b1440d5001c80403e085000352006d501207078900740000202c940399991188400c0196101711025001401400980007407118000380b0402a01d42c1519894103105840004590a410150300c1d0340d03002d105445200d010402da4481d11042906180301c994040d8102010701d1a10200900a4094607204220100100343e01040d5140c00c580c1c810b00c1d00710110f00c5824601c800038101188001031129000900c000c1640001200f0211034044c0c040c0c617080e40d01c54840802c071100d01d1201a4021b00307100c5040700090301111980c0d08110f00244051001c64440c0d82040c83c6400035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 2133425 1250 2132175 2132177
    0x1020703020c06030f0a090204020c01110d0c080708040813050901030f0203010c0503130204050c0405060f07030305010519140102071701020a0206060d0f030503150402030703050612010501030b01060e0301090210 93
    0x101101819030502c4200d41201040d0f4540e0f00d10f040408003000200802020504070b180d90320152030455545404440d2240b403158028001460040d000b105580d114844200e00c00c0e14043c0c180307041d40e02581c410741c8a526940c4030384010740e507683c951201c0f6600816225603900502e42c030100d42e40e61905200c902071402500041142c40052043c5400c47c1d044608a43c00c0c00000e004010a10f0f8a29003c0e416040c0e0540d8045103075100c00816040d83d0140b6084142c1c4044045034010030360007441c0c0a0034003680260350900403030766a8402c2c4a0885408155002007651412050244800c64a80082c80c110184100d8500e145c0d520031107a508446005009003d03500010100901c42d07041100581022003264001e40c551b45650315001c651204290041c24008003000090766101349482020344050080c4c0b0956480c40c0c5900f004005100841c1c00c1403183c01d105401d11074143d014032035103042e242d00c019400121703405c281050b41c943d4050a260b5501d59203071602c900058039006040078000f821 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 2134675 1250 2133425 2133427
    0x60f0603031e0206060a050f0a050612040c0b04050d080306120a0503030106020114090d08100b040305150106020303090c191e09050601020a0f020d06020403050d0809010506010c0b0103170c0f0102 86
    0x80b0541418180940c10105411948500d0501002d0b554507491041102c0c4100c890107030740c66114002c21a82d4450341d0101703a1103c804602010144212805144550710403110142000d407100702040040c09680100c641003500345449400285c005e200543e040000113005107261700240e00c00e03925103800220111095000800104200c030b809025150300094840d100da003941c0f0340045060741c1d61100a03020300c10445580c01181d14896a82000b40c058000050ba4580e1591203082040d901c1c2c2d01d980003503c0a1440d007000040882c80801520f01656080d0050412200141d04110003284601d100030300c864451035001890445651205486840d15980d04040301d02c0c00044104941c2c0003841d460543d00030f50000400200746d500c0304681560b046234000140801390a1000080c056904020510300c00d540400a038542c22884841c480c00c0080000e0000e56107102c0112402c50341c02d8401031000128400503c0020740201c0c160700e200020300c02440c248207040901c5407400005585010160754 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 2135925 1250 2134675 2134697
    0x90204060911030a1109030a050304030201020601050109030b0f07110d020601080c0d030f03020309070b070f0c06140403030503090307060c0801080d030c050d0e01060308031509060405090613060f060303 89
    0x1820301a00c001000c0c40141002003000800c07002e8110301c00141450710090342c48074201c10701015101510f100c580003908031031905101d4506241d0300e92003030005078058402d005c0009519889056080192039028103219243d858070f0450101401018181c101404061665044040810042414152060b40c002c0207907501d4070746120304282c80394000c3c03801110b2101e01500440d40004031131003048401d150050756a41c42040d46424440360790002c2039581d0b0002440d02c140031602c080003c20601402c0040b808541d40c1000b51101260403204d600448002e01003007021a014030b02860740003d96606036071070009145e1342c02048444103050345000c24044030040c4544101041481061001820700304038101c007055028201380509820011080d40315040c1c400741c410300707404c240c0007103074420403040d282d040c09500c90b81c910358013084c0940254050400a6814900f9024180c01410807038054582c58a901c42c41105184031800107a0301c10752100c100900000013485410000c500980c0d400c0820301e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 2137175 1250 2135925 2135929
    0x8030d060311030105040503160c08060c03010303021b030c060705070302060309070314010c17060315010303020c01020d140708030601090e010306050103031101050601140d060801020309030702010201060501080403081302041407030902 103
    0x401d0000c0302c180039078900020800040c070000211004c5010189000c03036980f0035841c0c980d070303d100170341c1080710b2a000e403500340041c102d000f0000c0d40c1a6442902a01d00f11041c15150315030072a42d08491035899400005202e8203810b1002c0101070040c020401d0383d0403907441e50041107203603006031004c840c1940304890400900000c07400c410700151104000307100202036004014510340d140d80d004508020b50002160461381e00b0000e0000010005a018650f50b03924200079496940c02d00466000d070141c4141050304600c5040c808001e410841040303401e020158450b406240c20080401d814020407031804141e40c0e02e0107004174006c0d4460074003c1002c0d811854000c11424240030281c81aa0421050001c280e070059900500340c0941a8a0b503142c195400c602c1c80079049607440005a54800014821621030100c01014402e000780c000781b01d1980e58a004440990046a01038005050319011a109188005550b282c19000901c00b040090000d0107504000c2c81c151036003c04a69240314180440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 2138425 1250 2137175 2137193
    0x5040813050603010605030412030f0e06010504050705040b0f161e020f0603010302030307060504030e040609060815040b07050a05040302100507150b010f05070203100509060106030f0506060a030b030708030d0603 93
    0x18000640303800d811035140440146c201e010181004200c3d51404610701d0f4040c3c0b19a00c0024480800301007880000c540c03074011500d44a080c00303498002c509010014038800e010350203c030103c0300a40006854422758218100c550741080101c0815107030140101c07800b0940010b1200040d4084185141032542c1e644100400d8190b441007a42c000c1c5024401000580e50200a071000a80c01100c0442d03150707a80d2070220391030390300a90b01e6170303100d40f502d4400300c2c0b400140c1c1d010f4003c0d900d80764100c074420740c100740d00d402c207141c000c90740200783c2c5180e88001481548a14007414120045040c01c0b030505482e68002a40003a6101c0890002240484d0540078018025440b088032081110108401400100020041d100c2c51800d1024400001454811505c04000381078601d03440307010401072400e00b64200c5868030b5080c483d5600090504c107501030040114400c0d00d014500c01408a07242050443c01600641021040541d0500840c079000450450a00c000e001e003100d0782c400022490b04600d001100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 2139675 1250 2138425 2138429
    0x302150708010315020c0a0b01090b01020609011109010c050307080706020c1903080610050403060c0816020f070501081f060906030e01090503041403030c0a030503070e030f0c090703020c0105040813 87
    0x1004070200c01000880d00d03c0c0f4400c2101c00c15100301503038441c0d212501d689400300281c0d00810280c0c50070000203000d01d21340d02c22503040509030f00b80c612a84500c150182619090743c428000d0200170021044190302403074800640714410410340b0b08208540d01d0300ca0481d0011071069808079000203092070301140c01c0c00b0308181c0e0b41c0c0302e1381c91004003a8030b070b10001c00f244001025103000703a405221350042c0600810994000350382c0f08100b445904000356004105142c295040d00080c030204141a0700c1a0000c6035030551484058002e0010030f2510740116000c01010303002d111030000044078086d0040ba540700640281101e500e03151001e03072800340024100e4041030004c420a9240035101d000066001c02202c048803400c174400e58500f503981c00040c0c1540314401844c82544627890040042503006005540310b00122380f242c0a06d1401242459250115401c1080f0746410030000b1001526040d405207400411903c0c0c0141007540110350507085078400d840558250700c1c082200c5c00703084104008080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 2140925 1250 2139675 2139677
    0x30702010f0c03020d0e01020a06020d06030506061816030209030105090c03060702120906030a0b03030a0207060e040b0303070b0408040f030309050406090b0604120302010b0604030305030402041109010e06031b0703021507 97
    0x184a0702c860b10020344454003003142000b0408071200a0029078420000004c010390810002c540d250840c510301d00c010400c43c80225030a006990004440f031400c4502020702000c00c1c1610310a80da22691440c7c07415101c0b1502d642415800c3c0800e5a55807024800c8602c16402c54005000f000d503490101843d2500080c819002c560001c5031501d801a000d0007900d408007001ea550a0b22901e66010a5000d08154061b981d0503110101c0d901c2c03035003035000901d4000c95410340c55004445000d28140f10580b80050030040c1c042c5e004000540018064689860703100d070081c0c1d06907040680711040914440c3c107583c010f0700000d58140c402c2c8203c2c03406114500040414000400c515000c090220b200c6002e6840b070002810020044541458001c0d0400d10151000038050390b070300e5841c0c0c07801502e50303003040e2030030b9000701d2400c0d01440320444100c0440d0b141003016103c058809182000700400c592009089800550f030070080414100a50340280190600c02c1e00a00ba10703000c4203000e01140800200020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 2142175 1250 2140925 2140937
    0x601080f060102070e0c07050303040503040e07050f030606070201030608070b090102010513020904080703030608030f0705010b0a0305070b0f040b0a0203032202090601120213030503040f050405041a0402010c14030702010f 97
    0x48216030b00020380c88103e85c1840e50300407041d922030742c40340c40c140159603015000e0f0100100b003200300320010006000b551601c0c40144aa40c40d404001c4440e409440000d203100c01040004c907900780b074908042c0000c3c1d80b0501d03000c40e070640c031130703000700e05002050740032400c0a8404184401550f0b020b0040307581c004040143c3c0c51421056400240e010100034001038110900040d910062510942004014003031702d4040742d698411001141500b50300402081d2429464596640746a00c1c003a085078046a0300311004100e00c0c1e0500c1c040c0352941c2e000c5280c10340181c200f0080000d00c0278004005c3d001c504072540140da207134034102180c541e004408a07410004c83d4400558a80140e5400101541101080c6408490039506034940d4009100784200c40b01f40c02c0e507500000080000010042040e90324400c0701c00b81881e40c54091205580085c1c030010180c40c1ea50030405425170301120415817060051502c105908201e840d60000181040d40c505041d82000400900390b581280c0804a4456246801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 2143425 1250 2142175 2142181
    0x1060504050c0d05061306031109010806040308010b0a051308030304020906060418020d09060e0d110f0a0609020a030b0705040801140702030a0305040203010b120304090e030a0c06150306050901050601080f 90
    0x181000344120451503d00030340d160089011501c1d00403030f009105444000411510b81c6906080400001040840c1d200e0f03455803001203000308004c20aa406264140c41d280d0059090104808090b04059140d00811070140540c03043c1c0c0c10b8003d8030900a166100245a0b207007428014001140801411603014400070042045442c60603c0c171175202091900b001602c8554181c0300e1030107070803010009000e80e418141004208200840c4043d0902400d03151110072611801803c0e4a0340c0a00808686a4218460039800b18900707030000d0450600c0103018000080d1640c3d20b081c1074450982d40b11002071401f050074005004244500c3c101d5400c0c0701003201d01440e103440020b50701c0c402d08406604141d00c800110301192002d400c428272084005140ca000c000e8201c3d400f81d81e941091103a802c0060a06480d404000d00200440b903071040385a0780c031854980c45440383d20240010448210000100020000c0407e01034400c060080d0605400030455007045400140720703841c00b4003010019600c40d400c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 2144675 1250 2143425 2143441
    0x9010203030c03060402041d070e0102010501050109050609060408060117070b0403020901030f020a03020402030903070312090803040209090c03030711040c02060106050301120f020306040b161403150301020c010c080601020106050405 102
    0x1603980c00341000d4030443c2e0b259075503804100a406550b000c140341070120000e4600303200010110a102c1e01d41c503580ca00075000000012402d95000b84180c2e4086480080c043c0030070b0900500030a0a0710001c2c008500c0c1541d614641403038880d00b40e11982c050306910b18400310340542408000300070001007041d030703081a040d600066840b0b48107201c01031441d400e981c400300071510350300c000400841d00200215100d00d4040e850b240c80343d04c0100c00310b00060400c14068038110361481003184454100c0c0c0814155a0b540c2d00b40511210040c01500b12446100000030b0075560820041505030711074501ca41760a2481ea0a001c00e9030291a0780f40250741001c40180813065004064070f046450140060b60130802c02d0800d101616202d06003c0d4040c050401000203100140800074000c01d104440104031080849044076a0113011500d19443d40b408c00c0400d00074180f510700c400221400070001450a5005520103003103c200c0c000b80390110750860200700d419038081c030484000b401c090b01c09000c18600071070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 2145925 1250 2144675 2144677
    0x4110306070c082a07060201150503150402010c0311010501062102091005090d0203060a06050901080303010b090105070c1502010905060703090203030403080a0c0c03080309011a01020d0c031206030c050306010501020309010203 99
    0x300710310241240042009440c0c44c03d104811044141d0043d80c10761511803600038041d1044595031400d004a025000170981030000780c91410f003400c502110956280c642c0115090034041c03001b9800c006e00e41c142e1041003502803242c203008214a07100c00c804900644c104004041d428030000a207948140040000b80d125904a001c2042ca10318001d40c3d1107016400050300d445400d10040e4040c03181c80b0400a2039502039109000b070f1442180c000341140c1e40d0b2924a07940e84003d0049200003101070091000650003200030b000ba2521403210229090f40355215203259603001400640140c0d103481e001000c0c44824000903801842a14050020041c0c40c1c02181d03a0b0710442c4401009184005010484980700d0b00c1c411440d240c0c0035011a40840c1c3e06d08008c0c4041d0000d0341d02001e00c4d4a0803e881798190750b0040c200302c85040603005001c503110040015a05d4180c3e44c013040d001e001c0d09040001e04c1c4051031203041c000c2d51181c440c0440c3d06040c0f000303040c54038005070091419035100b00035040a0b40c0e0008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 2147175 1250 2145925 2145937
    0x607030912080c0f040603020306030106080106080304140f0616030f020c010c020d050f010207050f070f0e0609040204060503030a0903050f030a050f0a0207030f03080603060a060509011205011404110306070c08 92
    0x410850300c0d0f500e42140c0c1803150b10a107008101900307004100450880c4d0f05400660045130110020300240b0380301c10b549802c0750b809120707074142a80100020000a40406191182d500f00100201c0c641d090f000041101548003905d80030580c0d80280c6c80d0400c143d000b00780300300d200100b48014501040c0b1200043c0060898070300103032290a46590480070000c2c200846456080c43e64002e45d01d0303020501c4e01c159559074103250800c05008024002c83d038420b08240d0b090481e800d80c0801c0d002500c405c0248003400001920a907040b9032100c4003c03545840c200028100b4804036038425400303903e141407140c245180b14420b00c01035003040028100f20b65001f0150746090710954402c0307a0746c00c0032305e100b40d20304440d0354030040221101040e948107154101a07118030810b41501580d002d0740c2c0b60640181103415602030640d210b0121b1005000703004c0081190303901c1034414030002a42603a200c3c0c00200c50030048408941c1ca016101e440806403c0034402c0b5074100b17071603041950070f007905c03079460150900030b44c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 2148425 1250 2147175 2147177
    0x1120903050301061101020702030a030203040e0717070c02060c070b1b010902030c040b0117090601030b0603010902130f020708031003120804050303060f150c010608061005060d0b040b0a0608010302030607030912 93
    0x15800310b0485c60006c0d81110087c2c0d42c010200c612800052401035101c0c1c1140c807600101211802c0090200c40c050040361401a101c451000c40035907a42000381c6104074148026600034806000030140404100003a0f4094116526140d444500d004c403004d54541c0b44580c0103001d030f4100b84c0048016100007520302c0c81004200c9003c620040d403080101ea04102800130600d6040c4148244414002c0111b08941a079000e100e105800f81e45400c145800e94401c440000d4010303401c038105144181c1e240d84464112011070790007500d04080d40c1c03288010f85d0001d0700c0a64800034890010420082d2a5000280e007503501d0408089900c1c06850300b40d03c0f808010301e503034099882000c100c0401d60f1030900429400d240d03044c100d07403151980c840040c002e040902541c40c9521940c808291a0110380c80358604483c0300078061880c1c9075006030322401030301c440500305401c15154491584550b451407030100c0a4446591040340542c5540101450404080c200005140c545121038001c100d603400580040251 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 2149675 1250 2148425 2148437
    0x41b080408030a1401060809071508040b0910060306060e010915031101050d020a0302030a050106050309030a030209040e070312140403080403031b0204050a0b010207051008010509070504081207020112090305030106 94
    0x603282210001d00380340c803050b4580d4807081d000482c0c085d400107090b81c001d50411048489c03594842d02030b28440303101809890b011940c1d0500040029021007006e5078804002810786044540f800024070684041d500107d8110751120401e014040036160803c0c0101401ea0080c00948810942d41d0340b03a40942c00064010345c0b81d001160102d901038022030b486e0320368001e421596040002c0000b070081d0801e4680c0c000241c100b1000054403480350040d2030040a0100103103142003101c6806800940c00000c1041e085601e40030081e0381140c0034402c010040d80100011001c1000c24440201601a074044d0030305035501c1840184003080c9880150740c05c0e00d51500782107020b040e403907a00c0c48664590040c000d50007814042000424500c80c3c11042907005c0c20307000c8481d2580ca4108014000607410402c0c1d0000b150000104440e20b4206109500990b00d03080203132409403203d25441c1410101001003500d0540059407104659108440c072500c000e000404100740c040580c2e0080180c031062048030f0401003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 2150925 1250 2149675 2149681
    0xc040b0c03120106090504050604050403120b01020c03060403030501150f0c060207021309060b010306080f06040f020d17030601120b090604051f08060108011b020c060703050403140c041b08040803 86
    0x390800840d45869010040c4041640e501c050051004126000e0745008500708404100c2c2814940282c4d400f9a5041c1c444140d01d00d009080c44000b0441815658110f102e42d1000c11400c0e01c3c24011107000d64004e9401080c9036040c94800c0308088111034101d000c11207011040d08003560b00050a149095200d0402f503a210700e41e000041300030902607240704000c0d2a080c1084200040c5a1041c49180000e8905204081c2e5070120540c961060500845d82500804009000a6441c402101c0f9107071000308000403c40c441c0e04c2e000f100c010440e5000b1b1018400005120389507810000c05020415a82d00902040f41c81c0c1c8046111a40041c2051f40110340394070100304070311607000d140150507026291001543c1d540e11400c50740c5070703c04c0c802c0403215441c1448507450b0309003198102d2003150360382c0c0007480e4a403110000d0214680c022070060301003100600001c0006841078550724800070402000704204890340b01000112084c2501c214030f41c1c41021404100260080c0d01b2310782c002c0c2c0080340103459039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 2152175 1250 2150925 2150947
    0x1608010504051005030d020a050705030a030e040507030e0a03090f0b0a050d05072001090c060504030206070f0f06020301060c0302060906090d0c0206040509040506010306050a05040c0b09010909060815090102030c040b 95
    0x1007060700074645c140284440030701c00560010764000c2040c0148102c51241d1350710402e040d00d4a40811000c0c0005401d44c103100503900b855000760b5004074440c0780000308051038005050400d08801d80450019280207820080d40c42c0d10700b0701030003400d05010701c50721700181c001c2e018260344a5202e200c08619100c0000440d071703900408a4070300c3c80f1045424903920042c519031580c000c0c2003c10085403c4c010781200415650320a00c284c4040c1c0f940540110300d081a103481c0c00b20119124041154480c441e2019040081ea003400a50700074080e60f200c00f500440c161801034109580101040301c02da01200800010030340014001600d0f01550914004a00003400400e596214a800c0103400c4084d10060004000c00043e0860480c0c1c0500810015030701c4101c07442007500c5c3d05603005001166940f905000ea200c80390300a0a441c1014103084510316a150044410303250a944140c0c81340c0c01c03000d50094509000000c142e80b1102c608000c510310300c0d00080d000903c3c001c0c0c0c015140e8600d00071031580419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 2153425 1250 2152175 2152201
    0x606080a0b0a050907050409050a0209010c030c0809040f060512010b030601050103270804050907020a02060306010302030601030902030f0705130605030d08070909061503060801020a0c02010e030a0206070b06010206160801050405 100
    0x1900001d0004c004610701600050826031251090f031401c9483d140000b00421068400e0300c0d0f254505941da404841100d03101150104541001a180810204032001280c0c0d100e124000d42e03400c00c500701103400d52400b820084030350032032031342d0800716414014101e006a40c040350031030644400f400d0011340d103807203058280b00789010b23400d1503040064103c200b00309114200001d8002ca860440318061581d48240c401c9840c0c0d4890b000094104000b8804030721258000e4000e15801700c010300d4002800d00c450f40000c0d02d0078400240034802508043c81c20b100c141022a1804c0d082d84000c41c080c0805031500d00803035554000808081e042003650780c04100d01e5845240d50100500c0c82600c02c3c04242d480340b400c0742d6a03000034540400413a150803030005e00c146040c000da491089250304c410080840c3c5400540f6000216105960305002d0b8800a80c0165141c2e00900101d81c000e0215020302d142c00000649400c0014054076035002c02c42100072081984415550306468040c2c8010450386c43c3c405400c425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 2154675 1250 2153425 2153429
    0x1150306020a0c080c0106090c050c06010311040222030c1d0105040207060b090709080c04090305091003060801020c030702040b0307050a03060207060b0a030809031204060903170403061d01050a0606080a0b0a 91
    0x44c2c03030340003e82c0c048045815081401510a031600400c40c00642c0390003601e8501c01d0841c140c640743c2101c00100046180303821000e41d00c0f680a0005480e00d00300b04409007580742c0b803008030028401c0c0d010b001e0082c09241820440600b007082c114411306029100485d68440781481124803d580016a0408004030b81c2c02001c0d0001000e002840d00381031600000d4001c48460080e4941480740c170403940c000f45841c0c040c090f01d481d0181c49107407038030b0345031014000b480c42c010404c101415110003001500074000d100500c000300c2c699001e5607c079a0305204000030f1b6021a13410034800d5000802c2441070b40e0301c6440300c5c4100d07a4852401641d4083d180341447c0506440d20b25140d014403c0039001092001d40d00c01021039030780031001d50f81000800d210079030490060340030b01000118140d0090000401003003610340440001407001c0e044c260340340e641c6000c1e600c0b100342c60003507a40034030100d400303429090290725040248240306003c1c06080c420000c2100d14020f00c0805559203418200c250754440d403d5200c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 2155925 1250 2154675 2154683
    0x512010f180308060402130306180503030a0c030b0607020303091e030106060507060b03070602061803040b03090102040317030702030304020d0204090c06051801020c030307020405090304090509010605090901150306020a0c 97
    0x100070040340d0481860540e40e0481035001c2030940340014643d28151003294244010500035038501820350310b88200800d410340c2e05068040b20610820f0201c0c8040014601c15001100e0220b480b42c1034150050540700040715442c060309091196500680d00801901c1040d40c0031341e40401da51507101032800412004120080c1c05501c2c00034040b48099000c1d00400d610b1b4050a4288006413841d0309240da42c0100f1306c51480140c12480100b187c05202400e4044409107a40c22282420b807a054560140d9009458441903a03600080070020410342074400844446480d1340d25040d49000e041c048d440f8170005100a200e100c01c24425011561998080703000b0981002d510009940c40710800b0740107500041c1542d80c00c16101d08001e480350b20014846d40f41600c041d0186043c4880d035820b0001604019007009220300080c800810034200030b1003074600c100d401f60004102e0350f01e81b1040c000a401e0103444054030764142641c41046005100d54079045960009006076280401001142c0d481000c0000030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 2157175 1250 2155925 2155931
    0x90a0b07050303010905010506031902030705071b15090303050301050d0204060e040b0604060801060506090609011e0807080f0106050a0c030203040504060b030103020a05090f070c06061203030c02060906010803040512010f 97
    0x250500c41c00201039816559030703901c10410390341c0b500c08001090100702c030b500140c140d8036650070386522090b401840d0004030711309055080c42a540c3e03882c0c01040d418003038043c40044140c1c041000201d1200812000b001c2ca040c030301c60050554400505510050044500400c1d03411000801c44d00c903039208600030010f0303280c071090078241403800c0102080305849840c0300e1401d091020030054410711410084860007000d96251454410610210760000030400e4184090300007101c24403c5541d4008030200602e030b4505601e072500e0840641054406040c80710343d800c1c15401845010f421408840e03000d0583d0920844007911880c080b40b46100303503000603400600706103000441d511a14091070507030384201c40d01c0708001c0c1c954080c041d141030200c0d0703140391a807840d001042205008680c0040780328010f00001c103405031aa80307220100b140c2182d0880c00203030f8032000c1145490b4144980c64103c00502e02804031075140c0b00700c82d503507801280a018400c44c00303200070001510b401d42c011401e044101c0814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 2158281 1106 2157175 2157187
    0xc01050c0d0305100b0304140105070504050d0305030402040e03040f2105030301030f06060305010c050901020c01020105060f0103020d1b0c020109060203030402090c030c0706050f09010605030303040804060302090a0b 95
    0xc44c40413140b100041105014500118401c0b400341610742c00300c940c404112421207d0080500341040411700c401d006540c0c8802d246840503400d450020f44a171990300015004108604612595110000f0001050091070780e0341003c40c0c4414850f01c0d034204c8800844c466501180c14020150741040006000040d500101c41450038003680f4000340c0e8948039a40d480c21203807506a85004100081880c4142c4c1d070b810003001d441040c080c4000d0006090140c0420071401d043c01159061503004181211b5501680e40003401216482003010b24038102000041d10a140c003800c140d0001d0740000380896024000004c803405564007801a6240c1d5036118200c0c8940e070000b802c00508a20100f241102003405070240307070b00425604842c0901414007040d594211501940054080d030400d008002c041551032040d101201c4481c10050781d00c03006500001e01d20348558210344100c2c5004564 = true := by decide +kernel

theorem cover : BRFrame.Cov 1978425 2158281 := by
  have h0 := BRFrame.cov_init 1978425
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1978425 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1978425 ≤ n) (h2 : n < 2158281) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
