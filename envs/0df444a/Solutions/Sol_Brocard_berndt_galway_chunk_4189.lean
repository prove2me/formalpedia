-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:49:27.123155+00:00
-- url     : https://prove2.me/submissions/54da3b22-8e81-4d4c-8dc6-d16a86182028

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753237410 ≤ n < 753417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753238660 1250 753237410 753237413
    0xa0f1803122a0609020d14030c0f0604030c1104060e01080106090e0c09010b13080a030503071b0210030221070207030c06050306010801090506060c0132010b040e3408060904 76
    0x101c00040d900003015984c030707100303040110345a01c0e0302ea40009500c8202e454844100e42006903e0703400c4059804858400c16420b0400c0150010300746001d180c05442d00034001850351200d800e240a41105141c00036180c0c1000942d103505100e8580c000d00307079034000082c8075091107400c1044d6820b0044451150344030100d0064152f8407403482c14115611800004e5450307441e035018103606511603120301813501031a103d0505064011004510440107503881402040803081d040b0030b401008240a500032030785074080a10140258010311451680748a032038000781d080c40450032040400c40d1050010f0300301e40e100304208080307084280082c202a0400c20308620f030500000f04500c2c014821038102c503807540081070491701d0b042c0444800c0007040009024610360700128207991012403421613211001061050036040468031198140c800b41c8203128609841c0541c02805c0c90070180c15a0344000050010301c07403465880c084444411850002c40d041103115500141c06004024075030f45c003079400b0408010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753239910 1250 753238660 753238727
    0xc0f04020f0405060c1018020a0e0702060109020c1e07030614070212070606090c110c060a020c040f11030703050a0b0d0201020a0f110d050304090b040b01050a0f180312 74
    0x341030301d405407660f54403150002c2e1710078507088240c2d40303035040145000951450703094590107102089009882c2400740715a112009128200304890701401a00500014020302403650010308805c40140225030010220310540503024a000303203040c0013944020420010081c043c09640309410700b1801001d0545050803000e07482d0040c100000c0c00a2400003442420028540d0001000d001400000c01181c00007560140001c7c1e07030151800d280380b0070080300c10f1403490301c4412175551400c2903010384a000314050902c0044d20003230342904200d944440810f0f0203654010080d51081d00b06507004100350404900410840c0c41d00c0b10ba690054660400100140c1d030002405161a640f02c0c0c1c084480300c0e92810605800840340c1d0880c0c0e8890503100c40801840790001c0a0001d581c0f03114400c0129002000400080740d01c1d40540310302140c418424410f106005180d818800e00460030402c089603090000029200c155800c2260389800c2c04809800311584040d15000c10b1505644100c80100c0d506860f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753241160 1250 753239910 753239917
    0x90708120a09030b0c030601020115080307021504030816031704081c060e070504081c0c231f0b030609031804110f0705190b0106031802120c0f04020f 66
    0x14500000940140c03074501c1028010011504182050b40f01e0514828110240d030044e6060345c015030034a8400c800b0300800c00208404c0350382c00001103190500c140d0900c03a0311102d0001100b5084021b02000000c00c08a00c02458201e03134101c40d54020141074580070f03005840381182030710f11407180c00400000880400072030311024200814141175505018825020300499000f0405d500750304004e100c0d07480d40200c080d10959452030265000b0300c03900c49424007082003031041000002c4138290414003090241410507017080341940c070600510800b08102c0c0c9880c00b810102c407440c4841c20b0050030340c400d940c49030b0354102c201180071f00440e0800d0340c01c40e40c0d84d000c0c0002c4813015440700b50b03644441c0d54480d0f1081d8181c00c01c5034a8252501100a02c034030b90b81e003091a050710706002e100c1e01c03180d000c102a0381c1c18040b16801100c60360303540d0030601c04400400d00c8541ea015a018414903d8000d41e49000880c00440751150040124090807014401c010101d060381e9400765005106020740d404050054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753242410 1250 753241160 753241183
    0x703050304020303070507080d030f1103011e0e010e0402040c0c1505090106030b0405030a08131a060d0b040609051b01080103060902011404080601090b1210150b040b03060405090708 80
    0x440d480ea1603500010741903208001004045200b1204009025080414004001401c2c0d840c20030168802c51802030603903c4107181e501800c80b0400041c07140241c000030300081d000c030f00ca0f00502500c2c0c603000140d11081007a00314940043e1481c0070082140307894000d000030072480345003801c004103890b910000782c00800600141580d03140d10001c1c503484401d500c014019600150031280d181000e08020f512680460841d07400a0404000200c0d0f0b940250500e04907207503c1110300840703035a1b10581e44200d8a0180c81c1e941c1c0044000c503260080b405011020b030243d40210000241d50049150040c6803681005109100d201c02c5090a68944c1e0028407190443e600300d107010640101c0c1d480120703030011009922455118010401041c100000612a13060310380308141006502241420001d80301e4119082ca007240e4412250140c0c231009680040d003107003024020401017070340c4400c40010a600107030001b040c5000007004220413403070700d8000c1c0d0740c01440c10400340c104242401d454648500d01c1103813 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753243660 1250 753242410 753242417
    0xd08090904050321040606080606180403140d0c1d0a03080304021206070c03030b010503061e1f11010f0605150c0f06010906080d17061c050d180f0302060703 69
    0x203000e1040074030440710413015641e9000202c58001250009540069070203807504c82c5016070215a0310000143c1c180941c800800c3d048840c2c50b64038106107502c100030f1084080000604201f21880956006442d1001e0082c10208800012500c000e000b85404030100c0103500d11180c2c021180c0d290a44854141ea0b08a11a5a1341b542c0d140046080400040c04240a41c45010f08201100360b0014100001e01d119642c107010700c0210000456103400169200c0398070984512032810f180d01c0007101d1740012003002c0e000068082d40210441c2030f00b03202c0e110030004500ca280c03640c2c00c034135020300c80e445002c0342020042100908140100ba1b2007c83d000720203008044c00a00300c00c0725407041010740003088148045a51541c1c4501545000d4030080c49101118420041e035212118041e0781814a541e600380426800382ea00d0788200120740110b08452100d4003002c4a40702c01240713090091070380c00003070ba8841000660140c2c120b166075010b02c1c3c0c01041102224001400140d0b41c580840305d6807605440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753244910 1250 753243660 753243679
    0x504240f03180c06080603060703090b0f0402120f03030a141b0901120218120d12110d0e1c0507050307030e0418060c03110a0206061201060e1003110d0809 68
    0x1400c07040300401c000c2c01500910500100140c0254032081481c8030340404e6098914070780301c0010640543e00c00e070f84020402300582c400502c00401c03110a0750361190004180781e0402d407040c044103041541403008915a90800002c0258520719030007a00d403403150001c07001049142c21128154812420040c548841500052010040e88100d00219124540c954110b6a820b0080c0150503d6884440755900580d0b142231030200d07100c00070610118501c50b60301e4941950440e03a001e80001d01c083d0308142c000250900c9000c2043c0e54501c9000070000081004040d4949101b45548400712100030340b8042180030800040014400310954000a9141c1813905a0010800020700642041c69800201760482007800e81030000c2d0307400114507035903182c90800c030724041c01242010f00c5c401c44000030301590286020804c00d082107205d804c007540640e0700014030240c481d0124403072554107603162034a110412034140184508a058411360364011a460881c10082e0340d40c0d0340650280b101c841d8411f60300310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753246160 1250 753244910 753244931
    0x150109020703020f19020109092c031908150603100b0313062a03150e130f051507051c0c030e060703060e010503060402240903010c0504240f03 63
    0x3c01241549100c1c21098405e031412108000703c1c20100c810050780001d060040c005440b991314400c1031451851410121903160410703c2e80d8070750038006523000345140f000304040c0d603158901e0306101001140994920302c03281410b0581c0c04100300380314243ca106880402c14007044100c8002260b048500c01c1c0442a2299224a13a807104031600c0301c0050710316801d1200705000400300240c124111030030700661507220b1504240480803a101e03034001000c01c08917200b0611640b207600355402e9000885c045114200212995128200800328904035990b900401080403012a90001c05a005138680f410300e0a00901b02203160315010051450000c0541d1203c143e1155842500703d506040010340c21182681031804006000f44494070400c0c40710032070303200049000c2c0380100b101070203603400511452081840d8254182c0103451010392102168003004621407130f840038054030808170426100c0580f42c0e440c11050f61105038151441c03102e0010088509403036540c2188080f070172103160f0320b000601d050f0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753247410 1250 753246160 753246163
    0x206041b03020a0b1b0105061c021c0b040b07050f070f02060c0f070501020f070b040311190906050f0306070c03052d0310060504031109060f040f0b0103060815010902070302 76
    0x11a08040d42100f01c01c0c1001c81c440403074000030844103610310000c0030303c000941e117a10b00b00c40050355203c0d40a2151100c1c1500c0014151003900340c140010b142e101c86155540000d07048000041c412143e004407442040180a00502000d6000c80103007460342c41c110303c00241415600c98124014065528000344209540b50402903403501220709041392607844e070140000d603441440744a0a401031003040740c50014000d01052480c1140d0001c41d44a00301030450f0785060720b02c0c0d2072211043d0496141c403280c1c10b000d080500c4c03003001030002c400d00003280f0742080144610480d60b80895800780d8415018010120382c06004040c00c00d0700740c5443c940341c4038a41c10203500d05450b8039200d6404607070302c03681c4406168001e0046008400c098218840e50303544d8641900e06010b030b0300c0080c1c40800d18446000c0c0320700b0075080e8036611003001400c1c4c50720711300790340c00103801c8844401c400d11100e580d43c0c2c8401047d5815200c1c0302c0241402000800c80082d020000780b40c09401401480f90b4150013280c0e40c81010700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753248660 1250 753247410 753247463
    0x11409060f0403060509060412090302010921020a0303120c14030612120403061406400507020307031701080d030e01090b0f0a200a0c03090f0f1e0501020604 69
    0xb80070030144058181b042d0801d0340c0e1401a10161601c452207160740c8501801015680101e035410386620818034a002406100f50600180403c1062400d030600c0005a441540354030156100c2e0311680344040d0301010100840f071038104942e00f4442c18200710541c006005069a40c44a001c0341d400b60903c0382c0001080c1040c0c0a03048403025104049004410442960420a038424401900315883d5441c482000716885485c7c86181c415040c2d05082d49a400c40f54102e030b0151400244030070b48028024602c04216081140c840b030040c0c0001c140c0d04101030303000c08454101d80e071030384801041e541441c50442d224075042c0660814555622650070040c907003904801820790f08103141d02c5542c50001d00c0c0c1e0719079100440304003683c42e2030448000403040506024200400d8400380481c1400090842907520240c0d2080c20340501c0075180b800100108082e207104041d0400c0d440d440c10b1079140500380c902d10508a0301e1a8502d501c00103060000c3c0c1da0010b80180d0146d00581c044500c00c603100b00103d1181c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753249910 1250 753248660 753248663
    0x60604052d121b100e1e03060109020c010e0a03081512030a031b0801080a020105070302150c0903160302030d05091801081b040c12050702030d050a0c020c011409060f0403 75
    0x22695981081c542c640070440e0844041c40d0b51103007a107070b2900020001e803800124118804103024461001c4241010f00c0d001001c90300d40c51024110150480001c0e2818100740d00c0941d8681d00000c00d800022401e004101a14407400010413080c0709998002d040c882c4000c18803074101a0015051000350313100e01e403205030b4440000650b81d807581d501d007004014020358801e04c0204505100e40c0b00b81248600c5525040f911000d0103441d602405900441d142c1d40202802d40862244000071842680b1080140e80504000c02003076070380e4503901d414181404000b2200300d40c1c01103016020005a10302140b203090072040342ca415a40c0d54030000001d51041c2003032580000b09a41c5100124524400040342a074002083c400340112000460400007540e6590b80c078400010b000000000c0140c50701c1d007003941c000805006607420203203d00045011910100c504081c880d0316808040d1507541c0620200665040a10301080040c85d245000c041c1441081d032040e005072000503030760700a1a01d5009680186 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753251160 1250 753249910 753249919
    0x21f060f0b03101e061d1002150a1a151c09061107050a020103151e0e07030203010b0412030918090b1501020c010c020a03050d0512060604052d 63
    0xe500c0728640403481d0400c0b03c60418903400c00d0408210600c02c0345856003800300108160321414208541242c19648101402141620800340360000b0303580e8241c0d000300c5418990050006034048140c220410070058452070b1100d02d0408402c081034200c0131383d1010110207440d882501c11442749190428031803200c42c0c81401d400e10740c00507591403003500b092000c10b0040909200c42c0c4030301c1624801910030030f1801001a40305a41700c900650180d04401d1502180c01406081c25030741c3e40b0440d04404070340451103101d202c010310034402e240508040365000242d51a0031400d640c1040c465550a201d2406044030f0300b5940080f680070544a140660080d10281301c00300280f1900020000107080c06e601e084901c00c00075000500c202c45003120448120005a008190003540d0000640d0039080140069030802050403012004c5002080800b02400c00750340d915940d01c88111100746990005089030b072140c14200000c014540e80c6455414525542d50f901e0203500c45034402c031100c0e01d01702c85a5030f07401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753252410 1250 753251160 753251189
    0x1140303040504150e04050f0607020714210609010221070206011a040f060801090f0506091906030b07020d0f0905062a06010b0a020106060302070b18070305150a0615021f06 76
    0x308280842e548c10340c03020f4181100c080d512814070a80c0c4510543c001c40c00340d52000a007540c001e141c001c0c043c0c0d081c0c40314100000c4d13000094030941800d01d0b2048514440c641c3d000540500400d2034402038082c5450800d088420342d00300704d08001d44518062140901c8481781e554031004c0c07050090b0071140101449411004030954820700070305808000d104005080c0d03d420303501a800d0309540201c0b481064010111040c036070301c440100c6082d103621032490382202c1d070f655400310009020400407070240d00b894000b400074106424005200d281c191254034200701c070000c005c0106490b00c0003a0743e01d500c040360103035141910840041d05140780000800f0340f1407003101d00006050742c03c0390041203220107035130081c400c0c20b0321780000764268454420002d2103034001000040c0f1074000b801e0b010801000c5501940c5000d656070f115907180440d11002032076030500301c50500c000266140b09607001000d0419052081410500c00a51600c01c11528842c1c1d0180700820489031300043d500880242c00300040102e007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753253660 1250 753252410 753252413
    0x108091002042303010c020c040e12030c04030c050319020d140d0f02010608160b07060603020604090203010915030327050d0803040605060103060807230603190501140303040504150e04 81
    0x4115030f1846010310500f441140c001820708060203440926026500108620715107202440010018850700b0903e40c081c5c0d1085648100c00c1000441c004c507a20301c50103444504504005030321040c19440704c0d219911010348034406050f0b01c40180c0c10795404039886811303090281441d0700c410315003401280c0725004003003030400f800703400c03480714503584130240c0c004c100064882c0c2d1907a80d113400d00315125a02d4040310604110104c822340c0200b500c1c070311455003c107590750740c0c0c0d020a105803c140c01660b8030340e40100c01030050504500c6030000c40c444600c44409018030b1503c0190210000412001e031001c64502040c418401d124020801800007404009481c40c41e8205981e464200f91003c0360954208804201c6542c4070303000d003800351000710000d448003910b230526001e003403072441c2c0d120000c001e2503240e060003599482010314440c216682d91016040100c003441003c580d030582040c540a0040e603102d0f0616100002580c041c0c500c2510001a910303403088980a508050b50b12070360740040785408000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753254910 1250 753253660 753253679
    0x902031e01060f120203061c050f0102030910290607060b030d120f0501151d090c300a0c050d09030f020609060714031f060f1b02090105010809100204 66
    0x211032005960f6110344004c4912a600300341e01c016105da59000b0002005042d48001e400c04464502d80f01c0c000f200d40c011b040403252820790b0070850721400313035420007075040b1003000e002c4c0550507482074007950340782c458840351910003003034000c0b000d02da402008089044010440b15500405851000504030b40310364614441c02000c1d20007185650131201d0030542a40c0740040b6034064a4180c82d03840201803c0c01881d0182124000071001419002c00c06074800c5080030b071509681c6d10f0082c40c002811030346e14401280505d05480d20f00e0305102500c80c2240150030b4401017a00500d40207011450007140302c00d5182011103c5020310a04410685d18003c01c09080641003940500740403129000e44505a031b036001c03070f2038980d4012038509000c160b17941608003040000900455012100c40902c0580c010355a47c48900d68101d50032800124408040206000e500080329400368441c0d5000748159003026404200c0200062142030f040c400c0e40c902140c1c03040014040074001151340501151241e668003103d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753256160 1250 753254910 753254927
    0xd2c0a080120040312081e0903031e0f0105060c010f150807170604060903171602011109030a020607020f0d06050a0f0c0c0f03050910030204091104030506010902031e0106 75
    0x704002c1c04000c40b0000b448408283c0701105d4000d1807010b01400081ca05940e0000010000c2021040003a604240b0f1303824698458044d24541c0020340c4c41c4d20f0641c03802120036400c2602019180e600100f00060b003035449101605403a81a540380ba125096185d29a0241c802c0c01c0e00350400d1411324032410360b032120708804071003140c0f614021107c0702079071390803170f00c0d045a10609560007e0704030310001400300b02d05810040c4407604c285007007180001c0d040701060100106543c0224051154050100311340d5090049407031001d17910411900e055030716400295100b0007a20020f0040030003094081c00d554408901c5402404041c1178403d5141c1c10345060310090900303c40c4a0511843c0c02ca01c02c00712001403049008414081d00d4112490303545481e03280080000070407c034201f28040207403000d83d0311010302030340941a180c0c82c05a2034900b043c0c80201500d681c491040107040e001c1c0010000304100080c0281100e0040400590700d85034583d5490703640c07a41a41088246404000001c0c41a42c0010b05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753257410 1250 753256160 753256181
    0x13090b0406090207080f2203080d0e0105060f010c05030f041d010f1202040e01110d1d1c0f02120a0c02040b04061a0c0307050106080a03110d2c0a0801 66
    0x70031a96807a0b1412204900440b40b001c1c003050420b201d03000d85044a04c1c01000c41505048a16500039098540b08a140720650000c5468910125800d81000428021041d4558109000740054540032001c181307807154030140c0f1030400003140c040209004090040b03804003048001d05581c0c840c0c50f2003919406085030000a050b11100800004400c440300f03203da410f840c41c1c88500218100603800700406080e54141c10700995580f0701140700080c40e210014040c0446031100400e0f0700003d001c003108580c0030700d1030356981038110242865104aa981c9046444482410311030089610381404078075106042c4c102c051070240000340080d90b00c4c0c01498209419200f11020700840c20721740103000540b0740350310807022518a243d02c2820044201009061040e442c442140d052010a84034507007501d61651100c4103e0b0031400044080c036a110114031a948201c1006280018691788020901603040e02d6411450307210058114950020000e031443c2404000c00e007100b00d9448001d440d001b802081c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753258660 1250 753257410 753257419
    0x1b03050c0a080309061c0209040507080a0f11091c0b041b05010c020f0f0117130606060203030f15061215030618060a020331201e030313090b 62
    0x10009040b220000c11101100c0c00540481d0402c20703c404821480d42184000c2410940c0030300c440c1c25551030780d00c00d0512908c95507940c901c4a050404082c0100c481c0e100d01036880c0340c10b000b02d0808080360142154488101502d95400c0c0090421030f032540068203001c02031507511458144400c0c04101c000f0000661006090305a03000e80c1d030380040d201c561500304000c0d00200208042d120070b1411510784001c00d1300605004030321039180b0070625400c560840304032a4001042d040002407001500c034820203030451740025440c500304800d68004080c0005c2c42288502000410010203407518001d484409045c402074481904040e044038501e107296400c654007034891807000524045641c4200e000600d1501b0291041c0e0b1140e80040c0c0103503000804240c5007400c648202158200030b00398141028003400e60103100d1005038503050f01d5082c907024040c400c1d04084601c820300b0366103000306d050301c1111000b1070622100890340407900b907010b070b803074040c44c10030054000207981e582507085030200d024200c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753259910 1250 753258660 753258679
    0xc120c12230d020d110606040e010b0d0501020c010c0513030b060303040b031305060609070512061233060a060503090a0b01260a0c0e040512070f020913020f0d1b03050c 74
    0x211308803640441c0001150495010034042082ca007001d070310081405e22000c001090a9401a010450704410f007401110943c0d400900c00d0541182849440090411841c1c8141761690066404048800901016041c0b6500c0404241c2e02e585c100111030040281649a41c1c0328500700110300d240e9440d288094490b400340e40001030785032901080e164403480198942074217011840119859020300206241d4214075002e65198060b501081800c8240c2070303106103400204401c920341003440385c80140880419a010080c00110341d280100c080a6a850380727080768070303a6500b14a103842c201c00340c18060040d11001c1c001003602002041d0000018030079160402400b0045075440b41d80d4410301c00040c0040720280b00a000c154040d02d843e9410500440c105c4020212008007410154000c40c2c4c11120915028460030450a1001407141d00030039041f201d0241c07274080d8020900e40002d11002c98458030080a600e01000031050007110716906041c031030014143c03245041c6039160101c2c40304500c20003090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753261160 1250 753259910 753259933
    0x1032004060e0c0903010902030708010606020d02010509030706020309010f051603060b030c120403110706020106090e0d023003090f16151206031e0c120c12230d02 72
    0x7402001d046540882d07203408140e942124821043e00804180d0754113548400850b8050798040101401030104030340000350040c23528401070300c0e0814602e680801c1da4103040800524083c00300c03c0e10306090b000781c000f5070380781c0d502c0c0c04a030300420b000300156040924240902022900007140701c0e8264145c0e41f000c10055440e48180c0c07203180403c03640300d0b42c6140200821407640c0c40d602c5010350082d200741444518114096401810308016411040c0103030754901c070070420400756000d48038118086034050083c0205c030301d0000b5224401c1c02249442481d5148402040c0e20041c81e9202401c10f100410a80300e041031820561207490003004500d00d80f08520004103010307880c41c2d40d4422a1030406250f614500681e07401c1e1496440009080c69a0340d45840c000040741e604840b1000c0c0f5078414200285551007031410b50f0342020130303070400035102c51114003100c00502c2c1e90540314103440d00303915607032646451858803406140c4406140d0700001015000d5502840c1e0010707102c540302c0c00381c1c1c00380c13840300c001d0307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753262410 1250 753261160 753261169
    0x309050709020f04090c0c0203030d1505060906220f060804110405221a090105071404060912020f19031a0402090114040b0319260304031d0306010320 66
    0x2100c07450701442030f040108210124a942c410f02c030500c42410413001103682a00040d05541291000721000f0352a2040c60071403076030f1407843c01c010740400c55405040206400102d00d03a0700943e103030a09000d400c4000017944160750070480c0e000345010155451600d403680780091010300c05031030071204580c400c208070741580740030b00a0034814a600301ca0a1403c80104008441c9400310f0b13402035a440f400354464800c18100131f401c1c0e910034003491001044500702203100070b14000c2c051001d1b48000c4010b02040c80111741c0401c1e0081101e15142800d40311300c00d02c0c0001b803e80f1600d401025402410b041150a500942034002400c9030b000d400c01e0030384849800748010181d50129002580001040010710100050744807036080c072038002c1d2000455141c008040fa1400700d00388005445041d150b05801c00308041615100020a400d0780081580c640e008401200f9010182c0020140140d00151003056100300101c8450468002d0465a40f942d43c2e0170300070000340915810022900c40107141c003186050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753263660 1250 753262410 753262417
    0x2030a080c0c0a0b2e1d0403080612030405040906060e070e01022119050418090c170a0c0906180b0f011808060906060108010e0903030712061203030905070902 70
    0x741502030003200c0340f140d0360200c503444024070300c0c1c41444039188040303903508103040c1648800300040801e019413070406412a5042450717405ea00c03c4401031100300800281e00034002c03030704400155810030b04810842003203411401075401003034121713181041c500207011550300110101d56803244415070584030048100c03000c61000f01c0081c050b9000a042c11094000285c07140030000090030403500f041c803400f45010301440800200400258045828000350307403044016214a05180c60812030080300b40e86550180f1564410320044500490314004005c10500844404650040116201030b449004802c01000c06014054480038031122418601906119500d442c0c50020921000c114038075004503594408540b403e152800c1c2c0680c00204001d04100240c090310b64400030f000d451902c40001414104140d004038001c5904206000a0301e802100f03c13900003c841c41c151850381c29103840c14020702880e50203440e8400e0051092024507a0541c00400f9080c895000d566005603120300140681c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753264910 1250 753263660 753263677
    0xb03010e0a020a1d163c1b0f0203010209130515040207050309100201020408030d061a030403050d020f040e0108030a090b09011b0f050d090810020a0e01050309071502030a080c 77
    0x610b600041020016140b0201008000740d2034070b0b0304946400c20340035940222180006c07411510722030000b500e80001801c01000003085207410211240c8810b00c0c400d0f200722405000d00415114000d10302035440070340480c2c0f09008054991740350f17100207290034030040004541450000d00045119041441c2500880d0360030313500310004504207284001005100740c1c40020103025036500304000500b218060014000740740c03507508005411841e082d00e511080c1c120780002800800c0400c1000002a000310540b04000750199006840d50340b408150311581c4078079000a2041403001d00002400c1c20000000d1000103055610f503080b841e910780c548502c0e400742140180c085800d250086010b1081c0b1852030305207a02a10000c64641c04a8071410304240d01c00640400085500800388081c40c010031020b4200d140c0b0741021032070841c074480c004004200f0710b619207041110000104103d082c042000c5005010301d0704504031058690301c4c020303641c1c3d8070041c400d0000c00d4010f80029601c000c440291400e14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753266160 1250 753264910 753264959
    0x603080d0f0908180d24060b121308091302071e11010c0f1b061d090a09060e06010b0310050f031e070f2309040f06050a0b03010e0a020a 60
    0x40104400c010b181401000103503003240100448002286d03112103500b550500d04030303006004a0404c0e4511098a00c21b80200003080c90401c07603489003070510000b4591110901b02004031680440c54106214400c2c15a16580040c100402c0e10704090554010500c41d44100714030030717681000014500c00860b43c080b001c3c2111509003881c9402d940140d141240c01840792482680c900d1095440c0030444918501c800181c403400001400755030342110b8450040c40a44008a02d401c04020010f124003030004c0400c07001540310225441049200e0704902110215181520342035030311070303034503606a4100702c03040ba5a1680041002a079030424111884c5003240c003030007902000d01c0079040301c1180e0040410700060341c41200d2001400b041c080d040040031341580110301c43e0580d0702d81140e8100504030842035126031168010702002841c1210031440040c0d002c10041215520720241ca001030002a1400760103500300b40f002c00c141840840c1818441c0d1080720810602d5480300021f207103545038400c0c2007510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753267410 1250 753266160 753266167
    0xe192c1b0405150907051c060501020c09010f140d0209040308150d0203060f090c120703021e010c23010f1d0607050f0904110715060b1c0905030d0603080d0f0908 71
    0x1428080003085d80f16070b450030300d130b450f00c500c204114094040d18000b200160b03a0f00d03903040c882503a0501152080040c00c41e00303c4001c0d4100aa2142841128418400c125a004504421640341d219510403259001821032525150609010300040030480701031600003010240444140f80010500400503000b5000f02100d5513000d006e500c401602810b2140144a83c5541c81c0b040d51750000041c00450160014001c414514414845d45400c6450b08059075070050085d9912a42d0007954583d14942190800b120500c04000b00030721030480c3c00707046019500b0182440f5000300765401a100140c80354014822295a0801a503140c3c14156540c000240040200c062102544c8014000c1c40000401c006601c0c40440b0007001594070035041203c500c401c8081d50b08550741c491241500405104464034075110f00c0701d10f14400c1100d9854845030459890004000784203080080d40d00e004034002003000b0b83c9440341030102d1550017910510341c202d42800c102d82d204c4c1646000354010750741d120f02054107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753268660 1250 753267410 753267451
    0x2070807050d060b031618020720040f0204090914060108061801020f1c0506010f080c0d020d24140f0904021c12090e192c1b0405 57
    0x41c010307442e003590f0701c548800d18941155070030700185484000042041030003518000001e03643e0b207440c10403543c1e81841485582d01040c1e02283e604004108400c0380c109035415071000030024040c60b850512a28070102e0003040280340d81d030180c04464042e04011550594080c40c4590302c500074041c102d0207070014004540e064420503005140f003c1c81c840050f04001c4000119411030b000529403000380241e605002c10480c440e032140c140c12210a2900c1c0400242000300a00514000740c030b240180c982c0000c04203240396060341030304c62540c0c0114040c4a41203200c41c00480c1c9005440304648061080e002c00170b5000c02028048584400283c00446404a8802003040c103040c002d00c00c1c0e0300044000078a04a8071003244420f501c8a215406010490703420200062030000c8a8201182c901480e105119207000c905043d03e031080b080030008504403c2c0000d00c0b10390520121103c200352207401c244040041c0003c034004031007600c1284600d00e0381c11098100f10581d6070940b006000c0c101000712841c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753269910 1250 753268660 753268669
    0xe0414151e190510080307050105071e08010302060c01200c0f030307080411040902060a0c060e0a110907020f06040b04201e0a1d0f15061602030c10030f0c0207080705 73
    0xf9402180e160600f13507096500c0c4c0c095800c1d0303400a8000c4810740d65440810100300c0d00040d403200d11070140304140c00248035814000c0c0c506101030102a104d842c0c04a100403089600350006000d8210000320702000445201001510b44c00c012100d907403501501280304503810300081568401c10b1a0707542d10700ca5413910f44800d034040e0742e0407030030940180d01d50b881100507840f0301009008103451a41d03107400b20802070800300126030a4992064050700a80d8000c03000c40c0d079013110717614034140840711110540c4581e10142c2c5080c4001081d007513640540410401031148180e8801e216038010520b0f2809402c100c002000e10f4070fa45032445501c01c61031258150142084160794040e460090070091055845107040000d001e10120302031600c408140406c210803400300b00441d003001441100002d074806200001d003e9015980c44981400c054204034030a65038100485035800c0d801401080d81040d42010017000f0b03112007442c10160b14144006030040b14400a80d10003280c880ba00505001400c007070401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753271160 1250 753269910 753269921
    0x219080a020a0c060806040b0a1503020306033c060106091e0515090f0306060609091506070f12020c0102060114060f0c03070312060f0e0414151e19 65
    0xa60442c810302420324005000c5451040c050481d5484030940c600e04841080103441580511a000d45024002040607802250b0607444491560802580f04d40e10000400d141840c1c2c40c0201c2c040c8d400e080540c1c1004a402c1190f01c85100001c02c0a0f42c0d1441450541d50b0741f10b0082c800c9000150034800200240304c1802c00d15078129001012480d4a203590310005110083c0c0c01c00051034942000a00110a1400108040e8041030980280c11030b8584140014400e01500700c0391409864800c00240d402030030582c1d14140c00c1c100401d001d44540301424003083e03204a40c1012650310380e256400701e4200d800015005141c880c168001c281a81c2000700900b2045600c8182c19000780e0b0034401500f008103c1009000404d070040000c2d0384810b02414010a0a8044a44035030700798036180e810301074035180f403003100183d41490448001c01e032140e1400b11242500c43c201d520080c05485540d150221980d00c01a0003107001c41029440102d010500c1440c1c150b00341c0304458a201003d00803212003480b40c116 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753272410 1250 753271160 753271177
    0x203c0a090203010315110702010f200715082502100903031d0f0c060c0a02060301080d030b1207060305130f0b0108060a020a0e04050711060408090307150c0b1b04091407021908 77
    0x1810b5008480d950340c0c298881d01016905c15004cd00c402d100c407080d211040310385414146050515414820014a07040382001c50000c851003442c2c01c001d080c14000c000c90b001c4800140d5040040c80c0381070500600810381030001c00c419000c8040c404500d0000020041426a05e0310040c3c58819403040c01c22440340d0000300704810502440c0030030340160391128080c6000700790550245c8000031848034010111000005090310407420044040001140003440d00c050300c8180c03e000034603896614a501c035034201c42100401c80d0407103a41c000e042107074040c03096040314200f10440389251550302000f01030b801541d1007040060079100c48840c0c50714103034000c0e80d040314142c00d052040710350ba0300185003015411a025180b03a8030000da503441505080ac0340301300a203c1403100d81c000c0c40469000422081c211140500340c81040004102e07407105004d00138103d11f01040d11750b503035250354243d118007a040403240c000c0005075000c0050003003170000c41e0303403030806280f1100110a10000d684420031500034424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753273660 1250 753272410 753272417
    0x50a0b0a030f0203060109050408030412210b0a0e011d1302060c0f0c1804060218060d09050709090b280207203c0a090203010315110702010f 62
    0x4545080d1105248040030318081e00e48441c41d0180c0303005041c5040c0060b44440d584914140422020070340d000d0030349030402d500c10f900a5004660210843d00c1c0b008140d800240030543d0f440300907540c607041d400506c80c0303101070b1040d40e40700ba0f0350889040e08080c01d114070f0385510030042c40c506810001c0310980e5481140040c240780ca04149070041130158204c940710700d000350300041e921600c140d002c2020340d12205040f160440078101c0c0302031100715030b00040c000415250b00421010001e08107940141440030000d810540ca80c60021800c0000d013110080681d83c1e40074500010401a0180c0078000215402090340388080d12086110174a0041d0303007070b030011009100b071030f4040d81c4151400105000c80c09114411891855906180c5540c0031490b000c0e807241509880b0250740d105150002140c20b05202100e81d402102402428004141b982e500b60340102a00d4002c01c4804195000c2c2d03058030b000b044001452021303244181c04403808801903040f052001e116180040d0b109280c400c0e1090243c0c503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753274910 1250 753273660 753273671
    0xc0a0902073801080c03120a02011b051b030708180d06020d05040b010e100501030b0109030c09021207090b030a0515040c08150a030308040809040207080c16060819050a 74
    0x8412005440c1a0704490b08441c141c40c2003510000340025140c00b41102070041c0036020440d600195442c15490310520040030041450034440d8001e5000d00605804070360307011049600400010401c1d408407511130070310690351042c80300766500041910840b82d03000f2890362409d210a2140e401108509207540c0d807202c0640100c0c0b0000b00c0c58000781c0201580c4540c0860242001d02d0582c41d07125050700101e445111100810942c00d218034040d008980b02070800092080072240120392088a68001401300301c54020001048038442d401000c1c200d2404110107425224504201c44a540030b20501d200d00e80207001103846400b082d40041e4000401e4805003041507242000701e415522401030703000c00309085000308601034181b18410714150000f195820000d81c1959805001803c000c5d0020707044290200380c82d800d54445070704451003e50045003047e00d0382e42c1280d4007940e590040c042c100b80049000c40000d0807900403e001030160344510050912846455045c0e402004001d040c1c02e00d440c0c840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753276160 1250 753274910 753274943
    0xc1c0c080307210c0b0402041d1f0b0316030b06010207032102070f08030f0904020f031f0b2803060b130f05090424020d110a0807020c0a090207 63
    0x1000104480c501c149001c0c40c42083c41d01e40c80d074000d030040c0143e1051100342540040028010a4a40d0384164100d500007a00343ca1010340b9552400c00b0320106015206102800e02c0c400c030750400c000c81000c40164240b10540d2003074245a03c4048151100b8200000340c242400020851001c0c107034410010300c111000c00781e40307443e4a4400f0303400034140404100310b8100c5801440c0c2c14030442001d00202e9801f080100e20707082030390340d99104110300e4038400b00000c1113450542d03a5039012203890700c401e0b201683d2603080c50313104200c06100e544c3e01e10301401511100010800144000c0e50305440481c50000c2aa00007a040c030b2121001011002040540d600b4002c00c07060004009040030040607101e100301030307041030548481c4c3c4209070012846a181002003000184e400d03004c105441c0007070715045260070020415040a13000e20714103012114286450222400c42560150070f007400c550795060259140c11000345d85884a16400941102141c1c900b40068481030b001001c3d1140b007001d08084101e00c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753277410 1250 753276160 753276163
    0x14010806100c080d14181c090e040503121312031d071404181e0c09020c010f050c180f15180f060a0203043005100c020c1c0c08 56
    0x1081d1340c040e20b02d40c2c41003403520769410800050f80c01485503c6008800d134440424640c2e41c00702e20700304100c00480030a0b41d240c1505c0368441900800c5444890704560400b4a803040d02d9030083c2e520120480724140008582c05001081d018109421411000560245002c100d01611006003858440c41c188000e1803e808010440b40004003407050003001da1444200411080c1da00d1200041c000c00004244039010401501020200c0104c1402c4040e2040662506aa842c0b2056020010262010034600300703440c010340000070006d0701d04c0d10800c0140d0300c03540d4911090061032002020f40030411b102e582c0c603050410880c10000c000410201c0860b9081d000700748a079200100f50100f0781040e00b003810f2075081c000e102d00d501d50700c112400342c2005443c1c03200940d40e00603803103540c10050441001480c50115256246802c1500b40c0601c003c101250400310365908510040020303051610610310215440400c008040c07030300c010948401c0004400c050301564003c110240c1d01c0c2101c2d1140003809400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753278660 1250 753277410 753277417
    0x11206020f071101110f1f060503100905060c03160309050327091e0c030c07021206070e0a0b0d05061207030b01060810380f090a14010806100c08 64
    0x101d4103c4280000e02d96000620104200740b04841c150300c01200d507080ba6401040480700d122902c00415004482e4168807000740410b07030300198140c001d001400402c2c05464100802c054080c0040f6101503c0b00b054451940c03004503004280d111a00301c10a1074184660040b01e0b2650103181142d062040801081c0ca06101442c41603803100d80e020310342400340c10000102030b4000002903070a8000442c03001040c04045008100d04404480040024010001c440aa07400903802030414548a030041c800e0036901c81d000c2d10b074080030902c1c020203030300180b83c00d00041d070999401800c0319040c170500c07040c42005400060b0146034004060291100d48000802010000714050903000c0070300e503d881005452030320064124551106520070520000365950440201e9040c14030b01410184240c803a450b5118036808000200000b0010700d04c10b440c21114040d1221070303802c98048180706e41d103030912400101a44906030204206800040341881c040818001c03008150a14032402101c590704d00c100f592 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753279910 1250 753278660 753278663
    0x40614100e04060902041508100b28082e060b1c1b020a140304050a03141c020f0d0201050f0604050408040b0304210e0d0b150d05151b03011206020f07 66
    0x107001d150408c40c1f003208208001c03c0c203d03030180420002e04503001007500c00c4500000245641141d03010120311118010b00d00e40200016070a5a00e2102e0701003080051000811b9000c0c181315081c0440307604161284103203800c80d200c0c01c40448c90141205406810b00000036545003031b01d43d0f2003200c1905418852481210088541e0281c240080d842c03500c9250f80781c2240c0c01400f580d00502050142e912840c80210070740750400b480b04000c2c0c924101440c83c00300ea045400b18504c1d503100300340010341d8000502070301c10407200080d20003c101c909401ca00303d603400c80f0406003082e1200045641c50030b00380d1140d0b40090041e03070b03410b281c1912908045051f510a1340d0483c1c4d40034070004100c00f010304000c003c1d440c200251600c035401ca4100c00001d0301214007400043c0441481d031300803c01914041e400895083c40207403c0d010344010318106039413180e000008101812201c03400141a40010602c202402e0810303030745290459003040e5005140fa07111f01c1048420590810a03007501460036400760007010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 753281160 1250 753279910 753279941
    0x9012a08040f060f0504080a11060d0c09031110080a05090a1403090a090c0509010f0909060609080f0705010c080d1503200418020607060b1008040614100e0406090204 73
    0x100d20384500201300b07000355000007007040014401804680008141c026070190400c1c418403160300c4000c00600c1e0b0f4400c4401ea403051134035015003a06519000060702007100d01500e0703140c40c00741c090400d01c500c601d84003009100207209080041c840500303650000ea0801c0c410f00407180708018680d01d081d008200a84021402e520100784401503240555080b40a4049002c0a01503000c0344400503085004084c0704034180100e0a1441c1c039103d124040c40d20003446d080e1400d2100a035074190190080f0750600030a102030044440304510418009459004c0710010b955107500b180c082e450f00b0160b60424001c150401d07840c1c841d0750400da02c014035900045c0d400b60304009050304141850002c0055030703100090207103041c240d100c0b04044003505441b100c0394041c1d031000c0e503601c3c80b0729040000340036412401d98032000c200081c404440d031141d0700324030551040f0b504114900c0c241d25041c001010807180640e0f490340c580410300500500007101c682080c810304000c00d051500b0360014003910504821341c42d0b40e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 753282410 1250 753281160 753281189
    0xb1c20090f012c06010f1106130203011d15040614010b0a020c01020703121409090a05310303020706020903010c020102221811070b0a14060609012a0804 67
    0x2220050801440241240c11200f00d00142d02e12810103402d004282c181800010104258200d024407181551200d12006450301484d20344ea0125106600714010fa001b5841c1c10120842d0419030044041d5049100300184a40c4002507486014410700a00403554646c4072880103a81d0301507000c07844c0c040c0480740801c9131511160075009190110800e10181154030418042005c1001d003980d01c2080481450028810a0454001e000500c070710410550030103a58003c22143d4040359100d00d0041c4040b0107d4044940c03070355040d802e010f00010700402260595400d41e000079011740c1c001d150b140c0c426103015040004034000a421076918104039805030350001010806006001480c0c41e04c00300c000d0000303462900b403c1261101c031140110643c005613880c8450f034481039003c0306450b120b0394854441040c2d07140c503c4c005e0b4041d10a060312041d200691350301262083c03901304180c0310343c490180d464034a0f1860b8801c0d0340300c210954029162075000c001864401080c0020003e00141411f000e0ba03021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 753283660 1250 753282410 753282419
    0x200a030b10050a0e09180303011418071b020d061407260a0903090b030a15060503010308070b040c080a0506040b0c03010302030d03090606050901180b1c20090f01 71
    0x1d2064246440c1d02004010008181899003084640c400b0550075a05409107554a140e1a000c49410643c0c00581c3d00c008400061000651018040f030450160b8000c05200c1401d840e403a0040801d41e0300002042c4400c5e1480c0f07089035515070402c0880d00003001da0301420b4080d2554030840c3e1407441c01654011842c401c00c4151900856039210824051903210101c81340403d80041c0c044000e892011120744800550051511035008403001e0070309598440c2d50b07810140c0f03540005040c140c001c0704004900300000503c042c020001d907070490b500809200d14003541c43c1d5424021010040c800c40f0507418480020540c04020482d1038260b6225100404040c1000d05011113800300051003140303100c01c20030050006882c04a080503102e00541004a04205039142074005401950840d64001034000000190400c0406802d40100c10402c0d08114840d28841400701c0044030001e19041100310005201c001807001c400141c143c001c1a070741c4403c04082e01c0010702d403034074291500c06800641200601 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 753284910 1250 753283660 753283669
    0x20a060305071e0f050306031002032503090803070513090c05090906030615090a0209131a100e0d080c010f05090d0c0201090b030601021606030e010f061206200a030b 73
    0x302e551801c40c3c01c0e07400d4050061002001d5581302c0c8031000c1081004030203e0356a480c20885121300d07082c020019034407850694200340c00000c0081c00ba0103c8001c881820039402c1c081e2165902140d04280340b9840c5503110134080d01c0780d500002500c00001464400040c85e451944580103160009540d00c075641d5454400b00301d01c0d10005490702e8866080007051000300c075420041a8000081030380c2030b0f00d0310b564089001c0d000740103003e20b09405c01549507180944000c00e0348441c0d00824070024201d001902541442a903209008082010510200c00c03d07001e0700e00142840032840c41070080900d8070107c050340c0307801d65020f00c5503013054640781c10078401000030910110340c215959241c1503108913450b4000800d500f11621940c6262100000414102c4c0d1003813010401300c0000d16201c1c54010f41d1000000d005042024074240d00b0351a000480e0f02221050041004032200c55881d060039101c1512000002c000c40c1c047d80d8500c981112502012550311409072102c00500e44000607501503013414407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 753286160 1250 753284910 753284927
    0xd060e011e0e071401200a0b15010807030b241b030c0a110a1e06030612021f051b0303100e060d12050c0a110a09020c03031f03020a06030507 62
    0x8402500b4550208a00100010288100c82d84c081d41d071903080c3c0020300182c90107000414100c0c40ca0120300806e195a03240058240d4880b0f214802d600c02a0b502d21010900d000004911240090745038804100f00702d01c0b0360031807500c454000340700000100d8204102f07003803d0000c009450800801048811200071084141ca1080d6600e00155140240c51100c0548803d04068024010700600100d41d81c90f480b00c1001c03401811401c401c3c0303e100c1c101c191528030030506d540b00c2d0900007420010007050458001c402c010380300354003a100cad204600c9940e41c0d107c840d84031a45410104002440540d4102d00380d0b1010880301034801018698a081c035000449055120350000800095684140501a2101e034500e040240c0c0003681da840c11202010211200c1c86440d04480b00c40c030a003030700300c0f0a0000143c0d4414152004032904440030380c0c1c0745c0520043c0e000e550f031403421640013400010903400d0350700f0030440059405026250800e4072540020101003654000d00006039450042204480d000740c2034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 753287410 1250 753286160 753286211
    0x1030e0f0c1507030804170d110c0f0c01020c010c060b0907260105060d0b12030c010c08150102071502070906061713080405010c0f1416090509060105010804020d060e01 74
    0x2e464030354540c6000e41030385401b80004040d0303950840d02c06c00c00d00c001c9050b1600c841a82c4d40c14040702044628050242c0c100000c0b24006000f4100c0b41105c0b10380020314004100c8060700a4203051102c80f0040d00c480c5091403081c0c4a0a4a501001c4480c3c1d450100701c0380700302c4040c0c4400c1c66041c81078440c1600054107400d10341e6903075440401808a070759103004ae00c1e1840c00b602000f040440f012004900c80c03034500d0402800f184804900d09004c0030041d002100d0400490b0b4030281181c2e40e40c1000240e04011102c40c0b40580c110520501c1030800e108440e122081e6a40100e80001c3e940e5655801154402d500c0000000c902d0030400a803080d80a41d9960815490044d04030b010a190710303041c00391700c50f074440d003810300407800c00701c004008202d640c000301680c001d01c02c002c004e40034106a9458071401c0241d07a40e07080d01d1001c0401c1070450380c82024000c03050b050003130031030f070b070a050042d02c80910240c07050f03030300005012038000044c0c0031b8040d03483c40101020000c204082c06089041000d13000800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 753288660 1250 753287410 753287449
    0xa061d0d060e070e1e060d020d02030d0801210f0201110a1b060311091005130f0b030103030908060702060a0b060f03040624050d020910080609030319090b130201030e0f0c 75
    0xb0b461716900141e40020f50004d4089400401440d26840000c14040b090720009405005482d640090b880c1c014040342d040303841d01020066420a03100240b1741d03100078032500034440b0341038480c0c200140d48510039003040d5541d542c045a00e20740b4951103154895400c080054640c048851040c06860382c18095081c0100c1c9002669080083c00c0e000209000c010b00d409104004001c47e20302c555401030608a0000c00003203c10811240d00c070340080016910900095001c1180d00c003001401c041c00041c550f100c2d0b503083d4050302c01c94031400b1416002e840c0c0d20303402e00d6200300140400508081528001c45c080c91080c60000790480d010003001c1c1c1301c0380b0b1050000020001081080220781c5030410300e441b403950704071505800780e40ca00c041141d083d2455000003616200d41020408900c80000007140a0808404c0e90194a920307682d4007415506803140081c003000364080819646400140010140b5205041c00f003401800546080d1409501d5025100f0907401800022b00c41e007880181c5484500b072040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 753289910 1250 753288660 753288691
    0x3030f0b061204151a1203030c070623160e0906030d080901020c011104030303180809060a0e0910030201080c0c060705030a0b0604140f0a061d0d060e070e 68
    0x800601c007405101411203000c01c802001a003006890340d1500e00340d00c84210f0800c0300c8009a136018043c0d801c0d03059000d019400181c038401d00e0200020550348901e004030145451b000042d43e450000d002e00b69982200050002d01c008404c0ca4000345051003460b161021450303040c903884000313111420a84040380075103481410b101590f280440c032160340d5550707424040c0240c2c07604c240c20360080c45042c9800c01c040d442c100c908002e05040310001c4c81100d000383d4082c480781e5403107201d111805440d1640101088800c000b150543e08100010f4200e00ca0982051805e042c0c1881c0400c04042084984620341c00e1071070414001c660b004031074030386c00142088089060403003100c00260782c0c0c00e020780142d05000c2f000c00095500d03145600f00196806028040d1501d40b607a51580c07401d50700c204000544a26801d603c90756407405d00250000444003151b98241424290a030070344c841100c4058160b4101c40000e440300041400b6014040d83e9041a000034501c1c50315280500c841d2000c0034100d20044032126 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 753291160 1250 753289910 753289931
    0x908190e031213030b0717010b040602071215361203091e0b060109080109020d08030a060909150e071217220303140a05030f04050a02180403030f 64
    0xb507000c648408000b01e150b84801040148902501d03e0b440141505500410000c916521048124102d840440720301050b0b40c85407008207481c0698002c40340181d01003141005421080d1030000c1001e80140d2230402200c0714002c01c60252803412060410b401140481d403640c0984a0840f40e00004e0040007500c1d1051490303549412105010300228201611515644107000c03c0b04294100201c17200c010f01c640225920b81500c2c516401c4500700d0202300340d0000000d0504040c080d00c020158000d010f008046c911b640d0360181600007401d4020382954500005c00c0c07a06403403095800340c500924208410103190002c3e174043e1411021740e00d540b07410201d010400b08411841c071003851a400742c0f216040e1104580d040b4514019114074018031303c500361002a4020042e007001d03042d43d02075903c16180150001025940d07220b1041c00e08001001000010911f00c0e04804a0350001c0c466000d0700d1044017035030005201c80d82854a00d10403a00b06200340410140c061080300d4400c28080d80038404403230007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 753292410 1250 753291160 753291163
    0x510090305090603060111030a090501030b0109030b04060e0c04060f0338090109020a0e0403020c011e0e04091b0e010519060305040c03050609150f010803030103240908190e03 77
    0x1038140c2d45008400200c081040350b8002c400c0001802c89a00c1103944030b020600f0001d145100a00c1124046071500102d107155501c940b0068080d43d8011400e070203641c4481e82c0d802e005020f80c0180480600540503186c0720b80ea240d0150000810740c0f48442100541142001c1410780707200391b244c0c2d00c0c241d11607490f204500304100c410105429049d451421554901d8a075070702400402000940c019031280b00807908400e54064640158042e508032041d01a1240c010f595000008018125024262940320b8415214528000c0300306c03030280010031408120faa502c1c221a2610220b0b00004120803824003202140c480d8413401030400315940700c500c1001195100c0305001c1c40c00b58104064a03040050288004241c40d640103540c400c0844010385403200d1030700e0b10740a85180c0c118503900c482c80424014282544024141e6040001562540e4650742da60b504040300403001d50390b0a000313000c000002a6442c40744902e001d0007145e040b40e0312100e2002213007038000d20500781820301c4090501140399880 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 753293660 1250 753292410 753292417
    0x913050f060106092108190f031413030e0303070c050126130618061d0303090c0d030c120e011715010806030705090115090e0106020a030521130510090305 68
    0x2031003401070301e1031300185034411100c1060500140180000248040081e2411281f03140c029141d070391041c40c9481e024104038240c40a80e4146002003c40c2c02c089045500100010501d80c0d200307090a2103410004400700b81940c00460081c2c0310001c820718100103c0d60400318038900180f8910000c15035510140e4183c90091028000a0141c800031100404101c010b40c803d000e14180180e1183c01c40e80d85182540c01380a250541c880310707214240d00200089000801c0c0c0f802118a1000307028000c42a0040c42034900503100c056042220a50501000c5051503190782001c50850f903c0d02051901100050910b03050a10703040100b046280401c4100141602c1c554000340c403d20700400203841c1c010000c4e03c1d1400d250880c560092007840009604000c0006207a1006c0e2291175450f4840d03070f03422501012010903c1400056048007030320f4000203100748010301707459019400d8550085007050400d00000c4e82207883c01030b004001a694014050100010860142c1c040404d0000030013a42c0c00a00702e02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 753294910 1250 753293660 753293669
    0x1e0c080108120306010e0613210b010b09010e0907030b031c17060a05040c05090415031e0303090c0b030405070807230a0503011107060c0c0f02010e010c020913050f06010609 76
    0x30044040f1301141e00c6504008041c1030028512501c444402e20a402104443e1150780204144200d6440c1520b071061012400c0c940c00c00d001c0f428a0703217040885d01d01a401090542d04112240544201d540d940c480703014000c03102c0d03950005180b6480f009040ca01100001001c880075055141c0300c80c032070340c460140c4c0e403424613034204010340781c0b64003021581150b51078000720390042c100966555400ea014025105401007100e0521018504000601d4a06030078003001d81581c4980c4a8440304003803500f5580d107014482d281c0010b0104864450b078298080350780248141070381c000140003d002c8108864405800104082e06a040c54001031700200304d420021100d500c054400140350580c0c1d0102604e0003404040c0c02030102d14000106600350340c1c03000c1800c40f8103602d412010041035104100c007480d003990010040c40b241c0c0c5190015a8600c004100e0541001030783c0040d080161107480005004032800881c602e110302680c940203041a1500e091040e65600102c01003100980c42102c00c403c030b0707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 753296160 1250 753294910 753294943
    0x4052112030f0112030c0c0611070b1806030c04120c03030e01020f07150903052b03020414060c011d0606030c01030b090a020f040b0408030a0e030604020109170a0203011e0c080108 79
    0x65001d1700d03043d5682c440e0598081c04040e0026000200c071504003d9400d0084200029214260786413400400070380500000c0301d03210882c0c5120b400042c20070800541e0011a50400300b030030190b440f00440d80d007030b201003170450342c510880008108150300401c84a40740c01d001d002800000300304040302503450000348104040d0405c200f80821409000324003003000765400c8000c0d2124680800242007001459108041e03008450220494140c1c0c4a03100340c500390345188041580c55907582c41000340c02d07002485030030419541d0710f80c103d0140c0c40c07052268a0907020315000c1c1c50b540c90140e04142c00c0c400030a800506040c1001141c0c141d40d96181c0800f640640050801a1a0f20b111852507810307006035003288205460014010503000d0000002c0c1000d075225541c2c0d024524a25002d05441c0c01098400902046c2c006d1824042e030070034008a0074071205440125203920082c1d0f000242514040707604880f01e4a910410705005c079050740203010f407030a4641803284244d4541180180d03980500b0310700c480304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 753297410 1250 753296160 753296189
    0x908040f1d15060903010203090706090e01063905010501091a03030316020a1e06050703060b1b0c10090e01050603041e0611121501110a08090604052112030f01 70
    0x40c2d42d90f0020f0f1102540c024000b1910303481c1440c400b41c3c1c0d8818070702031000400c1d648800004c2100c69040d40505035402907986446000e0b102c840701038440780a01080030742c02200c20707040011103c1c50b8018104a40500000b088a5140560350304c00c40b4080c0181154490130041c55203000c1d28000b003100d0300206030a0066012020380036040341004542040100400912144c0005c010003000e0390300c034014000e5600304195165400141d04907900792140c1080ea410500039100b031410343c140703c070040010703110079180b50700c480d07100040c0715000322007603d808920000030070b110440c420b04401c2d02412041c0e4055245040a0301c07048502107550910b80c1300880030085800070041c040d04145444828030301810303151503c04a0f8003180b00000c8814140e009401700e100c910303940c89200c1c14404029103402401c0d1280702501c03489031541c4414041500403404000c001807645800c40d40481d40c00c5c003603003109210b001c090502820070480c0030030100500014030622803c14058020b01e4111002c2d410786085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 753298660 1250 753297410 753297451
    0x16091404060902070b0115030c1704260406090906030201020a14011e0209011214061e0a080109021005030f0c0a1b030509030c030f0325060908040f1d 66
    0x1400d4642c00c50010240007060b00c40801143c1c14a440c180c900400150242001c4804c01300c1c00c54624a80080c002a070551101442900b0b040c1c501c8d030060b000c0c0081492502c5d11529290307600705501c60100e86104001000c00c450342c3c0c06a03418018020b00501846032901d140c00007580d6150280c80a01081d984040f00d4039096025400120040d030401034240d602910f41d40c00d18000c1d00b00c808558007280e00c018290000020354400c0c4186100d0b0208400c1c126150784080c4416920840726140d9113001c2c40c00030500c0c3d952811050303001003059400215046103684180700c580340c2d48030a400107100040c82880302160000d5181907210465001d20307070b203c20034600212101440fa20480e03048410719006581810340c80700003800070140c10780440e444000010203066480c00c0400c40090142c10511503203200055100c90003503142440800e14402000c0e640740c2000b107540c40d24040702d154400007400c003d00200040c40d0303401411000d940c2547d415040140c1c0310000c034010215101c5001c040c14a02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 753299910 1250 753298660 753298669
    0x50102030403080f2a030406030614130c0318080c12130303050904060b181203040803031302010e120f010f05190915021201030605010b13092307020c09160914 70
    0x454030b1791888602811503071825440740d1264014060400040d09140c008109080c1040c07440f11010b8010780041540c4c114400007500170701c60045048101600c4020311112500350301c051656080c002c010240e0384080c0000040d161011010300d8030741d44002840000501c85240c4141c0045942504240703a50744290700001d4010318a41e000f1841e0584082450f440a00b40d0f40d901807003032f00040d01c0022072601d5080b1400e1782c0303020728420481e596004000007802e1984d50a000b44080388181001c4010b042100700180319034846808100b9254810244264020404d02604a20a0740c00360100710034101b10303c1c144c49500144582141441c0c50300200010851002d030180040507a030704086480d0445100a44202d0307500b84001e17600c03181890004204000e04104896a0f101401c0b102010140ba10544102612907494540410404520050b04c3c041c0000c0d83e882c410700e0b4580c098404e9880510801c1410240030b400c450b4488070000c0e0241500ea00b0401503000c0d910389044400c1601d03c1940000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 753301160 1250 753299910 753299947
    0x509091509070809032b0b010201020405060d02090301150b0304030e04140402040e1203070309030206014a0c2d2d070b0103050d03090c0509090a0c031209050102030403080f 76
    0x38040c0b540d1203e030a086c006003407018401101c9800c10203200d50700054004a09078012070140c0780d80b002081015046d99036070b9500a06080d400640007181c81c403026905818008200d0b0702c54680404004200400c0661180301000102e02c202ca0400c29400c01420390030040e100180020300546e500d000c0c603081940100300a89444091805495a0303203810309009002c0e100b1420102c015204500010800b2a41c41c94107502c60040c01a0f000d6580c9404005000218a03000340d4601c40f1f140c0c0701088503001904a5618071505e5040d00d00c44d40e403440d4103c00c0f041c0240143c040200c00704202128007088180c84100d600d403034000d090700040f150f141c40e00203205803076241c0194400c900002d070360710401c114042038030b0490b801a02690000c000c02e50003a400d41d24001002005ca0b0380300030081c8814640740300000e402807410400c64609c85426681c0503a0b00026400030317201c40c169203405030040ca5011480d1009024284041c50074a0300d16a00c1030018007030f0310b49030300d001c510214607a2001c04481041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 753302410 1250 753301160 753301177
    0x201080c0c072403110a14040f3002400c03150f0e07031d01050f061203090d1407171605130c0519050909150907080903 53
    0x40d100110f40e41c02000d06214902c000c0c0d5903800c410344031500c80050007882080004001409118038010b00e1500880366440101002c0b02841c00512000c10f022220b80184000391201c141100086d104040100d083c4546d2903e4801e03410003004031900041e103420440c10380c64510b82c03929034400300c000007035194101d0002400900d404240c00001c0304400503600941210855910100704020031181311006e40c1413075009455030544401c0e000c005941780034507440e0b800305280c42c0000d52404404848550f900300c000d9285601e03034440c0180070210070169143c540240d01211a07406002c1e40c3c0800f19100d00940d100540320700d10220703c20040c0145114044105001e01054400554032018101c12003044584181c401d441403480d02c0140c95001c09401064039801001040310041c41170424024000c441c00030340400a007072040d941d0020481c2c0c20030007204031a445207238407003a030203007802140f2100134480c00c40e0005a403004802c0e80c031035580c05034000b0103a1030300d07030300a41d80d21500518501c40daa48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 753303660 1250 753302410 753302413
    0x191427100207060f06170319050412030e180709050f040b031510140a1401020c0a091e020313120c0c0609031109013212010b0111190201080c0c 63
    0x80c202e04018550388020341c0e40c10b0501d410044542c079a10101245103030400f0700c41082c1e0003001015402d903e10700284118542c18074245240940f203001c0e040e40383c034440c1805c03404110032000d640c01a14140c0e489400720002d60034000e11078641414002d00528451103070318014042c8890303425071511386801440c4403200c081c04441440d0b24807135005941c518215008000c0c071104032030111b03180100101d02404034500510220743c2608001046c103844a503040c509040d03204003a10004e05840303071f008040c0100a08a000109000c0f0100d4030109400c5002800b89001e00c10020056100b404900d91b480441d00203080c4240e035441d4030000d81d2041d08110019142004954000030102e5100b610082030f42d05c44c80504248003e00341c14400d02080a0003114060500b20014046070884215442a448001c500c0720042142d0b46011440015100d40d842810340d440e0a45040a541c1100405050094541c001c0444401c80c1c4031201000701c11040090412500401007008001c80205603044044d4800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 753304910 1250 753303660 753303667
    0x603021005031008070b120601020114010b04090b010309120c081e0d0b0904151107140f0c15040504020f0c011503060e030a090e0417031914271002 65
    0x2103028059810860700d42102c0c02001c0404201040045204411905803144840c02c12202080328505180001c06244c1159a40d20365900c000144420311402032070307250070381c903900d0303092030f203c4402e40d1a0945024107060401c14810000745200004070080c100503d401ca00b06103540c68180804c0c45000003e5555024204407803481181c0c0400616200c000c00c0010041104000203001c507a440861b0b014040542d040000242c1c070b407254000911100201c44902d15010040da200c031802c0e5080c403402c1816500088400140e01d0b4100001c603030555080300d00510716100410714500601c0741e4010640a542c0200310307505542c00540a8450b031503641d5000b84025413322644000f01e09451000707490081c2000382e4901c2039800802101c02184d410b0381d0f460407141c107202c500b401d0110040c104a918075010100c1042101042d0301541c00380c218041720040c6010781480120554148826450000319400d060001001c012050760f00000d015100682c0b1044808070710608003512403080032103460002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 753306160 1250 753304910 753304939
    0x30a110301030804051906172a0304020a0503160927030201020c070e1b091201242301080403030e0118030305090601080303060d110a06050403030f1805060d060302 72
    0xc03000344c419140c0568441000c00401071152007044038500c10000494000c904800003104009140c1d94082e03504000d003541620703e09000d8814016003100703c101c50070044284030443c42c0540c0103100410b0100c006019a08100c0303009040c00c401842001a46035039080c4051551881c0504008203560354810307005200c002e4107001e0302075030103415643c600d405166001308900c5d404040c1c040c0101400101d035a000d8510320750015540c2d00c090f500b5640328a80041c070204143c2d00740030f011003a5540c0d01010b0031a03107000c000140105ca250b08511545d08030a4103c3c822407402e0014802070850910308083e50b925107040680050034001d4640c1380950034001400c0d4071244149444000522036a030802040d03461a03030842d100e18003800b40040c580c0080011070351603c0c1c00104810700b41c0c010844043c2d800326890005078004080c2d400080410f0300801d00300b0a15030011103e18103a51941402d04c0d0343c0720a559102c00040c6903002e5942304c0d00b80860111a01200f41c5d0040c000340d40c7c098901200031290 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 753307410 1250 753306160 753306173
    0x50105150a0c0c2c09070b09060f180901090902030d0305060f300307020904170c010c080a0e0c010903150e010e0a0c1706070507110301050406050414160b030a11030103 74
    0x440b04850506060054840340034501104c03d98803a40c0544003400e9010308141c42100d240d846880c540e60b22510601c191003d481c207040007030100c10344600450110750070705c40a00c4060301d4160b201040844c64452100d001d40c402089108159190346000140b95072440d000412002c40035041079002008001540d066140c4604401109414031002d0122454158400b599911450b90000d41000040700403500145042000524622541c0070560500040040190841c1c0035210508000f40c030380428031600920720710910035031101400140262840e07442c000382040440e40b200500301504840036040c0762a580d4090300144030840021b000b842d40101441d540e49000010541b0000c1c0d0310400060348008296180011a8040c80981010703510703000151840e400401068481c0e08031507007008841d03902032143d80c0c030851040c440021541010300380301c843c2c1d003074440031511560300400c036504000341003458900868040c3e10707009540c4d60311031414034060440c45a0416202c0c4001c070011080046 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 753308660 1250 753307410 753307439
    0xd140c010e0a03241b05030a050a0e15070e04020d051501111b01050d020c012004050609040b0a05090f160509130b04140c070c0504050105150a0c0c 65
    0x80076039404080100d0001000380c400b41501c0014041e42a42200c03420300048804a641649440000011030204030300c0d500f01328400052024000803000000c00130300503a0ba115290300505045400c1165010400d20282d071410107081c0741c1d2194410400080d02c0c1751044072403070000c10000d807066448100c170040140c00ba0201b902d450a10710b500081c04c1040303500c03607070070400448110070060108110314800c500c1c69089804040d030400c1002c00032039102250500003007419101c00d000003e070401c0c84a4464a90000b0200b142e0204002080704010960b140810b171b65655008840001c8c03280c00e0074001403001026540599004400e010401094031101e00106208402421240b440945891001c07541445042e4401d0351180c00d0302903105d051b1849501980310ba0001600001c0d008040b0421502c2d0080211030104500000040c0401040b240b51000c20007480c060781c0502032541840d0014249a4103030503420070007003012030019545441031a1700038420b1303003092554000f6a01c402d00070200c6c24 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 753309910 1250 753308660 753308683
    0x180a08010e060a091e260319060e01140d06151806060f0804020d2f040204050307060503041a0703020d05090a0b07050c100221060102061504020304020d14 68
    0x50300000545841d80c41c004c8140d420350010840a0711660449546801c103001c1134165002940f40c41400d5424000312030501c80c40c0c80c6c00514039220302c0c00d1440c642c003600070b440e5090b01950070b0080c10440c1000c0c4d10b00813070544014945684070f500001000c00c09034220150050701442c20044084004807030f40103088141c441c41007400fa00503042660f880161240341c815000004c0030302280c540c14602c10192240c003e440100214185080c903200c00144010050020076603852403644140403803084800c00c2c0c1c00480940e825400d09140c01c00081d00e03140c80303110701c400f071220010000f42005480b00c050404186140b06a403c02d04290000070000e410025444280d549010082400035900140d814440d42d031050b03158845136201c010456070b6400204aa002d0391181c4d01140d0f11200c3c441c000b604c8550810703030a41c66201032440c544c1100d0000030388010b0640d0010b8091100500000403070103002d007802d46015030b076074803144049807100c01c12040261111403c1000380c5182e900100d85001a075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 753311160 1250 753309910 753309913
    0xf0602040509061f0c0204090209041109090d051602060f0310051309081e0910120c0e0915150f0918070f1d1c0510060b040506180a08010e 61
    0xf5561102030019015509036400c0400c8601035952030310383e104200c00c070078461010f0000f14480300360354041060a5015101142c120b007890340c0403c2c607070070709450855106081c60300400c1d00d00c0c1d510401901c64070450000c0840700d40c03111a801c0c10f64642c1c1040343c0940040e144501c0c2c4c1c03071508030b40c1543c0103006402141c0c896031045c12945401002c500070001c121b50060031444c80c0c14411143c030b0802881140604e124500184044000c940d68251075500110007902d480d03150502c20020305080790700b44086003051184a54285c0c070180c481c495070b5a0320002464400111100300d4002681450300c440d40d010521400080e10265800000d0140c01588000c0d110592203a84400089148110881d10200041d2035425100c85140c403c0301041d031981030464402da03030140030b180401c802180d404180350035680d07802161800c21200304100c900c1110182c0d000c01100c1e082002030b2100d4411407052500c10840804c2e05440203008c031081c02d03c01c1c01c0080500d0611170341c1c2c40e9154040c004050202046 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 753312410 1250 753311160 753311179
    0x1d0d021011070b0f090f18010f08010b09012103090801050c0a03200a03091104060b07020a0608100b0711040f060609090203040b01030f0309120305070209070e0d06020f070f06020405 80
    0x4104a0701628080050b940f80c990510300303200301b4026404566440540d200344205412a0641c0c1c82400080c0a820784003051071045007080540303420341e000343c002580103940d41c1004000c03028041c14891000e00303030400f02c074560703107480d044c11501d80119801408841d4a0402803001d1704031134200a2041e0449501c0503c0b031481d840c150000114030803150780c8100c01041282040c1544254401d010180c49141810400101c41000c01e0031243c9035080105100c0001a001b42903203041c0714080003e01a0b441c21204500d441c1844400c591414030407a240c203507020580c1e404000d103a07869411205005041000044400158040640003912920000c90500355000c11407444a0089a01c560341001c14005030364a140d540300030f030a2642d101135040100a0b80d01007050072180c0b600b1032145019503246030325410786004000300118007a000380140300603829103040b07c2c1c8480070807005050b0013450042e06c5070312103a0ba0341315130b10501c00c00400d01c0e0f1800321000c041000590281058407000d4610014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 753313660 1250 753312410 753312419
    0x140603010903021011120115140301150c020d1b03060e1518011b030621150c03060f0e010e01060801080a06050705040b040305030a120c1d0d02101107 66
    0x72541c4072080540144c104903104102e0405a030440808061401d05103860104564048003269a00380c00040c88161700004440d40d04d41d10075144841c80485095003855540361200310800591280c40d041c00340418946c581081d0b54070f46070700045294210500e2541030307120420345646514580421101645000c00c44a0311520014408219213007203000c1c4821900e40000803e6a141c00e841030306565925040002d2280101600c05010096161001701d0030b80e08109030404044008248020900544440036002c50001c1103c003100402c001030000d100300045508030094503154000c8410000040000107440c03004411241c1203a00c008910500c2d6602c4200440707100341c01b88103084040e1301042500d004a2000d505c850740207005070601303500e407642d982d000c0300340c1d508549d005544a4001244101c07060b9003100d0a903c03849002081080b40081691000d0100007040700050040c4d40070500c00d9429868006090190940040c8100c1d494011264020408103242c1003034445402401c90019 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 753314910 1250 753313660 753313663
    0x90d080d0c032f040b0a050703030b0411040909020301060806091b04050402101d0306040303090209130213020705010e010908041a0c1507020102070f0803071404050d06022b140603 79
    0x3490785900203440b030708183e507404005003040f404000c56203442c03000c004c000303034204076040205850714481d182c941d120030b06424064221401089180c2c0285e080c11110510014050115000e0b140c501c200080c0d41100d60011900400d01ca030800b204902c0f46000380662203a00264186c580c081610320b14444004210a2000b550001c0e140203402c80b00c20002ea500322030064956582e00303100d421b00c10301c40508120009241c81001e4034280c002c030307546d20046025401d24070341d43c60380080d04048001c20341400b640402c039100200290440d0310f50780400c1d002c08202c429006090001d422100074403020410f81801d0b030300d0f030340184504942d0780203074502c8980303564078041514400c0507400064420b40b010008801007810b4020005c2045550070001c841c0040c0181f07003031a00f1103006009145d12480c110902500d000b403080e000300d4a204c0144000c01c4035907551480b003120668002d1002d83c454130303000f1000f241622054035482e5503030369001c441030000089902042e0711041c00c000c9080292944000d15 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 753316160 1250 753314910 753314921
    0x105041802030c0603040213060e100e13060c05041a04050f03070602030909043e0402180d0f1406070806010806011d031204081c0207051014090d080d0c03 68
    0xe400d0b0304519103a611034a41079016551150019090423070441302507581c1402c40d10244c11508008030300d0390a026008a4054654001d01454160450b0606103c00204807080c04104001d00d41a1500046003aa5102c0e206a4006203409040e00c0e000c4448403070409843c0d001070180c1400307a86e0000450a041c0741c0058084100d4540d0307000345213884080c030280044010010804e4510304028410041003100d104028907a01c66118400401c0003201c801c1d03001589041c40b034152040e0300500440c088810720384042100300c0703412038080301300c005540b90182d01c5002d4100050510a03045a90503405900800d80d40d1040e1011b50b560141d55540c8001500c251005070b41c46030000300d040407548001810b80305031860300300006040315074414001c0701d103401662050b00060850741100c000c00820641912180715092200d001038001c903810407020402c03c0c01c003142c010080000042e003a64082d481007045800400c000781262110382036606103104268050b00441c00c2e994a088005410705102e4880c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 753317410 1250 753316160 753316163
    0x9041103060d0b060d120201050a0c26310b0702061324180507080d050703080a0f02120601080f0103080a0e1207120c06030e030430050601050418 64
    0x2c24107240d500361204441140010300c555000303c440c0c8540700c0400c07810a020440d07010981c1c008150b51600d1812841a24902481e500500c128405580c08402c0d2010050621000012818440b0350b41c08065071480764005104c00486101080502c9080500c40c2c940301200340600d42541c07080c3c42d4104100d0707443d0003c1343d040c800f41040803442c40004002e0b4041480d10480c10040020001c4400d046c2c07412103440d1b01a680c0c01c2591900404108507003445404000d100b820003500429602d404c001c4c01e00c3c8070f940d4000b401c0248030700020308208a103a20804803110f00010454443c51003148065000c030b800d50381180844c000900103071401541025072030689500c040c05606009000310151080d00300c00c0f4500340c3c0076018055022090400300590801484400d444201c2c00e009030030000c0704055560840c100f058208444007480007400401c6074200c861407207561b07a01c02001c1d109204104002c500038402c81808942c514180200010b040d030507100c4c2200c00f00003141c6443d004c51614002101c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 753318660 1250 753317410 753317419
    0x3040317010807030213020c060c1b060f0c031b03040f0606080303070c030318080310050103110a0509100c0609061a031b06030c040b04151412041410020a0201020904110306 76
    0x1018001418580100c2410f221b080c0790260500440e61010b50400400320355041c1c0e04500415100d151402000110303001e0024240542180d0825404422100314000c00300304500c00000080fd460008801c0d05424989103c00c110346c881c103191038055261110240f040e41c03075501300303800403603c07070b10120840e4001c203411746801100e44601d45e01900940080c160821060400c004014003240d03504c0000e5108461040d0160285c0c2d0814001400712603084046030028141401300d58459a088000c0318032a4504482e2000c2d4156840710898480f104c81900a0580e810032a58004000d104e4004011100c55040d81c8400511580d041c190b480c002818544102910340e900342100d0b0401c07000464015200c603124034605601e45142d81d4003a40650320240141003100c0e1021452540508030000c00400c80d440d161600d004c480c02c020744614040d00140c042c41c4c1c2ca140185042208110305149064001c0003036403100300120019000390420030000d4091400c00c00c480b00b0800d4608110303403007600001e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 753319910 1250 753318660 753318673
    0x4030602370c0311030406110106060212160204180b0709060f050d020f07060204060c0314120109050a0e010e2803021908040b03040c180b03070603020705100c05030403170108 77
    0x2404845490301410243c0500c59401c001002c0d0280520003040a400c0ba074507100d0104400600e06400c44d0483e40c030030021904410741038048100040c003207503074001c3e0481035012004501c1c00050700030a10748130081c4203000e40d40049010001c400316181e100307074a1030b00d400c0d0000ba642c060a07105440400d482c1d000040d41005081d40840c3c603a4080c00303100401152150030a615552520203e034800c3e0002004030300c65104c58400c05511580c074651100440000c0c50801d402048403c0c0c0c4403906000d450001901e50002542840302580304514001c0110001d00a03504441c0304261154400f61013001c00fa0102c4101c0060030802d1182a100158590300400184e20880000651400c600d08200d403100010000080c600c0c09036001381d400340d070060302d04012091070a034035010002d000b51a030345100ba0074190500b150b56404a82d001c201d0741d02d0b0601607031b104c40b545080d030709129011001c1c0030054580101651001d50000103184103502c2911480d0035565100d601c0f4440c2c04017407103000300a03070054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 753321160 1250 753319910 753320017
    0x3371214060916110304090603170910140d0f020a02191e03120c09061b0506010302090c0d06030b04021507051f060306020315010e01090501020304032604030602 71
    0x10140d10b10078105601d003c2255045221105045a0050788801c1d840d07a100c1740c061042c405901c40c90078107114641482c0b4507004004bc04900307034171880c04500c4103008180390316030b01c04c49842d000c551140c1c06441003000b00800c4e07003010354004d402030000d0400510401095a20503854040040301d01074100c10701c2c1580b04000c42801c3d8496a404904a0811400848810b4a51490300a125407039040e07407184201d03d814500d00034660000803c0c03011140c0052904c3c540030940c081840741c191307901600c0e104c00e15910102e8076602c81c03240ca034400c012189011400028449058040fa018a1080710510345030b40110b80c0d0810103000f601005031543d0000302000d0f890b130f84841c1411303081d49034a42c8045040c0365280c5800c0c00b2030704212107180606048049a12166a2017120812050790900300404039a0038240001c1d0307a4007036030000626182208600c82d00701002045002141e2222081c125591034413890200081d42240d110144504215a0300c80b0b00030007034100a42c4c201c041c02c0110184240310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 753322410 1250 753321160 753321181
    0x80a0209040207140a0302190201050d0c050408030714101b050304031b11090a0203010b0f13080307050706140315040b1201051620033712140609 64
    0x208510316445079003007001500092001a00c0d0742c000d100000901141c00e418240a41044000c1c4260118000b16020050060f03822505507801d90031050b40c00156030403108429509880340d40c0142e0403a00c400b0803c2402c000d80f100102c08800700702410741c0d000501c400480026a80600d0840384800a000e1040c1c1c112842440070795801800791400b05082c0b130692036504d80c0ca0030305c02d40a403200045103070b08152500f020000c991700400d18070800c62540d850400421003d010308003841401c11030000342c10060546030910000604010415030fa51034900340340990f5119218817460b0b01148200580310740c568005001c0e40d2045441528203030304407181e24200f00041c40070079040c561203c40303680d40c00c980c00700921405100e0080d040441020a00d54a0003a2840380214030341c1d41401503441c2c0000c860603020064400d5070210038425a41d420030034410b085091940c409007044141c0c888104243c0341d5114440201074043c0d15003c108041550801100e00442210300b660044680390200c0c0d0700e00c11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 753323660 1250 753322410 753322417
    0x91e051509030712090b1809070e0a0521070b03060a0b0a0507080901110a0302030307030e0303040c0e1b0f0d0f020a022509020f09011b03020c010c0822150f080a02 72
    0x30300e00080e5054070340d0103c899a42003440008950080720007a07d11501341601019004039090410707420420403078000854650071400b174a8000c902c40c0c580401d4046400200d54240026102968111900c406000050b508100c0711640305c0d0301d1040001845469250407504c05005603039515150801175112400c580d802410440d0400000c000c040c0d11800c814841c000e14203102c1e602455403810030410003030644210182d1092190010010f000024407c4c03440b03482146d00704442000300c0e85c1c41c0d03c498500d0599464090580d0000096203d500e400300c0e10003021030504e04101008040000d904880807400764101644c090391101c00c200b85109a00d05041c2a02c01c480004514015243c0408505036040140c11074150903001c144481a580c105262403160136a2220042300d00005031002503031940c40302051414020a110070b1400d203c08042111010000c5900780320700038020070451394001c9041d1080c4050010101240c250840c401c4012060404c1c03240e40b038020741c2d207031001c2c0c0c0c0b4002d61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 753324910 1250 753323660 753323693
    0x61b110a08030c0f1801030507111009051501030b010317270f0301090c050f04020307020307030806010c0f140d140d1a100504030b100302061903091e0515090307 71
    0x350705101d01d41859040b14000d2285d01428500070080d011210009030139500050303d44028400c060005000761580068141803009500c03801082909560401c1d80c20b04000714120814402820001710601075901c403841c2c100ea204030980e02015100c401200e0050088005c1112820040e258904251000c3d461035066030800030301100c105042440080d0031600e40a104458205000408024a28100542c0d0502c000c082d60306500d50316250000a4503440f5500004040c400d920001c1500c0d644142040490641c0c012444001010b01c0e05240c01e003101c410f0a058014459055524111403051011540005008414a003014014841c007030140410b240b64a60711110840c010502d0741d5041144401481c440d141d20380d0b283d01710b00784010000d4000f8441440200c3c0c1c1d41c0d0400050311410106c40501026560600402030040c00840c040c1400313050240000541514901d804515541e20b60500c6206004880360138011400c0b61059590865003280650003d004050124141c100c0c00020031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 753326160 1250 753324910 753324931
    0xc0c0b04170301080718110a0f0314011d1f0501200303070e01090801050105090c07050a150e0d020c13050403021608150105061303082104061b110a0803 67
    0x260300108aa0078641c00c260720103281d07035020780d82c06c0201c01d00d5943e40e0384000f90f000800b4401d08004c07240c09060b501c074401d101030411840907181d1800e2482944002c80c41e00d00d41e14605600c3d6502d0107099002469403410744000c10012000c21460191540402403903541140908a400e10300302c0103542d15500708501c4034800001c0d00b070310185514280015482100203445102c140c4460400041245100b80c02034001030703141c1030061040381e6880c2c0c4071550200c169500107590b9017552a100382009668000100325441210400303411b1501500520b10440902c0e049480040b130714030040780e0b6000401e4006030051034404013414207100903002240d105010780112004c0340c0c106085000e0348141c42c0d014400c0741d04409800324510b84440c44090040c44100d4085080c9859065a5024111581300007445802e0001d213940244c0580190901210024003540e03249203030500700140540009151044206840311140003418098014000c40c0300e2401e006004802056039581d1a550020f000035105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 753327410 1250 753326160 753326183
    0xd08030606210915041a10151d040603020a0e04031b150501090c1e020f0d050705060a0c0813170a030c0906210221010b030103150c0c0b04 61
    0x141140226850a40769982c004180c09103400d41200341031004801204021107005818440858010004001d00741900300025086403a20035188115210943c0980c2004242c040900909034000c0c1007454031070b500d03850080c00103d64104020445295000007940205441002d0011100c013194880e072081c4a070074000711013540c41500d40200b90a40754125809000c0c8101d26205642034000c1500500004030103100317040e43c0b0807001d084549403103a5002d0b43c506841c0590750251003003200140c0710b4902c1095407a950380c1c2c07280040c85a0b21140c0159824490240880d040d95140e2291120300200d81ea0b803120551140c00e00c40741500e00a2000b030790120005040d101c45094140001c1880c284203840019580034107890261010505501082c244040c45411060140c03207423060801140c074420700183d883e00c1248c0850110700c5540c94079560842c0c504000b0808030022001581030328001c9842d0180680c245645009075010300c2c12600018484106410008002410668000d807058951022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 753328660 1250 753327410 753327427
    0xe041a130f0f05101d040c050d03180f1a0309120313021e040f0501030308010611100204060512090723061e0301060f0905090106111207030305010e070c020d08030606 73
    0x9585080d524540c0b2903c0f034010400c40e00411740f030758000c6240702c0b094800321490300b911070b2608a18a44119401000c214241004240c82140862045910b40c100c5505080c0c40d181c849a0002c940d004d007003283d410310940c0e0906c02c6403100941e441401028020001840034100d409425000030b4401988842d190042d40c00503502c8040d28507031201032154940c0d030703140b05408210a0f9009130103102c0c400c41c54400140040b031b51145c1c00605403001d42c2070804000100e0080145000200d50310041e25034804078002c100903074001c0040590001640501d80303640c550306200c5440e040d50b48250030540c1d10002d14010800c4a03804c414016100c020081400d000e403407041d981100503007000e00010410000014060541c004c5803000c1544440d103003007990b107818000400c13410b09041c0a41d5040c442030055681000c2404c001d404503019008412603150207043c54040d001c2c0c9402e005540c80f4400440015049621134854040744d982c005204070303c0440d00fa100c441c0140c3c0080c102c3c40d000f550805c000d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 753329910 1250 753328660 753328691
    0x112030504080f16090920012007050a0b0a02030d0b130f06031b060e041d0a05060f060d02061611120c03280b070203190e041a130f 58
    0x41001d00700c00040e14102c1c4c540701608103d192150003030b0b06403500c1c240342403012820000c41010425101100007250070905001a0380602c000c13003541d445d00700010803150000c4404074400303085031400d1f81c1c800009030f15464024924010080305800603841400102c2000c1080d070400441c82001900d4050302098445541013a292690019200789403030348400c100304081408201d54000a1002c2c1c03602c41d41c1049002441c4005844080344600d031100b42440031508400d1042c00300302020421908500101d10300640c40300001c44403221180c000c0c1e4005002404c0c04410b0070301050317006003841d261042c000900d80711020110340c10780d0b5480b500300c013185d001d4a4001c0d240014100100c0240041c03a120001c02d032400129096010135a903a0395050303100781810703103460b1a206a109408281d030366100b1904a10358011000150715400b0000140005c89030480c0a600380c40c2070560302030000b07929040d000060a42c07000d03011900005005103400700380c2c03025801003100700400703040402c4040f854820360 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 753331160 1250 753329910 753329923
    0x3081f0b04080c010f031811150301030311100504020619140309011e021e0c030d0207030503010e0f0606221502011e060305060406090809040509070f060512011203050408 75
    0xc07078190b8411404030f0307125078210000c605610903a01d8180039001a10040403041d07035070404020000c481d400600c2103e41e0b182c1c0c60030611840b460b10074540365030703490034000d00300c0c152043c8958490280550713150180841d40101442a60094000c501c1c2c02c0354110b40c1441d03a031038034400404100343d00014448a03180b001c0114041c08510b00040351000c4204a0460004800d680340f030041c500c10001c1d0b200b4804c41c20102c14020140300003058030380c00b070154220709610030f80e92071310703041880003450070200b42d046000f84d81640c3c1110078158442c2d4403038204000b400d40c1596031591100e41841603403540740504c099106890030707801005014a69440b0f5401e80c90070271440741c1000d45d440c1c0084100c0046402000c0e0105403007010103109852650b1280d03074550401030800303041c5540714204a001d01404c2c0e400c07100010400b1380104914503280902c039444c0c240c3d90068a004e520014000101c10384a103069480342026801034050036482c003202c4001d4000c8603e001c409002c400d110009803c0e01c288600c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 753332410 1250 753331160 753331169
    0xc261909050a03023a0f0c05010603060603060b040507021b040605120706020d0906090e0703240501110c010909151d0601021e062e08100c03050403081f0b04 69
    0xc01d050140d0304c1030f41c2c3c05880c291040702c00c400314074051220240d0217000d8403040000142449529500790060880b0280318000000d040341d82004e000108120716030340180212400b440d0b0400006130218100320550f0b006464602c0141d00c0b003004c0700c4d0700c904149024a03440c8801400001e000303a43c1c0d40031a101c5240320340311510765003003140c1c00c01000340c051040500041c03107407070202c1c0313000e003440b10207010381c01980107500c2d903035606000081016000341d1000c41080d40350128a0840981d03080d5806992103980103d5000840c1c084101d001d4810018a01c8081c2405031140032229007010381103801800a20703840e04c1004142e00b4005219440100d440241c07031a0b4a00300c00381494a03c0000e841c0c2100b1a0030740081c0540794040311021a40030402c1c81c4c10034200740d146500b8803440c10620400c110340210020501c1e5041d200010100c900084800780080c40d50340c00c1c03000803644a41a000c540d804c9a024010800b140001a02030f980100701c1401e11685560103070302c2e651a003075401d0903504685c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 753333660 1250 753332410 753332413
    0x4050a0e07091506090303020304060804150204080307150614130207021203041a070215160203030a0f0305060d0b06090c1908090f060103050d050903030702090a0c261909050a0302 79
    0x450304080d918603d00400902414100308111610f10b58000b981c85c8642c1c49181c080100801c0070900b00b21030080c50310301d0900b040005540b515191b0f0541ca440f0350246074102c401b0640400501c0c608100da015110481d81a15a5040c08035140d40600090038072442c104900300750700300b006c07a00503a41d200300e00b043e10040c3d0005544590418000c80003100c0340c40c41c2d40e00240381c140000d00043e41d45001200b1101d0b98030810648420203240302003c0c00f100040d000754580000310310000810351100c003940030b01400c0d54080c00651544402c0c030034014109240508900440c00c001a05420000c1070103400c07014591035a032501c5500440000d140c08036880c840c0005040b0020b001d401303001008015a114517840250901e5459641c1e42941ca0304842c9a43d01480400726410b140d40c2d40620645004030f4029100d0080c070b15061000a000700b88940310f81c40803401c3c011485050b44103250b0100000301124800c08a2038440206c1c00c600d8404030069410030a80f90512440011000e01101c40e43d82e20030740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 753334910 1250 753333660 753333671
    0xc150702130e0a030c1a0405032218240b04030309051225030209040c05030106150f0507020a05060d0c020d020102210a061508090c09060105070204050a0e0709 70
    0xc1000145002004010181c0d41040d1858907144400300300c402d90360341e140c14100080119450b200c10811410080da41001d03a08900308018064040010003c0720094503410303180d202080b03170301c940750003850148000e5282030581411110030700740d004114101f91402a00129460350302c1420010a50340c100340145000031a00708105600300510b440544811280d51408242c2d1004081e954001c0440e040088002412401014804881440d0203150003804100440c03900b8100f281c5c00d4001d520a942c0039610b00240040e0045031240319009008265480300000c10f107414013150182c00001059a1182d0070402c001142da0740d136801440b802d10025408111400c01c610042c2c24490500e051606690041040080e801c01c2d6000020b242004540e400d1071079242c09009500034a1240c11008070324100403150702c44240c00980d1795105400010840d42d40e07030901c0c1c00340400c01805079030207404902c050043c6030043c0742c2900095406240d454002500600c20b6244926140c0039030300c0030014603510b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 753336160 1250 753334910 753334913
    0xc11040509011103340512280e15091b1912020a0504020412141e06150d030806040203090f07060c06051003080f030a151701050702010e0705120c1507 66
    0x201d2803200d41c1440c0c5c2c603140c0c0c40861002000c4c00d94810886d04000c0070b48040c0014004103485000c0300464000284251041c04102076004001c05810340580b0041c030460000e000320101c11075140d4480e116071300241454461070002c8481c0310900c00c0a0551024102400c071040a1413114034000030075200740c242d0001c6440c1c0c018082e103031210b038004901442c0100300c180281c5440a0040c08001c1e4000d034200c031280c594030fa5050400d801c41d0f181c01a041400d10856080c0940042c17011301036038840140700700c0009150200a92582c4921000700414003000004481d4580355018603800070504003640d2070905540005030500045811160101e03070912060014800b651103841d500400c200051407149085d611000c1007409180c2c03074140401c000000082130710302241c02c01e110b8200300e48070081c0f407291a0703182411107500c40005208550301e8040000c449900c140100503481c00301e800078003505400c0c6401e00c515003c404560b4806da1040044c4040380c0d4540c1110482045041034806498501c03d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 753337410 1250 753336160 753336211
    0xc061311120a02031009140c011b03031d010605130e060a050c091503010801060f1d061810031a041113200a030c0c0302030a120605061c0605010c11040509011103 71
    0x4130b841f00d13070704d61102d0208500380e600310340d09580741400455040c801541903d002c031702038580c0340001070f050950013820b03960319001500001e0649404603441d4003460380090100085450b480d0030203070760382e10450210b8021031042d40241e070083c1060303038031034504401503002c180d03a401000b0021420180000040020440a11409020700100300304074542710b1500301c51094941d140e401c100d81b241d500d05c0c0410750a41d0b4002c4036442c0d03130000a144012a00d41a281d64200029a21041d2103c40940084145a00c5d605c6402881aa8001a11207200e01024188450303490405103444001da078444185c0303001c0000a8200c140e81c11081140fa544a5807148000c060300c0200d14a507062108071000b82c00043e4001c1f054a21304019450007125200d4004100d101420441c1c0c030680c1c1202e000101c80031b205074501d6407242084100301c0d0600941d6a240d0044403281420000608840743c01e08030760307909152980140c3c0e0401030950001c00c001012780302402180e401a20b0501364440451401c6103503211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 753338660 1250 753337410 753337433
    0x105030708030714031306030b21030715150906051c03121e020c010504140f0709020306030313060c060606080f04030e15030a020c061311120a02031009 67
    0x4254080c0111524018103a542c03405010340c010481c03500000d55261800d400c1003600c0c52001481c00e42c10f5159500c02e4003070000c0c482409010301425041c15400d0b0011500000200c64040002c01145070100e40d0b00c40055580d2012541d14159454400058541601e40d20301c0c4050a10300100007081c610b00001c00a081812040009070b103c03541c0c40d50400f094000d021211100c42c3e884010540d099060011078a40b8800d02c07068459503c04035004c07601160540c001d034451840b8001e50b940c1707010240519555119402d940d120103500c4072074103004c41c030450380266030024800b40c2101e042104496a002d103105079038000e500061a8014884180b0aa44c0a40001401582804581400d02d000d0703034482620000c00c06824070000b06070295250b101c514000ea022043c20420300c0d100d040040e18200a076001d211400654410800459055040f400c5102c101651210b1007929055043d406c1c00740d0b00c10b482e01142c3e954050410710f400942c03070502c0b848400c1c0c40c9644000809103803e140880100c403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 753339910 1250 753338660 753338669
    0x7030603060e10060e06102d0e1002010608070b090f09040f020108151f0c0b070503160201050603210d11280806061c1e0506090c04030f020f04022101 66
    0x1008042482110748034031a0140c0303d038510307250400c1c030500c4030070040c0b2885850b807100740c8ca90008104010300c010b90000326031038450011030380c00700034140d058400c90a03a5030b14003a040340c80d0400c010401c0000e120b6001400340c0f040c0603160030509a603601c00a44140c000f00e4041c0c804c01000c002035021580d10080e05644406411080e07003a0007007500114031242d0b0900c1d03a0340c5980c0d0020103404811409024216a102d40c800b50325001d078989200000c25581068500e9070740004155805203e00b07006011741d52203800084d00504141d0850180028240305494010381060343c10004100c013000780d40103080840620300d48159503142200348000d02100c0101c40d4103001c40050103001f480a83c0b0000194000e170044940e01d840300c020001d40b640705140d40918551103490309500d4054541ca00da0380100400680a04101c42d030350b48014840030204c00c40302840c42040401050001400d8040c1045a050018002c0340c0c1a4030f0400114040ba80644041091071044903510a40314410701d040c0360240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 753341160 1250 753339910 753339929
    0x30602120c03090606090a09023f300d021c0509060a1a180a05010603020309061f0b07060f0b0609010c1e0210091a070c05010807030603060e1006 64
    0x43c54011642500c415018182c0d0f4401d61001010810031880f075044000e2107500100031802c104d4001c0151105c1d006103000d40c036850300c1c500c125602c0062603030b2944103000c08500c01034040760b0840ca01140070305911305114100c440c81c60040b18042c0e0304400103000d04503560301005030b40d040590f5060f8230300c0d21844080b5000b18104000c000c0d031468082400b581100c43c2d544040b9007803c0010b031420b440c0c0340f0030100b20780240007148124034544440907544c0c000c500c03440c420041170340c85502c110160b2008840640d038039400600030420000b0303103400d20030f0081c607110f84c4c00c140b4684980c05140742d03920400b0181c1d151902c070030600504512038030482c803103503e00b1244545450342c0400007910b0004600000303403101e4811410101071240d2040703200b019039401000700706203110385280035208004070f01500312448610030301a40351030100822170702403036001007200042500c0d0800468003900001d20640c20903032a4480080021050301690080d80d1410380684881c1420101074030880d000356119008a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 753342410 1250 753341160 753341167
    0x140711010216020d02010e1003020703140711060a0504180c020d0309120c020307050d060203190b010c2307032a0f03230609030d0b060304030f030b0102010e07030602120c 75
    0x100103101d0142001c030f6030588044280d00f000f400142d500d0102c2c50b00490300502d030040b60400300781d4103030300502085100c0e442d4081856442c0b51038070b9890080340d200800741040d0b00380242c2585001c501410800c1c2c86841c16500d0262250f00e00d10021181740d07004009213803a01c5100303140c02d8060000700d4051840d450104918001a00d0f007001c03000211008006002c200340d091403d545083c418503001d030074060003610303602403586808002507004940030302c201d00c845980c046140e5403a000f00c81081d14140d464148640c490344440540c82d404403440e1428501507094110007200a000c00c070019070003000f51503418403400013018503281070b81d8120040d0102d01c0b41c0a21050700354103201c006807500004c49070400291842c40b01c409443d00d042c500071921440c0104040000004028041d52030340220510030840c00c8800c0c082c06000a6070b004001c0354034002c0b60000e480c8240d1000d46070150500c00401c0402e0940a21800c110507500251452038000440d00910f201e000305a642081040c00a1b526 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 753343660 1250 753342410 753342427
    0x14010c02060a050612010e0a0b010506130b0a1b030215160813060908041e060c02130917070303020d050c0a0f05090102120c01050402090f090a23011407110102 70
    0x4031000d00a101190b0542d072a00881c3c0301361192120340c0752070301010008101042d40e05452036a180c071005030032552801c00300004143c03401d05105036990500b90500400360242030204400c02ca8014211100800442041d12107400d900d0300b00071443c3c240240c02408440c0da00e218560b080040c01010200d11b0000d03005c0b418100c80c0d0140c0010f0f80400015170410440d070503498083d0103040301c001d01510010011401040103007a21041c000d2280581c00e042010301d50740c0e442640d000e140d07a00301a502008903458403000e9541500300901032842505056054041d050101d040f07504990400d030006a80419280820207a07032150030b400460840289052111020004000004030303039504080080108039900d19900811486050842e81320a10b9182c50421046500030041118203a1085140c10041461070f445820f02d00d00031500440a851400501c3d100e02c426100b1850100005c1c0030014889845e1910078404c594130651725108409a50804442c001d109040d07030304040d400ca9104200e6a070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 753344910 1250 753343660 753343663
    0x31611070b03040f060606050d0c08040809060c01110c0a1b0b09190e0106030209030c040504031211070602190f0801050d030f0201090c0f091d1905100606090314010c02 74
    0x2000c071588540344950302d944501e0240300c28102210001d21080c1800c801150150304200508a59170090604015480604508a8041005550162600c04104450303509402c1c450000c1c60383d04032000c004030350b255056084000941c012a4440c400360000507035041000300160000c4564500b01900c01c00a80c14031200300300d14800c061000d0b00c1007640d4001c0340c050414460b00751006040c0755103806000d40c2d64020180c00ba52000c002c96100303010305070441c18245007600c9450301803074150381c4040c1200c1d4111040c00044c0105560110b682e10103201400005e10340f40001c1100c910049820401032800741d2007c1c150074204003000d410300800034014400d1f500c5124440c00c16070f82602e40221960301c004010b80c0100aa030344040d14255035240007080610b0751101c80e0080342c1003044100140348442d044809003e1134488061345035040420758098a031546805000d03014010340988000901c0c54802004a41e02c0ea0300c40804104409030420522220804904521040f00020b21004c0070b03010009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 753346160 1250 753344910 753344923
    0xe01050307091806140105040f0c1e05070203191109010b1206010c0b090a051b28121101030f021c200a020610050a060c081e0304030302031611 63
    0x6400030742d03100040d650300c00e0950308004800b80c108104000c119990642041704071000d0003100d00460400c040b000866101d0300c43c0c000c0d00c1540f9551000e6020902e20f078400c0900030342e0506020040e040c00b5000c050b0b60305014a403000200500601c101822915001801c604100c5402d4492007164004005000800080b18800300c40d40310000035070b0381da48006030f600c002c036010090700300413000741001444000058000c40b050300410844d0003913144c41003907840011201c8030541d009400c1c2c81490310320800221840603250084507070b1200311601d41c01c8030421580221000d071184120404100e07144e52301449658940d40d00b03d20258680440340344184420311498404880c1169036403040000c1180c50381081c0c4004840d03022546d610315102070003c0d51342109990066130103840c0c8400285034a4004204811070b4408d448951401d0015100c08185801400250f0f00305000041152078080000d0010f601c2039100751401a200d04005119402d01081c6144035030030f000d0b04079203828840c03c002564 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 753347410 1250 753346160 753346169
    0xf032701080406091b0b0309070f060203040905090c10020304060e0a03020a141807050c0106080d080412020a1b0819020901050f0616030807080a02030c0a080601030e1005060a0e01050307 82
    0x820310b1112403a2605d1307100700c0030f8000c0e122003030118404655504407500030345c01028200d080ba1089602e40c60841421581c5100f84005a4400c002c1003140b41d91a801081d400100035003501c14070f500700b102003202030091009050040c1c100080910545411880c18101480140d4400369882d0035903020407e00c2c6180e0140c4411404070310019800d60b81d900100b0007a51a14014041007410074103000385c46504282440310b072070350030060046005100014080d0081103159107000b5103880b20f031102d80c2000c900c80041e01c2103016403800200404c03c90040311b140320074892002d10055240540150400c95100240e58071041e504131604003503522030b064103041d42c201f219614001c030311080004400307220328040341104241002507c0103142d040352030140305040a031161061941c17400481c1040348001c4480703108004060000140092049008036840340301030600040c41e0044404581c0340c0b81d8880780707440405445030104611420701e0901d200c01003400320030b034800b95410440001e480305541d005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 753348660 1250 753347410 753347423
    0x10c060906090f0c05240307180b040b040e0a2310030204050108010e0d02030c0703060c140304121806140307051603050a031506080402090402030f0f0327010804 71
    0x882005004096100214072a840755036144440f00070b00e002c8600002601c0341c03c0c402c501602907a08100715505030701b840104209903c5146550700ca000b42c444c2030303200150201c000c01005001c100320700e18000910150070781da4481902c0340d140c080891940e07200100a220210704000c080495205c101c60a80d4010000303030040285079441e0840501102039903400603510605120000803100d2065101d5070081c45c01c1d4045d105030314210f28043e0b80d0b0340b00756902d2401e03030b0380010800c10101c1c205500001d558280303403405450710340c104044000039800c29202521500600d0f512030200d960882c850050000c00303015251903c80c0791580c00781ca80a125402101001c50000010710303600d00c10070484514004148851001c200035050080490b044a038002011a1424281403042d454542c04482241c03c40d41e600742c80c9070b07100d60a00c03140c4007010b84102d030148240c41a07142d101d8401c1c80015a10b09000e4025500ca08641a0402c0741040d1b191140780145c440400302c15590f43e20120b0117034401c1c0c2001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 753349910 1250 753348660 753348671
    0x2a0215041410090b010501020a021516021215011a0406120603050f0a030201050606032202010c050105071706041b1112030f19060b041e0e01120b0f06010c06 69
    0x240310800c50380c0c00c0881e8525000b81c0c03404500701541c40c1d002030045806000079a00030703030701c4900680c0c1d51080d4a101a60024111440030010107104004100c01c140d03408126150303041a40c040307030340c0c00e142e0644510660031001108404604e01003006005004615181c9070061481a1581261041d4001c03035081116241200e80500007680102c402151b110080b1140031320560305503a02c80b030002070201c005500f00313404200c0503d082d000740c1e4044d200a28442c040c0750140301180c40c421240e000d04a06000041d803d00700860f40030311940e403069a494962000149207002c250442a80040000b481586001211801d201c00301d080010b06035101e0400928030b54018071001c5c6041942e54a8075410b840010800c07100010700c1c220a4054401504008041350065000d142038401c0d5004442241c0da0510040110800210008031095026020210b400e0780f20440e05410034426000242c128010b03411900c01c100b140e544255110b00d507025403004c5402e00c44002040e07415041e00c0600a19144d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 753351160 1250 753349910 753349913
    0x103081803071a1e0c15011202130b032113050111030403060b0d050307061e0e1f0b0405090307050616090308090a0e070915020c010504090906020702132a021504 71
    0xe1440102c4010980a161691740740c40b101076440b03c0300d144200c00d0070209000040d14543c00403030101602e50041000c07510310301c03407900c03c40213006000c4040d9040c414011b0030886a581c0002005280d03105c0c80f43c169580040b004049100d030381c0c0341d201c241040544202c0310950320b804130079030b0700f62507100c0008100c0790401d800003281400240c84c09401400005064400c00840d6401703003465031f080c40c20176524150b10038044c2e0111000b4040500d0135801c5400e200b00048150507450190070303101c000016450704280e0100b4100c03001142c4840382c45e0300010300d400511004020300d56010101d1101440c0c03050650000500c81003851200800c03c550216003811103aa40c498441c000d40030108607600301e8a0700920060002600d403150140c81c444900c0c006800c40c0c40803032241c1480d20181c40e00c0340713010301e002c0608000b000b80c290166015a400e0041c3c9005a58181113044d04540c080000b00c5e040004160a0407204403661562880d9940400c0302c003051030300442c100140801115800400b541e65 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 753352410 1250 753351160 753351187
    0x110f04140102031e030f011202210715080a0f110a0503060310020a17070503010b0406081012031d0f0904120309140f160806010b0d11030103081803071a 67
    0x1803102d8040c194a400050b40f40036211031340554880c801d00d641940641c0d9a40b228207804603581d80010b90806907110f40150200504030741000210201411903c0d1140e0b500b03031840345000d81806000001e02c12105001e40d400c01802044149100e10702c040060a0303041000740300307074490001c00c0428000c0c0480010f2407135030140007a12a00803030340402c0d9903c85039000f00800706500103108030ba440290a010449881c0b140c0d003a00d0590b0342403d80c2e146003e050150544103401d0080880014420501010a03414000c00094011030b2113521003a400d0a4012800c81e10590742c00402d90080e142e03130b5540945503071403401207900b1980010b00400300845518049000e403680d80006019140b078403050142e80c8500040311420b085115054548210001d4090702003850144100c0e40542d00501c014441400b82d00010100306a1440c800107200035a17107040d4100c0c2d0802d03030040e50041404502c601c45038000d02011089a1021009060003c0c101102c1103030003080d0001d0303076a00c81d4021841c1e07400c1030304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 753353660 1250 753352410 753352417
    0x70312120501050f063f040b130c14060c0a0c0f0b0a020d030506060d050106020c0f0303040f0e0c3603012306030a0606090905010b030a0816150c090801110f0414010203 74
    0x40c8601020000d002608074261b66a8143c0c0c080711034441d1000040c0c1c040501030901c940407540802040c0c0781ca072030140340403132206080300740300d40c081c030104002001c20718100508840944211031494415103041d181c00e000050960008250104c01c0280c2c0341800d0340460301c03038240e880f07500f00080c15850307581c00b18040307004192007a01901d01d0100081641030700002d41c4400a00c04499013541c1018550900d03469008038881c6444c0d81d1003211052000c5500c000b2600c0c5d100c0201c0c0ca0490408290b1860249580000b2100c04003e010650807026100c2d4900a8001c01c5030060b4002e025090064405c1d0708040007250403100c6005040010540c0c80d074052002860098205000b840450740343c14504000300103048048450b58030341181c1e100301e4200030809007070b01c542110485041c01d5083c415201511500e6108a84241d00396251450159107407080b201ca582c01075440900d0350381000c803902d007101e100403140d410790081844050310390041d150403a016500308850b244000320711a00140c0c45c500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 753354910 1250 753353660 753353737
    0x15020a05040503011805160e0c03070507051b01080c0c100c02100f02130509040c060c06200c16050a03020d11030105011d010b0405010f05030702070312120501050f06 73
    0x500304511424018117160b05d2850450150381035035071504034116401e940390044e01c91801a10303801000038548005040165520040b41d003030641c81c200b49507855034101030054507051030000f84000c1d0180c007035900c80074181e48940c107205024501900c100c1010364070325101200d041016124440024040d100707000ba0090715013124000e210000b510400d81c00a5005211490703e04140aa8006650324220002c6806242c00558a001c0700c1d0500c1002c4030106580d00307058070450f44840c84c446807188010310580b28030120120441d2a0108030300c0490510160004040d5906c1c41d0780810702c0950f0f01c11040e4011280d04075035158485140f4601062041e5084440d26810b510f030500015041846211080b100302680c2e01030041071703807964500c2c1003601907805050300082000400c1d03da814040c07402540c008520780115001d055884d55000752500c000d001e070f640050001c0800c0d000c130744101d029080c00740800300c400c9510301c0e0220b0702266090182c12044559210001c0c9101c074640c20358001e40c040c18 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 753356160 1250 753354910 753354913
    0x6010c0219030813060e18190213030c03110f030c0d030309050303090115170705120c09040302030a0f030509120304140601120c0909020109050f15220e0415020a05040503 75
    0x4500003480a802030501d842071170041602101d0050f02032a040f041c99454a80b5801c00c00e615454403440e040e03c0c0c0c3d0b40969003211459081180f504120708281b020002184500c00070584e05040d441e22511500d18154114094140100798418658011841240c42c480940b1100e0a82507942011800b40500600103005d81c0030000c24004200b00c10340000d030800d903000800001040c0c2d079616080d0a00458828400541c0096805006516100c42004426401c020844058024030b01c0000d110100548044001d6480043c6031043d072a00090309514141d0f060501f00f181d0703d8003800d072a4444403158810324421000000090403c41d00d8003000f1071006000c0b044034038640c0c46010314141c0d0121100c040d40c2d94036030480c0004165056010f1402d41d2a81a0740303005041e883c1c20144600709098003141e0790700034220309101208458040c090a12030308209030b94089240410380648108c451798010040b080048007c20000c5001805e401c0c420502c7c40d0306c01680e13050300440440f05d41c0a00d03040903615 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 753357410 1250 753356160 753356167
    0x8070c0303091d0c0d020f0705012012070c0609020301020a0806040b0402071703071e080901053711161505070f0c020103110c0a0515090d0e03030d060b070b090606010c02190308 78
    0x6102c01540480324100c62604410036007401e007200341150f800303022003421030cc018200001d05018401c240f20303600e1740c0c46048042400101a4002800da0f00045c10000000380c0207000c0040d58945405401e86500d000d8804501d0002952500115085201c181d4140404d000002c100c549225035510048400d004400304220341240c0c000412076502560200d60542c00d1030f01241c1d4807031042c5400b021000321040220a001c43e40d0b28245021180c01c002a40c6031561100c0e0030303a00d4100d0070014805024588000094800d5030710b4600a04980e015088210510701400c10210301d03008040b2241401050a00800416031480101e01401450791100301d11900451117140241c000603c0030101c6203d04140d8911024410b40c04418034405c450755240350b805040515000b50054504096002001d8245c0e85050a002c00c500d05031807042c1c2c4001044680042c81c1c009210015031460780201c2c0000c098200303400c01c0c0d40001d0800ca80d00902900c50000c03107070310070b60400c0e0310000c0701d0003103074400c013800d0300c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 753358660 1250 753357410 753357413
    0x1a01092c15190303020f030a1b0507091b021c0c080d02091c14010c09090c02030906032703131503090f081801020a08040306021608070c0303091d0c0d020f07 69
    0x8100340b922040300580304800745c5650402020095130928149952142030304045000c0019407070942c03480c00d642d140200708011800201c2802144a03000c04000004058141228028075042c5400340c0100e40071136410049111a40c02004a040560421201d640712062480721100078400d420041e0350162070b03501b452108011882c02d0b02c0403180214502c070744900b60000ca407420b0314004041c200014070b0181301400840a1503008081d80c47d90713403044038140a030007808110036034020b5500320201c0c2010040318003840b50070801c030300845203150043c45c00c1859040e90551307444550f02614220040090303042140c40d11a80c0460b01c203a4200320140000758a034200980b641d071013540a90b0b4510b0305a0506000c0e54000034040c01c00390381c0500400e2910b480e64490200941041121a540041c4001c0b024046040300c00a003080d5400f5140ca480300b11702c2d51502030002e2845602a030310a0300c8085801c09103600f0028960360040c00d040005a6403102d01800100902c12101006040c1c0c0c00440c9000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753359910 1250 753358660 753358699
    0x409060e070305090a03020d1b020a14190807061223040c0501090305060609040201140328050402011209020121020408060109090b281a01092c15 64
    0x340122110b44081050361600e801c2141c0701c1001e2840500507a011800354078401d44104620b8201d1214800e5002480c0340c01d80c0041d560b80d066900100c90704200405615403031a00f500c2844880ca416030f06000c0d1540344c102c0503500c45400d845610240904040140503e04990f0408010562262002d40b00000001d9800e4003d20050b40c09941403036030920301141c40d50061864406583d000341c020881d0f550b80c04100404054010412410000030343d40b00f1117800c1b0780e00042c50152529035461800b090013000700d1500300200c444008803480c10407080c000540d03044121002d64501d2a0f4012441c5001740c001079600140310810b075240810070486440030a03c0d03d5000d001a5550102502c00a03643c5818030010b54034882000792000c0c10990100e50044410300302851258120381d10a9118800080d0260854921200c2031482401c00306002c0e141e9070340900d02001404500b00b13102c00c608c199004401d00c02c0d0a4400702503103010082c1c007041a40c0c004455900345010001c2580011810308842c15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753361160 1250 753359910 753359939
    0x5060603060a142e091401050f0313050a12110a080702010c06060b0d020c16031119090f0e0f150c0c0c1306030c140f041d0d0305070e060301030b0106080705040906 72
    0x103100058501030080303200b0814005c906d5040740140c1d00d81d030030640002c1c21548160301c041c0c00256030800b035209a100040c018080c00c0708050007582080642440b200d00078041c2a0580005103041d00484080d05c00a249141510031042d020302c1c00c40c2c4d85d1011441d01c0c0c0006c049e9034100300c20108001c902e41c000403082c1d80061403103100707000a036441c041414810003401d008600005000171400300c103d403000d0404040c50030b9210400119006580d5070b41180c24200d5600360a071440c05511101c07600b480703420800c0007440310750058000b4521103184030a5141d004101810840c0110b900042c10343d10440204801c11369944020b09855128483c1c0d0443d40042c000b51000300d44100c1d099030001101214140b0030034203994080d188011008844080000070040030351200074444948113a13200d104010000912401c109840010b198180148041e08030100141068800c0b001000184001110302d100f0b10304568140c1070540301e9841b0500300355401d00070340c0c1041000903e00a000210101c0c0320511 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753362410 1250 753361160 753361249
    0xe030a0f0305060a120816060203040c080604030e09090a080c06010906061409062b09031112071b03050d1806030207020f150c0f1005060603060a14 65
    0x64603a81035680d48103400390b41c41100c0c425400301c0080d80401070480d0720040c420a40780700b40c400394548031120b00340385216840c0d1001558540e50100c1004100518900c0d0780001d010043c0040880e4607050364000d142c40340004400380180b54030390118505040410070300d11a80d9110508544800851040d142d6510003413241210913414902d000848900440743e01d2096a0b810800d02e24005904007481116030220a16418403e500720030001d00d030903230b40e8a00a45c00508800442e12204604009100090f4003002e150303160002c0c071280e05074040110842e00a1940100c401c2d12075204d12046154031701c655030010707019000d103410000e0260f6004420300c030748005014920041302d4440f44100c0480c013a405000350840c11700c2641134468034014a48070300300075038400c01500d4010104842c80c188844586486003d5100008813000c0181501038503900c540166203050070340c40c5c1140000d069100d00d110350201410812140502611601d050181058031519000201c120b59004410f502520140d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753363660 1250 753362410 753362417
    0x40f05041101080c0703210e100b010e240f031906060509062a030f0405031005060901030206070611070b040b0a0c0503150d0c0303022803050403140f010e030a 70
    0x25555031660286200c40d0003034400c205401d041505d550fa080e070b038450f030103c8010a58450304001541b40320407805122604051300c1d0180400c2e20303594001c041aa005d80d0900f9042c06540c5408004a49132045402d16102c0889a04049840c050742c540c400d51241c814510504080081001000d0703002c101c16045a03c0300100030042d00e84d440034100d40c1d0740117100042c0c3d8051410440c031003001050310080c0caa0f264100500007061554880d05a1842d407107603010741001000410200320518060004010704074003840184900d1800c3d000203400c80c01305003c001e21550000c03800ca0140f00c0f5a51103210080f10080482e9a00e205d81e091041041e0310480341110b16a10003c0082c803850854010008082401d4a0b002c0c1140c881640a0b41c40015003101d45410107a50501031001c212a0030034480114001d8015041c00000145905030031403540999011500200c0140320000354000f0480d0201c0350041d190b5a5050101002c0d203081140300101d107405c642c2406002c0c140b051010004140810040e103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753364910 1250 753363660 753363683
    0x70309210c12030b1509040e07080f010b0307050d0b0907031a15011b0b090a02041109040e0a03121505031b1906020705150f03100815040f03031109040f0504 69
    0x150460030740d40076070082a000b46803011141781842150f400b4000d1000000c00c08181e510040c0800740c45c00074641c0c00b0448590001c03107400500c0d4020321a90610b142c080c0d0103480080d0030000461341d50062004010040800340001032600601802450040c41e0b1100c0c0003524a0244d4480d14203940d4250350303101589401c0c0b40340920720f6009240700580421215080481001c5e5511800409070004040c620140242e900c50001a905e6100303802402001c0d860254690100e0b03c28001180d5080c010080550322640314a03001c2500309103018000c0c6242c00380821101c4950200c0c2c2c84c05200f5070310194042c895180140d0101003031520b4101140750542e5a901480314401400c4088140c5100e41805600402424030031800c2103184800a050780e40545031525031740ba00080c241e6481110004884d130300140c001e0000c40c80500501401c50301310440500c4a003001c1d218010044100307000202030550302d01300100c01d00c0d01c42094525441c00280108000440300c803445020300000ca8003100c01c8007444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753366160 1250 753364910 753364943
    0x31b1a12160c0b0601020c150711010e090f06040605040c0804120513090e0f03040609030c050916030905072706080f0a02153a0606020303070309210c 66
    0x400c0c0420404442e650000010126122642c1c0104003401d010f0440c001c00702c408500c0e468911003d400c2c4ca082c502000d07510f050600703094078140802c5200c503040007285518600c0e940c0c0d92050207500004400b018071442d4444600041c0100815840319400074108482000c0340d54010342c0503846207000b04615110a1a00d4000301c4443c42080301000e0340035049d54090012110780d500800608407040c00705d41100c0c1c80d54000c10f245400a500180c00107c07011070500c10054416903180040c002554600c1c414100601100e40c80e04944800104250f52a210142848400c01188005060f40d0780400341c03c50b03400c0d4070120074441c1c0d15070010a180c01c10000040c8504002031440c06480c9802c0940154040d59082092038003900001642186051010f2000500b080c03a11000000424201c0074640700c64803c40209186524090b40038682307080300401c4190b401008813544020180f03000941101107103000403c800c405442525484542080d29039001c0c0c02c04441141b4902410700c104050303054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753367410 1250 753366160 753366181
    0xb0c0c150103021302090a031e05190f02100509040c030203090d0519231602041b0f110307061104031a0115140904091a011e031b1a12 59
    0xa02c002500016044660600407409502900c0c010000030040f41c0640d0740e985a83c2036800e0700c1c0414042c0c50040c1010701040082c1040000000800c0c02c1c1d50900c20203041d262480b208018104c00303030088503101800c3e00350b14403d00807507201d03d070300900401c03001580200c028004d40080b104496507110300c5100a6556024100355245000310b05854207810080c43c108a920501040c03400c1024650a01400015540313840035180ca54011410f0440400241c0100000e6030380701e148006070031400c3c0061903c40d60f803201800d03881420700c0c14040c2800c2043c141c520f01c0c621810202508040c43c2c160040684041d5100910450340a8442500d50210081c101401240207210340741a41212550528419015003006c081a075025004075080c05041008117080d6680d452045940d088600000d044c0c1b003003103200342405000800c040c40c1d00401035000718005a07026000160000b0706800340740b40011301220001e030150000d0008440900c2c0c0000300b48050b03401112100d524040706100044d0884c03030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753368660 1250 753367410 753367453
    0x70f0f0602120a05060a1211010306030f060207020306070801080a1101020f0d09030c062f1e0607030e01110909060d02182401050414010e0402130807050f0907050c01090b0c0c 77
    0x2487d0420030501e01056840281e005098607006040c16104d2100001098090340c40b11480d5019803c0540d03194254410507040000003480c4809026402c1c006019801001445000c225030185602c444038901a0042c3e252100d201d044c034003140310350019070f07141d554008040f47c2102d11404038240b0142d150441030310701c01c50300c0c0e10710070702012480003c0034200007500480248000000540d900541003400312100100000c07092021a440319091140c2030707070305200e05101002c9810082003540d81c11001c800c694450030406c00e00c107060203004600b09540d00070389076107800e5000741040029481018044011441295a01c00028250140803d00784100b600800d20700b40c16500e0610703190900c4ea4003000f03164100195410400780320401421500e452004003091081c2094540341a45800651854a0815041076003d03c0341c5480c4294162a09500310b50401b1103410142e0311103010120381c03170061402190280c00b20081100f1703c030509003204000d10080310344409075041c100250310140540003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753369910 1250 753368660 753368669
    0xb04020f0909071707030b13110901050913060303022b02060c031e01141201060f050120010204060e09090d120e030c0a1505060312070f0f0602120a05060a 68
    0xd1040041ca085440c10300680e50340704410341400c0c0b0050340340f0243c000400000f10b802c8000301e41d940010f4001403402c180d250600c81c04210003800015407401c003001c110300640602a060010120340206140c2c0c0795429000c034100b2642c4108003265503070500a598101034450743c600300c5514103004203141d02c0a060903a803003083c0e400610300d603203551a00c141d50394401418111303045403c90980c402e54041c800c28500070080c18030645642c10710b1104005446907102d4400d0b107a40c2c90440300300300c0507404100c00f004030303582401c20390003942090140c00b0004100a81041455100003000705003550414802501c40e58196140c0d1143c0c6d4558000326a18201c03c4008004980c8403241582d807c0490703040104290f210f101075901b02403030502c2d80c0380751040c19501120a2545609040040c22103845080c0d880352045000741460314510640340e14a1140d40e90262601003504074250a01000111500700613034440d004659031142e40c040c40982041c16100303010f00a0a0401280d01c501d4840308803019203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753371160 1250 753369910 753369937
    0xf0a0e0604030f12030207020d1a060303120a05061203130914070203191b050f0f0606060706020c0c0616020f040c12050a09080309070e0106080408090904030207091a040b0402 77
    0x110b0240c613221090000f6015100400d0b07020444440103841e88003a4000e002c1c030071403026a00299442c903110710281c000f400280294406d20100d0041e80c1000c0b001c40c0c10045002002469480ba1000b0070440c1c44010364060a42c0704c001803c0b41000b4203068440c08641d0080b00070000500c0380c0b040350301d03403200650f0f840005910610111040e02c560a259001105580c14a401d9000c00f11861002145031114141c40c0b9412141b10403141c540203014500d0308584640207010b007440c1440020308a80291400a4906e5502140e09220b1000404c244403030290300a1000d500d480301c0300c412400c0a212100d08034000c0c1d4111900403002d0501d805150400510b41e190f1481c40e0f09076200e984010000204120091500c40c0105408600d8101c019030152208401510b505400c00200070310485042c2c0c84001082290300c200008606090155192140100c07402c100c50b8036a41000c91400c08150030111400307140c40041502c0b01044183da14220f8070950b0b09007c0c10311018108000c034052150154003c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753372410 1250 753371160 753371183
    0x801030305090f0918060a05070906181805060f030115050103090507050a080a1a280b0909010b12191b0b0a0c0c0506032701020f0f0a0e060403 63
    0x7030059015101600026060072080c100090001c4d4807004140e03078692034039a04420105200c207091240e00e80c80010204284440d0400400c010702c200d00307038030800c01045480b80580c1601c0e440b4940840007440a0b00d8400c030800c0c51204038a004103416101180710742d220f240e02c0b030442d003018021001c11078944400c5524651a05005501904001c0000c98881c042c03030802081a50b104c98a240c0a04046c00041a0020361444c10708240800d03060401d001300d04400400c0404940801c0c0311440c01420603080240c07030183c2c0c00c003d01030082080c4051f40290030b0807c01c0400314055116205030030003203c141540016090342141c51303103100708081c00f0b4549564034030b101160b4128065241802030756030741e0b4001a5280790020300c035048440642c0004040a4003102404040b0301410040c1804031441495818111103040241d1100c06940780c040342c10220041c0480020f506403071151140010303c60f41c0c1c1c9112650114903502001c0160b0118139072000d072080500306042628141c0c1c1d84180000300703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753373660 1250 753372410 753372413
    0xc24060909061b0a05120c040f1a07030c06020933040506091c1e0c050108010b070f1113091a040203030435060f0a05190e0c06040b030f0108030703080103 68
    0x2203a9100060044c188901000081000c0d4118484248540411710f14651994100085031150785056441403010ba16548401060707510044101c0b401e240c0d041c101210b0a80c024038107203019014560160341d0040c3c80e030541803142d10083c4410b584051488032420408078420000c1d52003030003036001e84c40c3c101030103002c0362840741481211241d40c454800881e2889008035940d058245600074110002400700303240342d00c104500c1031707101c4002c0c12090820030340a60405182c2e082c01d006400d0f015000c014003401e502c0030300098400c512540341d005043c10b0034003920280000b01034801884112100401c1510182c4914989241c03580070f180e006000e103241c9450251794601082c0d003883c506064024000a220390507240307000b124426106600540135501e002e28410300a0f00004244051f00760a2130204101881d22004608100e8100c1c3d00026201e0640d51034203240082c080900380d009240024041003144600001e10301c07805002003d01c9441c0e07241c1c9022600d0380142c040c0107010a004000500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753374910 1250 753373660 753373711
    0x1060c0b180d1d09011a180603130311060f041202011104150f0819090f14010506120d050a1d0409060501090b01030207080904020c2406090906 63
    0x1034020100036540114829840c500c9030600a102c000c940c04100e5440121080705020205081005021104590158980740c0030542c1c048003001180320601c0c0010319541c038100c0d104124560664040c0c190341d12890040600c0e144400166000c6e4086005034002c0d0811070000103296118058074140082584c8495403030380130407030000c405e0106554075200b51001140e003a4000d0f00041001c40c8008840303100c41c03600175001005020042c010020310100304596612820646842d2162480c0001442180350410141490103a80010000500c407413a600072210150403c40c0039082c2102c07050704003041c2c1e42c1c00c079a5030032849080341e0102c1c5091144550045c0503002d581c02a04541c2e41400260204a00090407151550300072142c1c1a030b28401030060000c0c511814860ba6001e09003180741610070f46441c1524003c01c4000c42c0306640000d1810100e1038144500d1458201190410141082c9502810b80701c010856030240107040c00b100042c0080c0b40046e0560103103221360601200e00000070042d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753376160 1250 753374910 753374933
    0x32321060604120b0a0509010203060d080a030e19050c030706020a0209060a05030f0a060c1b1e0f081e0a0c030e15070c081b06030a02090418120f020601060c 69
    0x2035004505000008034060480081c0b10300c58401c60500402d032130201c0ca030400701c0b1400790440407c0c0c4e10502c01c20120b5114110f40200c520f40103243c0680382c140100044000d011104c001442c03501645000c80c0d058031401e405441c0040c451000d99900481c1074082c1565019140308040c0183d001000c008090701740117052640050016103900b0019490314007003031400f60f01c401030195980c05543c504040c00302070b2080008100c001d28220b0300c8440481c40006400c01c180c00060143c4507030400b4900c02d280c0e00003001d8042e45d44076005440e2100c56040659154203c6200300d40606a41d040d9440f030203012100300c076101c0300300d40c80d080803100c03070303510f08581041c45d40e001c043d000421010020a1320b08480c0c0541512889180c1d4a0340381d41c00c0c180d00900300400c02251280300c10401a174904a90b1394001503c2d80620768410060b1181086000203000e0010200c40d00ca04200000f0780d00c00b80440709066031060380c0750ba290f110b5030071031a0030101d80e0760340244901070029a440210b00b0003c0c042c229103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753377410 1250 753376160 753376171
    0xe0d080d09060e15010503010b13110d050c13050a06080a0c0905030f010605190e041511191805031c12050a09120503010303020601120807060504032321 67
    0x1000107180d074500c002c461981c0c40000e0f2540c00074100c0d00300c01300318505441c09420103500911442c6007800101c3ca44441d5690318800f2a074842d000c840101100c10150360313201d41128000c1c0640c1c18107840b224a40d9020900c0e4858660016901103082d06101c447d04003241c4d8981d650843d02d50312048480010014103850204005c8020000185650200306102040001c50000102207140000b04039100200444135044070012240400001040c5001c4550254000011000781c031000c09000b002441910703900a8804d4000c180f00c0000002000388007895189604c440c4444000c25902119440451250591545c0b00c80750a448004001d00c80c0b1700c410129081010040b4004501c0d8011f54004850504902d0703540d040c1e410500040214200088070142003031850740d41903031002512061305000d020009819018042e00b0070425100712244681c03c801d04000908181c64010008440715130442c5054482001100120744040111820b1000415000035880c0b06030003400c3c4c204500408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753378660 1250 753377410 753377437
    0xb121303121a0a0801050135030307030203241e060d090f0c1221090902180102070602070f15051303060e060f0f0f0604200304020f010e0d08 62
    0x18403034106010b002d0703400350481650b094100d6010900030320034014103030b80c0181c1c5107030f0604004002000c2100301c985a6000317071100c4612406860703241130f0718201c0b80350b203030000c584000001c100c40c055041c0c0c059401a00072641c5011078092038800003d80c1c0c9020170815901c440342d84400c001c207007407044100d0002d03a000742c51507041c01c41a50012080710b03000001620a004844140000c100070700c0803080103010349180d540c0031140c02d5125411351381d04405901c2000640100500417003406101d4041c014001c041c0103558819090704414104140c00c2d011034058411000b010a01d01e0001c01c448055841001c030003486680b80242c1184000e444020f9041801020400c4420107041c8070407030005503003e40b802068001641c0703001072908400600d07000344500c02d5000d0250301280a0103154001040c0e8805800c00d80302c5000080c01804107040d01803003402105a2500c083d12501c01851080e40215224458503000c000107481425005c4551a4000301d02c003400400100824090100c0e20b01c1d040703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753379910 1250 753378660 753378677
    0xc021905100903091a1c05040305040302120318150a030b0406030204020f03010303080601080103020901093306021614061c093207090f1407090f0b121303 68
    0x805a01c22288020b4080d0009102010140014001c0c07003401e1103c172030207421712071520040c2030b68401d2402c0044100b1121075190808582418070038002d860241d43c00134100203c07100160003041d0b41c1c0d80280704c00c108944010641c20346d5407a1907102c501c00240d02441c102d01d0160046400c50040103e118000d40c400d0351001c003c00513803030310720160805504841c2d0380c681d2941181005040018000d21040c10000b00303900510060b15407800c4076045031082207000c64410100030b1400074007003035030030f51002c542050b41c01c1e140c0481c0445a42021a00c403602581d520640044048030700150f40d0080404011a0400207900340c00d00100900a1804065072440340c0882103080c0b00c140c6030081c1d0259440b4070f0300030041c1c2281034012a8044845d88603038041c1030703000d0940340513030302c4030014810b1620b42e650360800d4458140b2503800802c0800c00c0500e06014500c3c010300c000d44402c1442c09407044080f1446000324404800d54101c03401d0010440342c40000750341d45441d070b81401c0c100002c100c04015109 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753381160 1250 753379910 753379933
    0x503060d170301030302150c04060c02060d1d07052e0e0102070306060b1306030c0215100e0109020a030c020712080904091505060f0121050a020705070e0403120c021905 74
    0x1c006180694803a0f40a40094075560305020900b03000905038455100c410001044200e03040528109940d40c152a042c1c0c45402081d00c5000910040010740d016090020410803801e2022035800180d031005c03501d100400840303c8184201540489031043e0300542d245802801501541006110404c14070485646644903594036003a203006901201542c0804100607540c410b2010801024200902c1c04110b000342da4130340255900c0104203952001040713440170981c1a50041d240710040d080002c400c8006503900c8000400030341c00350000c40c000a01e050700e40d0b41e01620110300c803021613041d022724041c0c200361601da440d07150b8000344040c0c1c0d100d03603580d82c0100040c090500d0504004180940001c00e03143c00000d119200015600103810412002070f820705c1c10f007007110400035140c1a02070018882d075030310346034000a2081140141191154020000e040c004540c0340030300c11842580e4911a00070415804000e40d6070840c10038000d44c0207180d4910011000c60080c00085006070708541c0c0c2c0e800d0b034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753382410 1250 753381160 753381203
    0x405130209030f0318041413111311030402030d05030606040905070e040603140f0715030b0f0301090b04110307060e0907180f030308090601060806060c16060c0218070503060d 77
    0xa00c0340c50000c2c2000742c541e4217540c40c29115518880c2403403541c8200c00d24007a00c1c03919280d10752001c002e210f84038038118540240c0b2800025107a41c00c04082c100015000f965603041c00b504111801c078400d1159030400c8210340d1050007030300d0058001600d428203207400d2901c0040079040c014900c80400c200012440301c50740d41c0b03000e52801940a01800c0c0105040c0d540c080c0d0400650707440040f580d6024071010480030640c5c00319444449060315001400342c0398000000da4540d00f84850961540c21b0144000030300611202090090b4401d01b50111020407500900da1075003614840d2901003a602440542542803007018180c0c0010289469145030b07100203815210203903a40c10800c003181e402d80082c0201600541e00a8110b07401000401c81e540c94000e005020907c010045405141c0100341105400010880300c08007402000c191038803244c444600801c940390001090b80300b0609010038107509400540303002d025200e207980d01c602c1c4d03546260078801c61450b051411900c000e104800b40c2d4680f0322 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753383660 1250 753382410 753382417
    0x1a060a0504050d1a1503010b04050906070f020c0d0c05010f110a06050a090c0e271207030c050111131409310812180303070c08120a090203010e030405130209030f03 72
    0x4d05036074030348005c403180060608403989810341d103000354a0700c014000c05050009417941c0c0204a880d0249030b60010200807030400203141c07046078024007038a4103a010400c03000c0086041c0c3c1e0080c0d89003103248588080071200380f054100e500c00180c020300251004074034240c00141d170000c03030040080741690382039a0755805044e031980080b100d14810028001504144c020703000c00c410100182c112110000610903489610448900060030400101c2d0010940500303140d02440e90010020420016070303000c4c0106690181c0b640030f8541c1220760011856071040c0c0f1001e001c0100c0540015010760310a4612100e0b4640f680b1510044a81000702510b10055050fa030600d1511921106807924241481c4000c00c1e01e024086d1f6030025008201c0084503031b40002500e62003103082c40c24107254030f500c0c100200c05101d490300640c070000400d4200088082c0070303040f04284501c268001c01c2400c00c01c80c00582c1300d000324041c1a62160f0100c0014a526149070054021400e005080c1c601503c0b500c2c092525661 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753384910 1250 753383660 753383671
    0x11071203200a0b06010f0903020a09090f0209010e041e050c13110a020a1505070c081812162102010e180727050f0918101a060a0504050d1a 61
    0x180d280c020010303d540d106c4412034004075182000d000c49800d690008035000c046005d00200075030748140c4801800300340503211a44940141140300203585492040c031072031004440c20740f03240000f00f0450718111842500709034507641200c06441c110840741c1c100020110b40303d20560300d5540364001003820480100c01002d1007440c0703030014500da411500c0c10f000744c0201700c401c0800300751803c02044403180d041440b003202654003004059403100500b0350001c00d01100115160800d849668140c1001c078001040c0d50341c0304400c0d411144144c1c1e07450400104d1112005964110710500840c3c10055014201c03100300c4a400030011203218040030303401c243d460400ca664900007111344205114442800305801140400008000036141c10075020800c80960a198603000d5034400c4000703484003003601020903006d201182130387c4440e410702031030754054030618901520324035145000348028a04003080b02c1142c6a1902e855060519207030800c5400c03800c0050544007010500c08540d4400a40c4a44a01c240c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753386160 1250 753384910 753384923
    0xc050106060906031d0601030807030525050c100e0f01230a1b0305040302061809071d01021c110313230f18090a0501020705030301030311071203200a 66
    0x82c0d2500600405992514014008400078601d100000f00070118015041d80c6e004000c4640e140f800d803400311101e10440107100090440f80301d4100d0700307001d0341a4944032103004408984815102004102c44d002c500501c0c0302c007241c1d450070f01c0855400c2050303002035240b0050420b07909c1860444901d4540c80382c2c4004c0e100c9070241c001902c1ca05103402590180540301d1100c18800031884a41d0058418407030390001070f20a50000c02d000d61440080d010040350031502900c0d030070311424000c5010b07100580c211010000c5118080c900001d5510025600000d00143c080c1d400701e990100509450301d0b5809800200d0724003081189420500c18103c0300340c0200141c0d216526a0003010403100040b10b081000075201c0d1900b191002d0b035030350341e0f40ca119810044800340300d20f240d181c407017929103000e03401f0384010078550000c00e4070028440040050740c1241d000c0e4848450081400314031649910490140c13801da0341c2c5500c40c1a0229100d400000c190f030405026a030702120900049500d480101c24085611 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753387410 1250 753386160 753386177
    0x180f160e1c1e0b0a0b060d020c0c0111010b01090b0f040302030a0b16050315120f0a11040606020105090d050c0705130c09150c170405040203090a060b06030420010c05010606 76
    0x108550840b0042e24000403a1024450412540e40d000301c0680107014404c400d07440d506407681e2540c8000490724440d248010031076440c1025000300ea12503244a11a9012504440341c0207030284040c001c07481c81100c141d44001c400742c00c2080403100e940040300c0b0554504800e000c0840182c60400c038040106d80100d030052460b02d070080e85142412400381280b01001002d0040c041c140b0200901401000d034200c4000c070840a0140783c0364030b080040e1925444500c0348401140505c07522411500321042c09803414003005854000030790036036200340d0790b400c5658403007681e900240780701e440075200d11828401030b40c80c10307a07450700007600565068030100801651a0001c030501c80e04884120000d01032034000ca500d103003000c1c80290a0400c40c82000d004483d00d140101000800740e4220340180034010801c5482c1c3c240108295640d0712440f00c200c8001d460705081015503d012015030b845207074400b0250b5900402110f850010240d200403590501910516800026900307001d140080c0c00039a48442e80b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753388660 1250 753387410 753387413
    0x9060e030a1d10080402280f0302040f0203010b040b030a020d09032001061401180b0a091503050408030412020c090903132c060a03060911180f160e1c 66
    0x10030341104841103218440c030658403c00e82d600940010380c000e404a5085508424043c48000082180c1d4420307500903420100c0415900b400f0a00380003940d0013540c0c108282202c2e0445d40c01248030030300452000240034041003090f0340c1000300840e448920608058104603882e0a104140c68240b1012004150305030352000c40c00f8210b103010070076480103400910009140003102c1108918940030581003181020300040c130413200c11040c900501c18010b440f580c55540340e10080c0041854001d080b031150f01c03541c3c550302140c402d0084500454101000c54a90346031580d580e10308900814029040d80140c1c1c50323020b810380c3c8000d40c252140340040c010b19035801d00025505e0030034550b6007280c185a6180300180442c80491078940c0484d000048007201d907074541c070001038180c88956000034140c0c0e08040c01c030010041c041d41a00488602616201200b50703c001146241027401c5030100302c02000503000648a181c4203131901501c03c0c2a05149500700440030108010022100c4807041443d60f803085c520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753389910 1250 753388660 753388697
    0x602030402090a14060402130503060c0717120c0912060406060f05150f0702030f0a0303020d050a0504030f120f0612020f030606011b051903020c04050a060b0a0309060e030a 76
    0x60344245503840401040d2072040002e1031071880908014099640030503c04507400b08d0354060009000c00804842d407a1400b4420100140d00500d411507192000e00d4200d081600400156035071044a18000050b9a0381e43c0c030341074200e8000f0321031298044070342212460080001d2000500450040c0c8010600745e00b040000b03a41c0b9903980e03010310300441e503a04511f91325503511350681d000c05182418203a910031850001901e808212044da41da140108281103081580650050003240c020f81001e00140d0b40390360407802280c1040b10050f000c2480e001c0c038410302a00c0355403074104602c140307030000854000305104003086645c2ca42250a12885102d05035003546085010820501c0084004010920702140002c00e81c3c101c41102711500c1102802c01801c1190500c56280d618003202200c500310840b40c00c009540b40c1e1105442e078021407a20000c42d4921266004500586408100451401c005020124010195603d05403030283d41d5004c03000c600c004c184018080441c09503540c6c02c641326950f1040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753391160 1250 753389910 753389929
    0x90a06050901020a0f020301230726010504020706110d0605010909111b07051807170105011d0f03030706092a05060d0905010c0206070f1d0d0507080a0602030402 71
    0x11040c0a03041c0030100141ea800500d4450055001495008001e014408070b40502580e100c249860402801da40005080300550244600c80503030310172420b80d141d44065800d481d403141500402012020042c401350520313030010f10303489218a0000034800d804035842c044039040034074103030112522154200450740e0700117003440150041c680200100d004010184c0c1041c42200d44031003e612030714000c040f584406000c045e0081c4809003804801c03041d000491302c145101150010045821151941c0c1190003010126069441c1a12000300000700c032201c0615400a1000c020762180b03070001503100350388051002d00a4184a0079001c03030004120702d0150f00c1640d40c58485445591041c07443c0242150a00b0b00208658003511000d5071408203199080180c003501001514a600f03051a0b409400d50005109110303a2055403051003011080600b100c0740c02e14407050303181c0c0b441c4418488000703152401000b40c1c1203110b001201c00d01c5079541c180a0821758040b00a0311002ea0100c200001c0d420040e081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753392410 1250 753391160 753391169
    0x2030a17040815150d020102031306050306040e0102072a05030f100c0f1205130614040b01050d0317090a0f0b091b10030c0905120601090b010305160c020d0b01060203090a 75
    0x3c954262400080101c2c400070b0f03401e40e50f80b040d20348000d000c06590003030044620400228010f01985515080d002e0003a5200392020b5000300c2c035041c0341c8149000b06109890039036500c144034035003c085403025090140c80c00860600510350405c8006a1964104608462034403480d0240600c0d40c40307500b1000846444d6024039003800f4919049140c401d600c043c0c108000c0303d60000c00203084d204d05290014403585000c0c014000362134000343e01500008024220b219a20030f80325502d881e0b80f680b051001c454448940203010034410003605424110b8001c100c1c1d441711080d000c9440541c425200d80d0403000d000b80e0255030346122102444070040c0c042c001c03418190386200d04102c08004041c041401c00d1a40411482010f507074803c0100c005128160ba8001804001d240c042652241010f02d40c80341001e10138114518030700703206148154001c1c02104d02c81c10100281e555982c003030420903120701c400306004a81c441c0444550b0070000384144a0785000e403029a00440e103d2070307001c080c40350240300d5800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753393660 1250 753392410 753392443
    0x10e0c03070e0426030c120718030b062404030c05030d080420100306050108060409020d031d090a0501050f032a010e1017100e0601030902030a170408 66
    0x14085502d41c0c0d003040350810750004c0181a00c0c90000550014000c0071020405020000814054080b040b417000d46140a0444505c040e1503c4c0e101090301c0030700096000b070080b85001c00040000c21726841203540d0103400a05401d0b41c0750000290300380d0030b0710406103403003980d14041030900611504c46a03500c040c00d030507002410210113843d000350545000420007004000049141b40d240c024154040c9a03900c2c0140c00d45d80d001420f080b006c0c0c00707409107000c1c841c00500c0d0840080c4c1e09140c6070090f40d0820750003418020303582c0d216860031206091039240c6450101c1540780110f850752031b00545107200d40c01c0d452000890754140800c0207400a00e8220340c0b0321076400403150746146026070808000b102d010410b2205136840c0c000c01038800a80308003810b6072020305002c05d10722943d004416003c50351084030080e00c2d80c1d0b44001006000e04003d0084801440901c3c000031003550195115001c071600003400c6408201503562400c02c141d81654080496004c0450101f01c1800c1c02c00220714007042403503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753394910 1250 753393660 753393673
    0x204180608060c0a1b03110a060c02120f070b100f0909030809030909060f15040905060a06020a0b0a0c0e04020c100c05070b0c0f0f161b0305030919050a08010e0c03 72
    0x110003410305c1080c000c0d02ca110620f460005040500030201d0744040d1144809445600a980c2403403030051003480c69200150180f20f5403004080c2660342110b83d01d00745040524209074440d10356000417900200b80450f80414440041620102d982041d402008200004900b02940e440e0081024001800c0c1140561090014806950350800c40030307842a400d4500107126466400000c055850846500d0802c0744001404159268246c1006200e200c040c0c0d003040d112a40e0b20012640c40400b51000f0300020700f000c021500107070894000d031f031140704107141c55500c460000c000a4102d81c045525031b00c5940c4031070b0548407108098050704410410340d040403800c5c40c07550303111064942c500404c0885032400001c0c0700100038442030203903000c48004d0003002e900c4000c0111076410f0780c04201d605076406403800503000c6241d02e80385031110960350710070b001e1818208218144405000740100b40c01c410059601c011030103440300005000180041c40000c1424405080700703a040c80724030102c60380650480b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753396160 1250 753394910 753394927
    0x14121308162402100c0c0515240a09020a0f0806011404050103091a0103030906180b0406031e05070507060f060e010501140d06140325090f0204180608060c 68
    0x45401201180410100c89655481000880c14015400030b0f2030844c51400d1420803c0b2503110090300e10141c4504222009480c80102558410404507503000d5026408250500d0380100034000d2104010042c1100f25810b4541010600742c4c0c00ca143c000000462402c61020042da00880c8540c00c14028240200d24940d10301c0420030350b22641c010141819101c0030340c502049024601950328440b0204813461650b100d04c0c0082c0a255244601300009894428002d005d00301e02c441002142c42c0116050b192038544601900a0101100907540483e00307865550588002401028880c41c3c090780d40c582e541d0b44a242040031928031040c481b040700c0c50443c0501c4030b42600b1045606540c001d00f403208880491440041c2644141040180c02e20b08009c400189403215048158140000310b05441594111504003000c440100c201185c10400d00d10b41000864419400201d83c3c81040304094541303500c40c200e880a1081070718042842e40c0d039a01c0c0421604600b03220050b00032848845d03003460320500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753397410 1250 753396160 753396179
    0x601090803180307030204020f0a020609011103070e0f28120c03081b031317010212010b0d0e03180103060602060c03061504120605071b0f1412130816 66
    0x162020311658400d400102d000790368041004100a41c1c0c010000c1d950b404001c00c0e04003054100214500c05449044041240028180a4030b501d600d00b90030002c5c1159900301c4110f848203980101035420040c040b1000d50303e03854041300c2c0c11040e603024821046400800d02d0700030109000d070340258140c20fa007180e40340001d0700c9100e003613040365000b0a40035180c0c40e14444240f4030740070307520f04455140b000103110703100d8034100107544044901080c503242031416444110350903841101c810b600d80d10802c0b00183b05154071140035118908100c4030000302c0701d184864551440d44200489180c418545000c800380c1d40c0d1601400c40601401d101030006814130050500d0b071800094030642c4602c0d1400101c0c10b541d802c20080e03130001c080c48490540340070098204640100010388180d000103003400e20400d481241c0900301001c2d0b907401420707c080c5030010740320950490401030b652081401040398040e181d40200c00034110003410801141e0507685405c00032131402c0a00048901e240301076001c02c00c0103014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753398660 1250 753397410 753397417
    0xf0106020c15090a12110310021207140903010c021509030a05040623070b04020108011514030402060409050117100b010905120f011d01140124170103080a080601090803 74
    0xb4000c0505480e46001000207a003110075070440080c0094820100c028011160b010703041e408001d44c1501d800c1041e03803075001300381c3c0710b0309401010764031500011960042c855800301414a812404940c14904906d0000b425994865200c80050b4030080082540102032100e075500300b900400194a00010084080d2081c0128801d68040c090281c1f2007941190034082e0102201508808466a030040c40c6482d10041d00306131026130000d05040008144a181540420500300c850344034600447d4580406200d41c0e03000801c120f030011001e000004004502e4014034ac080e000f458001d074110303c0c0d030031a054980003560b00d8007004281002c1b4032585503601300d002c510aa42e0251103100d22442ca2400d520729042d1b502207035103015840c0952100c480304101c000a003040402c0402401804910304005c8040b150038024013003002c4820501c4950030407400740443c4505624201090b012708108201020311209a00545260310009941e6103070a50002101e503100f9000d0910401c40ca050200c1c1c90354030b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753399910 1250 753398660 753398689
    0x30109050c010815060a050c0d020a03080604110c06010e1b280c150c090b0f090603040f05060906070e0301150302090a0b040908040e061017070504080d03050f0106020c 74
    0x6250000f1400c0c0c4e0b84491080c000301c0c0c0c4040e006550702d100c090801007041c2e000c16080c40c13441c010b480c0140142480442e0502c170035601551100c115450b8101040010006421081518002006140c0e0030701030610440340240400c100c0c10102e0f150211200c540070160704201c0b642c61104002c55200c0841c843c6910a40f87e04012095603a5801c0420a40d8110b520a50103484464901600d5210100a8001e108540d0540c2e441c8480281d17200718440e1980a2042104c101d000280120500f038102a400b03154414007c102002c0700d04802d40b00d841c20151309a03219060b070b410003400c02c40c800342c00c2090240490b40c01e41c000c000c3c0c0c6460310840344d180000b6000084c8110590707408110350303c0d440e400c42d048010005208010000051520010680c840c0c403c2c00490b1304000006000c62600010998950f520f94444249521751008240f080543c010144011311000b03000120311040b0411501040c55081e0b00c000440b4107054101e1144400c05900c56011940507480c41c41042d01c400a03c807070f61a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753401160 1250 753399910 753399917
    0x6070506070f050903030c0c0a06090e180c190f050a030f03030903260613050f0c0a02100218040e010e0307150608151503060402150a02010b0a150e030109050c01 71
    0x30b180100301199644a410f080c035915100204a104070114007003001e90306c1c84c0088a600310b13026034408003591752040602c1f80c00030500450000400d0614000c071154041c0180d00d0a4a41c0110407100284110054030030481030002d100ca001d1011480041c5560060301003107414512040c51541c0d0491030f4080700800070304141e00c400c505410540100c92101f059003222030001c48440d0020145814054100c5980e0710400e5a1140e029081d900b910030b9a005001d00c40e0380d9003490703a5800110304180c3c42144813608511235007412002e015498809489100910748814451198000c00c0006075110018035076042d0f49003d42d01054402c00000711203029900c08803818206201c020160f0091856510055907802141d12003c1070442e1043c40700e1180c919186480707050303040c0c002815910041140c000b5001521841c00c6a0b04a0100e0090100159075200128460144a001c03c641c0301166000c14092020b444da901c1c80340c1e40103c925070104c40c0030f50080145c14440c0d00c40c2075941240140e210b050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753402410 1250 753401160 753401177
    0x615050a031401080109111008011505040b16120801060206070e150d020c07080f0309060304140715090b03040803040f0804090c080103110f010f210603110406050607050607 76
    0x40c10300a8001c0110418060854061581d4a00d08640a031a850300100c81041844080d103010380360040808403032136166640da030500d81c20f20707410b401d058100407004400d216003804001044680e0340300500d60030090700d8104c1034622041c5018100c85401c1070020050002050051003507540c00581c5551040d00c40c50040040c40081d008281c0d0414600000540200c00184a0b44a084c81d074000b08510381c440b004603070bc503d984200b21754803250702c428003444a42003000340d200d1920340f10340035580082c02445080542004081028600b20040d48142480f00061018200700c94210030588010050750311100d15510b0b00ea503421781d4074400140010483d102a0a110061141400c107031000f425070120f08024900c1690780c007414201b0300344011542c0070401e03910f5141038182030a400401c524107840d40398011b220114160307608441c2030900c0e00c0f0582005d41c1e41880710800e000340c1c4d006501030000d001411414409020949142d0380265024440c10172246001407030001c0d4240e0f2000441c90180c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753403660 1250 753402410 753402427
    0x80606070b0a02090d0b241e09042102060f0705120a0c051603230a050702040b030118060609181205030402030c0901030605070e040c0f0c08040b072004061505 70
    0x1800745d0360303070009002d0409032001c001e446020400140510300380c040700c050007140108100b2258150034030303111010408045c0d290900781450340307066801501c0f40d00d41406e65900400038410034100441d9580059000301d0a01800a004801c2160818a1460207901d003282e51a800407180b6400703840e5807506030366461071a0819100d142910414142071403480401e00007070800030880b4014282c05c083d500b514000c01038112095104403031584106c3d40f502030520b540b68007000000c00c0c03a843c0310b42d0995203544004119000100da400d170344509c03e620004100c2d05000564044070240b80403c038000c03a08040391008201071400c126500e95543c17401995035921840840e09180e8440402031700165401c00100c02c0140e56081644201465600c9090000200040100303540595000f2808561181c0d440105544201c607505400c6d40030701d114a2400750355010b0407040c0c7c0e2209605460101d1140483c1c09984002d12b550204200c0485082c0046070810001250050b1441112024040700141040b03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753404910 1250 753403660 753403669
    0x615050c01090512071b18020c0f0123060a05011e050f0f0a0f08070e0f0102010207051e0d02030403051c020c03070f05010e0a0b030c0a0c0b1303080606070b0a0209 72
    0x40800da4002c00352400300c20382c0c1410b141180c212030403c8480075800c004c80d180c001b00c1c0d60340040803222000304220948030f41e5200040254080309803403800c0c1c041c541190f4121a402d02460340366040991508134441c8582e183d0508400f0b0240500740724984070300f801c120300d0b030b4040a03000400f00384a058401e6032034100c90035201c2d4440c1031f0451428900200d8840c06801c0701c84080d101e0b0400f079464441c0c0c1d08400d00811120550b08540100c0440c00e5007000c6034007030404c4c01c1412003115041c0001842d1020070389403540f5000008003040381d209502080d108000e1000d014108040e0500c2c0019400c0038115034400d40c4400b50860401880c41245002c4203401d0b208100444141c0000350070384286a80380c03d44264004114003405020608003000e0043e1420000a60000c40d2043c81440342940c5070701003484613070381c40007007040f04201031104040d002c104d040c80d05030300415403800e01044401d10781c41c01800264000b849644960001d00034070000c200d01d204803550050310007200580c0e4003404030004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753406160 1250 753404910 753404921
    0x10516060e06040606090b0a03031b0f11030f0a03021b01170a14070e0d0210090308120601140a0f08060310091a0a27060906020a020606010e040615050c01 68
    0x1408040c2881d1401c0d481e20804540d071070141c0d0280c00c0520940f030702c6045010590300039140d070341c0e0002e51038030f0304101184c030400e040ba6071001521032030080801207440e80111000c00d004143c8050400084d503050510b020401e07082d034405640054039001030b941d20040d440b000b100d41c0700300380c051004000306407680c8100101030100d008920511041d040181c1c00c0c0d001400307015000344452028801080c4040c0c041d104103041740d000108507011031442542885005451160040c052011458000c0f0009101d0b00203020001350904440340940b409000040032803c0c2071507240542e070303020850321002a0b07000c01d40200e61074945c00c2c1042151102c801192800440d4058038807203a2030314030408108004819004815042003000d0801900c0c3c01020404031600c4414000c2c2d4000f80c0e0100102c070942c2c1c1c01c90b240020340900070014450041e9201c1200b83ea03c1803d203000142c10820410003e9a0012a4090305410a4400300300c2d140c2021100051503d81648100a1107000701e00092030b00000d4100c2c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753407410 1250 753406160 753406163
    0xe01090216020d030c110909030d0e070b04170c0406060516021f030e0c03160e0a0e01020706060602160b031b130306050907090504050613051501180e060f0105010516 73
    0x15910021a400c0080c5400182c410884116a160700d40c006c0c0762030108032107800344208801951519240c800344200808618861403101c0c0a0b10100203180d001740005071000b0301460711405118900201c0c0d481c1440d40b1418414411481c0c62010f2040c140c0c44000e03070345601e50404491085c80441e0002a101d1091560590754000381150080d1310903506400160064111804544440ba003040030183c075104079030168145240c11443c10030100000e0440c041e0820580040000c5007611207026600366031001000340c546544501080100581c10429107410300c009104861240703003001ca43c85901c1c0300142c1604003017902e200700080c080325900100c40d244141003485509095803490b185001e800300f00c42ea035005004171840010303949258060113105c0ea0f480800342c9015a00d1019903200e130f6640c0d040650350751103458500700220403c2081540079244501d291402c1c04a40c61040040d29200395a1150300e400860600c0303030302440018074605440007403d10540b03e0400703148420305404038440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753408660 1250 753407410 753407419
    0x180f011806110c04090203102307052a0d1202091e120a030903060c05040302061209010b0f0607020f04090203061006030c0c023106140a06090e0109021602 68
    0x3000181d4682000000360180080019155041d030010b081004503004a64040d401d6041404000b000d40f80c0c0da07000c403525002d051440a20f034071041d1241200c60b4070407038091001c40e200040740074107400192103420741c40142001040001d00d212008a4840740054026000c2c4241700540512460703481e01039521542001e040340445e05c2c860000c0380a04900c4021160048403010304240c00c8403800300c0c5020400f034040c4c44000b04286140c0d03615004212400c1c021702000700a00000c80180d445900030700c0d1800c00d002152125040c4100d90310b085440b136480851060490509481c421788802080d44e140d00d4045503500d03141c0745041c0c0840c02034101088005e42c94003560080105004400b1414406c2d01c110b81e4040158002010081d039844000b104080e510841248011000c2050801d0b0b5140c1108440e1200040700c02080450301510110b81202c000c0312043e40312046a03041c550034102c0200450315114030030034980480c0f180c0080060080f4902d450300090001c6e4042007158030b40c42020b070701a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753409910 1250 753408660 753408707
    0x30f09081006212d0609030c33050a110a0f0206130f02090a0e07141c11010f020307051209130e06060d140607020f060a02180f01 57
    0x1010758004104070300450700c01c203600c10b180f0b06051101c2e2111690a9a00c07016051030403e180f1420484036034200070691514501d4244c56002130002c2c0103800186102e603c600d1a0180c0920700107640051680c1550b8444102414a2840c40002c03a0101c05040da40c400000d455151240c682d130242150424404132035400103120146e8035400f0500c507070b201c0e055509459607a200d80b0300a4000380c4c80c00c24080c003060f105410350300140c941004405e4014030a444001a100200e9010f582844170030760200d035881d1035150700710040d802c001081c0d94007040010b0035060300c00c00541c0c03880c2c460490340c03002d54104a03182070400041c500800407284034079000000c5603040c840352243d861040e40300c01d10040c0036035012004039403460007034028070310388a20a1000d40340c07541c2c0740c3e4280071641c901500300341c0703401c010308001140303009007808224084d29580d0302800500311000b403980d14002002d81203070340d00c510412240204030425840542008008c90340c0d000316050040c0104d68140498080765041140c0380c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753411160 1250 753409910 753409933
    0x2120a020703050d03051b0313020a0311270a0b03030c010204030c060909020c210d060815090615010e1807110111090f060f040f0b0a1b0807030f0908 66
    0x700d6408807403250f4111041108807032030403401e964050313841004c1010350070441803030b1402c5100038545c40f500125050101031903980000f01c0160081e4801c1c0c07011011001c81103680d0421821444a40707166422140a207401e100d0217424203030000f480e200d00e41b952101025241c4d50248101e41550380080002e544564580c203013481c20b010f0600c0740700c020407075100000445412134001c0d01d40114070b02000d051003021040540780c1c090246845c0b042c0301c1c0c034200b01c881144000303441000003030a406001040348402c101901c0980502c041c2c10300c801c41d07200c1c008018026900e14030f14181038030700f0b10f0062803900f0f110000c00d0000d429000c40c100c0c665503110400101960020045805d601c000000f400100c0e03216440b001c00340301d110300d82d54202c441c0d401809003d080070f10042010050600a20f490a82d49a0400d01101000d8202c0402543d0004508146c564415600c101201440801c03081410150f43d40308114441e038a0f004080c4454900c4140005019002410081560f2815100c00c001b1381e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753412410 1250 753411160 753411163
    0x1502130816030f08181e091602031801090b0a0203030415022a03071211061018020705030d060e0a14010b040302100c0c0627050a03031d19081905120a02120a02 70
    0x311450b4074040c287c04c030001402150551a0550b139249a80c0245280580c2d0b103500720b250381015480141840440c9000041500d1a0402840d01d1441703507000c1e40e2a400c06240c80c2071052824420201414010300000c0241e00ba00718071810f00c0500015849555448524414198007680c03502414400540100600968010726201c0d246007080f4161046552003403803110301e150107030068100c60400b10314004982e060550040c00320500940c103d84c14800c620144c101650880d4006840203000030702444070460749801228034940c0f2816030960b5940c10244ca00110707028070b1001a20810b07035804d003141e8440c01000d85102540d082001001034580710356018194403c03d110312203640d0301c3c1c801340303c545a403009548000e03964014042038a080c0703582c90440b092849501d075003a1113446c2074031403a019901c2c541ca02e03032102100c6030301802452524003494240040504211114990508828001140032943e82480000411400d80b02c0d284031108900c1c0101e2114040540c41e00040c400460540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753413660 1250 753412410 753412459
    0x606030c03150b10050d0908041205031e090102120d1803091406070c1a0c030c061006030912030203090102042607120506131502130816030f0818 64
    0x2c40882c14070245509500740a105102c0324100700006009105039071a0100d030350808407283d03004030912414151541390b0b0441048030381d20100c0340b6520008000060405043c03280302c01c69801000c650400c101c800010303494031501d068880241d44001038100704400f035988a0f0354601c00c106043c812200d02c6141c041e003690098011314030507400f01d100d64840c42c5064400c84c1d0000740d21040681c800d5250940d040b01e0000340b880712080340c1000f400380e0b243c060700400c0949050706000c0c0090840f400e100c90100c81d0040c00d03130001010941882c4400c0c003c00c0680702040d00344180d0b481e006940e075448451a41c0240940c0d0400840742c0e0030b80202c1200d15050f40c03064079085803d0402d071522955244030b41c940a103610030000304560441800211051110305040070050b00540381109120102148682241d1140a5109aa840c2c0c000b090054103410043c80c0042640201c81d07250f5241182c58071040c060ba100320090850700c002940b1030641c90b505010054154000e003800d22403010710404c44c003600e034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753414910 1250 753413660 753413693
    0x60908100c2001241202100302070f110910211b0e0414030c0d0c0201021c1e080712020d11211005090a02030405011e140627040606030c03 61
    0x11411000d40c292891107002002c80e545143d05210401c007680c244103508040e035a01d0705c08c5c19403d001c0100403034622001c0c0c5040910600c0170392140150b61040103159071000d81031701d80520940c041401550024031144003030070031705443c85100480511300042d51403d5022504041020003400080086a020b40140110710448911060740c5607506181d50324021620000c50a6000003120141a80070319900020705006106990102d40c10402d024050040316003400e002511b103a0340418000c3e500d070750943c0700d501c1502e403403d018244100002c104404145030103014035400256080d031503407568482005140301d00d550a03141c007905c1018104a0205c140d641000d1004240022250480c0104500c1030701c0d0020044406178560030240402900024411141c40d0342c0c0f07094500e00c0702488180743d03200d6038810740007140b88034818212045188000d045e007409081040086a100c10f6031624100107007a5991201c4102e80c0c0754102030015103190b92016050001c102004810302031240141010321 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753416160 1250 753414910 753414941
    0x20f0d050d020c0a1a0708130e2701050906190e07060507030219050d0c05190b070207060e0303070f2d02090705090a450501060908100c2001 62
    0x1640c0d002c199610003061750214144540802c458070016400001a11040d0000c4400c0c0c84144c0c2ca5800321120041c09a4182e000c0e020492544c200240d404d104404404000d80c00901030307402c10101da07640d651005412042c480a00f120341580e4640c2d80e030711980c807402d1300008079410569208009005540300c00c1094005002d800c6803604891030002c0e907200c1d00c0e0342c0321008101110a00508552030305c95240304035000d0240c00c401e4503110412001c110011030103108007008030f080440f40039240040540c080000c3c0b003031841c03000c141c80d6404410303510720039000400d4510b01d030001c0c40c058038000e03d4a80c052002c415020404040d4088108103070303410b10b10030745e00b00c1c0894071102001d42d054001c1403810f0340e206003210414014903081c64848250724140d180441441141582081190420149041c0b4540d07406441410302c9021405200c1c01883c090070020b400e0380c2010b0555482d00841041c41060310748031622224951f1241c0795012001c8401c403004804003074500e80b8640a482c0b104104c4124 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753417266 1106 753416160 753416179
    0x41e05100201060501030e07080a060506120a0c0501081803030402040e070b0a05030a050109020906030a0506210d02072102012303090f1005040f020f0d050d020c 71
    0x1211410340000c51114102000141100c001c1c0c0340c201f20f00c0d4843d5100300810b43c4042403183e10a50010004185541e483c000b040c250100c82124000710320403500f000c414400d90110300002d84000366070f6040c2644400340b0792444079001112000070350300200082001490154407440b209842e2005403030b40c4079600c1011b50019006003001502051001041100d40c820500c0b5042c05410101402c6013080310744800304580d03000052440c040f4903629408105690f84421008040c2075520302a00740502c007003011952542103040400c0003500c65013001066030081440d42c0c800e030545602c081443c1803059001100d41d86410103104109203070760034016840f078400000440c0b06020441c0104040603a0705038051610b50300c0b05001041a203000305010018070b1034680904121780450300c40061031107020000709000a64840200a4851403854200d06a00840c21315078800d001c071858002e = true := by decide +kernel

theorem cover : BRFrame.Cov 753237410 753417266 := by
  have h0 := BRFrame.cov_init 753237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753237410 ≤ n) (h2 : n < 753417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
