-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:32.421265+00:00
-- url     : https://prove2.me/submissions/b455064b-9e3c-453a-a986-c37314b27c78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582014388 ≤ n < 582194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582015638 1250 582014388 582014399
    0x10c0b0f1b07030e18090a0312020d0e0a05010e030c1002070f0f060f05090c090112030905060f0a0806040c05090f030709110414010c051e2103060a050a0f03061a030313 74
    0x4e501c03004224001c442e2100362909441c040d1f581c40e038020005040080c502104c10110032140e054403a0541c0c0c6280c1070113400c03010f40811b65a809240410b54640d4604125103070028000401c58202c224503002038071500c40445a02c0e8025045414241c442101d40300b20b110003e0088211441580e21445001031903401c8500711100300c8400401b60b81c0154480d50707a0341080e507103102c0d883c0d044442421a00d00b012019240c121022042540040d0700000301080001c01c0281280140c02c3c0200142c3c1e80c84202e5031440c003004140c87c0344101c40d401191040101c90752074100100010410340001d000c132020395661385840400c031501c081955280a001140500a80d0318040040003000824070f41410f01c0e0541d616140d8030345542d040390309444680c0507041c0070940024444440c20302c62000c198800b074401484014001c0d07108440007441786200c404041b900f460920070840035660440d4000c4459411b603a43c9000419030310800b50101d0300041e00400300381e941040246600a21084642201d61038034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582016888 1250 582015638 582015649
    0xf010314130f0f060f0f1107022b30050409022b150503060f0c18090106110d0206070518031e160b070201050a0309080c06070305070e010c0b0f1b07030e 67
    0x5081604141000802c801c03c901004c10f40c0e0f01c030380d011642003404010780e60100c5684d454040800020711a410ac00d00f003406400340340003031846840c030704588030121204110058101e0428004020a5052006020000180d070144c000c00f0fa450f480104444004422040707650700309801181d46e541c854403550346000031145240010030041e0003c2804d42880038001031464801400b1442045020902d903100c1c0141420031041c2000107407400e0b6640d610f4240040c074840c280e240408081c4034010a2140942c40010000d10941190b0342c0c070350900c84d0001d2442c004c074198a000740d5043c0300d1880e03003a030096100c0072940000490007005050072034805040e00e501c000d03554411569031405009000141c3d130024102c91000802e0f1030005070156251500d01118050082d10101d28401d1074108401107415502c81405035604c0d071a001c1024145500440300c0d012a03a030300030a85501e48020500d059250040305401522459042410560040d00d200068000001c2900090900c01d4021a01e0910 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582018138 1250 582016888 582016901
    0x609040b1801110a021506130915020d0b0a24141b0a060c0521060a0e070801081e0a060b0619020102121b1603020f0d020c0f010314130f0f060f 63
    0x1070303020440c6c0b0751404c040025000390709940100c4415441c0c041710000c2120f80010040862000141151104565652f00b001000c2422545004200d075010100d40403092045141415078186102d6141d03004004046865070758600d25400c242c2424007510000e017402ca442c8a00705950342009003d45290740c20000c050360340c1203034171900b841002c10520810b030b000020010355000400c82c0100c0302c4d49590010450083d200c0d40404500000135080c00344655101c0c6240b4100c03500c25003181d0f030321243c4110940704111400d0380000b403079010385950030000d00981c024404980e0020940c40c104515044e2030880c004144c44400300503540000c40c54405c000100005400031088214040250300142a4110610030a0a08046c0000c80c12001c01010b100300b141c603888010f41c0040c0c40e0b4410022101035030702c824150401388224203441803a039855200c1c0c8545407000301d0700e2040d19016220300c2d400d030b103643c13a40b04415241c81c1d151402c7c110116001030103102160384600c40000d154140e4283e072a0850b01c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582019388 1250 582018138 582018163
    0x170a050d0509101d090c09090106210504110312070c0807060c0605100b0c100509010218100507050102120a050601020a0c05040c0504081c170609040b1801110a02 71
    0x81c00d12038800c19850b440c400324400e4100307050422110344440c03c029007800c005a051031303005025004001318041568060900d2000c00d540154241c1d886620583d40b002010801001001c56680452921042600300301d420134041e00000a0414010020030304095288010142e100780028081003084241c070b201d40c0040641002411540d401e0060003000c08070440c07000740c540f9448130007248040360311070309070340007841c000340315075510540714924945603030518800c041c506e0f1804002486500040c02101c011015081020410082d10010801015094074024007009020300c07181001600174030007092075052001000f043c5140c24101003081c3c0b40b0040249045420011070140024422900541503480403200401d88001700c01003110140110390010f851841100ba0f2241000040841a080080340d0358861f501c3d03411203080764410100946100d40c014000741e001802054400300c440360400f13050103a003000e1101c5c2004450940314051340903101030310002070311981c05404120440800c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582020638 1250 582019388 582019397
    0xc020c10080f1816083702090405070e04112b17071502071e0507090906020f13080618060a050408040e0406050609010e090d0f09170a050d 61
    0x60080d000c0380c1c00c00e0380a005960141000d03d6102010441400242100c13010b8502a02099540c0c2010700c0c3d4590710f25652140001549081c41010040b50b003150f00c0e6104100d1804010007010b9090000c134140c028015aa1800381c04004101d03051a80c031711a00490181002044200464041110b044458a07042000c80c00340300c2c0ca81410324442e41080f1005411450300c1707110011541100c89580b04407600200008040d211040302001142c2c00340000c0c0e4042d60568010030800c40c04c3c1c5450130302c502000b41c1540e2041c44100b14404664003c028424410b10b030250801c241c1e12500001c6401505424036034000d00c0030706020b85141003142c99070096241c0b00c4013400da41c3e10007915444240241044038144d88850016090003003000440300102210214a15181b51038207141008020540c2c4452080000d0030001543c0180038030080d019000540280a40c104184015101c9034440c0c0042c805010601c9400541c1d1002c682c101d00703201d0190009001141c04034500ba5040c00c152404650038007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582021888 1250 582020638 582020641
    0x3250203010c4d0303090f070b040b0a0201091e0b0604020a0e040504020a1a0a11150604150b0f040801230402060a1e0306031b030201020c130e010c020c1008 69
    0x71081c4010380c02e5440c480443c0101c1003a0050340400302d004156034000014420303c070a500e42202c00100851103010400261007a60900701b0380b041c0c03102c0003032007110040c005c03d10003030000c0480078004024440c0140000a11551596503841c081c0d034140c0c60b074110b25040100b1600c24800042906948503001310741c11460b1000c94003000d080d10552030f480602680d907a000041c115250030032000b02900310401d2411480e40702601001c140d9200c8081d0303d0000e000382c4d050528030440082c81c142c800c08200310343c1b08a6501c103c10301008060145c901041c92a1080f40014400d8100000300203180e6002c05551b5218100314940b403d4800000503002e8404003403c0c0401d4500c0601e00841e0456811149244e239005544070444518101e990b810382c00104c814000c0c843c664041e0300030000c0301d10582c40260100c0e442c0d08100117484170b034480a40540c10041840109252032448212034855030440081d4a401c118070990031180da42035140007507800654440c01c01e140100c220520b082c0315151644c0c2a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582023138 1250 582021888 582021917
    0x50c0d0506030606150c3c0c031005060409020d0501230105030c01081f0f0609050619030c020106081006090501120f0201080c040e0f060a0f120206070503250203010c 73
    0x65035110302034075006010100741c4001402c401d0005600042c4a01c205401e0598181c405891f4000e484501e0344603440310302c1c0c00040400c408983c4a01031103004015024044c5860f4040d40030b40300c000c0840d079003e075440c101c1e8801a500d02646025943c0034800000c2c4d1000c903d00c191400c4041008140070103440c010040020b6038000612032441c2000386400d03034080d161198401c2c458148203144000044404401054001040203c441220f0700340c7c3e500c085465540d414054284036180207204d036404034505503d5201d000340c01c1b1820000b000e200000c0d203c2c0e6140700c1c2c1d03400c094503207e21510454540100b00260040381c040e03d1b002d09401c0c804601072400030b0740c03211402070551100a06000c1214006040707030405c0b030160340c020240803040e20518a000e4018401450701203032404d00c500d902200128200c11714041b1881518140580e4000e18810307602001899000260b04850a200c100315880403890841084105c9124241440d01481c105204040c03d4901c804002c504010050161015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582024388 1250 582023138 582023149
    0x6020109020d021203040e15040606110d03111e030108010510210c0b0406030902030f031312210f03060b0a0801061b0222050105030a0b1602010f050c0d0506030606 72
    0xb100d42c1c1201c0010748101c00c48003a5085000d140e10480280a96804004003103c00c0000e240141d91304a604001070754480005441d0011000d05d03071079669120440e5956041d0080e4000442211054402410322070001d41030030310318407403074003425154101000401040c1c0c0b09001d003a4000010008866410341440c040701503055004103d0741e00050510b40345800d01c40e29501d614040c007028000c9503651038540b4000f401170505000704900a02c0f5101d5894500007000c02079499400110040030521468254a003000004c1c072082980c1610031001c074050070b580b103640a142030408945884003050800c0101500b2602e50fa4041d042e120b0081050740c9161794030200080c151000d0381095484440b50b20b0800103031606000009401070f28400006640d85031200d542c40d0884243e0030140b1843ea00c1d40181070722505580b0300201600303507600c00f28022501c4160034082c0c2000c0d038800001ca111440d0b240105846040d030300800412070000322107581366140d024266000609400914050400070040344 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582025638 1250 582024388 582024409
    0xc0e0f060c030a0f030e0106060c03021516030b0103110a020601060206010b03010605030a09030c02042405060c0303040b07110d0f1707080a0b0411040b03090105130b041b170114010602010902 84
    0x241040441d8180344d90701806903000d10742c280c500310000c002c07403500e0306005485940503407070940c0544943e09120201125a071b4003039100382d07280034910300d2580d6641b2090300a0f006901039141450380301d09085a80700c0d602405080103c6055000701007a5252000c040d040c048183c109074601074040005115441d0854101c94101c0340d00c1c100040c81d100076045c2210ba240101c0c00007907010b41002c90741500c0e002131031b400510094540e2510f0140c10358510811065100f0280ca0b03261030b070030501c000703004a440d280341c4560011280c281140d41f5410703a0300c0141440840c0140001068040008501079a4000500c1901d490400c1502001d03060041014001c00001040003a0706503c2d0754150083e502d980c3c10001040404941032500c0340d45417403030040950002c8907102c00700c2d8a000300094016804403403500900c0c2d00101511019212519080700d050340781d220b01d05582da103d400000e20340c2e008860701017a800900e400062055042031201644100c107900c880e08680c141005c21003d6030301d40c152078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582026888 1250 582025638 582025657
    0xf06050a080f041e1515050102061605130b0409050a0902031f0e0f0708010f1b030509031207020322052824090504051005091302040c0e0f060c03 64
    0x10b11941e214540003904e000035813810341d044100d00084004010721118101c0d80d40c0c00050f0107004910805908280400c124072400340141d1000c40840d248452400e00c490481e0300c1072525900d8904020410188414141e015031116580041c0410180e06548942608075141b00c0b81403140c1c135810b0300041c0c0d558072442c4000c15400030400070100003915035402010440c05450503140340003491594240c44404500c41c4500e03a50070f00c41c5a0352106824403070030075105910344101001d03643d011022030041c000100250018442000901c1d10801a0559548110000d5000b56640c80d0b00900421a808001d01e1900001000c580d045c41540d6518810000210604601a450b800d100013540381e42e500d290b00500307080c41ea04c1c203101551442c480b10080c140380280ca036502c080740e80700d05000896608945a030340d0b1103103045d4140094079003010300716009010403240c001e4540306d9400007000c4441603468507010811554000c1d0f401d0400e10029052848103ca006080114510517036131a4890301070318 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582028138 1250 582026888 582026911
    0x504050d121806030b0f120601060f02010f0908091815010f0306090603080a0809061005120109022e11060a090201180902031801090c0501080c0708070803010f06050a08 74
    0x91140142c414008403403038480e0039040c0822542c0c1c81002034024000c014000c6c0c0183c80c00d003800c52003030400b524110a05210b1100030305841e86455070441d407825203191900c0c1155240d0002c8415401140640c202440c0110440c0ea61404080d04001c84191030785440041700000404000082d41c81d1125041d840d0001c1c02c01500c2d03002c02c3c070300c124020182ca8101c1000780d864034001009000c400400b40100d007a07603443c0c035152034503101d003110741d03484040b16200394008585105001c1c6040c6807000c203e00cae4444a0010404800320b900050454503d940e1f211044290070b00d12104c800071602c400e50300e8103118105482a05810503215489040052910b149261118050070869203d000d111200c1c0340c03102010804545c44060040195005031790a40501003159950610b18606100d9440800e46c0000d101c48018a040c0054958141c01001f079804650244803d20100b5441c0000f0b1409500c61030109036290705100c036082400180d90400386c1001420f1152808440c0c0280100340c004554404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582029388 1250 582028138 582028163
    0x602070e130b071d0a0909030e090108190201050f0d0b010207140102060a09021c080306090f010b090d2a0f0e220507030f05010b0f061c0b04020f070309080705010504050d 75
    0x1504011306100310102c42d04a200100001040682c0f42d10800c1102d210380ea51302402050352040241e9030320213025980040e080010490f4110401d0307500e00304103a00c181030160900a20340c0203541241c000341c000880c0c0740d448500143c0a9a818400c2c40c01905508024505819103940000d41d1204010401c402c019a201c1c4244295518403002c0c1e0075075101c0a0008242d1401c83c5421130003500203459840c0540800c40200c1c582d060781003901d505a890f111004d5003031014410402036030441000d4281d6801c00c5e030b902c03513048000c0d842400300c000071000d80d04907003014905003150043c1d040960001c400d2016034014085040074501841c01800c580c9007101184031807508205080c00e000703510080c80c01d0040c0d4140020044190001c0104102c200c5840031401c1c80442400207900c245440840c034500c09214216a107152a4400560030754003610043c104148030100d50145e50261718207401080c00b05074204120001008004c1c040d18081ca40181400c0c680804988034001000004007000c80204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582030638 1250 582029388 582029417
    0xa021e2802061012140303091b0402070b070f0306081902010909060f03170c010501090e0606040606050d1a062d0408030405270117010c02030913150f0602070e130b07 73
    0x81c41c5a082c41005480d0340e802c10144183d030791200f00d60900398540104400d081c2d03506d8984240d450343e64100c0d1408100c0d3b41da07000b0855015000c02071280c10301d9a1041d011400c0d280410a0900d81d0810351400807640301240005401d02100c1e40c030840c02d0038103051050250005001140e400c580d4030200c1c4404000d00c50318084180c0c00b6201e0710076429860f00e80005000f801c180c02555086128109a034401e40314074042c0015541c00b4000c04001c114100801c10f018030103541700545140350001084881c0920200191050740000c0c9900c8552066203000c0e001200c1c0482c5000185140482d041d140601d0449001e84134040c0788240e9200b605e03181c0002107060000703c00d42c2001650754044010030360b100e078940c2910500c804d01c0343c44550719000c80843c20074000022903c2c103000050102040e400c015000c00041c0483c1071351054804c03c1f01800041540400456001800d0303140c02900d00c46081100c840203c03a4004d101c04068942c2c0b103a08000b08a0502290303811220034941448004c1940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582031888 1250 582030638 582030653
    0x31d0d1404090e01090c120302070b0f0706020c0303220302120703030204050303071a010506070b06040f0b030d051225230a0215010e040b0a021e2802061012 69
    0x2c0e800044150308015032600f100d0b0066110315410351107050a5400d05440f00a18241c0109007000200076911900c428002400300300060041c2c00b0a21703200ca403601c2e1003546c42c08184d030462100340305154800300500001d5030500c003100d40c104c10340b81d00030b10701004180c030000d682e10b004240441a0f070400262032000d05109804aa01600014044a80d01d4026141412001c840b1615005210030803c0001c243d5160a0302103841841d041140201c05480710010880208440d0300d0010b9165500d0a4041d100e85040c0f2141008130b985494098450aa550307403824540d900504d2141c40e140c1c1d118046880805203100713402c034007606d464091802c4003801e00b4680112060100c01084490204468030125170000345012840a0f40d2021546079030f03580c3da200c5034408250750003003031006480005004c01002c3e50240040c1e240900c3c0304a02d4074442c400404456004104821039211180f05881c1244900303950190340c10341031b01c01071200340f829000e542d80c0c00d0114050554a036480723910404c04d10404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582033138 1250 582031888 582031897
    0x30a0c030e0d150606020d120b040e12030f0601050f0a0c02120316061103130f0f020607080a0e0f010e0d03090506040e0f09010903020d0305130606031101031d0d14 72
    0x2402500014200e42810506403d80c0b4100d4669141411004a03030580f0108400c0311245c22521031860900e21a03203a4406804000d070010b800554446030003050001c00c020050007000310381505962814450800d01e440c26005002c2d90501608012903442000c405003201c02c141d41c18904a007420425200085420341c10306070141c40d40c030021410400a601d610b81c011821449903008219844081404041034041114090303c40303409840e0000120340c0301003d03003103041e1181151100300541c80d8001102c9800c2100240c40440c2c0120b00e051665030080d800c03148041048415608c4c1c081d9450000305810781c440c0807240a00c0529607030b0420580901c10a03405004003c006544490300c0c9d2500b64907466046481c5040804400c0114201c42c0042c480c4402050309940586440051240e00307501906000c0e00f1602c54401050070000824107d1080384043c51145004101402c5203000040642c1c55641003842d8048500380601c4052000183d405120341c8603050044d8019004c03a400250b500a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582034388 1250 582033138 582033167
    0x31d0d080408071a0405011d0105010f060807021203010f03150b09150307050402030c1908010e011a042d0504150509060f0303030a05070f0507081c0b030703052d030a0c03 75
    0x1804c409000400c1019000710000e0724000382c962022210b06c401e00e078203a660038400c01d070224900700418483d0714814521710b984511540102c901312a0713506001402544268804030510740c189e5014410403420204e640c240d202140018428907044000080c80c191000d0000307100104444c7c8000e1813618144030100003828001d000719200e240c80014841a603000c0841561040c0200701d002c0c100900810001d03060300c001401d005102d03030a102d010340340800800340034072500da030501c40020554040c11035140e440706480d411007544505010240a50507050300014460b90401100486000c0c0280d9004110355040318503114940340d1710041040c100840198680500000040200e080a0703a00f160b80114415611980c2160001d042107810b401240c10003081c01004002c8903060b00e00c20361038001c000000341d0700080d40e00c80c98000203203800b030540d04c120380d25080450340e890102c00f0520201c6005100c040c0d02c0351440302a503075150b1644180c1d0405070a01620100c0c490900d4422403010008e60b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582035638 1250 582034388 582034433
    0x20c220c0804140a0b040312060b030109021201050a050609010305060d0c030f0b0105090618091c0207051306050102030f0d0b0907121d0607210507031d0d08040807 72
    0x106000c00108803920448080d54140d03880c0d40107100312100050140c2d4070719040109030103562240d0b079080301d018010040c10380703410f5203401021680d140c448000358002c00090900603034848282c94141d44ca0f0005a21031807141c4c0b0301050400032134030b503c0c0440d0700014007407034006140c1c1e4600d40050707410700c0d604001820051842d9000300401c1a9070980306640790080240020380e0307981d0001c01140c03e20480307515400004010000e95a5450310125603000301e4000b0541d074a0680224404044070410303001d40e80141e1110400300300c80d042c405803030001c440402d101804410b003002c2c0041e41d01c4c41200700d2165040400150301e50504281da2107050803e00081003a0b0517400c0403007000301603411641c0301c0040e25281c0142c510081c21840386e10200b001c5041d002d8901c07550b42d4081074070f401110b410340c1c1742c1072244594008019244c9124562041150f80c80025006020426600307090345581c1140b001c550002d84442d99a542007010540e00c00d82c0021000d070345880c2c900e01a00302d03031510490341c0040c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582036888 1250 582035638 582035651
    0x1205060f240a030618020f07120201180c05151e130f18060b09150307030f0501170c06040f090207140a0b22030804020d0203010621051c020c22 63
    0x190f40c1600031808a80c0d422a585607500700e410301c3e44049100b6666542c10600c8204031001c0000c40046140d5101e9000e80000500d40b0b00f9021424103c1042800407219288110300522851030b1044201c0102c900500495040070700140d603401002c40d0244003403003402c0000c03441d610304c42c514411318005400a0f802c030340c49255480260707041c0b038501d08181e40182e03070a0000106400103c0e409884075090000d100040c608540410707016103510292200007015121481104004114080d4034003c00781400d04a0340c4919040308281000184501030780305600c10001000f10260138040030b002d45a5100c001a40c428661421220220606020000e240204441c2c1424000071029140c8100da80742208941da0484c17140365101c817031404000801240e2260081009420400c908401c07a510140001489035140c0c00101107a1050782c0c0121300030400c80b0500410080c2c248108401b580a0078621007072948185406903d59070407201c198000c3c1601c110010b600341076803480c0036188003030720402c0001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582038138 1250 582036888 582036907
    0x7051606050d05070804081e16050c030106060c1218050a1403010c36030506010f061701060e06070515130c0e01080703031b0b0c0a1205060f24 63
    0x11a00a02c0210700309038a440005007104d8090f190703941c0b1890340700348298904003414883c4a42106100b020714680b05050020f85501d507030f0103003800c21240c05403004003051100c2e20101425a007041e002903040090004036180020300c1e0301c0650070748103c0d5040c40c5d0584004820107505002d5581d000c0b961040350340b0070009901e6080884079065040a800034041c0259240080da0800c426461040c551510041d06440100200d8407094940741c88100426085940791540c5281100070b0f04130514004070340d4000c110709900408180c4140103a0006520a503140031009001c120b0203018650048000207205404c12406210800b00318070000809a82c90074240c98803c1c5003822148200d5100c03980d61030204403204100c002d60b040b221940010400542540d400b2a00084481c66848071081c034070b2030a6000400030740009100f01440140781d80c958192050003440140309140304a1524a0401449266112100382c1030b141c400c140c40e0001e0000080f20f0000140d6211209144040700200f03e4200703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582039388 1250 582038138 582038147
    0x307060501060305090a03141b010903030209100c020d0f020424050a0f0b090f0607050604050307111c03081305190204060608010e270d030506100905030a0807051606 73
    0x5a40341943c08005568030b90400903603e9000d10f1029000c24655a00001400e0441c001003544138104042c1280e10002d81c202c2d1400d42e56229001c90100ea00481c411416003080c0600c0840f840300c03450169040c04080e0045070300150b080c1005064201c03040400000c3d0f4940c1d4001404803c40245030542104c41c04c03030030182ca40751a02646100e585541d0001401c03102d02c2003500140c1d030154843c28030b003094002c02c01017074500c070312105500300600744490008a541400810301c22400362014603900c40c01854100784401940944600c100c030f01c0230b9213b5000c1c8618162100c880e5040c200000192aa07400034000c01e402d805004003035128414070a01c8038403050214142c002e01c07d40302070081a807504816034032520240601408411050000360120f5031446030a1007002901340071140c901400502c2c0f90403c524890b541011030b45078410f110060400e521000400c40c124a03203000c0c0721781030000080e1549101d000140601001048482c10311005000055842500103400108540c1d40d010150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582040638 1250 582039388 582039391
    0x318160f150c240b1504050f120f0c040606030e0a120905060a0e040e061626010b0702130b0a06120e06070809060f06090f0a0f050c1e0703050403081b03070605 70
    0x32816030400c882c80301c060802d0144405d1514030501c0c103505150909080c840180d1304141ca03d0f600510807034060303071202014002d00458401d0203020307150707041080060106071107156204c3e004141c5880038070101d044000c24112503095100841c5900010390100440b0307011003980003a58000ca0010320058595045900200e000c00c06131818001f0075001c0403401c2e103503070080f2486060703a00a402c0120f6031611400c45002440c40e06c4110340c804980d80c0340048040c4401740c02074514601d0002d403603015403900c2d454140c1c202d6003200040c000c450700b03103010821542c00c52040c20b05000420301c6158010110740c01010540056204451980c0f030010002003031508180d0b0300d02d180d8052035021612215030300380201c0c0300d40005401880e0540310350b0700915090384000d00c6196210340c0c8a640000c480c1140c0101c0d4040c0344040c03812034031030a050550b501a905241203999125400b0003110340001e4019003071302c0480340c03c032001a48a910317200c400e00c112078915031400385500000900170108100c503449103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582041888 1250 582040638 582040703
    0x2040b0408070f0b030f22030804051009031d0f120d12020f0a0507061407020f16120602070201050c0703150605040203062d060318160f150c 62
    0x141c581c0b0380c1e5801065180c443d00d004050000e2420000108400c090004140d001104c801140031002982a1501100071081c041100010041c1c4144024460200102d08030355189040402441520f96005020214496408400710b51200d224032403030307610704070350320100000070b801050301c080544042611403504c0400c42e000708000c5c032026042000ca0f07109a502000c0103141c0d80d80762441d0301d902514241c200b0b40c421078102da10340d01c00010780b03075000500d980101040e030010000ea003500d00d00c80d400d041c04807800c055070680305441004001f480110071407006805c40e4005030303125481c3c00100d0304c0e03125001c4001418400d0725000070810950700602145010515010810540c0310020041607100903940194099a064400300116868051050030721072610648281140080e001c41c402d13400803100c4803018610003d41e003640d4041071010030b25007225412600c0406042c80c0e840d074404400b5014410080c1541e00b00401c0c1140100007940d035980c2c11281842c8200582c516111042c10031038081c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582043138 1250 582041888 582041893
    0x60608011d07060e012d020a030e03011811191401020c06090618220b0a1403030d23160f090b1e040302060c060103050105010608070f05090a03020402040b0408 70
    0x503103410207008a4400107440c1c00e56144400340c0221401100c800c0c031018443d10302920004440c1800211440d200c108070481074014003540b1202d03081c00741c08851a41040340c001c3e4180b03c120348541e440501031190a42c2d02c54541aa410403500c04100c00f00394550560f842c4401d40301d408220750305a0103142c031000000b6421110040303a44410301880b40a062202070f000359090220101c0030714a501400728144015000c0305050358140c0b610004c44c144080e030351035041d03520310201070a800c0c581d065002400e60704003100c54003520344000c80e580344118580c3c01c40d025078034080a0303007044031281a50303025a20455001c1940c00c00e02c2800314002d00320303819040488c4001000d4640c6c0e034040c11030348003200c1456144905112801b500260014122850894002410480800160f407108080d001800c8805c2c01807000b98198537041c0d0841304181c0203001486409004c012110340d00540184041e1340a103080381e1901c1000c1c2c0400e80140301600000c0d031040c008900450300400ba48080e1040f40c464608 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582044388 1250 582043138 582043181
    0x40f0e030408211207030e0a060c03020d050604090503030f041515050102060a0b01050d021e130807080a11060904090c030308160504030f02090405070f0f030b0c0a0806090603030706060801 83
    0xc0c004454410040c85109051032000054001800f962003184003980c042c055030b0700030b1515a143d1049a4ac4404482d0201c1c3d8081421280104907200d8190702460644040124140303585550fa5207020050000780c6000445000804011030400181524100e019050100d80000303083d00d40340cac043d14040c4900511481d00014415109402401c0644506840d4a8604440c485120f4040d5024154201e0040340078044200004400c0009058000380e0122500209041c110a03074204020369000c0da6030755000054040201c0d050500d01950704030112080380d030b9032178190046030103000128409090700707070307a0358000003031607002640940300700400c0d0741c4e1007819002c540e4280e40e40e002d00d010140c01409004c0107500103080a00119400502803011904929a95062189905241c0e04a03412640701070104108001c0459040c9411400e240f0101d800d0201d440300c0200b24030b000500d23184c8680311140c08241c245d14180304480150781c112906021041d02c3c1c0501c14040c20450588510000c2501c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582045638 1250 582044388 582044443
    0x41d150402160201140424030c053402030604030c0311070341070602010605012d0e1e091803070605090709140604060906080a02040f0e030408 63
    0x100b240c6100100950350314210030103400444000d141522482d50310302c1c01300001b1450440e100e203400070071504000301204004070803000a007598040200141032020620410022000119000040302e2800c0907001e0b000b4541082c0c184a9148003c000c2c1d058015a8140010b041e409414141c20b24025119507041038502071a003503035401da0f840091b102c40c0300c0301080400d180d004000100c56100b008880b400b42d0000d11010924540005035030b500ca50b00c00c0381d0411942d502802180001e01c42403c2480010300e4002101c01c02c00000c0c0c2c40c4400c036003134030f002c0f84080034011361500c0703000f0070003501d0440c001c89000c280301c0900c40300640c40317841030101000061090380f100102c0c00c07041104030082e60402006a89482c0a42006070404a081c00750f00b50210b882100c0d03104d218402030100c0d0900956061520921003103c0c80d43d04104221030510310b060100180000b10705c8070380d41d8140c6000466090701100e80b4020121300003074003c030340000280010004000210001308251107003902e0540541d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582046888 1250 582045638 582045641
    0x30e0423090d021b18010b1b0102040e0103020d240603150501060e091005030604061b0201091e0204200417010902180c13030804151701030803040305041d1504 70
    0x310b0200180d00500c5113401450380200d10004000d00600b511826070004024242c0c1075070241c01c1080748410100b426003c01152140b51071503000b210008504d090704000c071a0b503294805006c040c0c01505024070400c200a0300400c000d0000c540d041c442c581c1c900130140240007406040c4401d4420b030b4141011220b9603621846030b98102e1311b0b65190100f1a01000702403080454008015040c8103108c0040000d65440501c241817140b8891038000a80000610385820b20008020404d4116803402c03a5000c0043c0c0084808500024161041d1100c1700c00380c03001802410141884070141c182c002510224504081c01800c161160f046107410302c0e803d070b00c4c565802c0700c103040b00280d84002c1550742203051880701c01c0007075002440d000902d440c0010400a0034552815a4022500410002400c01402854038040814150149416030210103443c0203400d6000040c007006d01404000000306e42018003510441c1e006080512600340d00742010071020f802c442d0200e584a241100c101818110b81c0b0b400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582048138 1250 582046888 582046903
    0x1020a17030a0b09090303150a0f0e1014030c1e040f0207330b010507060c0e040501080d0203040905090a0c03060b0907031e05041419020f010804120507030e042309 72
    0x5402182140c0e140925880a62184003519030090411500450203e0ad201d040101501c2c03215280489800d0002c02d07200c81071203682c0115000540d0801002071a50046860703559004120381081c1140001807284805039000b04000354024504010807c0700c2002d9000303031404034055580919103002031400c8184240c07250001000d80700132110001c00d5907680d5800300304500f1042c500a4140745843c0d844100b114081180380003c00c1c055900740365140b4040c002c050150103001c2c06000140400e05000e55280030354090000350035120030006002541c100304660f4103a800810b149009a500d003451001016071012560203900d83c02d000550b440d0207070081e20f02c0c00034500011100a00d001d41444000d010280040b43c0d01c0c20b818141800005041011043d042c030075001d42c0300351056a104104041070b000007414103000c40081040b010882c500c901415610050410035036440c8a454112601103a0011482c2d010f450540220a0115200807180000607240042815900c929049941e82c101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582049388 1250 582048138 582048151
    0x1823060603060c13050a0603051f060e040203090a0f0804090e0d05090d151a031c1719050114120703050613080c030a02030a12021602060901020a17030a0b09 69
    0x400c202243d02410710078002c24000380450450342500d034440000400b5007049500043c002500d41c1c0074001a02d00034001c003803441c020000d01c0807400e8900702028018408110445100da5800301c0092030200040c07007405490303940000c0c0400c40c100b103841e2803840e80d0494002e00c2c0c41305181c00100b00111200040c224a01c104070b481d00b41c104222075040140715452a5012990380c0c0003980307441558080341c040c01c020f034030000c007040300c00171007003804d25241c26000c0d43c01c084100820862102040c1e00112040302c1e01d170a5101c4010195101c40805904145980b80309605603e0080000354245460000d144001002c0b01d4a80c19440354560080d07551405000140003500050007094580e10007200b4100a07030301c541005403c2c05101d00c082801c6400c240105e00150b040002c9100c13044ea44140c038440c00c085040170031800c10280c8001d03880d04241c10350700203014410000320064580c3c020050a2803007a840424150b41c082220501041074009481c5223210508012000b081ea262825160788500c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582050638 1250 582049388 582049393
    0xf070504050433050411040e010e04050a0503070602180303120a05060111030d05161b020f0f0907032c0c151306080609240909011823060603 62
    0xa080000b000018400d0f0041892081d040f0303c59525090340380e5240c104100f10318083c26908615003010310040d80c1d40324040301042401040f01b0f001000349900c62030f054909082501c40c0d1940e0380c1c80c00c00d00d016045600580343c1d110200d045000c000c4190024003660b5003241d02e268990505400703040e541e01607801c40007a105686800202905120340c4a141e21080500d482d042032040e800d03c490850307001561080e101030315001004524400401845a080c0880c501104050320304174aa4600079400c80c0028498915441c445c41e095a0380304194003403030002000d451441c1403825010f0020948d50152010b000c0c4403100d1780a0001d140c3d0307462203900c044413015101070200d0000300803481c401e41d2800f1004260602602c400c41d4040707014031025207001c0d01e0385030583c2014001c001401a0003001c044000b8404840e41d0611603400d003171180411410b5800c000c25860b07009c01140500300d41030104001000c681c510909210103522201c217a4141c0d445006404c603000391400e034480c50300b22062a0990b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582051888 1250 582050638 582050647
    0x41503080702010309030207050a080102120106181a070c080a1a060102070314101b1d0f0f0111010e01091103010b011e020304030c090504140a110d05030f04060c0b0f0705 75
    0x41d40250000c0c5c00d22886441a944410340320000151a0315544c1c020b45e02c503a60100b11000700e0f00000001c50301404036424240c1d0390b5203240c880b211103800f29001d0104002441001230440740940025640b481d90b01a00b81000e4035100e602039a43e8003c600c50607100015055020140e240048410900a10042c0d0103840440e0841d02c40ca500c020180805060a21031003140646801044c0b14060311050080440800c41885401c010103060005c0800800020150345040142c1d80300540f89001d0401910b02303c0c001d012440050312804441401000d40c1d50901e002440c1110040d0320120140f0320940543c4160f44240e01818203c0b11041c100314041b500010101c09580c0c0103080b213a000305410700c101c0e45403035108da0301e1500100c55980040b030240d0b1070b0401d10041004110203800f07007489c29401080f92001d940c444202142c084550306000d140d8560380c0c801400410f004a503107091500f11460380c1d03140d07501c800412080c90101300343e49a20ba088041070342076103c2c100150080c14143e4a030343c1070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582053138 1250 582051888 582051893
    0x170610060909110d0203070305100e07021f0b0d0524100509090a080a1809020a021b040605040219080f0106080103080d0f05190c020f121b0303150415030807 69
    0x400d0311028442c40c003c8207001300303d030305a824001103215000f80d0b6804030b22401d1517901d030704180d11a900041609020300b804c1140c51940059a1040c440703501038104ca00c80c818203a18801807542410013600082e103410701d2414094000750006c40b6200701e4022004080d60440f1040301c01100b81e800c07060040300514200700d0344c0303000c041140c0c12074060b800780d42c2207030401c0e5614101640019103140108503140c0b00b5445400080803160002c00303a0100c1546000700c00304000b52a800d0007a000891404021242043c507116075111001810000c0c10444d569a03480c00311140c0d80c10003d446400181d0f91400141c04103150f072001c907049030200d0703d03001d1503a401c540e101e4000d60004441c100b00240da402c9185500b40e1a401098080c50942c1c003115050000304891a043e6854a80711106541c00861100c6001400003070b01c0200c482c000e0411354032580000300c1992480d40c100c100b00614071021003400041b040c2032003515140c1108540400041c4005034115207400c07003911010300803107014001c1d17001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582054388 1250 582053138 582053141
    0x60705120c03040b040e1608060612150a0801020426100c17040b04140d0c020108190e03190f050d021606051503010e150402060f090901170610060909 66
    0x440c041c840c000c2da400d050303d40c001d0051a421a070300030840c42c078200c420301c4021120b80c0c2804884001e5403811055529000021400a101d04900c20311a4402c80d00041c1501d10300e0f001482d0007030002040b82040750707640c07420700303010f508140514420420600341c0303041a9620840007211190820020340007040d20042204001c1c024801014244419000d04212008031030480305d02c2036100341360031011420700d801c2c0011035103201480e45142c1d0780000c80400006400940c1600007aa0920b03200342640c2c1d13888450000c0d071101d640020003550400f040880c504e40048050420b5041d040041c45403034100c1102101c0ca003034004007060110343c080280360b120382e1803600200340500713034080d10307030290038043c0d8030710302124022246009040710418490304c05180a0160306c0c60030310054020809820700110408901c00c0152000340300c3d5034005043c0c020021180e00782d0b2001d200050440d807256948002070140500d00ca10010101c5c0180300000e61007600a10001c41943d02c5641d6882045041441850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582055638 1250 582054388 582054397
    0x7030201180c180e0109140118080d02161e030f05040608150414070807030f020301150f112b170402060c070819020301050912030f04031103131406070512 68
    0x2521502c1308103c0c1c80b090000d0060f00b080c144694070607008020013551607403c4508107441d07449900c00c0b02c155000400c00d9501901c07181003550b00011f81d40c005903c04110303000e032403040042c0301004e6070407100780315140c440c0c46003006400794848006080078000c0c00c6445108a01803c0081816031001c614000188049105992006000042e045000500d2441c3c4084122500400107200000700700d00c03940c0c9406030801d200510a0f0550071075050541078805111041c00d60420000626140e289a504c5601c9683e1060420b80c26112410b1060345410210728140889034401c6050000c080c61952040c000d042c44c00e10001580040d64480e0303400c00070713a82c0c0000800a00380c41100800716907000180401844150704003000d9820402c1803040c035007503c00007007400b011904410511518419504120b03030341308400708100c280c2c0e641d179807800341da02c01c400d40c000d00c00034800481d403015a481c10a11a405440c80d04400c0380100010004100c1b1904c40e52000500d03e8005c00d0154040703040c54000360 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582056888 1250 582055638 582055679
    0x30a020a0b0705070b0c09243f0106020c010e0609100306030b010e0609181905030c10020310050a050307090e1005010902090909010b0a0b0c0705030105070c110f1c030314070507030201180c 83
    0x3c000000140300b27003003d80241c40d000324011422000100217440d01000f202c1e01845084c2402ca0550703240c1e0f40010500d000c0c4520403400b90036070240c01051188240d0009024551003500700c003195071508a40481d001c011104640500000000f04000031a80c0032460060200c400c000c100c81800d0240d0303102c185060542c100c03041d120620480080d14400e114404054004100058032481c00003a5400194113941c0510b0294244010600c0319807404188003043c2ca0405101140100c00f0300e4040d450030450034490001c00b0f00d00f10010030705070001d40080c9038521080702d804103a41c944564003422103014144040d400f5000b81c400b00141031901c00034009080c11a02540e07417a55807000482d007528030854100000510b00c1402c80104411110300322840042a103442d10605004404070310720210041c44420110300c045460810903120360000740c1c3c032454050a001081c20802805030641d0002d0320118090f500703201180c038401c00c100004440c3c494001c0106d20f245440c108102480031f141c049903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582058138 1250 582056888 582056947
    0x12070e06062b0b030601080d200c120c04050112032c1203120705040f0e09070603110d090320060606090f011404080a14030a020a0b0705070b0c0924 65
    0x4680155409010305c1d8002c18120f0301504006c10b84210042c040b20241c106c0c100740b502c0d011200c100c071400000e412440c1d914240c0d550b040360341c0482000d910389101c05001d90751103400c0c000041703071a1a0392400030b00914425100c40945c01c16001d040101000320200c540d051600d910340200c03851500c46d0078003034400014420380740341c00c6040641e0720f00d1000484581c008078900040130880000010445c500500b880085010282440c510302c40d20790685208010030161101c52404464001904a840180ca442000c205d03103480d528004d4400c3d00d20244020840e00380e1080b4201d1004040742082c41101d0003401e05d0b103007003007410801001701c8980300418100011012a00c030313400143c030001c0000d800140010899800c4620b041d91000d000e02c001c3d110304c0d400501c019801550000b43c03a42000742d20074465066941d03105000c60b40da010b4000042c056024201c00d0010f1031a4480042140e039109a618014034042c0c54411105809007040400522404001903d01290701e0350701c6403046402c00303c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582059388 1250 582058138 582058151
    0x9090b151c05010305030403110303070b1f091b030b040908030c0f0c0f0c1e010c060e100c18090c1d01030b06121609050a0303080c0912070e06062b 65
    0x80b030350240c0040360702d5400080d0034401d21400644541d03001038110002d6240c40c0d020b0b03858035a14007019004130008041c107941034031607484041810307000e450094010004040d000088904091440c400030020901d4081486501d05149c0a03020754a030304144020b03d0740e25940c840c408903a1020f0380a1200300801d02034080440710500c150041643c241c401002e24a9906040181e40d0410484049001098002201c1e0990300843c00980f080e80041000483d5141007040c2810300c2e69511418030b80c1d614203025803c030560030a11088071045104199032032036450750034400450b400d80c070725080030504108003001280014910740525a00c10304d0003043c4440040040740d03094100072407411901514030304000c01024040410014480e80d8984a04e280c0d1403c400300f9035104203808003908120802d0002040380114008031506108090130103c0b40319481902d6030b858214034010b614090481c60081041480c5c100140c0b07407852036001c0a0042001c131203619818400d240070036254500d45800c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582060638 1250 582059388 582059437
    0x7080106110c15190203070303050906070801051c02100504081b0901170a1209080c150a0c020f03060c0c1618020a12050a02090a060804050a2a140109090b15 69
    0x7860302c0741c80181750000c5848811515020f000d40301c00820503082a84a0400c1014450307120211504483c000d8524100b101c0b107500c0200d0a00710340040207904000c0102428081d04c0d445001007080b20807003030566082441410311090300060300c400c1e2651080c0c0c044014044008564800d03654400b00200302c800e100e286503507104411a070000c0c08d00200d02c20340c0080041403414000d51007450002c485c030324800c40c030121841045008000c194010002010320240071525950b400b0100c0090040031038001e4901404503440c550301c49581c0d0300c0e00f8044e0100c0c0c15082c000c01900182a1814550401d980d0655a005d000094104113220340c1000690001a40754100d544651350041518250240c1d95032480e00600c404106154021010061035604100200b0800306441c0e41303680d1f200030741243c0e50013041801503915440d048841c030805d1128100140e0402171100940c1d07082003e80701c81200c03039610307000030046820b10b005841e046506d04600e00e03035031410303034004003d1f4000500b1321082100218 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582061888 1250 582060638 582060667
    0x61005040905151503092d070915060206070c080a05040902030709090b060a120902030708030a0201020703180312140f0403050609120f0a0509030a021807080106110c15 74
    0x1a580d040c601ca001d03010380c41d40380c24011015102504e400e940c0e14170f54203008200c65a44c1910740200c03c214022140e000e00141c034680006200b508440c2d045916441d203a00380d107001030580070303c0a40700800d071200c0050f9941c004a030442c4264516102d1100c0050703c0d8540c00700b20390080c4180d6040080c100f0003c80c0c00445480618000c01443e5201031980e030510154204550f03030311410790302c50321060090342c0040b80c0c0402a030486a11424000c11200c405201003403500040d6001402d090102081c0c00000c00d1b4154058081c01e400f0b9503509255030002001c4c001c0d103a04500000c0d02c0d0068131b000300802c5a000760b44000040c0c5c3c4000046290890414400f1815049504111000d420210500c400d0034020814a81000e041304582c2e0318140070701501c08d00511078003c9070010700c040403980c07008659052101c60040798001d803a4008001d007004c034464000004490003004a08010000b0682e50310a0b0407404500c00a180100300e040c503000c0401121000d01c00e040740303105208010221008401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582063138 1250 582061888 582061891
    0x7061401060f1404230d0f0311070f030305030609040f17040603060b0901020d110c040501090f050f040c05041505030d11070b0c030306041e1b110a0506061005040905 73
    0x15075959000059800030024846040f01080184501c0240014400d10300312070181000c0e52003140000409800050104240816104011f80701c0b14120021606044e042608441c2d00d145840039a21441e07120b4907145094041c0740009000a1414000aa500c0c145200307915007140c010000701840c894550b450804202107900c200d210260013080c2041000c1d01801120302400407455094100204100003e503222418055078040004000d00c40304403080c148610740c40e119000c0c200384150740e180e180c44005010380b404500c1d003540c6480000382500f09401540c0e0300640d400030303160054502e00070800c8007034104584204200c40e0b0303500000810f650104401d80e0841043c1e2a807005207891948045c2c1080501d80c030001074100c01708841104c03014003008072030303101e04126000211100080700c0e50a429200e4071505240c01d1504118050440d10b9003000f0706203200d51390300c111450403000b07040c64032000c0e619001030040e404140404c2c25485c0141100b04062139070b03e02641080d40d590550307410740e2030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582064388 1250 582063138 582063149
    0xa02091005130806091c050c0703030e0f01020a0201080a05190212060301240618080d020c1c02060301030b0601050f040e1009050c090d03110f0c3307061401 69
    0x100002ca1000e200000d1071144010309103a00602510315291412603258850128000d14819003121084641e40c0580140d42c103500b40e901c2281e868076200c0c54003034404404041c2e60341c414910700c009406d0a602c0090300164050781a540d15000e0707103034103c50070040c1402600500110b403100740c141c035040c0d456101a0070b1440445c025004d45040000c185400c5900405501d11445001d881d10b8070242900c0e07021400303e50741850140c1a4130190502010510b00b140c0200b800c60144c841420f401507400602031119500458600c0c000c070a4441032003a019281d03000007500800144010030103d0380000d030003030740f0035411306240c0d1800a0030300101c3d4969000380c0101c1001080710040c0b0840e90307411001d8070003030140c0320b50412450070a10325614103400741c40d80140c49000c0c3c010b407000c10144201c0014603540d5046048900d0010315a10035a2035240b41c19000b4003c031003060825020f45035089100c1c405450300500001440d01c16a85d100d07840d40503000642c0c41603221120703107100c6503c443c41e00c1d00034038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582065638 1250 582064388 582064397
    0xb07020d0302010e0d0306030c090b15031015030c1409030a030305060d1e0606050315220203061501030e010606050a081005060307090303030b0a051f1404060903021206070e090a020910 81
    0x500310f191004014a00741c025900f1141f40c01c0040c80bd40d11268540c140c019909a165500e942d1901c2c18000d018402e500003c0c5240644e02414000300d415070000f41c1101c0c40ca071101c441c20311010341908034034007aa0500952551080c1501c1b80424044e0340320f0703604030300007504182d600281a2100c8022405905c0322080b90500104a50140320140c481c0c04040d20040b0040d000d07542403001190075000002d440c07001c401d08032850b50052901039680d80702c00c95601038140c1e01075151601c5400340f0701d041641c2150219040c11000f9a040340c0611480040d2401500d801d818101074100c22144001c1c01441c280c02010001008107907541c0301030103907224400540e6140c003075504614004007940e4030102a40e0107030922100c2448183d44120040b608100c0070b8220340c0101d5002c5a01300d032210074503050964441c40001d4003041044d170111245043c2e84c003d40d000304900c007100c0052a40e0f2030007190301000044c00e1102003822440e0442159030031500d48035000d0304148440d00005d48000c0c50180140105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582066888 1250 582065638 582065651
    0x6070804050306070f0c080c100e0d021920060c01020f0d0b06090a05060a032301030308071d0405060a05090a050604060f030837090e0a02040b07020d0302010e0d03 72
    0xd1400f0803400343c1c0b010380c9107800b0202100d0740c10082d16024075510010024000810b1441c00032400700100a800300c4052002c1c080903001c0c8400a85660510007540014007418081a07a009500b0101c0d451040d401010842004140c0c0480c07a02008480e04841c1d12490802200010290034000340c45007092400401c2d90b079010034081076044422000009000350000d104042169590020309001c840054415076a252800a07003100186402008464034408904808144800039443d2a050b24404d485107205604c0324503066038004103103080c000c0403400d00b2600f41090b042940045c1d8010001520641c00d103070729040090180c001c1201e100c80e20f1a995000c0002d549014051203005040e00c40c244100c1d14150740380c0f00300c80d00c9003101103540c2429800741d8410f5400c050346008900018070328000011540b00700e0040040720140b140e0600c12000d080441d00d16080c5100f15012030b00e2840060385400d001d5403c0c032244020341c0c1e400b034056560390200045010400d0000e1489264a6030740061007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582068138 1250 582066888 582066899
    0x110303130e0a0b01230f1b010f090f120e04060e0a0506040e07091116140d021c0f12020c0c190509010501210903050c06060d0c0b070503040506070804 66
    0x407079400801c80519a4107020210340703070b070b41c0144a61001d0145011011040100c1d103206055a00c56181c00301e482000009503842d0360800812010b01c50071100b0024400c0e48400340821050b580d200502070640032040c041000060851040c00c2c0010700c40e800c140c42c014482200203411121036500c01841a80540d080140f81180ca200301c41e407202c400c580c100801410201e52981c2c03008240910a00103503076041101d100d01030755098130100e1011420001e0103180c00c0c600050004040000e1084621828603c580040d00104450342040da030090140e441601104003110b6061010300c0070070510842c200030000c0c40c0b0060005040c07407182c44c030050038660740034018800e0200080401085c0c8940f44607060140ea661002000e04503842440c101110404103040350405041d00703068140e04604c4e01120038100354018020345918500f200c1a1a20342c0e640d2400d0248030102940c00400b00d541d031800c1032154030341c2c6502400354a802001164140707600e800c00f14105030f11044c1d00740d90500005c03804110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582069388 1250 582068138 582068159
    0x1a010305061608180106033804020f0609041b0f0908070b0a0305040c0803182b0b09012007020a0f14040209012105060907020a030e0d11030313 63
    0x10080c0008002070382181c202c24009003098400f8101c040e0814006603d544003031425001840a5500905001400f84d01c0600000e08003012407100b078514000306070005030f241c10b0780c010144601c0d00a423050381c0c510303543c408020703075540004d00e00d80c2e00a54580e90422041d800b0030307a007940480d058a0700700e46000440400380109290f40d1184403107911843c0213024a401e00b4050318409025800c0118240d2a645070105220701c180d0822a40c070700c00030441400b0301001e20900b9504d114280c0c5d60300001d001150400c2079001e006400781c0024181c0c4800c0c103002414143ca07050303000821314000a680e8400091200c10f444045541c24000080800d041065190401d100001008000519200c080c500408002001c14071051140714950204210750242d0068150301c100459030100301c0072062500100e00c008210903522640640e06420001c0d021500001e5800f0110307426443d655216810103040103483e613141e2104440324a0065686c1d45961030802c050060745205070000700341103060011071700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582070638 1250 582069388 582069391
    0xd050909130f050a020a140d1103120c06010f06090b12040c0510080402030d020102071e020d08030115030e0c1804060f020309030a02012009010804110a09150f0501090b161a01030506 80
    0x21241d41c02000400940c2d460041c25118180d00100309c607141c90214002a06001070000c2c0800c001c140001c1c018440c1c2000305125042c0c40c0c140d4464402d498a9000880c0e04507400e001c1d049501504000c1e540e100506070380010381c49440740c3c10100c11181c407071010440d1140252040000304414205100851070140410070001007548021424400c0076111171040c50380400e00381c0254070305103010307000350346800c1c00021444d504410500e0b40e9583d5140700a881c550b10b882004001703840e1688030042c511001c00c0d103181e0706070003c1a49010f1500160f000c02c0006000d0000c07109035170348207080c507250f85e6540040e42c0310350391240240da1a125a141c2c003070f003504c19801303c08010541a200c28840c0310030765015920800000c0c41c06402950302ca19100f40460b076540a11030b44a01112000200300209401c8030390850034624480701e50a0351410100800015400390724086800300717400344003c6884002030000803090411080700c03850a5200e01012070f4520408001d61403185c03005005004c1c0402845 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582071888 1250 582070638 582070649
    0x313030215090d12020f030a090302030c09251b0c0512030301082e050108030a120b0310020c19061407020d0c02010e0d05060a1d0d050909130f050a020a 67
    0x491401240b0000140300311100f0f0002480d03031070a00c002e810302d1403081007007401501d0600d040301c4d6103060b07009000d04004401d200483c802c3c46000c0c001c43d040e09103405140c0c0075a0b0385401c8a26034041640c242e460315880d17151035200b003000c00300340c1e1820340347c410070401c41c514040c07202d8180c141c0c10501840009007180104003010b9200300010424058001074401c84034543e48036900303803403100800c130b484000d400402c0c0e05e042c03038100000851688000300050107510700035103520500c1d0f40404550410b1710703140084958507400c0760700c145419404c0c40d0010941c54a500c02681d1224400680c9112300903072412082d24103540d40c40d02d011300f0f15000c0c2d011030b4210285000070100090583e000a281074101d1038002d04100601c1885002034490404060b05641c1c0142521920b1802c2c41c0ea1100900705011019603030290010502d00601d40400e402c81c1001556542c94034003006403041c4288038201400d840481d01c051031400b030118040903100f541c1c031072061b8080c14404405004205945400340c210 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582073138 1250 582071888 582071929
    0x212010b0f030403050d0603050114180f07170f030f0403050118050c010e1f05090a05010906080103080c0c0d29070e12010b09041401060605070f03030e0f03130302 72
    0x10300707000c440a501500d500c20751516200e640d0380d6110042101602c1540e1009082d503081c451050080b600c8150f40500c102151705a01c0c0d007860309401c9d82ca680340d01c18100b659880d0441340c4103001c035001d00d00c1c2d15119400e07401d040f00e106c109031405291071a882000c10f0303007075803c022400780104103081c022404060f000080c100da034000705841e00d5444e10704500c3c0d81411f01c010010700000f1900e48a205910104078079005a103403070103a22000d0420347c0106082440b0f000381810211700366000e031a1200a4030815912200e5030381c219030303607068a40e1025020845c0c40c8a00c040c9410544e4481c2c40c50745c4210311803981013000000c44082008004c000c00600705008548100b00600198040034160391640200d42120701c3c20b2602003400d00410b50400300c1604881d04004020900c101c440c00d40d65040c001c103000b0041141d554504548034041c8850052100940c401d580d80403038403d411407220747c840c600c15962510b04540d1403c3c9075510a03441001107800510042041d4074001034907400c0c0d90b554044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582074388 1250 582073138 582073147
    0xc0602070303081608160c08030702030d050f01030506010b070503121005010201150e06060a0c0804030b10091a09060f030706020105010f05040614011838120a0b0f030307060212010b 80
    0x10003901044004022485403200311b266450080c4c812840450800d400403a200e54074101458002e4490380800340300480c1d14103150102c0c1d0144d615185080c100e03901f003c050322450b401e1000d141082d82c802d140c2600c8a10040c0103014040d041c0c1c41100340a200f8213118006114540800a400d448680c3c0410201869040d820010041e40b00300d8154065011514940d4039030b0086410303100501080d074060f10700b44c40031a02108110f400d0031894000c4a85080c520300c2c0741e50f0303142c00a0a807a90a290460319011200f060601030418154154201500410402c0c9030f4a40e0000310b032400255500c803000613911340004200c0c0c84070b000082d601074030050f070f0203004003411f0125940c0c48592803a51541001960400c40500080c0c2d91140030260103640c0e1034000843e018400311042e00000550001c0303c201c2e014010491407448000c50702200f1842c0340c1d098007517030b8030342c03002c4000c000701c41b0900e4100780c81410000499030240005d241092140c800141c8901c4181842c3c0041d00058200c0d80c8218010407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582075638 1250 582074388 582074431
    0x203070507050613080105010806090f03190c080c011b0e0f0117040320010c03140f160219060203040b06030705090417070c06030e06060f210a0c060207030308 70
    0x1e9079405803442514003a5507045030307044010071140150f221030a154a003500100745004041000d40c0104144401c880b06c40a88503140703070300c82c0b04501c1d0f514016400d03c04410b05d101e0044051401880c0a218000d05180000d1450390964242c025071500b071002d544070821100d5082002d01d804050182c803c907903452408030001e404ca074dc000949401078440c020000e4100b5205561100780761204210640156111040383d03070207041c9141043c0b01290605075685586031482890704e04c101c070b40c541e002c40701c1e40340c0540d5000c0d419900f140d07040440c062030895081a031084d4680c0c0300b00d144107040060b602d1505080000031184085d10151003070f040604204030300d540c5e1003060f40d0002d4000c0c1c2101000010b407035204817607104546c0001c1c8800c078900b400160703841d010b034099100004003005854155852034104820a2302c40008140d00560007901003018641034218022000c00740001c8801c2d918603134a85010207002e41e846000140e03c10303001402096030083c10f50380c0110340c10705091002403040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582076888 1250 582075638 582075643
    0xf090b07120204261e0706080a201c05010609090e070305060f13020d0804080115031e02150403060920011704030e0d0302011523060f1c06051002030705 67
    0x10300e4113002032100707984001100c40d014000702c640003d2200c4402042d9030404521500c45007944940404240e0b11380c00034414012500a4005800c28030710143e5004000d207618071200e421501c49240254148583c2e61107250711031007400d018140c00c0c2c40b4032411a00c2c0c82404020f641d552410307141c49070401036080000071000542950032051044911805a40329207420350300d0b600c2e4140c0650311803d044810303414004504010001c1d01c05a10003840f00000034041e401240b05184001800305c1c20342c05d4603200c3e20f14441400140144010807031802c49a40105080700e030741151b04266603443d501d000501c10003502c605800c800701340900b1190f0059008000103845451316a00442040419800103020148561044600080002c22480a084280c00c00038000d00410165100b500e80f5240046440e2041c40072a603800781030503040f09842402c040c24490340390006660b160243d9802d0142440d1058515080300d046403840500081075440c0c4010440c0c044441a0031314190b400c1000b100780480c101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582078138 1250 582076888 582076919
    0x1107050a08070603050618130201080604140f070e060d060f0608010f0b0703030902180a0c1814150a020c01031103061c14010906051005030601060f0f030f090b07120204 74
    0x15007000102550380310040350380d0f68404841000c0f010747c0d400400c000000745000c1204098000c5c0d0300c641c944c1e80c47d1001d1100701d40784401401e20100158000403820f1000c000c0d0fa9500a03034524060800c061000c022500070380041021045160301c03110f0921414007100d0361103005041a150409003949031110a1400a44030b00403005c04030b00019100701454081d40121140c03e82c054428070301c0d0a414044404820b00c103942716001d280c04d100b40c08107000e21a03940c4c01d000342c61043c0f101210301c0c1380c02d181000208070070b884160000c8280c000040f503200d103c0094103000055402519050b0100c1d0001000c40301111211600190b0600c00e000e5903440b481550200382e6008150048031201d1400c0c14142d11160403100354081d82801c0c0b03ca010003000b03400c103900a4018241d0702c0c01242c0c0b188100f54a89400740940350014010302c2410700032074800c9603451420103448c2000110001800d90800513240511001d0b11000740d01424403807840d911966000e00300d00e1a80e01141802d040000c0890800c0a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582079388 1250 582078138 582078149
    0x60610030f0b061b100c050f03041406041415040c12170c160b0306010e01140c030403030e030c01140409091407060206070f0203130e0a1b1107050a0807 67
    0x654004910102000b903000e40c469080c020400b9403111040d01d10007444040d9080191290b008001016103210707024000da050039001c50715440c1c100400780058a2041e00010003d41d80c4204455017002c406406101d840d000c2c600a49003031001880001002d0303e40001441c030200289100d508202c04a600340c6508400d40300f60607041c0981c1c0c086420a0351480141c468607890b2940000f8500d03801180001c2d807000c0818100c00d80400c1035940b04034401403800120350040c0400c2c03103000025025881a20381c140f000b141000742a05203125881c03442d00d950080d8100710301042d00d080d4119201d1804010020340c0f90400d20f0300060740c0e15401640c0d42d00380590b1090304400350b1503a413010204190403028510720200e80e41103802c20359490100940d00c280a50781400454861071021003c05d02c08001c40724017441420004241a14050700940541e400410540c1035540e03030101e1081e1407405c5201468090444c1d641d088004000b100d0441c104038540d40403500c04c08886000300900d58000c90014225503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582080638 1250 582079388 582079391
    0x605040b0309030c0708030406020c0f06030604090314070803150603060a0603021c180c0b0c1c12020309010c02100608100b011704030f081b07060b280302030d0206061003 75
    0x1120b00e442d1034507500a40c01c1003030460003600c0b1701040f0014008098012120b040d4212450f44000105011403d88075811042d0800d070f0800020300541410f4005203070b128880d16165030742a5004031900c405070030003602107030010000401c2c050124000e901050280c41d080355018614100300e40025164000d41c422503080c141c011481c0000c80344201038140151220840074010085104c4d02c03a424152501c0007180c1c0150210703004a01840b0900070703210810042d000038500ca051b04040301d0321822502c2e40080030002c02d2032908403042a680091405456504004aa8645030400c06810502041455505146400810815408000361000303041900f00380002c0d01e06c80140048501c805450b415400902d0840280010950b01202405203540c41e0f5031000348645490300a0140b8101c101d40414918406018690110703040703a2081c0c0c1e911800400300049201509080380ca600f1000340e044040ca40d03940b80400942c1000d01c49017003500c0e01c510141500345498400514280c0034a102c010805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582081888 1250 582080638 582080641
    0x5040e1b090f031606090915081b06070609231b0913020603091005070e10050a18180e0c0109030b18032a0105060105030606091c030c03180605040b03 66
    0x203840510144c410310601801c1007008944400001e000841940300d100c1c1800d00c2c0100305400c500c4280c0e02d48040d030f91300c40094250b0180003507100948030000c03040300d03501400070270413800010381910404030684d2180c010195218900c11013044844244454428284c000400c010000003c055489800c05411036000c01c8540f0b41d094146145c811100b070080d00a48000180603a40f14009043c1012000c40381044c080c039941c0001c00c5405103144000b04d500140c0d492003001455001d640501604591440c022789a6402e00ac0c9484401c0e40030f40c400d1542f0030035542100707103800c41c90180780038003040d03c002840b039005607030002407800c00c50344805883d0548840106401950b02007154a180d01c1d000122900d0352a01000d0340401039002001800003200c911221041110601505104100503151507013181d03201c50520640394010b001d00c0d80c0c0981044102d1408541c041624500a0b01940d202e40490203d445c001d04419099289154621000340080250036444000c031401d91b5001d01a0a403203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582083138 1250 582081888 582081919
    0x2160b19030e060a050907082b030e15010f0504060b040302060f1606141305100e0c04060b0301030204150312030218030f0f1e070902070c1505040e1b09 67
    0x401d565115034425000f040240003500009030049401541800c1c00d6641a654031000c03142d40d00d0307040013249851030383c504150151b80714900c109152030741d0b43d0a0115211480f074040a08009415130395905100000c0c005200580c5060521409424199020040d403401c2102c954021b0290340301c024400c603c0001d5480c0010025000e54046854802c3e0303064880c2e0040c900140074240038080e8a01c010401c8000a20700030030064015030441c3c1000107000e0745402c03000d00e20064071841c0110140743c42022000105512070b4420030004180603500b040c1c4030f50651040000780c5265104100b90880c80c440c00b030020507041b00c0800e40c40b0920381401640e858035158036410200e03402c00e0090b0b240c000c00500824009000c101381009848800540b080e25426016a0000015000600029600101040c01001d2141e4028140325014004040e506a07503401d401284c00400505100004c3c0e000c00c041143d0a00e24901031382000091151000c00c2d05440300c0e40995000c0e1441841c811440d4140708600d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582084388 1250 582083138 582083141
    0x409060b121b011e0f180b030f090304080d0f121107060e03030112111f050414010f080f060f060307030b12070302030604122d02160b1903 61
    0x21480c5018102803201d94100c041a500d8200c0c42c20160300140c0c094804542540c841c2500f00e09940c41d0030480f89400f003c0c503c04548900884503a072050001e80b0b800300703c1402c41d5a03078103c0141010101c160792494542d500d40c144280240c0318951540c014401440704070400309210000082e40d180015140300c0a110031a610501c11030070418580c5012400d00f002c1440b8401000c210f40261403c8c0a1000d83c0c95a10350341744000d10404000d400c0e10010f010004404422114040304e0007445170108010302409140e00c10084025000407500000e82003103819500d0b05044011903090131310b0780b035655441c80042d102d03043c001c2105040060740c2c4002035036691503c0000c640a04090b09039601ea24141802900904802e910244900c04003c030410300040001042700075280d024010b0300e6580c44503074408001110311110f410500071080c0900c0258171030001d048040c0580954194200c00d41c40e5000f0381007010803031610611543c04a800d0020845660849680c80c104005910b45a20341c00c3c0200e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582085638 1250 582084388 582084401
    0xa0503030f220306110405041d300301081e1516051308070f171207141209041406010c02060d0905031b16081c09120308150307060905040906 62
    0x6000700e25044080b03250400170390142040d14400d0310100041a03058410000c0510b000c084000f06601c80200a01540c82c600961a85d031040300c074000c02002c1c48000140d19580090300001c2e40c55000d0100c00e0f82c0d0b82c440d070700c852034610440409020020078506420505c00d2008110a1002c19840c50086003144500201c401c401036440e0207005aa8544001640307070606446480a400c4810340085545914207804100d00102200204844d20302080680c081d900b1143c002e542400c0481e140d95a000c00501c41e000c030880c0d0b4004140e940f000c0300000c00044410107124101d41103d42020010503980000b0321044888d012285540c580300b0b424001c03000703001e141c0001440b50202264042400d14801032608174400c000c0b0a80e500744d503c0308130b000c8140c2c01c6441401c12a501052003202481a900080c1c2d480804514000201c02d8807540054103500e440601100094400c03400c21803000c0c0d9070b008aa1514800320042d03c90180b820a0050942046000e45031050b6603d1428204100d41540102c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582086888 1250 582085638 582085643
    0x1030605060f12060d050d0f0908030f041802090603100302031504030206060f061306050714030a1b06060e0112060506010e0d02120c090709210b0f0a060b0d0b0a0503030f2203 77
    0x441c1c2d40d41c5880c800400c0408e506429001240401b100845c403100003005641d041132211040320f0034075241081030f912102019500c4102e0a03400c22403900551034802c02544038100300c4c041c40c0a0030b859441410f10b0000221078000c1c4490440c0709001c00681d000c036200381c1148044035110502411000050620300c218800c10302c1c0240040d10008041c1d4003c0003a011f514050f0b0408440d40c2565400642c0703920075070100c4030026404c00305c8200c0491103c401052154002c003400191103484400100d07850b1400e03000103643c071400f03120302001c0103607078003842c0d42c82a400c1ca8110310002600010580071402c00310002e10894034041c00180d082000c0100a19104004040e603509003085000a003050109005110f15041d039505013034902043c0009842d490380c1d02c58045941540c0e0704c210303a144104040c100e08a01503c03482d0028041012201070709081c2e001c1c02d000502019104c04002c5217400607407265019800a0018a084020240c2070b12655000144845c2208541000070b660304c01064000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582088138 1250 582086888 582086893
    0x60c011b0216030f11011e030903020606030a1e030c0203011415030106050f04021b15040506070f0c060f021210091514010e01140d0204030b0105010e0a0915170303040201030605060f12060d05 84
    0x7c50111503240c4c0144071300c90301903025a49280c41e40340c14551188444000500390b0403103c507030348001c0501442100d40c3c0700d000f4500a01010786985c006803e54020080605580407410305102c0300b081c1214280b0000341084000b00b28641c40c2c03102081880a080750030610440d80881c56104c00e0703201307070319680602d5503400039182003180c8001c0c0299044402d440c241d889105410020345900d004034a035030300c054080d482d039203c901b481e50340c1d54000d440310f48490344620307800b40100c4251140100071180128031120300c0202242c20b00e0340c1a0215000c040002c030343c021003e0800c0004110b8448d02080c00d41082c60700040c8540043e0041c1c43c1007a440c45004609100060a1a0070002503030103801602e00c5030500b00041e03640c0e407004407000144001a95801030400008100000f080c0d8000c16102417002008284140c4d0f807030242040854404a80b21190000010001103603454411400a070a088a100b8200034050f031406645024a03d05030300c01c0c000a6000c1901640c03201417403242950300c40e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582089388 1250 582088138 582088187
    0x91a040e010e2503020d2405150303270604050907021c11061612020a020a05161d04030504150203070b010608010b0d0209060c011b0216030f1101 64
    0x100d1030003803400801440ea640962041c031400c1d46144100ea50030190401900c105160841d02002030400000780c2c00c540d91000910000440304000311b9444030102d0607440004d16143c4100075103410b4407410030082c41b0350000c00581a100c10400c141c280c80d0b41200a034000043c0310100448c05911681c2c1045600069203020441290703800607002e508034109100d108902c611812083d0343c840c0d146214840d66412180010302d8404006e40c180302040c02c01d00d0200c01c00043c07481800200e0f8804503016005800404410007844810058190418201c2018844080c40c0c00c84120710600c03038010b28040d1b1703183d40001c241031503c0340b421b4402400503100800160300000401135030325030109204840724425003000181c0301c1d00800e03405048401c126821880e04120402c0c0d00000e50040078201d41c020b10238440c031081d4180074820405100c0c0c805240864250040c00080d1916070401c800c0d50000e40d907840c5c01e10010344207403078410910381e210403040d00001d18000107039545004070345480d250686407034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582090638 1250 582089388 582089411
    0x8190212030c21040b0904050a090b010605220f1505190306050414041211161e0e010605090f0301021c02030621061501110105040510061509091a04 65
    0x4045141400000490180307004001100c03100d8015840b905c00b00300c105211000841c101600140d90080760003200180f814100c0c0c3d14a2141d0501781c00071400250046880052940c03843c04203038050380f500f264085104d00d0059244404200c44c0100d8410b51903041c0e6083c1c0241c016415190601c6c0b80000d41c499480210784024000c020911030b00c4c0c8034904000340301e0305480700204103501490300b202266045428007102601d2482076a0841503041c852400a440c82d040c0c0d12040c0c0004e08000b06501401c016100c07210094070750b0503006540300e00d103050010001250014100c0e80f000d00180c40c0c40429040c070f080003031300a02034400c0c4404000160794908075801103550085208941c03c807107540080781c0c82c40071541d0882541e94804400e500c41e10120b881d0864030741944010000526103640400c1d00b40550034250b0f401a0742c200d83c0c65000b0500a030300c2c00214091000541408070100f0061145150020300d081054440d44070a2030f92168018200c802c02d01c0c1492103440098000d0103140043c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582091888 1250 582090638 582090643
    0x10501060525051b03101109040b09090303060409060209060a02010c0207080a020f0402030c0c1203060405011a1c2d0b0a050604060f0203071e03020d03050108190212030c 75
    0x42c4035581807045109225100c40080002e1918250804000c1c8100c4007030960100c1c400c0610410320b903040c0728100514042040a0044081e0701d151101f045459100e5071013840152803010300403900c03c0c4a00010030040150000503658859000c9901050500c4a414120001d05c0f03400d81d40e0f1341260000801c3c10b4001c0c5c0541006400381000c1c0c1c201c1e10400e0f6180045901c4107070b5550000c0d403000e2445580c079810b2600c1c0d00038503009084083c12914240118039118a004503016401d1070881c80401000f034a03240070f10846005181501c1e41c0100200c04a04c427800600c2122007c1c1590405010240b800f201c00340d1104000904100748414050040700e60303101e000c0106003910044030700f01381d0a41e00c01c5c14009402412a4005048282003504106058450049602c000b004500c4240000d0001c640714410b5159a0301448110700800d5006d030600a040c203003511074010605090200420101e94009a2503884d9001032044c1c8800186e01c2c800100d10040c0c0042210b041d2002194003400500c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582093138 1250 582091888 582091897
    0xa1d03120c0405010917030f0a0c110301020f09010503070905030d020f0615010c29040807031e02060114150c060f01090e0601030f150f060810090f030e030a050105010605 75
    0x40c218042020303910000500d805201d03d024160004940c05000c000c04000050000c080f1003440007035070f0901da1400c94481c00b0b0f0b0000c400c9440003030441c088601c144800c01c011282d1f01003040e0020b624002044050000380c1c440c80d080541003000c00000144e10700e22a00031034000e454002c1c241e40d032050001900a40d01c0300d89a0f0103a106000310404a16030110380c6c010f44017040410703101e620030204252a03000303a1848008051030401d4001c80780300701da240d481040d41e1085129001103500c0322441d050040520201e501140e0003040854203400030703150002006411106c4c1c00296881140700403020807101018040ca803070000c030004c604c2484044001c07078440c0c401e40c000c0d401800c15a03a14821601550300c045641d444a401290050000c52020f019104c4868004c1340000003100250042c181164001080c2c2082c4503034500017408000130a1100c25002980d482e000c0c4017840090f11076212104021100405012000c2c05442460b20b0500c05803220a8004000704559a50341502401c190310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582094388 1250 582093138 582093157
    0x702010e12010c051c0b0d02090c04082a0405041a060a0519080105090607080408030c040b0c070602010b120714031515100c0525080706030b180f0403080a1d03 70
    0x2c0e9603185220404480c41100071540c0004c007094525050768090040274078016210259500c0100000700d4041c400b0000248101045495400c1d2001035100c1e5007104269491003500c80c50400e0140008200c4881d03100c14005500002000c0e241c0751107000403880f4407180c3c030203074201d0502c1d0190714044541390707062012585900001e22581c1ea84084c2203446207821034655000c00c2c40310b8003040208440c200910341c4800a841041c0c03500d6240e268400f11038000035000340f010341c0900c4050201e55428052011b05d40c5041d02d40c0c0c031003411001d00c06501c0d580c140c0100c0032204407501c0b01e0701b841c4d507041200d0500c915450381c1e0a01a03050503001d106400c200382481500408640c1d0b03120115500c00c07039071445801c1e045000ba01030700429180c1c101c0040300c20152042d031190807000100b00c00b04203105140080c000394400203050326040c02880442c00403c00650000c400c5001085036820154501d07540c4540d2502d80400640e86003400c880040c0140c00169034180ca240382c0d08095088000004c090040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582095638 1250 582094388 582094417
    0x2007090203040605160f03020a0c14030a031b05070803100e190e0307020603060f0d0203060a0c030e03090a05010f091a04060e030a021c1a090d1403010501050702010e12010c05 77
    0x7502d104007001c0c24001704a01e2400a409076141403a5075100b5405800082c4d01e03868034035100a2152070f410240c100c1c01c0d8612185400020314070403840e07014828840c2c020403003114200c401900081c064800d00400d1005091f0707400020009610541e10700030003020705070b950320690301810140e00c20074946507001e294510b40b502e000c940d0588042c00005a07104035900a2509165607219800e00040400300491603810500300003142006940a02c0041d208001840000520505000c0300800f512814140c600c03035034104105151141d115043d4540c1a1242030901a40811541f001141c4006046d4006508410f001c144e0707541218405006008513401c59403038206c40300c40703403041584420344080e00943c4045a050030405102c1540030310012a402603a42c510f85034410207005422200c101c0b504101a04900e09003825250484c0410f600741004200f03440c110360600002915500c66654003038140250036290850b0380c0d4a1241c03020421881030024498401103090203001500306c8081000310341d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582096888 1250 582095638 582095641
    0x121b0106230a060e0f040e010b0409060c140f0403110d0c0608100608130b070509040617061f061209020d2003030702011707020708070b040810050609072007090203040605 75
    0x1803040e000a41c4107130004000094595000e800c02c00101440218a40155250300c01d2141e03030740da58882c0613030160044402003090300c1c640a00908090042d01000a80301c010b002c0d0048924180060300d09503940903d80641e408505d40c0000d15440c0c40160052101c2114440130903520b500101040c082e920030882020100e0b203500003901c1da5103003100c9600c009100d90701c02c0c01c04207c1c0704104c0e41d04640a401c05928001f1040c0c040f90075a04590804070100c0240201310303224600070440700303510180c0e055030340c440e103001c00c2030002d0f01c420782d80324180030403a01e20000450102694800e484140e1300804445112421746031024004a00f00700000c0c9d40c104980584813a424080101c8000960595030140c240d40104c150a03911080038212104510501c0b4020a40b05420011400070b00351a0b11401e071240e16101489182c0f10b8007803139030030f142c0d41030006001040c0c40b40980e145d0000703550304003000803c8004183d4000c00d052a20444150301c5000d00c001428201a40150300450256509000d503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582098138 1250 582096888 582096899
    0x1090c0b160204320115020c06030403031523131109090c0c030301080f06090106260a0b011502100b01090501080a140403051b121b0106230a 62
    0x901490301d0000904509403550001454035900091242010480500c0200c0c0f04078050019401d510304282c02030f80020380140318581111201012034a40d03880204110300103180810002d01000d44010140354480c40214241f03a416825036014102e1200004001e401c030313203071781044c54030410302a900407043c1c2c9072034401c00352241c050300c04940ca0f050111072a05401409100c0340010003488412002c03001c4c4a0320090306010720003135000b8420080109000b00300e03014001d08182d005818800b02da8905201041802d00600c8000e0240d6079840310031004605500302d1605128406000070b00744100c850000c10b14200300d14111030601c106600321584d445c20340341c00e201140e0034480324901282c0d80580c208055841110b040c2c1d406050366501180c4440d4020a911003240306580440c04a000843c1c0075984459980300c0b8590700307104200509401c01c0c404600c60907031280d84200d04800540481001d030310301c800d401810081620703400180700c680c0706461442c030380204000d080b440307000c0c0740100152 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582099388 1250 582098138 582098159
    0x121e0c0b09060609010b090f0a0e16030204032d05060f090f060f060d170c010929011a040e010b04082406222d020a0507060207050c030f01090c 63
    0xf0481000d48040190790801c00195042d4204544042d800f04000d8088000c903155540b040c4020706c21000b5a200303504000c032040100c5418075820001b01403040c070040000c98002802c1030040c0c520445e5141c828003004400d240165070121010305940f10f04014070055101e551015441119490261241d0070344041310030b9100c0b4400d440844041900402042d810701e400d2080c1c814807807240210702803c0e05031b140c000000c0c1d00140c25290325a5502c1d05101d040c00001d4400520034005507501245000c0c52a41d1070310000c1042c082c0140145072800320b4034080c0c85180456016003505601e030000356030364011071541c0768043e0085014034001d11030046064180322550003104102d14011005a503500340c1130090303d41070422007480e45105260001c3e101c50341d910071a0340007800e03810101004140070b9601c0d8905000c03503002c089003038030411540300c1141d803050940c2e01041e0f2120000d03079141030504003117190041d81c104459160003105e000f000c00450540c020b0200c1441100c401c00c203a5664040c194 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582100638 1250 582099388 582099391
    0x9050f0102070905090304080a0803150f240903030d020301140901150f05071208060301060602070b18030a061409010b03011406060705070e1e0a0b0d121e0c0b0906 72
    0xd000d81e0109105200f800d540380c0050354004402421641841d90fa101c4041c54102410700642c3c2c01c120000500a456960450559051030192031180400c180080491040d41585010f401d110540001b1100d2322200c00049803402c030b1000701201e4542d600505604029030003031003256071020705010a600d07181444001e20341214010001411813070000b803c02c0d2000403000c81c01e0000c0101c1006110002214001858031014055440341c805103000c5c01030508440d0190031020941d44000c000700304242413141114007000c541c900d10031040001d080400e203000c0c881c181c001c05941c148240840303a4904d489020f48980781c500028400d1905480c180741c201c400c0040510a8500f42900203611418900024200940300f041100c903203564903969150070440c1a1101e44c0620003000c0d8210510420b2807900e50001245081000501c450400240b074002c09400001d200c01c000311703110a10300340501072091002d0310104c038001d081c601d140001800407802c1081111440340382000305064000c00240e0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 582101888 1250 582100638 582100669
    0x606050d0b0f100c080d0501090506091308031305030c0d360e060f1009080d110a031b15060f0602150f06151204030905090c12070c060203100302010905 67
    0x303a41c8a980303011503850404c0715040c0d03255002001407024a011502c5030900a280020000500341400810012201d030040c141c500c10308054208000402c040ca4201e81d0811610404c001460545140c000d04502610041541900071140d00448182d04150742c2d8090b8030503001541c05035a5110010091050b01074600109690140c1c402d12035003c0d0a800303541c121702e008000b1152840c8440c00a00c118070f81d80c01080001d00002c42c1004117a00803c646440f0f0050750600c640d45c01108681d16035114000700b00641003003a40034122158a1182e04540c030001d801401c0e1848500814244078043c050780e03c5110080400410300041075480481d01f440c5030860200d0910154171500c40f43da06d660b05c060031b0070746d00030b14000a4061019110005045007007444800b40410300c0e085c1805401d01001358402400341c843c0c0c40412403200e68840450740c41c1c1030a5481c6910b50345554104858000c95040300a000500c0042840400c0803400c1c1008101c0340300760303110003a49440c0d10130f0150280c904800d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 582103138 1250 582101888 582101899
    0xa0e030a0807030b0a030f0f05060709061b060e03040e060315090309090c0c030406170708044103180109380715151a0309010f0606050d0b0f 62
    0xc02c01d60703440703504120040e1100a0107403240a40366200e404120244800440d2304111660308441008014013410768403410346e0030203444452030700d00054892040101d5448441103d880706608114403584250b21400da03250440780c58545070560030802000c00c1e00c403544a845030003a10003001080c82c20103442183c030341c00a1420008184c00b44070b0705c458050320392101e080c820b0060798a045c0007080035200800981d40c84c4c83c0b50601c12842c4560b1071a0150201d020818500b04020100c4c01160003000c10005612043c00028070a94051040078180003000321882c001c100c0090035010f001011380303091111b0f400d0094521005000640e2188014840e0b0002c203544001080625085560031811040340031a00703650015282000040700d500c000c00c11942da0800c482000c805010720301c50181400c0170001003008050509480c00e1480c09d810445440031480000001c404240c290850401000e54000500c21540c40e01d901820980191031916141460294603001d98549214000e1031f4210240c036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 582104388 1250 582103138 582103141
    0xf05150c04090203060409151e0b030705061308070605190f0807030b0d08030c0c06010e010b090d03021f021b1603080a0c0f0b160c0c09051509040b0a0e030a08 70
    0x403400b001c2c2d00300034007660b4043e0f9a0f140b51004070340110300c104a01d504141000810443c4140d85410052030f012101702d1182c41d107081c100f070070303100028110b095580496135240c803030850301e02120410070035400019543c0a0010001011608900a469800c0c5400240101403500c581d0440e80c1a5101d0302000018a00c2e80204a0140c02503011101c0910044d10001e012461621204019401941d003002d036240e0015209100150034410742c0c3c09000c10081c0d0031341c6545888450b103141e001c0c180c4100c2c030840c95522114209402040400000300141411260750604084544001d4104082409520041e6031758070101000124218200c1e125020520140310b0035611500301a80051090724103201c03880c10403a02003008500c1601c070052044112548628224800b4010f41040d001410148a03400c000a000034071007503d403100361070414000140f50350700c00194a10050b81c40041c5c607000481c0905000910484901e407030320810101200b40f2280c10b40310001642d80c418401c170b000024520340e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 582105638 1250 582104388 582104399
    0x302030411060c25031e08120a0e0f010c1b0b0123060c010e0705010f1e02010204050409030e040c020627010b0418020109050f1507050a0804030f05150c04 68
    0x3000c1c02200650504540224040340807511401141c4404d00e07013400c15420701001004075000b441aa01240703c2c1e0341070018030383c646d07802e0340f503008414042c3c2c0e46840301400680f00030749a40c031184014081504079442c0c207014880c0d544c006c0c140e0b9408440043d03054500380b80240721888058821981c0144c0c511240c2c1e1038042c6c00e032a2401100c02034000301031000c005903450741e1500040c00c0700c542601c0001400c4901c0c2c0b980589401100d030302680c14004038494481d41550440766051180020203541d004000c0030302422402442107400c850b611074689914072040c95071115600e00900000d81d020015070703071003840683c1d407030100311002d40d0416409002407100c44000031807000001c0c01136001040030b822003000503043e00d0b201c1c0c08102a00b001a004c1c00290360344043c00e00000c3c2002c0d6007a0100e502290046800111414111b240210340041e04004012042020920140c1c00070032940c1c4907503c07031800c0e003400302d0300c6181922a0322921910007100319844c4140c60144040d01c0d4550310b0145044c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 582106888 1250 582105638 582105649
    0xf0405160c0f0b041a0a06050901050105090a090f0905070f08030a1211120406150503030406050711090c030106020f06060a14180906101d0f13060623010302030411 72
    0x741c00b107501840d50748010001451089030680258400c2c0c6100d4841103420014000e0a400181a184614102502006030703495082c0c0c15419144e080ca002030342c035a0a500401d10080199001d800d00c1441e056a0310400030055014200c0303103210f4400e4031070076540c0d200480d0240c2918020018650000c1010518507801001610b801d48082c0c04003190a628100d442401034012a43c2956005415803c020400489101d52805005609401846941001d002c00e54900840c09070380184500000c40009105910707026904a19001700f001c2c84034585071308080e009400a202d84405441780f12a42c2d0210072001c581035208070f20180100111a182601c00c4000590300c00259404c09640101100c4900c400c802e00c80c850f5900300d0040100d400c3c43d82c8044402c0ca03060b40f0030010403203005032000d41008440c88041d007008081000b00100d4076201904c145000a00c01e004100d07624000b80040e5020381004402c00c40034181400520583e02400190142d100c00c890040030740311011284034030382c07a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 582108138 1250 582106888 582106907
    0x301060504050115261e1f0308130b030c09190612090c090509150c0c0a0b0604020903100509011109090403110102090a0801060e060a030c06080601020c0d060b0f040516 74
    0x2c10001642045c5980401402d241e010780d041c620013124209400b09801341e210303074a030304181c041020100121801c80880f0042c81c50303000040000900107050280c2910010700c0c0703070203009600141540c0c0e09080d0322204041d88201080c81c01003121f200503c0d505190050503070207c55180d10b84a001c40c130b0041001004046400e0704a4900320351a80202d0b800e07a071846486c2c8503411b0a0020312802c000360300d251411283c000d110380303041141009042004540454892049a804141c1c200705403100400180030b402041c5140d505481450445440d0104d02d2308664040c21001d8000c01090707e090341304401602c6844603540c0c105508502203400680307c0c44030300ea65a05148001410b01501c480085e9510040b40d20010007030b91109424420000c94030440f07600f02a04032400210145990340e40742c40d80542d4403401060086900000303840d64024080c403840d00707400a05068000c202450b1400c010400030f00600e001d403841421041c0c207400c040c402c6501904c80c54040d55401c8030a00b504480c140103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 582109388 1250 582108138 582108167
    0xa0306110f1206030c030c0102030f0c011b090f06020a120c0303092001030605121914160e330111010e0c01020f03070209011203021f06050301060504050115 69
    0x18200034020703525420402400651222122111403401e0030004c041c907248003d10064442c0d041900d440000340c1c0c00204403503203902d40c03001898580d40341580c582d00606032020080c00c1d4691020081c400f80b030717100c0c1000c000d84500700d4140003800d4803440100c0e584c07600c0050041003405c003c071a003a0164010904096000c0c440c1c540420340d64020b40d94004c15071a824915010303112240850f0a4640e058040c200c06014195402c080c5888004101992090882412810010941c5412041c42400c41d0000d035072010080c122012803540103010584c00000e0300c28030782c1d0824100c01041c0300c0f041000d4074051180c542400c5100032034481022030702e00e001c054420340c1801a507070341c0304403420703820300894401901020180c0403107903084c0c2c0007a0521408405600300750b0003c0240400503503600b001b40d81900d403080c5901c0401c1c03155207410f0f881e01003100b0940180356500d9810900001076a0050019a0f000390000c4c8a2603030f89005002c2030320001c5c019040d0040055609244107445405103211101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 582110638 1250 582109388 582109421
    0x31207170a09111e01020d05070b13080706110a110a03090308161406090c090912031b130302030d14031b0f0a0503010f0f0b03150102070504061e0806060a0306 70
    0xb803000b400070304d80d4055a54258400c14219800f60000e6805001c501551010380c1440e44c0b400fa040d0b44c0d041c49464004081440424004c4900c4050088030030a07240c0465002400300300b000340d804201c0c00680c118141d6503000500407a0304041070b020219807031882603415281c0c0490541965920b011942000304540040c848101c407000219100c040840b12000e86103028005500700341c034000e410103d4a841c454014100103003405818940021142800e00d82c4000607500d0f900e40074144107100459030342d070004403d00894541640000000e0400c103ca10860484181504c421740690303003103451001e040e201443c18800107560134803c4458001600c0c1440402d0316000051010000c5900200c006600091000c00180048140710201c9809001801c0c940000c0c1490301c1c0e1801081c0c403000302810003036010f001c1c00110a0740204108805000002c0080c0003441c0ca445880405413562584016421014940003600b4103010034260300030000070700b0007042c080c1541c031400d014000c09034440c500358 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 582111888 1250 582110638 582110663
    0x40b0403021606030e010506090c04031502121806010e0c07030e0a0b04031208010602011509020706110c0a03021207020a06080403020a12050a11010b1e0a03060905031207170a09 78
    0xa4005694640030f407500d903e0004141704d88600f19403c56100410050050313070000e05000030403080d00c003601c04076940448000000c04060030814068040c840d00d0100c03014a020a224500c6e15440d40001307030074840011155185c0c2c0c0d600c81d1100858003601c0d00304844000300820b10100c0c5c890f00e100d000050001d44803900740c9640b40c644821980c1b2660059441180380a52006130b0f50307200c1a010b0041c101d030703c020b0045040c1659010504d0310148200b80d061980050020108426a04821001e040321001a0b440307080c2c03085056140c1d18181401c9005006c1d0b9907041d809968000180c0e0f050b5600034142c0d03c0d015082040641304400090810f4082d4414000e059000901c1000d00b86801852561415200c071a403900103840e000340c0c10150809030341040d0046150f42c030f445460f840e8815a051000741c000d102e91012840e2070340c45410242415081042007000d000c800002080b44045003520144141e543c94804c880400d00f031003000c15541d00020102d090021260441d1810501426000a04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 582113138 1250 582111888 582111913
    0x1031a061b1507030203041e02090f0a090f05070503010609060b040e071101020c0a020f0607050c01030216081305090f04080d0c0e180109231603090813030512040e040b040302 77
    0x1460000c0f40c082c030009400004000400010103411400540416282281101180e00003101c4110007841c903d401e00d41c040020360300355150b0b00500a03e0307030010740c01c04081002d8108207890f40c0041c01198002d6003000000540c05025115400c1242c41e4081e0041c20203007001020314030218090161000c115480c0d4414802c0751081c070003801c1c0150350030b008091b0a0128414440114100031419200e82c009000c00e1000c160003140301040d04c01e091800513034036910107400c604072014504002d0080385c40400d0091440d408106c020081c2c0c0c00847d0003c1041c0d482403880c0324440c44c00c0b180200013003820702c000803200f44150003040003142e260030000c1d108444100440c81e01c042d00c2c1c04400b003c02c2140c004001c3c4501c1842a40c41c0c22942e030b000000308502d5111440e0b041e00003d40900039500e10609600c0c0120302c00d51199000582c01350b00e55a03103550101e80341c10f0741c2d01503000c203039a0b078041c0780d20364500440102d084800710b40780c85024600b280d5131a100c28a03a458014030a8096000304800c2022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 582114388 1250 582113138 582113173
    0x7120c09091b090609050f090d08100f080c04050901020c030a03050a0f0203161805101b0b010e010617040b010b16121d1512091606030b01031a061b 65
    0x1800e02c3c104006000c83c5040041026a0805001444042d04683c11300c00090f802181c0d2031001412070500751200c3d12206407501403950550710602035402c44030408903000700086800c904184040703405002c29140c040340d85080744542203880d0703400c0e070082200e1100a40240c104a510403000b42000468070007600303104040e68030407507030340c4104a02c4008d41803565030011503006030300c9205100c00041c03e0030301d40800d8061035003844220501080f00d038000f018422450000c4803903680245000c18070750b0741c5c6207420200d05082c01100080307640712019202002c200c1074041e1003aa0003980030300c6d0036441c003040025640d00071a50314121403411141d64002c9200c00312440622a000d560b4143c010361051421900f80c103506040c20300c256506812100c8401c0440152000070400840d02e489a0b250032102c0c902d00700c4c048a10b907104280090002034016015400b110502c0000e072002e00c0700000c10340190148040021250341c0c0540c041c8080c260304500034500d183d00c0c0b0504400c55140e00f0001c100bc2c01d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 582115638 1250 582114388 582114443
    0xc10050417010612150c031b03020f1605010905211206010522060e03011b0819060b0d0c0e0d0818090a0b0307060504060206070815190807120c0909 65
    0x210307000c41003065498041506c0c45800c0c0c42040901d41040140000c0d209149003908407041c0c60708044e00800c60404c00ca06420403104203a00e000d2092240c961540f40290203003468a02c19960303400303030200e140da40e000840212141e44d4184072106d803030401c1190f40700c81d01c60b40c0070b05014104102400140310307582c4509512603550a444c0346d5402c900d480c18a00410000b42000c1140c0664103148060810109217075984074446c843e42030040035a40c64203400d5003040704102801810605188001032500c0e1028000c040b60011854140607050b07a60b4020350350020307100c030500d4012804014580109400d01c015001c5244145242c541e14001d440025549031401c0da80c1200813a628440c0364018074041025400038841414068203042c86c000c001780d1600c2005003c0c100740042e1000042d00000c00b03500700e422001e0020f003c0c0d4504803c4200e8410781141c60700603803a461284c0603011505107101141c0e0600b0340e50240602900c2401d00c40c40030081c0080e800100c980c261644e05104c005228800c041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 582116888 1250 582115638 582115643
    0x26040605010513020c0a0807020d0203030a0509030610030b1501030f06180f06050102070b0d020405180a06050108010810020d0608030316032313050a080a020304080c10050417010612 80
    0x109495042c141000304011050480845241c030400072010000d8020900b00342507a04410107c0c4c441000d400422000940000c0080d45400000f40400b003035900140a4110b02c002039084484030343c4e856400b01840036aa02000c0c180b2466100051040c0d079101c52400b12001c0306240c003161030103030f1400410540301c4541106201c072424408600303501c843c0d4401c1c4030500d2400c071028012145040c001030348860407402079403020781c40012600a80e80c02601200e0082c00003a00060402c0c0e10f2709041816140700341e071340c10390880c10718100148540c8209030180c141d44207030000e010105011600d40d0020351140190036543c90b222140081c4c403c0050000d1842140d6040c0150b20701c1c24001d00c01070072100e14031000fa10b44516061140851411a08040e50240c490541c68070413410909081d0716003649160300610310b480c00a01802420382c04800760040f1800c0d00110380e851300c0508208031344005595107000006030180f00400100d1240c0d0b01d10b40c5031000c04000041c8881c0c540b9185007034146118000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 582118138 1250 582116888 582116891
    0x705011b020d0e06031509150319150908090402070203070e01060203042603090f06071b0f05041e02210f010e0609060f040c030f090c0f060c0c06260406 67
    0x3400800d80201e0454200d01c01110021716620b0030805160301c41e02e500d214a4001e192880025135110303207071900d0491480300201107a400c0c001c011120411140d1544e42100c918050620714010141c4601807004900d03031104005060111040c1070000035080707400140d038140709642000410091100040d80644481d5014603512070500f403641044850b001c2c2c00c81141207029400003007005011069450950040b01c940c420382c0c13140000685580101c010140c004984408200382e103180c260755020481d003034844091a8966a84c04010458500b10100792902038030204120030340c4466030003004c400c025110f4140350302840342c09050080c44100d03504225088000010b2050305241e51078154004421502d04485140c003400ac1078008036800b1116001d0381d100d0b000404d4031f41c0240c00030b03c0240c0361403100b00541c54160400ca400c008043c482c4020032800c20b103001c28598412414050400c2d08940c07944010313807614404896007400f1000494460b04990108040848003114460146008510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 582119388 1250 582118138 582118153
    0xd0f0c06050a0f15060c0308070c0602030a050403030b030109020a0b070602070f1415060d140f0a0501091101020a0209040f020a05040c120b06130e0c09030313060e090415020705011b02 81
    0x880703001c0b540148450501156004c0c010030200d03030b1000c801d080a942c9840c1046054490b01810386070030b043c144000f01418004410003c1ea45002c4d8040da00c43c40c0280d4081c0090f5030317640c050500b220b841107400b0790080070b1144203014071081072000301440b0784612030040c03408075140c403034580740119045c00b101d0724060b0038114400400c1c10071103800500000e050101c02402c1940001b08001074602e00105200407001e911440180e0501c00d003021000440c0c1581c1e02c1c0c1c0c00302d151442c02000009022206c102c40d001000407039510004121520541c0a0410740301600c45844903000c40c1e9510f0004c9a110f25005404140340d1524004c0c400c00b140c031500e4401c3c42d821160a00710503038600c540f40d1800340c0e41c148101c0b070f451800090680d0071204013048440d0282c071400340f021071501c615040b445d010700c00003070b1914100e10703022850812144195514840002d02d401003281007401503501600d40101c80400c5101211241d00500714140f16000001c9c40703800401e040d1468141c0d80000e080582c00c81c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 582120638 1250 582119388 582119411
    0x50f040b0f07050403021c171b121b011b050318010c270b19120506130e030d05040809010908010e0d0e0a18150602010902030d0f0c06050a 61
    0x40300d801800c40d04044403646031038480100980603c0c07001911412030540300120308001e4046000040707400c01da589006074800301c1c252055510101c0d1407446001070040207100d015000c81d141c884480c0e182c400c6403403d0407003800e01d50350200300441750915540e50300f82240e01c50010f41c445a104829916440c0e200e240c4029141245210021201e480d40d041822200c541c95001e50074003480b00782c10500000d52004200816102c002075040201c2c85880040c2c0030300400404142d1745a82d03507059450000c214500d40200003942e0054480a812014010303240182c20303010f80164003076a0070708085a040220782c01c10b080039100191010b41c5e8042c00026a01d04959201070660082c02601c8002d200070b071064601c2695601e03410b01d500d030400a80c1c44c0120125521152004014803940c034950101c11070302d0915900400c0c40c80e0b2105115600000001031060040c040e03c11615001400b806031000000c00070b4950351085210001000600068400040c40c9846800c1c060292603400155034032800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 582121888 1250 582120638 582120653
    0x9030f0c06060a29180a030602090a080a0b0609070e06070303090b07020109080906090307031a0a0b0f09071206090e01060801050606090d08090103090c030f0c060809120c10050f04 79
    0x903000404401408504081c1d51181680c040352141c10828800350b807071400c154175074100d003884044158441d440400000c113100d030f0ba4025083d0580211070400000342c1e00d0b000300355105030510006142202800000307c480c81d0110855601ca034560501601e4003801e040003a00070383c001d12007200460ba03601d40e2201480001102507a0060050008100301c80050311480d000e4000c01700e0a601c00c6d000040c45d400c0d19201400784800856202c403050411502c1028400d0103e032040345c802d01c0c003030314002840e6035600e4641002c681003c0d014006c2500b0792034240c403c81d40010b0f081814a00280c941c60002003056030383c466115420410400050795030b060948907400d540020704010310800091121102990740d00541043d540d500910350340d5075400b0800141c02078400c01030701600141000c90000705000c220f007411034200b40b02d0f40058071500d0b210181541c0c050020360320005075a0108001420a558900003089003181203011a504224a00142010b5034030031542002c200c00508180010071500c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 582123138 1250 582121888 582121909
    0x10180b090a0b0702011a0616051e0607050307120902040e1614090c04060810030b010f06080702120a030b030a050f15090a02060307032f0a12060807060809030f0c0606 73
    0x6200a100e44075000c6c100c0040c1400d004c03c400e104600c009800a201d50002c40b1100300c89501c0343c107455109561880c0c844074030301c4011000880b401341d08001043c840c400c074110307842090a80c903101502005114420001c040d010001c0b030f003040c0da07165100d800300d90400208400c8820310595424990400000841c0503aa511200340182c82c1402807044c0d0003141d000b03440c15681c1031302d0071250581c0c07a1380f0204240301e09607002403e428040e0340080f580b00b24103500101a01d0141e21800b1031900d664000300d031b45000321b00809034419400c6c0020410b80c2d1107500000c0002e08028100c41c2e03220b03135030707100c045c2040c020003a240c4113580040060550000c0c155030305540066104c0c050914500d40c0e80205501d4400140024101744c0d0f11950f02a1440c0c2c9c8121010306040c40318401c0c0c607403400c500070ba010b90798098007010f030124906e1072a030580481c56000300c03001e41d00c68038050485645094010382c0c60000207810322a240c001032014000924540014042d4103031202c0080076542440020321a40c03000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 582124388 1250 582123138 582123151
    0xf0c011b020c010e0310050c0d0606120b180a02031e2d090715110102070629030a020d080909090c1f0203310b121810180b090a0b 57
    0x34000c004d202e6a000b0501703802242c42c0c0000401c0729654182e40e0b404074894100c0071503240b458900041000d035031102c40c0301d00c6800a141d0801610080c0410006044481c100241020300d007400001c0c1031a140d60043c64108142810540d130641032140840d000740001c45410065049000d8407084008074a09000346c08258032040341c8007030820f8062147c40b014103000d055500711542c0300c1e99250500c1650840b9284d00c481000f15164905c0303242c600003404401e0480e20199043c144800c2d8541d1460031504601d4200400401400b0301c164240204010946415505008207200082d029128001010312440c6003101400e456000724082084140d2000c2d05000603112905071001e01c00e400004640c080140c1d5000000c40c81e070340c0e40751010900a4210b5081c0c451801c0180011054452006454001120901100e040c9c0d00e1100f501109100f03040c12400c190f002402c1d48010120391b900c0a44d621911004010303401040d502d4048208406907414403003680324180c60340900c4000d402d107a41204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 582125638 1250 582124388 582124397
    0x30207170a0c0803041106070311060105060901090302010e0301140f040b090c091311100909050c0c03030606071104060b03090f070812090406091406150a02060c0f0c011b020c01 78
    0x81401c001000380d00e04901c000c1c02c01d02c000010030306100c0c885800c0007490f440103015550721046413800800d24032807220240b1607442a10004078051801009844004a06a462659551954004444180014003c00e425550702c4841c1c04000d00383c11101072007000d400e018001c06003440e103408036100360004c11303040190304040c089109640e0317400049900700d90318100302d0719583c180341003100c1c4051143d880c4981c405503041002d61800d070080200ca08485c210745003004981d440a0300e8488500c80c034080c424442d04100300050652511034058414a4002c0030f8090794480400e000c10221102908040b06002c800b00400400000030003240503482003807400340130402c0c5850202da07520b03c1c2d03481035240c4443c1c0216007185103896652210700180850340c0180084420750200045034042914594040c0d1500381070845685001001c481c440c8281e9402070203d41e17126241240182c02018000d025007408010150360b6500034010b40d940d180800d203600c4e0b0b03c10480b10010789826401e0300f0590601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 582126888 1250 582125638 582125647
    0x1403070e010b0906030901140a0501140108010305121c0c03062c010e1909390504050a09020907020c130e060c07060615080108010f0e031602060f0a03020717 69
    0xb84030107030545203a9401030316a0741d1651201d05029024240244001d2a111480410001c0d251503d811441c100d41c010348800c115010020011902c04209000c043c00740c0c0d00984d095802d4541f2400241800400c4d480803c0080b4640f443c6030056803081e0501ca00042e0b2503070400d02000001e24a403500c0000810206019680c20b01c4451201c10070510032211001e0000c000680c030009114070032011401121004c001144481c5045481178107409040303468200000b1080b07010b550030303111035a00300403030003600d1000c280b400080201820f0000c180200407512225090010b8503003c51490040b0215006020f0b054282740501060b00c0c00d03070310004500380c18100c540794980c07404201180c10101c500c10031607460388030b13042410181c4407541c41070404c20030b041254407620380c1c00344103d41079801a00085c03001e03102c00b00d900c8003030380e03000c1918140c103800c100144845081c001d01b00014092002d0f128504100900454a04607081421640d02081d00000c058042003000b107004e041c408075104946040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 582128138 1250 582126888 582126899
    0x50103020702010f0809120409021c0b09040f02060d02030a1e06061d06040506030412020f1b10090f0902091207080a1b081b0f0109140114040503071403070e01 70
    0x10b4003103c045405105d103000c04110b0000e814443e40080340203d80d0b001d40e5075a90380c8103210095010700d40d0807400b0440c00e100060091000d00617900703032400040410242d6102c0e0b80702c0c044240705d11003007264440c0c010802c91003109e0050003d50300c81c0d001e9000002d03041c0540c2c461215038003d80707100034a400e0301c0c00c0002e000140c2c01c007450b0380900d170020080142c41850030021071103500c9640c2000d90302910100c20032040220782019081b0121041d82510f14900c8005461540e480291107071441da080c81000700c01e42c0d805d090624170350f14a081c0ca07180c49250307903038420700100c04442c0d001190407d070000ba0311034039030410703c0c030740400000c441d0f0051550a10f0820901e0f251141107800a10005003801031140194074001c0c3d03c4060030014003601c24943c450103001d4441c000121210f800f44102d00c2580006601441041c0201c0d03030011246030103902c83c80e0044070410001c0d00000a505e406100210350340d2804c015600141001000720300c2c12020200402d45001010351111175002190f4005100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 582129388 1250 582128138 582128147
    0x50610081c1d01020c0d060522020d030e04140708010614030f0f0727062a030305190908030109050c030106050708161a0f06060a0c0206090d290105010302070201 71
    0x3040b044000400080030070103004034100440d01c0b900c00c0c2c0c03144068a03850240410303940500c0c081c9100200612590b9160122004010841000a9406074043c5075403000302c4c0c01202889040f1400074400141e5441c00c0000001d504002d0343c0b19000118140e0060004540020400c805800640062030561811220b45104244001d05a100700740304400800c8406001e00c0c806001080300050b04032690000c140c0c282007070610342c8036480000d290804030b20411010703040811004280c2e504040e04c048000d407402d402910307024001c030004041403454401c58000c90712900ca1390030f21034102142d030b82d450f00c4255001e4400192036030680c0707101000100110345d08442101c040d240e1100005440d1188036102e203010510128014196040c08014810303904490041e5074810100d80c0203849d4652034000038411140114070241d00031420100242001d403602c8000b62410071b07401010000009030b540d4a5204400b20440d906003500051041e00112420602040b0b026003820b290444c01c0100c6500000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 582130638 1250 582129388 582129407
    0xe12060112170304080c0106090207020102030706050c0f070b04020f012d3e010506030d0e060c030c15060306160302282001050f04150603050610081c 66
    0x21458141004900412000c0c82440c40540b04010107039450345070504080040760f01a80460100d5440c2100100325080140b082d00c50b020703010f90086080c03202a50b900001020064180520500207020300315001c000d180c010300311144140f0a02c06681028414485503040c091082c5c3d060103000c0b40d0300400400344040c842c0ca0340b040004588244c082181050341c031208842100102400940700d1001c510b04108015a1195001c0b0104006031132402e0105080b0703501690001d605800210300b0440c084e10504044c810400d00400c0c061602d00d484110b54610342c8041030000042d00000e5500c8604001820b25541c048415005409240341044501740030458415001c0d00b07059001c81c80403901142a604c12064000304101c8022042ea8038201800c02110401041d6070030009032054581a4011300a0502a1240344501c8869440315a1880f401c0c02074541c00b496919a00d60001011070740810900e80034020080c840c480c42c500b4200c80a041612030091240c2c1d100c6007001540c0c030554012040c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 582131888 1250 582130638 582130649
    0x6060a080411090f060f100207062a0f02011101090302030724050103030806030706110303060111030c03071a07050a200106180c1803110d0201030207060213060e120601 74
    0x20000380d9680c0c5401c00e10641652807554100c1441e108000c0c00011581600d4003c10040b504c00300e14002d882d007000316010b51540b442d80103802c910810860a17005109804005d817002940c01510514003184009441c41c07c02c00341e8120303ea4102c981e05550300290204003480d1440000d01c0000c4007500d020f5a039102c0c9100043c140c1c41c1c055218070404203e2445018103101d8514148041d580d0782c1030040c044071068441900c60b01654030006003a5001d01844958000030001560031507650780015900701407255809019408100001c00e0505010300042050510928520040280210050b081e8800003802e1105010742045102c504603080356000b400e04c0911115008030303042140d420b0780581459030020782a03085004401d40344001d580c102c50040241c0703a8881121482e40140071100181c1c600c40034082e2108030386c81d80c842d810174109174101c090041c1805443e22410307942d240d04980c0080d40280710001084814000c11341d010241035080441103507503001112200c10f110341c1341c1e041031180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 582133138 1250 582131888 582131897
    0x71404060f1b0c030b070203070b0f09031306050c070501080c0d1d10091a0112080f1201060f02010b03061009050a0e0f150c210601021f0c1706060a 65
    0x11002514480c1182e44001106014030825025030b91900208100c042c0c0401c0f100c401169000a420361710000c00c2c0c1d207419401688000d1191540180b403450502c024003c20b0840c0020801481c8c0e283e60000c40034001c121a54401d541e41c00c4015059091010300e070170450411204005102140016405503080c681c1a0f1900180070a40381e8000140c40e640d20010449034001c65241848420781640000010340c0640703082111102d012500c4d03081001c00340100b40c070440007869083c0c0880e9035030000c1d0541c848c0703820b911840c0030184401c41c08410801d0313000f0030000350401c1c00c205100390f0a0113140401581a001032040c0c3c203140c0550440800e160144142d010350701d400140d214042034010034516480001514904d02030303154150380311102441000c4010003c0c074045410700c0402021034000e44218240884408000c0d07960441c848005032000d030441c46402c04995440354410445544400e003100300250351420880041e0424011801a1100c910780700e0800c07c0b10740f42d4800b00d03450300015240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 582134388 1250 582133138 582133157
    0x11090405061206071d04050402010f1202041e03031101060b0901260f01030b010e04030f110c09010f1406190813140c1302070f1211030d060e07140406 66
    0x10511400b50802070000750302c1180188084035800100300310f004596106459413083c0c20710240000c0d548103030703030090000d000b182462031241e1040c4154401031a000f817000d440c00b9560307007004032041c181c542c50340e1700091040c03420001c00d900030086000014005000f800000c1c6041040d480782c4c004d1606040c10301c18420b00004103d81c0c210b40e10700c1620308400990500b400c0c10880261401800d0004540d4400c041c40045025a10041c3c0e083c0f003280d01d55110134020394810000c880e40c840b441101e003800d00c6008107082907580c0c1c54034400d000c0c0c0841c042c440c00c00d500d000b910076800c114000030329010b03442c00c20048950307800c0d80390204c60790300460420b680c580d241c80c5500660181106c00180c80e0103440000c0d020303500d4000ca56000c0f0408100d80c40c80c0582120320812040f8420010010103042c440d004000000b401d0300d00300a4100900c0c00c10358003070380c490f0b881c007421903100010220b102e81c1d45040a00c4008040f461558000d00285442e911886202c00079808a2141e4010030092281501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 582135638 1250 582134388 582134401
    0x60b0909190212071e0501030c1112070609021c0201030c0c020d1202030c03070c080c0a06122f030a1506050706020310170f071e060503090a020a0320010311090405 72
    0x200300c031300900d40300c035030040303507080300421101e480d134050003540e00090078165600d84103071042c69440381a0034040080d02030a4414880c10348981d004035011100d540c0c40390314680240c1d462030004150044035202d5072042c20f03e14800103040341c0701a010501130000311440344000d038449036034134004980e010401d40f5408100301e200760300d540546003031048288400505e6004000e000c0c1007078401c446121003100c0034594944104104e07808030340607003800076100700049000b01702e964000100c80d000a461480c85000c0e804809103044000c08207504020100200788a00e90500c0d114800003160701c561403a000d9402c1100060843c071a10601401d081d40201c041010107090b0001c0c0d000420070044946400184c104079952154078214019046000c0d403400003030502d203020900c074401314540302c03584030003820700c03000307031402e400190410301140300c1c0c84512001038031054401e00c0a140651001c100211140071400200441500c03518101130400d9454941e44580e001030714007910003250701040c217035100c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 582136888 1250 582135638 582135643
    0x30d020c28120905010f0302090135010506121f08060f07030506010e03120a0e040609060515181c020307140103150b0711010507050703060b0909190212 67
    0x403041107280440c6046286400c05500307038026214441d0025414a0b140e5010036121820140b203201d0114034401d082c1141c0307610a90003840c000e04141010000343d00340d41d10031002102290122403058803008400072000c0c0c50004441c0c01044c0c115000f625103030704501344c411400c80c040c00034541d1001441144118990020041003e020310700e04840403880e103085030720000c2c0390998800d004a854400400d201d5445103083d41d400c110090300170000380c81034080300320141e070003d20341c501004550740285903e9941d6015640c020308900a002c00e4060814003000300b60703200188922050b13003007085410208249424400c07000c0b002100e021030b0b9000e01c620507019210f480e0500035414040c1da04080342460503500c20a1a100c021ba900700f00a00c2d0020042c180c0340d0030f5000e1225162001d200100000d08002036074002a10306250503824540c0075594546000c0c10b03034008451068840c1490040780c207003c40b8066000103280001c01c1c1048081641c1800031a0313061020b80640d0031880d199140d403504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 582138138 1250 582136888 582136903
    0x108032a030403081e07080319140f10210303140f130804170a0302010c050f03162a11041a120c0a090e06060103020c1519020a0503100b0408030d020c 66
    0x170300c400566034002d03860012020380c0f08560351100110b0980400c40d03110f686200f0000d8200000c036100000b610384010403448000e006042543c540c2c2004008580000300503414044101380c8820581d03000e80d01c0c600982510141052480149410820001640c80041200d0303000200040708022401c5142080e840621aa0f00b000b41078001494410381805000564201014044c0e8000c020500001c001103c40f81b16400a070001580144081510300c401406070711011806410180c01c0101c00307400140074550750001c15141e0528072110801401513044003011310170070440301000a80110b4a140884901c4c000e0b401b8010f83c0107410303911040100b00702103411203200901e4001030355621240e45014208088803128035005207000319140b54007a00a40d4640840c3c44007818418078020740311700b030a20005041c44a603111141984007500d05030f10044c01c801d01c40b95165507a030702c2c01c0481d45441180aa0104401000c2040204844034002c001d49180243c1d003080903956540e4030840c02c0c9000c14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 582139388 1250 582138138 582138187
    0xc07021306030803270d18030f080c120f0a1b0c0b09040f020f1b100c030b091303090b0d0f06080109050d030203013b0108032a03040308 60
    0x80e15002006100c885000b071031203043d05c816a2114500e40c0e020f110240101440f2040c840e503c803041050040340100058640c0d501403502c000c54140d500d4480ca02d01200f40c0101b07495454001650075040c40d03052100ba00c41c4010400303883c3c0b501001198102c91403207066a45820030502130114084034030401e0680d61200d410080d008402ca0300c40803910088d07400380c1c4015218910700060030018080c94000da0700c2071f4104481803400c200c11100c550b60400007481d482d1205000700d116440d9002040d03c40c01d18143c003503a600184000000c000d001080c00042c1c02c580b40c1c842e20f2054100040da0000701c21082ea0892000c02e61900b8885d5031150107048440342c441103040c182200401c1c43d00055002e07210b410b000381c045900109000ca02a4100e100a0080e202400003400807055850160b03071404000866000c0c40f00400c0c04030031200c0402540a0b00903190030f820001d000c4002011100020100610001400c40d50079281181107a5901c00c03403200400c1130501056442c1c003101404071601c40d0b0007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 582140638 1250 582139388 582139391
    0x90706021b130b100906020c010e06070b0709080307030f0807080907090c0e21070b120604020306010e0d14060718140609090106020106031a09101a1005040810140c070213 75
    0x7440d03c00a825810180290b5005210305043c0648c290700c51419590404005018a0304d80300094481c10a0341c0340041c404000d00c168814005000001000140261402a55140c0115070000d400030002c3d070700505800c082200c0c2c5414000b80c060049040000c81c1c0da8a0b0002550410700310341034403400c03610040503034050001103200c00000c4030003055000c03032092802951189c80e20b802c040350490281ca2504164809200001400c90801750300454020700e05062200b203135950900041d481c000c107800111005042e0620b01c01c0035400410949801801c02e08010030940f031440c1b07004058000078802c1d01015540700003041070545808041b00c240c0e05001c0c201c01420f41c0c680301c02901030440c9220884002c80d00d045824503111421006500a01240740034090601c2ca81180e0300150400c100e096000703c4140307406541c5540e50340d82c00320200c1c15907240e098a544c6000c2649003040042668210440e0502980303d08031101d840310b03107901c83e48181c2c500e601d5428034000b19100921007911030880c107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 582141888 1250 582140638 582140659
    0x809010b10080f07080115180e09031207050c2503080408070807080c1f0905310204030b07050c010f0203012d0510050904020c01050c03090706021b130b 67
    0x10350b40031424622907602070007082050f0b00c480b503088417001c0f002d114280401e044c018042c00514403031158692009401d0380407281854035540b029480510540b101802d69000180540c0c6418008641d13690292075810400c1c2001c0115140da5102c078901799694a000c011803084a0440780c904007050b01070754101d0207107070302e942d12441055502c80490060719858499000b00150300d000026003020401000750160b01040c42d40d29225035a8804051040280803092030b0110b034545408207039041d45807464644209800502100c100e1013004c120046407030754010082400400d01141095410110900d010360340d56540f000f03518010000219021030407030001000141c24a0220310020443c501c2090058404000030302114642d4114802d031a00a2400800651401d01031f002a12481c080500b025282802c80c82d009402c580c01141e0040c407003a808800d02000c000e00300b0840018040c50b00040c5040c458440403a0018082140c000784500740150001c01c207a007168110030040d00000c2d2540144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 582143138 1250 582141888 582141919
    0x60d0201170408091212180d0f051609090c03030e0105120a0614060a08150303131806080d120c050c011406090703110415030b090106030f0609050103120809010b 71
    0xb5a4001c200242c818064804510250300c2c000c00c21101c10304036110303103a24005a5005804603e40541c0045910010a40d08c4101040c42500c48511480c40365029004206e1806012010003c0f290804050703e032503c4451400110403a0540c0c050b00d405081c03100c0c1c55041000102c42a10540f0049000300d11500240030706900715802800603a94203002d41140d01400000b4402d050181a08882c000f0b1603400c045929000280300c4402c2d400405010f0384e1074003440b90b01d08460160903900021100d81da0400c40c202d40c3c00c0510881011308110b401034103030300580ca04024401d0b0750201040380a20350340c01d00c501006001c0c0003125811716968000784480c1400f0b0292450500046a82d20f000b8002000001d0607103201c1e21602c98440c460b201918205800e014081d01d039290791000364005c1c955121403400b519510b4080d050b00800e815030b030118040c00f080d00010107543c66603120300501b074280001400054441001d803844084246042c1c0748581e41c682c0e50501400151080b031f44c2022740b0300340c004d51 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 582144388 1250 582143138 582143153
    0xd02280807030c1517150301020c06010f0f1d0c04030b1302040b04020405010c031b050f10180305030402060915210112020f13020d02030a06080115030308060d02011704 74
    0x21240a40110a0141da803403400308030080c2035854078000070b020b11000045e05440030000d582c0114035005a03150100c0c042c00400d003268840030005403564080d5004200ca066a00b80307070b002420704400c60305501d91501481d0180801c842140d064240e40c598005407003206805c041d0b600a54102c05c16912074141922116109660803074240c0c0100c0c00d050807601c0030f040c2402240c04550040c0e44901e500c0503107880445d4507000c0340c1c500c0f80f88207031064124404510200f05004203843c21401420103c107003484414121203081d03c2482070790242a4401020035000426280d0054041c8c0e81d031503444601030002480040f581d96a03098000c00070407140355150751400d20201b031029011031414181d8a03460300b20310104c0d403040000e500a8200b01445d42d0b6040142c8100c2007201c00c103401505003804280c61400380d0b0411901d192103e9964242005180c0007401080e103030748820342d1840c00031415910000c061100003001c5c1d5024040c0c400b0700e4011644901c260100051491250404070b00b0503142184 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 582145638 1250 582144388 582144403
    0x20a0507020310091e110603040606080d11030913090b0406050a20180109030c060f09231c0206160c060203030c22120c03031d0d022808 60
    0x80c080c0c411501d0f240c0c0c2840591280007040c5401440004441c2a040d4000400c101400022503c620f503501d56102d0503192140030b03600841c072415020490604180d90340f8a05212100c001080004018007884450000f00894223940003d131684150b0414000c1030001901840e01c0c0200100390304410082030080d564030035800b40381b0b4480c0600154209201d000001010032080c00601d00c41007020514031198504990412481810301c0005a0f507651281c8803c50a140d0100c00403c09446000080551005d0004064480c41c0d806a20508a000d45680b0351041c8500c400e00071001404005001c441440614140075401070065507940740c9100144070090310000201c4021030a084086100760020040d81d03c41e4107045499070034a501d4244e501c01900301143d601078134030300b0f440340490700310400701c006c54819014030791900361245989001082a110380341c041c800007503000301000290780d400c0d00400c14290112115070404912060341000348480320b0301007040110001d80018104d1001c00c550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 582146888 1250 582145638 582145643
    0x1e0c150f0206060a1406210a020301053a05010608010e0f01060e0c0d0b061b0a11010305060a06080417130e0703180803091c0509030c0d0201170903070204020a0507 72
    0x8800ca92a08414807030340c0000350240d40e25003030000c11108103601b0460054680103500c0e40307020302c05460700f800c02640c0c4002610645400c580000c0148641e040640800e00d110070006c82810940100c2d0000c3e075034085483d03198101d11440601d5040500c40c0c25040340016140f5100208040f0600304041c0b83d07650b42541d242007895003030002c00104003203081c0f117091240b1340f031004084c40c0c140000d40034402031138880d12030b549c010300a0228514800402941d8114036001c5001480522828200510704880000032281018140020443c0c1600c802c184002100c0990800d143d82e0344480c5003c1d402d569040300685408500031804c050003034510160001103400140e004112505c0d10001202907038500720100400400c401c0d11107000030302c500025640281d41005503580f0440071103003004100c40d0540103030000b91002c20078024515041c002e400c03080004480301000d135000c540c00030b0030080e00741c1c141e02800010b41000504409052088502c8194010720031550b510f221080a01300d074000707107801d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 582148138 1250 582146888 582146893
    0x40201020a052a091605070602040305031201030b0901051915050d1208010806150d050c04051f080c0d1101140a08042001020705040e01060504020f0a0e010c1e0c150f02 74
    0x26429402c0c44904c60740980c1824003c0040c042c18040c05581035404401c04842c015400c0000102203101030000d02880358481a00540c1c0354590308218442c1c2c04003800840050745001c0070f02110807000c51103004c1c0342c4400000803888881c000d007003c0c41c00801d0b41c411030b0441c44985610301007000200c5c500a8081031522200b1042e40c94031117050303a0b200f08944014500b1010600710f14a0f10700507080001c9140300700216803802113003101007801e03100d0642d0360300101c08504608080b4080d2060f42d84003c0e082900080034290248400a0305990103a880648000382134514654203074401c0300442002a0006480790356981106001000d101c011541134030f4800100f1709144050403000320b080040c5074140d0080c021581080200001804d40c0290f14000350340e6103500140c1602e0300e0001d840040088d800490726600d841d5009003260305035003403c5041040301c40394040000d04069078413040110402130300d41140c92510b0224125406030b0000c25074200107000c0e503540c541d8400d1882103481220303400e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 582149388 1250 582148138 582148213
    0x150603021009080c0f121504021f020a060f09020a0602061609064e060902030c0d0b0d060e06091b150f0d0c39020405040201020a05 58
    0x40440d081142c902406841d50800c081152882c03821511200201d540107100c0c800c4c0034001c1d04105d10f403881c42c81c0858107010040040000b03510340b900c0540b2001d03102a00d2120300b034400400082d02e03102d00320f01c010495540d50704540c841c100c4560082010380c0d40a083d4601707070340d160500030750348507030407501743c54060820031510f10228420303401c510403203405481b0b04c2c859000c0104031041c280d45661900410801b070f1546015a513508540a17a810303e0118103100403500350000391401e40340d680c1c0150902c90b00402c01d100701000900100c1d00140d844441c005a0551604000791f600388110002900700c6060480403140c1c002c0105e409401003401034216890541c1d07441120203044241026954080304a891a40310740d40408010400c074100d16400394503200d008a0343c4001c54482000d0103000a910000107103d14404072000c0c40d9068035140406034061540405100c900300d0490300038080c4d42c079840030404690003045202c01c00b41c3d101003560b50181d001114661001c11400070803001c02074141 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 582150638 1250 582149388 582149419
    0x90507091415070201050d0f060f0303030e070806071b0f061d0c060d200d0504030207081c0e010c151b08040803040f1e080a030e1504020907050715060302 68
    0x403480b81081c01985000740c00c01d600c1d40c0040d6510b40042c41001d60864890580c6c0c480c41c0340300d10801018041c4102d03800321050860034018121003480c0e4424506a10418060010140005e1802e600c0074152504020508225080003200108040003c00070041d0006000170805c1d00d070426565400c9102d00c81c040d840003a561940d072056400d2000ba04083d0800c030028409074a60000f11400200e07001580300800b481c003682c156030313010310a2000710725a141d082c041095814400100140340c014001d0110b040710002502240d80c0c40707009031050091582e00602140d0059012000c1550880340103030780004ca00c40350001900c001c10b0417580d204500b10710140d2150103096083c2c05240c12203c41421035031903503242101034980d540b0903580c1010f000c42c10212032130502c0035001410b10504415442c1e1b1076020014059070804101100950450035145e041e2000c100b14080d0f010b40c0440d07040c1000e8461000c1541d052043c114094020f0309400308a0351025031940080742140c0c801c1d5518a454503820707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 582151888 1250 582150638 582150649
    0x7211103010516140408070801050703060509010b030601180e0709140d0308040b07030603170702042d0c050c01020f071203060503060c030915070201090209161b08040905070914 78
    0x1c40e1a40c01c1101011070303c50000d03120301492400f101c06403083c2071620303803200403c0707207400600c0c0d0002038180c0d1540c007000070480d490300482e0700070501662425519414900103070110b020080c201410444c2500714a12000028405400100680702001415041018004040306d145006070f54080c070281c0398403c3c00b420402c440008103a0107a9420105450315076400c50a484040d1440e01015183d01010000c1041c02d04241d0241a00d000c03043e9139010f440c81804142d801d008880c0a001603c00301166408074891742c204080c4000003c000780703200d61404107482134010028540d03403035171002c01c2c0c0841c404460340041c0316050003201590b2050001e03603400c4040c0d8035580241605178100c40040360802d49214095a001030204050b280312007002e28055060030700441d00d0600603034407180c9180c01d50070a0740d40250024011020111502c100020140580010760707080400c042d04140184140145803003598007412001000f07101a0a110400030806103190107403c14510741c882c1403402e2131406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 582153138 1250 582151888 582151891
    0x120c04111801050f070c23010c08090111070e0109020c12030105030d080a062309070c0201080112170318100b090103060b040b031f110408120309072111030105 70
    0x780e1640700310007a90300c401140d9a400080404100300000d004200000703080c80c0b103550103000c00105100c4041000c0100d03880a140c051840c40c1800814409440824849011220018802e003040a00003d00e10710280c41c20903d035006075001c1d98404008030703491026030001d26414642200300e5043c05440d100c0003a0910083c401c0c55815400695242d0a2a01807226070f50712803015100010810380d502400c5009038031000c40c21100c40903400f0340b92110b1a10003c4150040707003d141110200501d0b0380080e00e42007040c000c05516021060b0400104102c00130b14040800c00da4844644031b081c4202800c1c904102c107e02d06103039010b5200b40c81140c032950f01c50080020300c01002e07843c46901e507440c2d0380c00500390141400e81280d242ca604144a0300c0422400700004401d01c001c0d17400861244c64402260540b2070075140d09041003108100c00c4000203486161803503040c03003590396900d40940d030f00c1c6850010b601450942c2c201c1050101d1301e41d02510354081007406403a840315a1006070041608a640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 582154388 1250 582153138 582153157
    0x10b0303070b18060a0f06060206150915131a010c3f0e0109092003060103020910111212070c02010203360f131a120c0411 54
    0x5026001c040380c106809541c010490036600c1c041e04021490460a2502c1262491907060b00c034035010050303110600c240c0d4001d02661001d005c0ba81041c0c0d41141105405010b003a116025840c00300b021102950800350030392000420440180400140e004c000d000440411440360070b01400c1003610b540980c0c0040c600c00e03030048104400400c031146003914500f000754045503c0840c810721181489415083d46101c80c2d5645600e140c1d00350805c0014640911501b2507a407083c1408070480070a402c01d141e6a503500d030b11003039884c0c80741d8607a0700403002070089400b2260b2110f61076100669035900a41142c00d1070351440140e403060021501400b030903209103245800d4440b44a8001a410342c0f181c0d0101c0703040d902c1441941e10701038000400d0f490461140380002d118101c52012a09810704944245101030703000c0c0d69151500c0b48180005a0800e0800ca10300000c1c1e44030074449803501b942199644244000400c0041c0c8490318010f40781c0c0d00c0c01542003540c0900c0c86c04580500e0240740000f40c801404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 582155638 1250 582154388 582154393
    0x3060402032a060c031b12070b060427120302091f0e0613080f01090804050d0807050a030806030d020a110d0606030510020a0f05090a060305040f0203060108010f0e010b03 75
    0xc41d004508240780200d002d006040d00402203400c00c050791100002d1020740301c068001c5440e480c0329449010103648039228250580d00042c40381003c2030741401640c40107900440402c805640e03003c04100a080050980c07046400000074010714400b08003c00740c0118003600c942d00700c004803e4400e030120710402c4c00311075100c05661060309242e14861003900520800f071402c1c034024080c0201080c09a0007a681412a03003000c00014425a04c041100c005100d40c0b00d0024440b03402652620b100910440c054280211420b11502c0244605202100c0c00c465110f021900c00306000d0800902074081926000d12902651451540180c400900400c0d80d030b03001071002c8110000041000416070780280d08840c80b5480b00c0d40003000c1201440324220f0700343ca0401c0581d403005003800003445008515001e0081c8401801042001c0e1920301002c1c0a803104c038140018151102c0c02d0500c540420200000d50504c500000030907151019004500400300140c0180030760361089041c10f09a860b880420ba0305903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 582156888 1250 582155638 582155653
    0x207031a04110d060f05071d011701151b030503040c0504090c150c060204030b0f010f06050405130b1002070513090b1501030b0a120201231e09180907050306040203 72
    0x524204110360b085a00c02c1c080000c11a0001110000b030b5030302110b181000c1171013032324900003140f201220f5241e441c0d024a0604006440501703065001101800341d202000755140c22a2002402441d42e8222806000c1981c510b5810f180750040659000302e17011101c0c0100c80400060300c2c00c26001e6000002c0c0e015080102c82e0b81842015440030454000c00f60800160b0380782127012030980c1c4010000b95000e185991503610349200703244500841039204c03e40c4040390000400c001c991000554082e01c0f07040b205c6901080070002603c020b0000c0c01c2150790302c82c3c82c01c41111036140c0c00007001c4040340c0702590700319038062880307011401b00c94841c4400703002001954000f941e0b1280e004e01e104032512050400040315000303d000308140c283d230b40d00b18645e41040c940c41c81080d036802c580d40c10322900c116482071114400409070310744640a45689003401c103410800c07118011104206441c6100005071000c0c90301c0b160341668203112881503e41c10260300030700e00e002c10b02d0b00740414803620a6070083c1c001d181e00f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 582158138 1250 582156888 582156923
    0xa17060d060e031605160b090a03030e010e06041502060a0b06070807062003010e0c04150e011707020109060623090c041809051e07060f110601060207031a04 69
    0x6070580c644441064001000154440220003944d00000740c040c40c010030741c0d4030481c10006840503c0341c01500742c110080c401d030f21003695000320079001e5a5161421504583c1c41303100503a400b840c070f402c503568001804503000c203604d03904605981c3e5200b081c1d8212000c0d602c66001c2102103800e01542d060300300400b0054031000c81c41e05401040c8180c801c540001d5002c0030000c3e50303010188007030100354011800100410649400c2c0452680040645403080d1030140b07013101040401d480120150280121501ca404a681c0074007042102502541c20564407490300c40b400034000e104d0350000f118514907042d40498014400f0340002401901c603d00c4e0044d02903090200030003503200505c00e05061030704000102e403001c80e88003118000c101000c40070034a41e00511b045401c190800e4000194013155035030400151300c3c0010740b5422510181808102220300704400c07101e941001c42012440d1040d00c0002444960025101c81164002d20781080040d60215203642a00410b94011f0030456038590607107803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 582159388 1250 582158138 582158141
    0x3070c030e010e1302160206120402030706050408060714090d05070f08150a0e1608100e0a0215222903010e0411040b03060421030b1818060108030a17060d06 69
    0x783c0401c40701c00d030308440387c4c00541320783d21090358a06400201d00610046080402103400500003508080c0d003010305103403a43d40d803a00020010400c120258404007070035003000e0211014040003600741c01401c0450300700b0682d14040d602c24110407400b20715000034810400710344050b86c01a00c0c40d0740c0d084e603200e011000303000d4172080701024018003070510f0040483c802c030740c480001450780390081c00311840f031900b01c0d070101d41003640e4003115500079000c1140142e480303154119007403c10aa11a48412851004201000742110b00c5ca0415413820710100700c018510742c000070a5019072181d84445014024484001d000038801c4203066080c45000c1000240c41c1420300120880160000490301c45034000a45401400d131425545800400007980b01006c07a0812000c0107811400e080c01090b8000001c10a9205016010030151001c00007180280d0041600e03400010506c004030365465840d5440c0c16241d610002c24100440c8000c00d980a861900c44003d0b48262001001d00282c41543d446020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 582160638 1250 582159388 582159397
    0x10090c0207090e0f0607020f100614010810090e0601080c04060608010b0904020f0a08070e09060d061e060b0c060f0115050703021c020c010320030105061e03070c030e010e1302 77
    0x200d130244100c54051004100061403103058140c3c0200f100c2c1e42000801820200c801e10000740443c14044203101d82a130128448504600030b2034160042d030b80d041ba02d11a040d080b6042599401d060003c7c69840543c000345180c1a01c0c40c039025201102118400c10048a40c01e108a0001c5500c1800400209100b5406040141030140c40036103020002882210303180e022404a40c0451001d0045c04101035000302c1e8a00c0c0300c407003a542c40c600b504040c400508071150408001b09816103e441c001c5a840c081c007031170303020070914400c14032080361100900b0351107030070031009012940300c1c03080091641c5094900050403654055080500c12030381180440783e0340d21005068003948140410351200851405030080e82c1102a80980190385804000500b9981d2480c41100b450340203c14a030b03407070424101147d045580440368070b5075400c5c03142c000000700b506101c0c006d03080348000300802100c5a0446808103c8503c82d03500d00c4203c005540c01514400600505107801c8102001d0751005415164000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 582161888 1250 582160638 582160661
    0x2090106180b1305031e3a091d09100e12070309030b0c0a09030f050f0d080610020714010f02120a090e09060405101d100e0c15070f0c180510090c020709 67
    0x404481f500120320070140d0108440703600024440b400200178103200c0000c9071403280341040300b8443c181409007505d5620108145055202c03a1365494001303c14000704000e515400031109010b450716071030309002e080300070030f440103030b862020f00d20004840300350800480d400302030f254a0340407510782540c8861040b0482801c0880e0380380700d00a400703031200340b040002000c190403035510407480786048000e1004201680580c802994480c174400c0c01444003c1089440c010401c0c03909030380034400c40a040f440c0c030383c0c02c8180040c880c00000e40c03040c10715401165a819242901484c259030b450f81845070f0399459085030041d04c00d4104200d0206400348540080e0021080d020320007405c1d504c0e00341d41a040c484915103154000342d0f0390401740020001480004144403088441d00e8821040030011107107445400e03402803011220780d84110400840b0b0b9803c1011b0456042a1516005c141003040010101551601107003041c000c2e000540d00800d0003a045008001d5028100452030010050040c10555002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 582163138 1250 582161888 582161953
    0x340f020d0501290103020408070b0306061902031315080a20040e1005090106170a0f0e1b040507050403020d1a0f041403040302090106180b1305031e 65
    0x80008920240501d000c40d0b00d59103441c2e0f040120540420061141c4040b0b4281414014041049202c0c40418210f04441088050960b26529540029000d100c0c02088a01085d445100a2075003a4008090241403003014000010346458800190300002d01d200c80c08002003560740001c0700280340f5004241d18441031803020b07142c002c10b0343c02100e040e000368001c01c46c43c5c1c00300d40400840c4d5000c1510200100426a560422941003610003002c04ca0907403d02e007511014400440c0d880e04aa40c4107000b605c51074002045210f0030b1500070341d01c9052032142d8001d403019100186226140c0b038817906001c3c3d6981d1b110280b0f400c0c6075509022480354202415103291400c0025008070b0700803920190300c520f1503170b8030039a128902441c00044881203031541d80060790041c04144016203c061800741540c24504041c45074644120700310094040039003202142c0701010580c82076211040c2414002d8501c01c5040d5400e05080500e490201d5a0f884101c08166112000ca480840801d030440717034007032184508 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 582164388 1250 582163138 582163159
    0x30c0201060f0b13090c0203040b0f0c0a03111005012304061203050c060108030a0f030209030a050d0201330b071704030f110409050706030c05040306060803340f02 72
    0x440031034040b50f5444506141c800145040310100e1804e4401d0240c002041c1c1084203441c0c0134402566400369000c0c00e9a18400000d001ea0581540e01c00e0b6441d48803020100c6e2980c061a01e401050900400d050400f14403400c00782c130528404138040c981c180d482c05650b031000e00c9030143c00840c01c24035566a864000340d5550010034404103a901860000b80640c07200d0780c0e500c030354485007031820074160300c1600d04e90814010601da45030b00c01c501d40c1e144040c42c13070056129102100080d04240002d5401409032181200c00d5170015010341184c0f42080782e00440c41856801d4898400c004038200403820029101c400c03080c04400d551101915101c1c1c0181d071800b8250307946e945507100f142d01c650070668907101120304180c1009940c56142c0040481680d0a00c94550a9501d4580c0d036910b601800d401d240c3c0f80c6146000c1d041c03045081e10f00844d040fa40034000e240d541d80c807064981e03000d190381c00b13580e00c2c90201002080400309e44c02ca110301e00c0c00c0b80000014a40d901c800b158107206203802ca03800047d480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 582165638 1250 582164388 582164399
    0x200c091504090b0a020712020601120308220f0620070803090106050303040305100c0c030519050c0d03050103110108060102030706020c030d060e1005190603051905070f080a02071101030c020106 85
    0x3004948103a1300d41c0e60041e40c414050410b00c0440da04e0b50017074002c5500800060105e55a2040329440f0340d03606040c000c40a48800c850711002205c0c030090711032404003000401c003d00c260716281c0901c083c0141c104001c801501d00b00d044a03004100d20f45401000104441000a8110001194884884000000c419842e10f000a056a01c1a4401d1b0341070b60000440c64683c643c940f11b9048403c006003885004120165005011030040c040e92a01d0781d0461040c11502500a00485036614229020749051502d000e03009001407500b07020603075040f140f01048198550040034018040e00c0160029404e085450f99041c0107036101c052052120b01007405144005c45490107401c010f8160080d1034142c13071800c3d0b00e050001d80c03ca5030165100d20481c604100c1c8295003094520280d5600385404580c81c2e444801810b0703454a0002e62401d0146800704000b400355201c5000c0020a00550b5010519114000740e90180d0003007031405410b8036000c0d1101d800c55802540601f4a00005000206000f60f07501c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 582166888 1250 582165638 582165653
    0x5030d0c02160602010506100c020d0c0b0705100203040215070c0e0a060312080601050a0f051e0301050111010e0303061e0307030809040605010306031205070201050d0c200c09150409 80
    0x240c6140541d020a00c00320b004202801080003804161000300801d18210f00000c406008125828003400f840b00300100c01d64681c48803c031501034109001001890f0745800321070403544950801d95490040c080c2e9409103127494000c4078000c0d9001441101c0e5402d02001584281c2d11560048542d1050903100098100891240750310400ba240381c002405441c5040507014140e142108a003008900c3d01000000d80e000000c2e200c170000d0783d00d030000c2841a071641c240c441c0e1041d810303410540329420501001c680d064100840c10388500781d81d00c6560154800182c2d0903102c141282c844c00b900180001140ba09106e0b12208052070140c41c14503003482800007103424050300e500700380c64000703000403048003a0030980100b4000740f0080c0380421580386940c86280a00a910501e0800c0140008101056a200304250341c0904410201003007190070802c4003600500900300203001e0341c83c0404c441084c40101160103001c00d00080d000159a43c1d450041c0c100011080342c1091b40269940c981c0c0002c250203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 582168138 1250 582166888 582166901
    0x16060e100606030b1e010c12030b1c1e0b010b0304030c20040b030c060301031727040b1c030e04150905010e09010c1706030a0807060b0f1002071205030d 67
    0x2d075240001d0f0b0840c100d0900c00300c40c13114103011884070742d0842c43d0201664082c5083c010b942e0000032520312440b40720000c4000e0a414880e05c0c0e400419070550040c000d03d05040340c030ba41846503c800403035900c0d280308100400380d640d001500364201d0740010403090460500540d4051300ca03182c4481c10340c40308d0380c807030110a0369518044084c60000040100340d0800d803051030101001100104015000580010f000e0303c01404010072244202611103000d20b0b120782901c060742400d80d03c00f07003104d080d541400f60381c0300032400084c8603d041002000040c1441007003080c200c0c40302e000810b103100c100e48003907417814070310718046401590320340326429140500d5024101400c000800826654505500740c00c18000150003580c07181d240800031500d02e038010100808222003004072414560302d2400103400c0120105015000380000100001008110341c00300d0319280c012210508030818020034040c40b048030b48480f501691100074140084441d464020b1016481078045070b1811000781940b900b070700c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 582169388 1250 582168138 582168149
    0xa1508191b18050105093102060c0f0c0d0c030204090c0509131109070f140c060406050703231906030f0c060f05070201170402130c0509040b01020316060e1006 70
    0x1c00b03099115020321402114010007017102c401046003428501c181c511450108114202c02c0300c00c0d040d540b1040741e03401c03242d016900180481d448018a2a856849141c0c41e900c0d08070900559250101a150601e14144526003060b18251101d085500384001010103070001c0d105c3e24401c3e100040c45598124000b88180b228200c5030038500400e00d044108156508200c40c40362005000b00400203900c6064100d4102032840c100e0103215000038880160311440303c100c40b5900078070040005004464020314000d80d55547c013008a10400d0450244000014007190300120050000c503858110040310005810031030b0074001982c56595803000c2c5050f1811500b16040d014003d410402c49070021107095105016081181c5014680d50008001d403d2072418040d156020074080303415034075807501c86100c48420200c01c1140c054001c601500319081030b4a92032084d07003003810320020b551021082e01d44060720301d070007132901070100c1c2c1e500390140c101a2115116481040720101c042c02c0e850140070010310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 582170638 1250 582169388 582169409
    0x120703050114130e0f070f0504050606090402091507051c08100314010b0d0f020109061103030c2a0a051002040e0f040f050601140406051005030406090503160503030a1508191b 77
    0x511f01240c20000060a41c000c51003585000b080140c5a254001190b800380c104540069562a01e440010a13144010601e100c190f2800b207109070412100186003480c0b501305801002c5100c0002604030b030658002c503940c00c05c159401d50104005102590146402c00c0500f002048800c10280850390085c4070000c248d0b50401005204019543c0000d0000c2c064585403400d404006100143d80e0340e2480043c1041c01c1d01b410015001c1c4441d50a4407400c1014641c1111070550303044941d100c1556842140e0003030300c0c0340c01895141d4184041500c00c81e411200b010039045495514500a021301c0340d8001c2060710900044d20480300000d4050ac1a213000e40b094107101410610584244011600584c0201d40580200000301650b1134000081d01da01540c0a1401b25500200345001421401a500444480780c54074091004206022000d07520490024004100d4150080c0d00c0074411041c52042000c079422110142c8044240380411000442c003034003030340c41a1021084a1100d02090390300442204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 582171888 1250 582170638 582170653
    0xe190305030f4b010923190b060d0c0206090c06310e180f0303060108010302091b040b180d02060f1b01060902120703050114130e0f 58
    0x4007030201d15030760003401d0b54004407110885260241511010401100490003009000e8042e410f00300c848030300303020107070322220640d0350351051294043d101030551400300c0d401c000c1c402140c0201c07900509115031248a1000c0507442413100100041003843d9495400590801014028082c9070040303210b2100310394014071851807d005040d09212031050302d6482480c08202c4011010072000d200380f0072145860301d078010004150b0800070141510391200f04a40016000c02c442440d04e55948001d1080c86015103441c2201d44800546900c012100603000ca16050f005101505041900545c8401402c100001801c00005001000d4005a21502c011507001403080744c4560400c01c0e031041118213540e078078092081c07a40014010b01031003d01030600b5034045884242c00c3c0542e0750250a00034910000c000060311408050040e40c03000700f9041030031503060040f440e418828840c4034105e84860800703404051091040101c126500c103500103130241c07117011001d4a40c000b48071400055900c03200600c0311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 582173138 1250 582171888 582171901
    0x20c190b060d11191e030b18030409020f0d0f0c020c09010b030a0504050f0f010603120513060806030c150901090f080a0f0614090c040c0e010818030717030105040f0605130e19030503 80
    0xc402c0041c840c002d045481d5200420b070410000954ac10f40b0018000541c81d5180210310481c40d00840c00c5540c91282070144001d9000c0b410b07401400902c1c1a6400d07070312025621802c6c0201c2181c20311440c01000403c2000032141646540415086841641a5000ca082500255140c04250004425a039560300d6080080220141015084489900b0482e080a0641c0303030104051025114000505c200e4800082036550107012407280e20394000d200e004020302207810b150a581051200301c0c00f09640307060219038079000030446011544c035040104205000d03540c0300760380000b1200040368016106c0ca540f08064200c11880791040d04050b0050040710182c80810040d1040c0b04001401d00c050500c10f80303e140d0b4030440c61648901492085800d0303c1081c003030349195101c0c0c2c10000d82240d0310209540466040c400c003e50403500d0840b400d2040300c0d1a07219581c11901ca5100d544d500c8000304090070341d840015040315601031106c506449140c42d460495802403035031480114000741c00001004074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 582174388 1250 582173138 582173153
    0xe07030f120e040504030e100509040207111003060b030403050f040b03040b0a0507030b0a0e091c0809010e070608130f0b01060203072604060c06020c190b060d11191e03 74
    0x82c008040307805111609254038040c003910305860fa0280640c02111078208818001c500b04c8400c041c0140003107641e2941c0d0b00300503040450340c400d207500c1000e00c0c82845d60316521a001e0b076400d44511009252a64603503580c00d42c0c10740e20001c0415444e40b4148400510300c651203001d5441507000b14041c9000b0f207441610801140d800401030820300d480c107824032a6a4948550003400c0d101d0032025104562030b401c004d00d05e02100400c100341b20400ca00610100942d00c401101e0050440000034170840c01c20501c2940ca92205016900000d900500040c0b003549091008542c018010b00c0e04100300350881e200c00896010903040340700541d00001c0c0440c00c2041940038444041584009501c02110704241c0c5200c41c881c83c46244104080102024180700c0c0550441d000710700f81d04201c1d8050851480d510761a0f90070b4000580d44d15181400048030342c00c021461814260740700c81496420219501000f21003004e852203200078840402000ca80c49101e0701c11030b100e1704400e0002e000e02d40e25507e0300c1d08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 582175638 1250 582174388 582174407
    0x150512030a231206091f06030e031c0e07080f19060207020301050114011409060406200f070501120c1e050d050a0b0f0d0f0f1a1e010f14040e07030f12 66
    0x10114407286c150340e040c5e9403e2145001e841181c500403880500c5034403524514000d135400b00600c40d002c00400811840541c1c081c2c6006001d141c1902d2400307580f400110703116860b00c0012203058010303003241001c0d515110326605110b403190200500b0a42e9507000301e0f084070802d07003050a038180740714880f01580d038004e200c0603107080992680524140c0c03804d0108059016921442040c170443d841034000415000e00d5003601d1944482c1216060b40702c1003402980c03100c0c24490240410b800c40038000b90225240103075104414039403a507690030038600075100c15542808210f20100070b0140420018003074680030b580d025230702400022403003000041c2041850400182d5070307031003400b03440840400150015401414150800b85082003030700b40742081c116840904035600f03038840802003041030303140300040540c1c4045e400310f8481c03800760380340e02450003194500e008203030490000101c01c0301646010740200314244840419600101e035a030b82e5914490402803030072210300e907000d010f0032443c3d5031101c000e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 582176888 1250 582175638 582175651
    0xc0f0f0c06041211040b1207031506140d030306180603050d09030c06080c0d110a02060f06150d0608121b03160f02030a080a03150512030a23120609 65
    0xa450035242400c07010f840c40d800d86004186124000e9080076039a03c42d40a0417a002d0040c0c040000d1103031360700c07540751101001c1c00121104903e80408507415051440707110180ca80148940c43c24184070070030080c4101d03109400f1000c058503007601007021050200345070200300c20fa403c00f04125045103010f60414400c5e0402c2c0040000c1d01c0d2040000c500140701d103200b22500e509040d0301c16215034020002921078108070b048200e003000803a401054214005103070340861542a10119268481d0000001c1019a400c990000304041d0f40880965110024100280700000c001402135554052a0074940714405e0004000c002060003a400c0b001c0c0603610b5460381580d03021310700e840e000e0400e00b03101200340c80c4042c14440700c0411103030841d20104002e042041e0000c00140c1c0351180f8600007270240c102070740c00c491240c065040000b0303035080c1103980903a14510080a1410281140e030119001000701030046499840300c03601d0114541000028041150160204031b104d160030320900c221040041d014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 582178138 1250 582176888 582176899
    0xc1020011406090c1629100501050901031d0a21020d030207050c15031b0304080a0503040201140409050a05131104021c14220510050c0c0f0f0c 63
    0x15441c5140350441555000304200c3d9030903080e450f80b540c0ca4520340151200401050f203840ba000090102d11003000c0c02c00c09441050000d00f284800d10100701410586a440702154940d0b0140200e40c000c002034804198180b4000070012440e042088400d1911858002a5005034a06000340315031078404043c3c2e2007080907003070554105140029620320001c0e100c81c0c10142e0101c0c041081100070b0018501508000f09140043e03080c07404031407169801950301e450101e281c0080a48200c41e55001d80e44982d4001b4482401e002480c0c100fa11075500081c0308904000544c8c0f8049502500c8002910180072800c900055510713010040000f100c00141038009100340b91520728000850078211680030b8201501e0250b104c500445501c3c0610642c00301b41c42c46c20341005c050301200c01c0d91300501ca119061100182c90014222480b00110727806072503024106030403504e90392580201d9500500e42101041400c180780207150040b145c1030100b000c10000c070341c1e000a803111411500070000003040e004110748 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 582179388 1250 582178138 582178151
    0x2d09140702030a080105010818011a0307140f0f04060f0b070c1d0621070b07020312040b12060f04020705010c020708060112061830170105010305090c102001 69
    0x10058a2010140b00c6c2904000c02000080d03901c10b04440c02c0000640c042c0000e118800d807443c80c5140c54101e042c2c80030300078860040002081034103080b544c000da6001815582d00c4507a42014403103400700301d000d00707034201d07494407800608105000100002401400c00e159261081494140121003c5034042e8010b801c400c0d2070b04e43c14880c889078080d0030a0040302d503a0081c0c448402c00b030280000b4142c42840c1070080440000765100300d607000f4080c461003181590110882e500340920540124058495844028011015960398124500b504882d00500c0f0240c1c1074499000103050b43e01c0014100e80c3c2d070351a01b4a0344041034041207018040c00e003902c041c060035030400710096202c0c1c41458002d0140e40d20340700608481d1401c641e00c07801d55138001208842004c050101451902000c50343c02c82c40711078507003e0002c424803850610b200b02c1c40302c40e4030b5141c0b6442d2500441c00380c07102509121441c002d00c814458982c2da01c0074182c40c201402c0d15200320010303558034150304c00749920000540300e0b41048c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582180638 1250 582179388 582179407
    0x203030703110406080f04060f1803180803090d330c030b1f090b0f0a1107050310110d091b05030c240c06011d0105040e072d0914070203 60
    0x203413a9a44006d40400504059036103080003406400404140010140b4090380c901503c0030320a01c413065140179840d804411800c240c4103640e000014460001150424810307822030786065403100300101d021701500035454250b0100b0401d80e40071030028a90a00c038100c02c4c640805054002c0d440740110703c1c18108000705105d004560034100c90443c110014074400e0400c5003883c010000700703014055a8100035283c01c100c600b5884540d0000c00d8007404104654031580417000e00050b40401d0791005009440036031400712403076010380a84204124980024001007d03c03010501c51007030b2480c012461000490b010041400c2045100d03000140260049d80111803680c44102079164518101056035907403003a00da4086066002d00300f541c0005018900c00012001100012041e0840d03250350720400b2a644d82d400c120894510300c08510326034002120821225540d0200850485440024495005052200459120041c0d082070b45000d0ba590700d486e40d50042c800e051540841540011480d00380b800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582181888 1250 582180638 582180647
    0xf02060618130803010b030a0605030d0e042a030902010909110304022103030406060f0f0510080903090a03051018051917041203140a120902041104060203030703110406 74
    0x18010428144149000c10190040d10340550b03511904001d0168981d44c440340280b09540c41a1190541c0751704000c03001c01c8918000c1500c030004265502d500441d040e00c1c03018000501010080c402c24281403400000203079280204240e41c0c00e0895400080e080b00920002d0806007041c0c201002c41791421200d10341c43c03045c20b02180e8010b901140c1c1b40c0c0d0b04000000e181e0f1402110713404642024000402480300304000c0d40c10410aa40b688080c4490b21521101d44816542c8907110b002e40c46040d07010364505060060110746d8101680b4025640740461400100d01c00d00b0207680200c1c0c283e030084005410711503080c443c0b1100c007544209096810080380d101c0540d00c02c1c1d13490fa000c18a0002039950420040515600d80e0441c0c000c284003500c0c0d1781d540e074601110000680d030540100d1144500c05401c1111784007150303402403507501e035803200a054aa090000303282032002203801960716002d1420700d2803180e0190000307001603801141d82c0e180000e8003c0603101c07508072800d9862002e010a01c003c5400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582183138 1250 582181888 582181909
    0x50c090607110409020a0f091a090a0507093512070b09070f0b0306120c010f0e0316032a0311010c032d0e0306010e0112030207031a070f020606 63
    0x102c030949044a5080002e401003000c10802076000c00328440014000d80e043d0842c404440001808000c0c50880c5c1e0207040810002c540c01c1c0d58040020303400601d032400340d64000c0f50054650f00c0d0800509450b015140d9440344080c0b51050284003009100d032900c410b220003220b100808401910140c003400f10403407021f01603030100510307854000000a0b90085d04014120040100a01020040f6580c074140380032540700740e0342e8900078100340400300a482000515038140c00010b030b50b102e43c0e01c07482500441d50922580f283c150b041c0504901051210821010305000d140641e1064800e000b040b01d4400380c17452116601030300742c44c031500d0030008240500d81203800002c003824a500041290301e02140d0180f2107511b041041e0825604420328020342c2403410040c400c050700c2e5140030380082e204050341e40c0400d205542c4411189030050100c100c09040040c1d440b4071900455800b2500c80c2d8802c50620300b840b1503458580c003104208009140e00922180c4202e5039800074000500300301b000b083c4003021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582184388 1250 582183138 582183143
    0x9010504021c090c030212010b010806121011030108150730090c18090c03080c0a020603090f0601050924030c0409051f05090d0315050a031104050c090607 68
    0x1030100c0c100041801c101e00310b40418404480800c0400080d140031130700c540b000c0c04140d024000d00c02d618081d00405204000c42144141c55154072983da0b001004041c1e850041d114030f003402641e003c032001e00860300911494a0f2003018140d101d604080d40030303140c400c03104400c0003140a85d500b44042c841e04a44108402c9140400b900403215000c01c7c40e00d1031a5002c040070340c1c0c203840e10810718280300c81c0b100c80c0c505039041075001d82c1540120214140070b0b0703862b0000150100540d182c00f0400191410001d00820f0301080603a801164103800166464000300c0c1c410304030350003400c2c40302c00c0b00c4014041e49000d084c049540750b074a82400004ac444908240c41c40a0040040880a07909941c040005000c060b500500900c42c0c020b00b0b140c4942c555169400350b002c07007901d0203640d0354030b03003900e018052156407900020b10b07d01120704400c40184c52010038051020800b44008507441d151050a940514000e0300384d00e0060002100340001c0b90001040d910300c0c82d006201c0c2c0c0d4080d41d80c41d0220350500340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582185638 1250 582184388 582184391
    0x503010f1b0306031505091914120a05090d050a02060f03010312030c090e190e010e0c0f0f0904080f030a2702030c1005040f06031d0f030304020607231b010e09010504 73
    0x1034504070401d107040c2301a0908207540e030119110780304005040218200486140c4103494801080c6050348419004003005a004100c0c00d2000b00e20394141445102c0d6142d02490459000203150f0300424499481003064a1100e0b800000600c00e0200a0352603800b00c80d41403604011903685010014518450350080e580e5a001c1080406e1450100c8086c4181d21041d08404110031942da241060080c10050128117160084041d500280e15203005c0100c000703400035001003006005502000b200000091040b600c9460034000b14440000c80d42c007941c81218031210000750405a091003e00d4100005540040e844036042a00c0c01a20042128075a424050b240d03141003c0307200105850a00940c0c00c103603000d94032104001001e0b907150f00a41c4903400310a80e842c8000c1c45590b481c5817281c81c00e00c02820b8079031041003c2001814803a000340701c0c00e4003950800c0544080385080045040ca03181c0d41c0d80f01a406400c04c003c0101c280040c003036541e0402d08000c41d0740f4081201103110000144159031296 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582186888 1250 582185638 582185641
    0x3040e0a050a02090915122b11161406090f04050c0d1b08160504060c021c12081503071503180f05070e061f0203040503010f1b0306031505 61
    0xe0950151a049280200140c00c0c514155500c002c0030f910000c4190722642e0500503215030801f000c030b0700c40080e02200481c901119545640d1601c5441254a50820410280c3c1c0c04e80901800b8403a07143d0b118103101081d0055403506078076001c1c03905400c041910031041040304510340ea075070f04008080740341e00f5500803480b07689080100d403213401103085000380141003000390390004029145140c0302c000b4a071104503143e2100319200c41500503c0d1104000726200300014403400e80110041c1072420300c001c1819000141c10b07188560403a103000c0342100c1d50158020011010340d04100e00350751250350032084802003422000080d9071054903200b815003140c00c00380000481c602c40d80012441e03c0c9585001c00900030145010710b200001c10200361038074001d40300007044601c0b070909158015000107161a040c14158030840f402160807159180562004000009080d1402e00680d400c036039000b4000120741d200084100b1444d42644500820503180c49030a02c000360804035203080b01d205a49000409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582188138 1250 582186888 582186901
    0x7020a0b060f041a0306090a02011b0f06020a0810061e05160203010606080103062711010216081e0a08040308160501060b0d150305100c030609050c1b03040e0a05 71
    0x908141d0b28041e40c210b402c103081c400c0c0340c895041c59854850000c0c0c04075080c66a071a41c1150303e444250703d00a00050307800c603207d41a174008200b00c240c580c0c02502d6a620989095685000701d0384030301201e0000ca00080304003d0340f4500081800001d04007824050041d00702403000d040e8030180c1e401d01c1401c0c02808112003921044040c2020a101d902400801c01c0588480018015078000d04c01140d0712030800c1815090028411041d9005031084c0c0c1e5801d100649a6484ca111091000146c2d0f0440c0715560710050810065005e407001400c2002c003030010501000081400c031100010000c00b59405151101d0000d00d603041103800b180c0e00000000d40310224a16041d01007110060050095130070180007198403194a8001e010401e80340d1010406089000803110010609100c00381c070540111032480840c100c00e400803103400042e440c0c0003511a0300d800c003542c00c843c0103680d81c3c50300440114101000300e80c6080520034070004035000b1400d10b1301e0300e60051100700005005083c05030b03c2d007021909 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582189388 1250 582188138 582188149
    0x90708240402040303020a02100507050a140f0a060e0c090c030f0408070f0302070e090a020112050c1b0703030f090b04031b09050424060501021c0c050d0f02060f07020a0b06 76
    0x280000c005000707654403656810025030b10105254207a01c9803003496000f840940c000c10451702103640c45000b800300c1000640b9605007001c03029036461041e011704200125040d0040c00183c0b241c0348103e60001b2003960300d10314a86040e201d40440740c080d0550304140420420041b0643e60b0004c0b11100001507a80d81d40b0b401e5543e4003880303034014002440032080301b08054011641c0e20949400030316461065480c7c2520640d03800d000784000c2e0210781010011140242d29802c22540207000300d1000f460b01103a01030400c0329252400728200c0c180c10502040c0300301507201d040d002d0051103034a040010b07103007050491411440f43d41700c01400b072131041c01c903020b0361411144074800611030003408119900d800e0030f040c0d0024400d141c0c0c0700da0b05c003010008411180c029119100650301e041e8000c001407225682141031a0203020440300c24401e0141b000d0380011030070401b20b02c03000355590700d40402042c40c03400030345030100c043c10501041d0395040402c01e10742e900103584040d0b15040b400e04007407620f941c40400c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582190638 1250 582189388 582189451
    0x309210f03140703080118110a0c060605060d06051f0915021c0206040c05011b06090507050303031f09051e0a06080d020a0308100e1605091008090c090708 68
    0x400d018400f0440400345500315100c14102c5142e4141d00390034150501c030020803100c03005010f00300036200b80701d84030030a4410b01d01c0c4160b4500c00c1100088a984070030016155411241c2164001ca4480006004600f0489006161010b40483d1107004240c01400644200380500a2420300e841403103400410340d100b045000815189940102101c0e1f0007a88000d49604045900396541c61640b2400103265115454005e040403d5024035600f00100c0c0d9541406072404030b6064031203200307a40700800c4c0e565051006500483c0c0d0148214441d1428443c01a440c0105601044c020b80c904010000e4107140e40305610007601c25084515151b6446a01010080c441d58001d1a4144a4558100881c603000600134804034002d48075149159244000c25000d21410302554001a041c3e03004155008012244012540341a01741503040c103d4010208900c52160002d401c00a071100c01805901c000034030490002c504140c5030a0350768a0181c0024203e5003010f010003030002040038410500a10b00c0c0c0c1c021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582191888 1250 582190638 582190667
    0xb0d05070e1518070f170c1b01060b0901080c040f090c120c0e0102071406040b0f0d021c14060306060906010201060506070c060e03030c12090d140a0309210f03 70
    0x82401c60440c0140f011601011283c034000700b2400940c0201d005e00440301000411040c02c20290150380b15040036440b40c000d24074012641700340d100c492203030000c01e000d81c0d405030800643e8107491701a16000106030382e40141ca490f440400401c42842256200c50000c8144c030069100841c00c131110b52011117035243c2d01030601800a10f095001000c09074810f80034501c0c0c2c042603007101d100e03503110001015803080e86050340341d0002003000104211415540500703c0f0301c450490342418050580f4180051f40c0c0502c680c00f940201e0742c00d40c1c010b000840c1c0300c2c180e89808104007244061030b050700841d40e20000034191030b12075516200005c046030f00c00d400c000042d10000d001c2c0307500c0c1d500600d040c1340ea049080c0160000f052841002c596281000400d8030b80e00030052004000c040c00c2810030081135400302c4841303900412080b03222004161f0040004260fa01504000d00e103012503410000c1040c1516088801e0012080955540b098036019480d101150070030017440010f84d1914090362000c8240544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582193138 1250 582191888 582191899
    0xc1c020603040605010305010506101b0203120d0606030c05030708070c050717030712020f070612331406040b091c050601081603020904120e03030c01020d0b0d05070e15 74
    0x2040100f080c0d030b070002e5040700d105100038400c039280c0c50308102a100340c041d4910300103002940c00954000e4a481700d801702030b0016041d5082e0981c82d00c0481d129500009106650945680c401c010042e8141705100341804d4a2038014110b040c0828010406280545280100000d640c00d0409001040c400180202042801f5a10302078100d61099180d8000e40350030b8803500344100f0712900c10b500206030244c0d45500c0303c014000150030204145e030420001c07605100803507a0750113402c5214001008070140c2c0003c1038004029054105034440710783d84141c11501030400e440c408040c203911048113413030544004940307482d00c4080c84004a268032009407648007144a040d5542e02c02d002002c500c4a0680341940d003614012174018540301d0042c82c951100035000041072001030041500c0702200c025009003482c108042c90186000207283d500814285102654001054812070010b803041100c4035a0641c4c043c60185c2071502c07005e031911001c1c459400d000005100088481d003000308100400c4200425 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582194244 1106 582193138 582193141
    0x907020f06040c03060507021209010309080c030427060b0a080a090b190c0e06070206031b0706020a080708042616080c010b0a080c1c020603 62
    0x40408600426018028121061141d18003640c02000030310482c90642c10700a0454078080c0941003507500412a503000c0d269514182c512054090034001218035a42c01c18004504c540c0c80c1850305400000384c0840c003841ca078208070385004004e41e49841c0d1180d6500000301201d169009400c4402028001340b0301a0f80700307455090f4014800d80010030422003c0e618118801001c0d2291110300090100306c40c0d1140403445481700390364403880d1607001954010049440c074456824040d020344000030015045400d80c03509c1c2e081798100291340036030340c10a0342031250080d0000061100050885008984503510030305d081030280d500129031120040034200e8090a05401c0e0b80c421301031607014000c110780301012000010f141c034000c0f07004680e035041410516084890013103c0c1480303520119020f1103080400a92200c0110080e103866410840101c42c100e100541d609001b9840b610000 = true := by decide +kernel

theorem cover : BRFrame.Cov 582014388 582194244 := by
  have h0 := BRFrame.cov_init 582014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582014388 ≤ n) (h2 : n < 582194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
