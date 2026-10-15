-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:56:46.002401+00:00
-- url     : https://prove2.me/submissions/bac41b9c-9e1d-4049-a633-45672be343d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982374100 ≤ n < 982553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982375350 1250 982374100 982374103
    0xc0703022b2a151b050417011d03040305070e01030f060b010201020c010e0f0105070c0209070f030609020c1c080c2a0f06090601080a03090e151c14 65
    0x490000c41501890103654004000c8442c800c064030b4014041c0c40210070b25200088030301204090a200e0300b00740400001c426102425a60000045002040d074000c03401d0401d5000404e860a841e182d03a0035221440c0c01e6601e280c050121a06001100010300d069280010000710050055030302030b00803110340c1a0b450014608640307003484050840480c90941d100000c84d02e4202c04217516051001504144850703406030308450142c495000c4550240400d2042d2403401c0c065241c1c040350071304000400b25801d401046105034020b06030010031844c5150348103824080d42c40030020309000c0008640b100961000c080d9100051050004281a8014000c01103441080e4051103001805112070905a0048846140b03000a4910400703440c8030b03100e00c1000d160104060340000101100910050824806c028201201070b040407140f508040301d40c0c1c0200360448181400c480c041d001c940351a0380d5120700c0b070300a210070402c4070381d000c00b5100160b10111608424144143c1c0141c401c03120900c0180c0b40709 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982376600 1250 982375350 982375393
    0x30f060515060a110c060a030e1002090306070c0f050313031e0206160201050f030a02040323211e3106080705040b07030519033c050c070302 62
    0x342d000b0000c1000c0c0200920410443c50903000040407180c2c00c1e210303040061443d800506580c1d0019944900e00d030792180c03040203413242080030a80c045142c008802c2c01b013521160002c0612060025600c2840100000305000a1095400505880d254010040780c4a0040f4141c1701c141c0e10b040b4518080d84401600b00c43c0ca40c803031030b401007a40b45000701c4002d4005440c900010143d0612009018035044071481700b00840c45084921401a034880c210f1030049603600c1035402c416040c6424130f0279000c04507000142c1d40313281e0b90305c861000c1000384070000e4804a440780c4c810001a9000030040050300c59140d00c09442c1402d20408600c00d60034100301c0160703083c0790356522080c58190505081120074012400303140c00421614185280944904d0a00c01641c03040301c086000950000c1c80d07108500803c05140e8001c0c40c5d502e01841441d48499080e4100d035007a08801e02d403241050320100c03042220303001c03151003030044202c1480700c0c3c41d120820881903080010181c01502844401d600f403180603000700e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982377850 1250 982376600 982376641
    0x20c010206011e050618031c2a2003060c0a120203131a06010f0302030906040624060918020307021b13020d0902040609052716030f0605 60
    0x400c0183e02e8408010401031807032030480c401242c01c140c04609510303044020004a46417400400b0b091880c038052611700f021001e1911600701d9031140311000c0c0c0d54004a46919100d00f44c1000d0512480e0394800291455022002030903104820181c0107041d4070102c038004034004c2102552001d94038800844001e00c202000790000a42603440051800703070f55070145400283e02210404451031a50b99050310921000d82c62413520400820810b0540e4032480d19401010340e80f8095045040c0401e24550355400904007c15080d2600c0d40c4116840440504005c226240c0b0b001804c15070703644101600780d100d43e0084010040c1c4826848079444070300d00849024040f168024210280c4c2802c10120b103802c044849544000b04e0080024012094006001c0c2c1c05804080011a40c174507204001c1129010f601c165502410314081007103154442040b5420942d07000104082c5160a00ca00e9040044501038480d00421900d00403040c007030384060072001035100f8641000241c03281c0300644180d80301c4008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982379100 1250 982377850 982377853
    0x40212030307051b0a0b09070e0a060f0308072402090103180515130b0403031b030e030306010f0509040e010b031207020f01050c1509011b090b0322060504030c060507020c0102 77
    0x1041c00c2c00440040003101c48480e510a480361780c08a07a0340e4014110701660600020740c4414024040c1c40303103070342c001d0b90031082c000da0400c10589800d00c111100d442d51f102c0640480030200f4040c06000e80b11300b80c00f081079000f803002c44010507001586402074122a45c9240042c0c0740c0840651402420a1403540c019007000c01070190748040c44000b40001c20040044141c889042b030755000148141042500035072081c0c0700801d007204401e0340b03100c0004650504800701400c0050030b080f411400700c02c0325040402881e0161100250003015115440784090384c907080352402201c0d00d866203042d03000f02c0300d0b0742046003504d075524114000880f0b14007038804043d6103c4200d290950b510342c001c100600741035841e001902d40c021800d00780d1023000d40044603010b190ba5180c070040864034401e00031502c002281e40c101a052107007031a0340d070071a43c000140b8110303400c6501c082c00320701028850351400b202544143c0a000354600b5180c01428401c0042c3c08452150070407010800c92400440c0c0c030031003c4010b90 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982380350 1250 982379100 982379107
    0x608060f06100c0b04060609140601081911130311061201090209130c1713030504121a04030c02190608070e0429090901020f1e0d09030804021203030705 67
    0x1000c2101d8804003034507140620220035a16000944d8080045218034000c190010391646000c4c2c154083d90b080020b41c1c1a034150348010130500340e0300301301d07000d07080218095a103040085084491000b00841007090b40c4103c4081000c0b10207500640500c01030741c3c45400405003092495041c080a401a041c0054010303d19070011702c243d911030350107054410301c0107212100000007007100c1400c0300c40c400d07038a000181c00207016019190810301075a8000c80c5002d612564807000d40c0f40249240550b000b880741c02001c02c03031100d050200032440c80b070302c0408000031101035040501d0054444030f1404801c9000e07010b4080c4c190318041c1d440903020102c900a803211652980c0301401200e0103011064410740c041e036683c10f8041003002800c2050b8000e500c0b508a2100d1010342c0007004001d00d8020001c55050f0700400c1451000c41105050720362121594040203202c04e0001510900c50003030f00c2103402e00c1c4c0c0c0342c00014810305521000d514003d0380269622503240c0c208650f40343c0c0b0381c4000c0701c566010680c00c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982381600 1250 982380350 982380361
    0x1104080a08030702070905041a18031204020d0b090313080703020112051f0605090f2b0f050102181207210c0b16030219030801050d050102090d030504090608060f 71
    0x1e00065902c200340344140da00b620745442c1c0c68011100c090b80d050f00d00405003400c07010850440513065811091990328070b000c403552003586954a200d61a90503005415120218045440721000900c080d40d01180d140c0e043d2504083c4207035240c0081c0f0103c070825078104000966010080351540c01d41e42c0694032401440c1f000c040302005803002410390a400c006100c640e07040d030b04603000b0304005403099070b070749540e02d0403c0742c10026aa581c2246441c800c0310717101c000380607a214030388101045241c138404000003c40340c2e0410316548040d14001401350f5000203004182d141d0035801c154003002088401c4c1e0200c07a4010b1240f943e640c40750180303100c41d01010781c10101c801074180300c007038020b8819481b99041d15111a000e1140c0d4101d80b590000894656104074101038041c0450000308100000941c21014282c0700101400010321816008580c80849682401008c0d0111405203a014046915440042c03500030012780c8a44141d0411a160a80c003050301903012480600031445003200e0f13400d54448 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982382850 1250 982381600 982381613
    0xa090e040c060813021906181202010309021f0354061a04290114121626011a0c07170601050108010503100b01030e0304181104080a 58
    0xa0030812416544c64040030040e90340c404101020203004200b8240149059806426800011031030410000c040c0d106110740030000380f402020a07024078010418900b540013041c07040b945640d2058094060f200110392032601034000000103403c00818101c00860011009a00200d828880200b10fa0080c2c01003c8100c030f10040000c5007401c03245007c0507241655496040310034005414101100c41840e80f00f0038a468402c0d45c0d0348407100c0d0000f00440d440c9601c05607808038445041810321000720000c0d1a010a0002078805c0300c9611280400c032070401e1100f03d4078100ea650701d0701001500b15008508459422032940318196018826512203908103042d82c07404061030301000a400700c0c20b12448080e00300070444c03a0028600ca410a5a25051002201e0304240050700311905002013040104040c2e100010f01100c0c0020720f800000d0741961140040f800703406a10031352a546c0c400454007003a1070100c01112001b04c0e00c4c2c081c0070450900c070100503000394004c41c82500c07221f400c08800c2c0000f1440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982384100 1250 982382850 982382867
    0x3260a0332151807031112010602030c010e0729070b071808010b010801170a05061609050301110403031101150b0403020103050f0402130903020c03030f0a090e040c06 73
    0x100c4050711a03030260024500c4a510540d04501d14080c048010b000d4000261400c0c210440020340f00c0c0e514030f83d00c0300c0b080c800301d6401901305000c240d80e4400b0303500600d05100940d102c0d81200c192003071300c65a543c01c00958a0304854491080f0354640f520301c425032500020404100c94078040804000d00306803540c0165915141411280c1560401072800040c00880580d4030500c081e88038009030340820f0b018040016942e0f0880c9600707038540180d080b02607800c200384904584075001c0720040800413840c510304142c11000020014401c64041c40b8011120103000c0010031566a00c031400d9507a6081010300f62503a031900c071510380404001c02d01c0400e2040401280c254403150020690314002004500c910186a00c0340340d0840c400301381882150b91500496410445001c103001ca0390405800094070000324444c031100385030f0745c2c05464040500034400d002080800070140c1c1d03201c0c0505600708000350b1000c1400343c0003d002c1e15000c602d1050000100303010701e03080b407000410036050100580e040300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982385350 1250 982384100 982384121
    0x1f0c0602070602130f0e240102100c0302090f0f0d060b0604080d050a17060a0b0a0c06140a0b0d03020309010c0201030b270a02092b0c0b0403260a03 65
    0x360200701c41d40118116000400704050510342e0f01d44041d103024000e285810898100c510110f041c070040c03141c0506a04400500100804074405c01c42c03a5050042c2e24000c044403c007061141000c1e2190590f9415901a01c4042400e40b48558029112820003540100d88919194011003500346040400d403d80d204807041640034040c0b9250070f4840080c54a40031203003040f80b00044e40019800d00841d48208000700000d009030001009040c01000100410481d004040600002040305105180700300d51840020740c029074100f0819030b40d642d0250f0100400c54102100c02d05182c0001000e0a0a08003004072613010740c003560400c0342e40001110a11288802a0b04064580741c4048542d61070040c2c00104600c82d112014000050400c401000700004088002c9244140505041c80d2640030000503449111185030003500507149504d60349046080000d030111014510110b0742104072001441903034000c102020750015903004a0310b003805414520f0200e40302c18064010814000d400181500b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982386600 1250 982385350 982385363
    0x708060a060906230f070501091a070807081015020705030c060708071e140a1101030c0c060e10020c250609170f030c0106031a09070303110f0d08060f1f0c 68
    0x100fa0000385d90440d04062010b640a9640e224100d0070003003145001d41c0c45002c018141d43c13562600f1038020702000390040044c4140905076000404460245017140c0241541a404910030482d50038004d544003542e0003032034040e129407400d040c0b40340740c43c03000c2d01c0c0041d501c01d0b0b0161a10f8503517540e1807908000103240f04255912495042c001801d0340c044c40d407400700c0720760003800c0801280c20701004044260035007905141c0f501e0403000c8510780c4000500400b036005000032480143c0c603800c443c035060003501d260301c0e01403006c200360b480043d01281d4803000d0350030710302c0c8000f60103600703080c801c1401c02500c0360382c0c04581105800c01c007000c42c039200c45480c43c03c814241e8404c1c031203072503005003135501c003516011540c0d566040a00402a1000c5006001130390003039041110728211500c80e544d1401400b018003071224048e0440b0290b0307030821441c0c04001d802400e07240c040f40c410001078a0400141e8955201d4020103407041e03d141408002d20b02030040e00c01c1c003807203c54034607030381543c81c1178821a094507407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982387850 1250 982386600 982386607
    0x280804050111100f090b10060509040b03030405150c0706020102030c18060d050a020c0106061b0b310b0105030d0f081e010308030901110f180105120708060a06090623 73
    0x103d00701d00c50b441d4813090f00507000c030350480d441c9000016204d008000400a50f403010003408026031080544110300002e40300002e0b41c0d80754030002032460107141d0100350b00c9807040c0b441000307442508020344038500f0101e007200c00c8983c58150603400c0c4e0008641980c07007035900703001000d0840310325030800f14000005428207190102c0e205c030040c155001110220b50480e000282c40756424400d104d100010003462500c4059000c0740d0b02015803100030b00c240600000104000b16a143e003001c4403248035100400300395800012070311100c074280c20600b902624044c8080d000010b0340d003004511a0056038040c5d13a09810544109001d90740110040c0c021680c0803000d42e03140080c10402141180614003608a107500c91074451107c6094600308803555440240c24029401a2081002619485151002101040004503004039942d0040102c00b19494240009000195400000003401941c080d62002074140d100c520640308024a07118280015001070401024018844000130401c12108140343c40d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982389100 1250 982387850 982387873
    0x8072f030a020106051e03070902090402091e011211220f03051501080307020112200f0a0906181a0c251d0601030b1809280804050111 59
    0x5103801ca4001c080261307640e80c000b4803942c038181184080c9021400c02c07102103040040c000c20784600c41071003001442c0e0340100b031111595540e90146c0c0c00b5210054080850402442031748410003c9038000280800c01840207001d406d04540201c64854a041064920b0b10925008454414005041d4429100e0701e030000402e09482c400d00c10310085004800401c081e280d0809015110401030b400038031139902c00c0100a0060340c0000c51841130200d441000101c80920100c0382c0301502c035034218249442d1000818941316081d507009410201d070141ea0780c541ea60b03100c907016200a0f103910641103806241c07a40c10011a50039559180b99201a00c0916080400e00ca901c289803558450031803501002000740c0300440b01002080e034005241c48103250048803d4882c2c441c442c0a0302a00c15410507440d208020196100c280400c0300700c140c0d80455040515003511900c3d103412500c91002071001c07062181e151840d21001d1461020382e00080890310703080c82c200040da080501c1d86102c500f14081c0c20707250346 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982390350 1250 982389100 982389103
    0x15061b070b07020301060e0907031203091a040b090c0105160c1707060f020601060c030503070203130b0a02010b01111510030b0703020d0516020c090a06080303040f0b0708072f 77
    0x1002800c03655000c0b03844400c244101425250705030406811441b200c401c005a1070000a00c500460707400c201803004c5180d11201c1100034100c65034001e07021410125040504000084260344202d0080c03050142c1034503203904031600c41c101c280d41203001074400c3c42082c140c44000208a8610b1740720780f011140a03503039400306220300010420400320503001681e0803c030098000040d98950800303440904030a604004001d09403030100700002d01003217404000542902d0007082250305070240b0200b6403150541c0e0388400c00035030f44508107031001942003001c440711550040601c4400107c041001d02201301c0405402401031200500c840d03840c0c1e100d484000301080b244603685010f102c640da00542d9030208404034805564014190441441102c401400010b5021034414146842241c80c2d100c0b50700e13458111000380640d41c1083d5460300000050000b00a818941500804d101d1a405000c680e5240400d80303126004032200d0001c1013404044007a001407072040328980590840f448400c1001103241d00707 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982391600 1250 982390350 982390363
    0x170d06030212012703080c1b030d060609080309010801030b0618071205181f06170309100905060403060c02030f0c0a020102100515010c050a080a05030a0f020315061b 73
    0x2c5035075510030414507040010300ca4000d07081450584103400c54034035500200300c204001d1003030507000000706080501c422013040c090040307040d020860703881e00814178481c0d0092101b0300c00c3c4c03c0030400d00500083c0c1007201000380c0c0e440c0b0380142c4440400340e18544640c6805200101155803092440c20000c004c02403404859000324040e03030307814264444500074141199409042c1c0c0001c803003a0716458801c403400040e00700c00300c24810802d22034403003400b02c40700141455400007042d980d1211000c41600304004007030440208110703541d01101051080503202e89105010b00c64100304100028400309460707410026941045204507440d080e8640f2110740039400500e40e1050310303040028650300307540c0d040100400c0c0108800080255062100c01d100c040c100078802e49041c400e1200000c000d016061220780455904880581c1d5074000c7c0b104010102e0f07208640540c881d0f450f00220407103020b00d81c400e50f0712550140a032903400361064401c006c02900052154282c21102c01310701103005a043c45030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982392850 1250 982391600 982391629
    0x71422180510050c030705070c080f15010f03050c0607050c06030c0d0c0f1d011e020105100f0e01090b040b030f0706030b041a010c0f0519030e040207170d060302 71
    0x1100806446440c10070b08019803010060b0081c2e0401050041101c10711040300c0d080b810a0802c96601d6036540380210b44607440d50320011040c06450310030b14030400b02003420106600d049080390707001d81c0c0f2090b1003010b41d40c0c6800b0241040e8820703881c1d0700390360500030010b10400e40a1070845580c82c01001c0003540507030089403c4400154017046a941030700c6135001d00c04040009040c682041100c51000800050800c00d1865201c68440003c0d00d441c0d002d8083c10880840010010200488101c0064007070701c01034410543d61201094006140c024001000040c0d410004004e01d490746001c1d5958094140e0307280700b42d4040d50340c90321039482e580c0c2046090342c2061000081c040140c50402c0140444040e8a9014007860409a0140d10f409012240140b141400d00b0040130141881c18044804202c0150040c218440c0e9600d0389034090054120440c0944207540760110000403c050200347d0140500041c027031f91244620a288582810240c100011034840000c2d849540e41c00042c1c00642c403820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982394100 1250 982392850 982392881
    0xa021513030f030c0c080a03020f03040507030b07090321050c100c0e240c010e031b07090c0e0d15060e011415071407120809090108071422 61
    0x2800d4007010b400090444602000742020000842c20820181c44030710415001412003200180020b5580d01a0f4141d81c0012810a0019142e03c2c045c5001130b0b44000c1c5000580b502500200007800080c45403100b0b03c1500d60001000798820307541c160000704140001d14090174402c00784259081800104411241c12480c0c1d40041340b180380a50015010414540ca0341e80a00014030b9003269034502141d5018900700a902d00766542c00c1c0304224540101a61102c101c0d09010010b54050181e400c1b800c40c036080811603007900d245a0ba180c1d103044c21203110021070b401255022011802c186008441ea00d0f03410f00440b0683e40c00c50800d031016044840c9508180c40c0e910300300005100140501d281455003401c01da5410110500d9110b1022843c040c11200074100a1268200100498144036034001856072030180b441070080c0f0300d0f154842d80c20040509009030024000000d02040000c1c0741f10031514a0410080808081000d03c080380b5200c8203140170246d4050803c5900d0b2005104200c000203034080d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982395350 1250 982394100 982394131
    0x100309050109021f0e0103020a0512090a020d0f0606091a0103150e0702210f0301030b0a0209040c0302030739020612070509101707050702040b09010e09010e0a0f06020a0215 76
    0x100180c04081c0c0b449015040608c140918107041c3d03041000c8841404042e40064600c2d503d8031401840c140c24a58001c4d00140d0b41004041007015401003008083d200307910511001391038105440450384450a6007142a21a20402515501030750203d001c400e81c10b0484002c140c1c40d009403480c8110156641001a4444d507107040c0c8001407441000039010541c2c03006850100304ca120540c45010600019100010610101e503a0400c10f9040b1401c011010f0400e014940210f400034009400c212840c1000c0389000501000d00c02030303c59100079161511641604544036064200e00e1103140e4001207800a000304881e84512810740fa1041c4141c411b90389980d81c0b10469000c2c401500b20f0880c4901c00d01081c2440f680d00300c5070508409610107260b103410354546440d4000030300600040e21a20713421160075130022035481c1140b02c4151107041c40b50000d02100e4800030701c0c03507651003203180301070020070000940030700144650300244261145881120b07244205181d8403a22001d050390f24044204104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982396600 1250 982395350 982395409
    0x20303070b07080a0e0703230708070603141e0c0906130e160f0906050a05040b0c0106061d0612090721120f1d01180b030612060610030905010902 64
    0x44c0a170015440840c0080c040305031455442424081d4224036106009940d5090104419800c100c902c0c000c1c0703250011241d1095580202074010302c0180211451030360b0407000511880030384041c032421050f40021705185035a640c504841360790803d21030340ba4400300070041d8414660030310346d0341005080e140002e86041d0030302480002c171003000161403c0c2070000c030b910011038803500702c0b211604660039421b10320f45d2080d010601b100d0764070903504002030b040300c0031410192940055002d5002d591443d2a01081c2c2c4e031702d0182243c42e4903142888540d00c80e40812070610402c1ea08840a43c1002c1d820741241e4a554907803c0d41013052544006101207035601c185035905000c4501c00401c07228045007418600c1051060008200760000c0b0508030b40340320b101c00c2e00c0c10164840d031007003184041201001180b8541b00c1d4043c0e00c0c0c0b54410303a40c4038451605e060582859030b40c0820814002c00700101030380104000d40500f5000350808110a9500c0c3d50f032041d107640035884540c82d00b401841070000005d41c51228 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982397850 1250 982396600 982396621
    0x81905070537080c0a0f09030b0f060307090e10021305030d050d1b0804031b05010c0e031b061b01020702100324140103020f04231c020a12020303070b0708 68
    0x1076042c500100008801403006035070140d0700300c82d1218102c4ca0606000781c0d090000380d602d1962640000c26401d115003c000381038169192080c0501012015103406030707610202c44080e20a001c12086060f04240d04078201d40c000e95000f000f400c040c41000020042c1d94400080c24a103240303040d03401040d0b000400540c0380c0342510800b0310960907800b01341c0c000610b1010040107054000e2008042c80070600c2d91140340003814580e0401c40758440300030300c401392410340024100d201171041c00c0d00901c20384000190990600d044d03144001130141c8442d040c0303e07040341960740c1c1943c008030865495508006103009a1196609228440786544000c100e04580c8200781d0503004080c42e00c105071460711070007030040c080e09082c0200c80d01424030300580c5501d05003a4041c0303988901d521108401d4803034058051004081c00c000320f040002180c02a0080c03d418921145108028030002d40c480854034083c4528602c50000a8545001a003201d003866071661b106811040c050315441d0106114500f0010721442 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982399100 1250 982397850 982397947
    0x435010903170c0307030e030c1b0f120318190b180319030302090310150617070903021c020607060b040c03060305100e0c1c050105070819050705 64
    0x942d611507030090701d042003880740a0b01019100700c04060325115141085441082a0b408091500c0c1c20381d50042c1038601008800050300506901440303041c189101e80f480c02540d07190b192140d48020707504c0c08611071861038081c0000e072304c070a500200031004104501150071214000e4800f5414840e91006d030404940056020030340300a210b5880085917010520f004c0024056895150601580303542a20000074100003190460382040b61030040c0c141d0015104184020454800e902c41109002e4004943e11903000c00f103400300003050217a0303801c00050514041032103a02440d14248103231591543e0000780e4075804048192000c03074503480c1c205454a0305101d40e0180c0f4000d8203042088034515550389807640042182600c6441d600d06107001001401e200550703c01000500c215003d171210190941c12a0130703944191415861702c00064035460040c0030700303402122110140105c02c041c800b044000b902000b4031030020094144440684641c0329400c01003a0500100309491031040a203040301080e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982400350 1250 982399100 982399127
    0x80709020d0f0b0f0d0c050607030c06050709051008420a18020d020403050706020303160306050d0b1503010501060905011d010e09040c051c02010e0102060402060435010903 76
    0x3440c008440b002642c0b140c40918841c0300c2600d0170395042800382006194180035074402a04000c0c001610320406a229506121451040ea020009a140c0320390803a0720344034a00400e600701075113180c0c1904181c0030f00603240d440740024102d00400100c41c140480e14100802d02c0040c60304a155481d0003000c0894100c0e50303d00010340c0c0200c0300038038020000480314010300801441c40e82c0000c0a9031500c85a4045401564001003220090b45e03807498001d40c0e0703902c211091100b5070005032404600320301c03034003c1070100c480003006d030a170500d508e0719188007500f0060041c140e540c0340941100341d01d480a0103554003c02042d103404204034544000909228000501c20710610880f218030b02150b81c0215880381d5942c1c060300ca4101e541c0d1149408041c0901e5078000030f80c400040c00303603107455102c071003502030100c0d02c00e90703400c0c51802180c1c0041e84c1da1401910001c3d0b014205020900840e0740001e104062007074500c601c200e03451411445e1181c03001000002c85100d0751941030311018107800640001c03809 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982401600 1250 982400350 982400381
    0xf030306060f1e1d1c0b0f0c0d0c030e0d08010f1e09090c120c090b0d0b0f1b030a020a02250909240905060c121f080709020d 55
    0x551100002c4043c5506092048144031a024000303c0ca038281c0410038040090140000d61070b0b855000710b060f03507100f001500b103602c154501c0c001140e4407038100120307004d02d000000190615001080d06005410903a50341c004041c2d42e00308030072480f03a0030404102002407948800c80103504025480d00c2c180242d801c10b8001e4500094005a40209000c00c40111042c1103400220030780c16103013454040308258071045829620041c0e00c0c0a200b0003548200844c0d107095005c1100034100024480c4030220807201400d400701070f03070000c0d420840d124580d550100c0303134005c0e1a2a1103014100321010307400a03241c0200f01341d0f02103524110180c04119080c0d440e20b4600341004201d401000d5440300e42841c2c058400c0c882e460302ca416007003024040c3d0341d160a41c00e00c1c105401c038803e0000d046005166000094882c0c2c480c10001c20341c0d03041100e080307030340404024400300c0903643c501001815481038881c42c8003a0007600f0340e000800785028025100036201e80c28016a88284040500060311040340d0709a40c01d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982402850 1250 982401600 982401617
    0x5150f07170402060a03021b0c01020c0a03051504110d1401061226040e1f05010306061d03070e13060e070e04030305070e030d11070b040308030c0f070f030306060f 72
    0x7400c400305191a44554100c036a1903440c0311816089003e8000c500e04da48948501001c000483c80011440990030a000c0c3e00705d8012070107007810012074040520015120340c001140b03c82e0b45490a0b9809a44280158048201c0030104004203d05601d11318040d90803120820500c038811400f802104003c241c60b044c40c00d40c01d016511014140300c0c40110003494115204030040f040311100c81514000e10074610784503a40c6c504070072010486145030790250100074507444040744542c081d00c640010395446a07100c80c4a5100606a120524000c9103100d9051080c503d00042c2c54104a10369071090004d49038552000d05140b030040c00796407185d00ca00441d0303001038900780301042141490a620540503c3c2c04074154a806c00140c5681401d100220f405004801c503061b01c00d9000600d042c51190550b00702c070b203465070b900c842c00440e0095000c01000c0c03260410104005032aa41c0240c0303821080054024603084c400da8540416180d842011004079450300c01c100803040e040114a080c10a0f6410130441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982404100 1250 982402850 982402877
    0x20a111b0a080a11091e100603050702120301171c0c120201060308071e15020406091e09051f140405010902120f0c0702040905370201050a0c05150f07 66
    0xa000100b0202500483c00c1c640003c4410702c3c41d0b81e1a031440c040c6141b0107502402c20001c1c0050f08a01030007107001003414803021030300d017030701c001449400c0803220660703a811642400c45200c0103013907040600c54288030316000321921540a4500d00000c2045072a0324181451701d14001c000085c010f001c00080d6494801d08002081d0188101c2e0301640d404500403040340284c00108171901d90a0401030182003002f10768010758a0b803030f80204180d40e0151900d50b801c3d962040001078a45070540c0d400c40c1d03001c1001080005001356000a504800b030614440006011034812000c1010546d0100c00d4103003040c43d82003128141880303424098012400194034010304174803e504444000791101005a000e80005044444440c090b40c0c2140d81c01042404203d516040955031045204480611402044201d0380710349079170030240201c02c071049061100800c858005542c82d801a040312024400302c40d01c1d1000245042c072400346600c208800c0580f16003400d207201e400000303000300040b0600460264030304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982405350 1250 982404100 982404113
    0x306031a0103111e040b181e3108040512010b090112020d170f0a09030605010b03040210030e1609020705151005060c0f1618020f030a020a111b0a080a 66
    0x10340d13031401550042519204400441c0344d440301030f01d081544400110a0003110a01d4915540e5107071152019829a51a102d9100041401c034010b01c540c071020000c104041c1448a1003080245401084641c2c00e05580b003010801c1d1520303451030792030240d45d218404111481d28503010ba01600111182e800c1242403a80071070080c0c14104405014101501c0101d44c0c10f00703140c4225440c030020340684584402075010f014259400380d0000700c50043c248400400c0c000300c2c14003940e229a40092050681480285054006100903000c044142c01065002c0078244650682d50000b042c01c05001a0f848015045c542e080604644030709000e038082d1024081c101c0c04003030a80301520011508265205040c404040c1b0f02000c6485100c0c5034041e11020101c00c02968003400100e035081260700424140c0800350608900c250ba600e40380405090000c1100c03403d4684c0a0107040d00d960420a040c010000c4016180446c20311000a030750391504400c2c22141406201c4100803e4650001c2048101c80e5443c107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982406600 1250 982405350 982405399
    0xa0c0804021c062405030105070e060711030a14151005061c360f120e0d0803010f0501020319051c0e0604060c050a020a120306031a010311 61
    0x680b141c100740680031944640700b020450b036168464010001d0a010400c00c0c03100480308080c0604c4106800d00004140c1418081c03a4410304190f40c408150600c46020031000e90080351040c1c40707240800b140740c0c04540b01007105415080c060118100034021400b0040d10b0300391401e0041c1c4480030b004040c04403e9006084d02d400381c80781120995203a4003c21a42c105c19a0804000b0301d901d802c00e5070140064020310841e00c0700a000d06058646580e07031480b03000d820100032034002c01c40d1000320005c0010900c84102d4100f901101e207440303a80c41101c0300001d5061941c108080e01d803a9000801001424280303180000201000e00145003025000340c00c98441d0002d408500d0140100011045685490072400d10f00d1040c0c80c1404100c084d416041045d03903603404840c111115480c210712110b41c0d5010744240c40b45125035600410040a00b561803482000300c0740d001ca001c0c1a11404084001500001d14880401075541078103907661550030b014240707501800c1e06a00400c40c0f0b10383d21400c580c420046 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982407850 1250 982406600 982406603
    0x180b0105152a010c020304180b06040509151e01050708030c04120302012702090402121c2f1509030715090c0e060f0d0f050f060f0a0c0804 61
    0x100719000e40800024a601d206807040090720040306001058035550064034500e40351155002000140f40a400590703881c401e42c0210281c0016002c207042204000c0d4001081144010b010b141c105581e403800b00d910f40005a490050080b0010750b208030b18244000d8030040410307101c0c850702c00c1d41d02d043e0019185102c0c1c0c80000d040c603903002002a186c0f0f101c64040310010081032801713034880c550302e0600a00038501407480300146880b0186945600b0720201d00d040740150000d10700700842c1c0720f9070700300126200350031803501d0b0f24001d85a502800703c1440401c03102541054869000007007501c414414610081c072594491540425100300490790002100310000c2d0304581c241055485008105203107018900d40101090380307025811940411035005066128810005a002c0a4982e09134400100381200d0b50b60300300344034004001c028238102c0f00180301e050045c100e4100c02119071b00c4031824041001c01200c1298803100900c90000d0b9150030b100d5015002c4001085101d50951004110b00e101400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982409100 1250 982407850 982407859
    0x2210304051c2001060b0a12050603030304020f090a0b130204180e15090a0c090b0906120c15040b0d020a0219030c030c03051306020d030608030910110a1a0a180b0105 73
    0x3210403c100254030140c0a80707440d2001645403001014010f004800b4503a8250900d402c10000c40c01c2814004141c1e4007903035008041121350741d4044140820114001e01c1a08842e0701d82d858141151540c000c8024185026280580d03900e003000004603c0b00c0a040c41030141e0303490842095018000070038014030110b50314201c208030f516a80011888d01d6003130440949952009400000d0001d02035100c038103038250030f81e509651550384208000607034000ca2045601030704002ca00428510305840110032100e40b1209240c24951a0700b40041130f50082021802044c0d8009021054203804006030b4502c44200034503c07c1c100c082d550001e04100d2804402020b01c0109110102003600880c190b8146031903088130381c3c40391551903900964551f0f01c03c115130007003843d040010035480404000c443c560700c000340c04601c110341c0011007207501180c0768410203041c0c002e41000200062001c00c42e03030707010751510816101074102008100c044403d4610034451b6043d0b0450a540042c4d8010720b950f046940440703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982410350 1250 982409100 982409147
    0x15040308070f0c030510060e090d0f050a1101020d0e122803020d090b0103170c340806040c0504050717060109171f0209010206040f0302210304051c 65
    0xa0903c00742022600001c089020345c9160450051460b03100f00700725603504070341d0941a183d0080c025107130443c41000b080040c803607504a40200d40a98024604035020740303480000742c3c0c0c035a40c0d10703800c80e0401503433041569200c4200d40400801006441014400604e06d540b404559007248020b641203020001c80d40f1005d080f4200d10035000f541600c42103604a082801880300341d1604c0f40c02c20030240411201041041c8035400b042a540341607502c0d41d00f4400c018103640c0b500a002080d00e001403012080350040b0844288240c009904000b00206031300c90003420f25003018503107200b0000c02031304058000c40c940b00030421807981c000061071101c18902103010700341e1120030048401c1c21441d044840c214100060740e03546400c000030790003078498850901007910241421200103901c41c4403d990700582c00100441c0220740c040d2203450400d4864011140c91031056007000030602d41525101110503404001c0100380711045c028100b240d00d4011781d040b00000803c070007030118420b0b1000180b000740c03540d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982411600 1250 982410350 982410353
    0xb06012a02040b04021b060c0f0403110307080102040f080709020f030703050717010b09040b1e120a15090210031103070e04090c0e0621120f12010308040515040308070f 74
    0x80d8041400044003404c10b560b10324813842d00c0c043c840c9007190502000e1060400040d951040c0005440540d4007d4000702d107810b10316100c0c40c41c00480d0004041e403602800c500000d43c0c98091005000505200a170020303814540504d9a0074030740c5642c041801940100850303801003100300112a800b10340340c10b00180545448404681d0048030030400b0184941e10b2001181710345034038000d0101c03514122814407107000000240140301c4104d00c00404200c40055112040c0e1a003584401030001c42c00c81214805191911401c006101c140844d0040c26643c2880c5006c2d414042402180e0b04820f040900011680c0f03414600144402040c250405c0485c1550000300e0780c031703504840f50603a0030804219000740c48080d00c15039400192006c5100e0041030031810389019003030312440240740c540720281c0300c0124102d030061202d81c0268174240c07468808202e02280004074041f007034040c40c012001182c40707a0410003030218044e030f01484030540785410700040001540d00c200311940d4507400035500700c035509107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982412850 1250 982411600 982411609
    0xc0609120b190b0a06050c010f0b2b080a1701081c050d1113050f15120a060302031f1d2109130e0c1e0d020121090b06012a02 55
    0x100c070183d075440410404000744096202000c0c140c0500ca001c000c010044405031140100d030402090a40c10141c00700c01c41d00c0e50725104403034050f0601350900d1403044070003903520840c0a9000940c0e10000c40d480341c0064460704410030700342d4003506503140102840413003403030f00119428203058000308100000400c85c44e01c5506400c8404100c01060407581c4420b5200c1d07032060300c1d01035400760501a64042e40d128003145401c01c1c80d0f41e00c0344910501c252501c180d04185205101d002008000c03003030f465200000041e00c040004500c094054600440ca04000001a80580c3d4010184ea88429441501c0b904019000f03c1c8021406511103540540e128100740d0003401e034007a1140240c0c0c444003042c140e0f1540d140580214208403126420344010303602050400c102640340907042d03400000703500d420403441c0c10701d000700962140c0141020180c1c0800404540f00748000c0b054649070458a50503101c04000300c4849803500a002401c00816002085500f401000300c8a104000346208440c05181035444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982414100 1250 982412850 982412861
    0x9070207090f0e01050604090c030602071e150e061b0304020a080f060912040b0d0207020f04020c010c0e0405011410050c060717070c0206092b0c0609120b19 69
    0x15660750a02c4000c201500107401045902d10001c42942004d000440503d414414070024039405400d00001c00d00b107480c0d042c002c0d000684200d0b21507125042c104410020100d84070205841807001c0c8101031241e0300060180c56041215042c142d02400c24030a00c0000c3c1520b440390b846400c2a0f850716941c0d140005a1049100c6c3e00c0104940035030302c03141c2640c40022800c1407080950a0032100c901f822491117942c3c91055100d04850b00b41c050080078810025500103008650000b480060368000001c0010100d901040000116a650b255a68000d1b604803441c200c02e040d04550030040b079803500c5e503451198100b440066200c1c203605546144024054005d0310401780c0c204048405600d400040508070310103060a1801000200e0001a2031074800d010400708240d000e03100c5030400b041030050110340c00096100d00703082c0c01502d400844c072410301c00b1a101c0f4203025510300c0c1e04841c9450405031013154950000301c1100000c41c0320303401084160000a400c86202800c0203644942d60300980e00608 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982415350 1250 982414100 982414109
    0x1801050a17010b09130311071d0601020307020901090605011404050d080f13060509042405040c051e0712080108030f2a0a05010e0a0521210f01140f09070207 69
    0x2c0b500d0302400302c2d0f600030480c4039080c0ca2003901c5140387d00207180c294a54500491280d641080e03607800d00c10a18042c6070b800c89420190600490703042103155400104000c009801006a00c0d554110420466900c45d200d1034141407240d4449103030034200030101e901142206005480f0b80400101d4040c0d10700c003981142c00800401103050b64054640400802e180e1040340d10340d200c1e03418075100c0507541100d2401601150800160040032910300000e0001421482803e03405100302400443d0200c5c0850750741109421440f1800b07540c0342c440340b92000710700401500303a1041041c0400113202d007540000c00c0b0791020202100e0385850300040410340303000c08035400c05181404111409500e030f80c9030000ba00210a0b00c548002d2210300801c0402a40d0b5000840d1b004d441070b40706207038074141000788101d600e02c1c1a80c0742807030525003031108074000c0c800c8103140a20200135403410b042106110001500c1c5014041402004800d00d55100010f102024030442c0700384102c0004010607003c500070000c070b50040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982416600 1250 982415350 982415359
    0x21206010306061806150f11070b040f14030703150207020d081b010e0c120f0a0c030308090c0105030a020a1e0f02060609040803070503091009111801050a17010b 71
    0x25a1a03140c000040c184902c104c0e09040100c900344e00c1c04641034029602907071031404502a21032000201144e90f142480c0004003400410303030304905202d0043c024074010f42540c508240e0354918020b400e81e19405250b20001e561000384032a0229960b01250310411203411030b1501a08960360500f24000b403003286802588038103c100324400700094203000d010041c1006800010612100c2401403d071100c3c590703a101150440900f10b0308070701e40080311581500071107080390b446004111030744e0320708805020140c540e420902410401c0551295030035500000c408090030b039100740d240019285020240856070070725000301d91b03001c580c1d1141455181403840c0081000b442c01500c04068240c04003c103007070005000d440c000804508061107484d010302d03403000c1d0061550b5110041282c45030009404c2d44860700030b001000840c060300317008140b5054091140c0504000c402000c03c002200030300c11030000801d09000420040d270fa015000c034119411030400d00e8068040d070304058014842c004189a01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982417850 1250 982416600 982416613
    0x406030b070f030615080f090c0108011203030b0319120302091507061e02040f0e1506030612060403021e0c030a06150506041701060602060f1303090b0a0e03060c040506070f0212 78
    0x1025401800d0710b01034080035004119503200c00030708c180c884c455584140d01240091004007c50703903c103003503499445c0c003900c3c0000d0200c11007400070381040040803c1b240424500e4a940052103440700c0d12540c059614181185030074048070200b40038035010041014282804240007090200c241c000c00640690010110f01d40c020b030040c064025005030040915014480802054200301e901c0d00501802c40303002107408080c07580d0100720706588000c08140d00a0030409107403a6079241001400d010b1842074001d00140ea44201c00e008043c022424180300139442400756031440e840101300400e0464100401140c2c0014002035820115140d038003d540051001900160344a61500304040c51403c20b8028840f060b40c0d01c10072a81c60006403140e540110150000c200e00003080d03425007a02600c42d003026189281c0c3d0b90240c02564014294100c0821007055500714079150901006a1180076101118101070070702c4049105400b60500c014a00b5103e044007905650340c40a4800b540301c4188201c0c1d54 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982419100 1250 982417850 982417889
    0x3110409060f15080703020f040f060f03030503040b07210f0b03030c030403020a05040501051e0406033915050309030408190b06010306031101030203270f0c0406030b070f0306 77
    0x3000518411032104070f100c6000b14003e42c0101d0fa034811a43c0040032a0420000c03071041200500b454030500b00c406a5645c030020f00140d070035812500642c044d0301c0300c68070303403070700381004020f1803002003844d000c002450b441c064004148042c509600c503556140003901d50844240d0100a00301d086086915100201f07048410340c9001000b841078910035030324500100d45e5041484103a0b142802a00e07400030880201d851034066016010240c440c0081000c0762060f40c0b40c40f0061190081003880e00c0041c10720101ea001911003c8200400c600211191141c90745000c032100a002e034604608410084000040f50190004105880c0034020b40000c1d1504044d01203803500c1d02800300031045441050220025807198068810001200e410440f806402c50b841c400460007540700a00e010361842a51181200004e9030b10b1a2501003c00320008052480040c20010315054030304070703207910560400e2014070000b1050110303035401003054100420b49140e14102a0003a002e243c200e40c4400c10303600d00488 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982420350 1250 982419100 982419131
    0x20c090c07060e010203131e0813031e0209161112041502010b1809031b0607021b130e10150f0602010c02120310050604080d0e010512010311040906 65
    0x141140b050310208502c0140c1d02c4001c0c01e07404121186030703000d01807802c20404511814001140d24038040900c442d1a150b40d0340782800b58002d185900034885220405104001d504448154920102c0c040c102035001c13268000b898050340200b1406c0e8001c506814030b22918094409040102102c1c000d0700c103c404070a03a4190903401c85e2203480194020469080f007684e0061040a011000240609040c441038036005a0f5070180901456030902c010058605c0c40b100300080d840490740e0001c00b4044a040280009144c000440c1000f0130f120b440040340186a950a5400c800e544030340100420b4208420300400d007020603032695030010704c1c03c00e00303000c4c00c0103201c04855007900c20010a8030303509a2203031800c03803c1b60410001c01e80942c2c00f11030a5000d039002c0030302a50b4011104920401e1454451000c21800e400540c0300304c840d503014000042d013098002590540b085400c0c03900504003464a450600b11440600c80600484010342d613078612034685802045003550040ca040c8180801c0100c3c92 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982421600 1250 982420350 982420357
    0x80a0306052403071101020c07030c090b0901090c0201020f0c060105030106171b040609060e09011d070303050a02010f021210050901062c03010c020d03060b0703120c020c090c 77
    0x100103440e082020825180100022424009002c0303030841a03030703001ca010400e80d07001034050020700002010502c03440c3d0713003400280346000000b8040c049981c91071609400450786a0400000c0302d0504419100303d45540303134424115910824040780c0104080c60503802880b8001c9040001c102c001a803514507100050401d0480700268020045aa59002518008a403407040c88040d5002189e000d41e206001101419075518000c00005505944012120480780140c3c426030ba0858548200700f00b648080c0b081c5081c100315914424240307541c102c4200c0d2100442c0c04010240900440e2005c059031003540080d40e00700f0940760855a90140039103a00c1c1500d000c07944030901000c0700350007203991b08282c0a902d04071101034580e50114040304860000381c0100084451504601c00018205682c01f40168a03070310800741c01815030f003034400b90001d041c0c80d002d070032084911104019a40c0040c0e071188110031a1044d406001a04000081c2e040382000c0040c10300c00c0e4803901d03240600c5101440d65001307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982422850 1250 982421600 982421617
    0x2181006050909060f04060b031003060b030601030807080c01020d05100509090a0c050d08300a0603020d0602090105070210030c02010c0201050f0601260c1e07120302180d08 76
    0x1002510303500c10040390944201000c507608a07910601090890812020403c13441000a00c0803502545806d02c0154582040312000314010b0803d80400610002d032145461031002500580f003e0760450712642124410785000401c481e1002a000c400c1c82000e40c140e6200c015144402d10981c1444050300c91450b01a000b40c92044240001207030581c0400914000751680c42148010307010302d41002c1001e4100143d00035110024104654078422400712544e1090201340311008030400700c0d4210030b0705200d0340200a411014034114003440580d4840a80040041e4840c2c00507030b4403014140100c8032400b032040025040410300c3c108074445a010313003000400e22002d500170083c00820f01d030200d00380c6034240e520029900c120004070740194810b6603512095200946494541c2600d800d000154a03811a60243c4c2c2e000f01081d8100d17030758482c43c0346d400a1104502101c1c108460794a0b211080d041041005041c1a0b000622901e6120101c101401c2e00100400b0b43c40000d00a0038004610350000300b9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982424100 1250 982422850 982422871
    0x10312110304090b310507050409020304050a050c0324070306180b09060d0b011802070515161e030b0f0d0c090b0a0f0e060102100c0c03080106090503030d15030218 72
    0x2002100c0071480000c074885c0078040c220301d00c41c5070051095100410000d4031050070000104004200380025000850003644207000500d10b101041c00c18a040001d00c0e51481d1290300031402e40c0400d003900320301203404091051000019a200c20b182a401850b8035403040c4128040560248083c0501d41d20820740d1f90000d440c0074503640d03900810000800d040600041c00780c1e040c0c6d00144401110204662262011004010314180254a40620b8004207100102400700b5007402c0080ca525044e03000d42e06401c1e10f060112006840007207000410020380604030030107558881c1c501c4640e48144403a400c40390041c08620a00c41c580c10f00031042c0c03643d070043d084483c1c249800c22149041c0550400c0c116100301036004803050810702c2400d0306079409460701e81184a00c3c809092050b10724420f04040c07855648424540103c2403070050034000b0164000014402c50b070030100210b45000c02101c070407903504440021003206100c0c00c6808580144c0019401501d801d0041404000040080c0c0c06a8003000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982425350 1250 982424100 982424119
    0x50904121d0a030b090a080705071a09090105240d020414031926040b0c0c0108010602070b0c100c091e06020c0d1505040303050a0b01020f06010312110304090b 70
    0x22400545070072041e09190001c0103444100040351100c1381e4290010b1118081d0b42c0d40e40101c1d01c0d01b42d02c9800c44101540c40d50006c1104000701c9050680c0c1b80c000324884d0142c3ca05000f24440010700070070b014441c490007551100c01c42109180700c002c07045146001c401031640c0f14114042800300a40150107203185028440340507c1700c62500003544c0e42d540000109074250380402d943c4a02c0280340300c2240d9000b01c080c0d2500c00f80040d00c0d410180010f00140c0c04125110600c4415407441c210080048605000300e800051180355070100e110000d60340200301183d83ca44420f00e800d403074061181d01d0603020902c0c0c01800d100141d0302034800c030121018852850b0680380c2201040103100078034481c0c000980d01c5000383c1c41e25802d00c5200310325481e00800050145050f102d4500007503400031141200000d07510810003501c194540f1885407800c40a200800c020b0420905550f138504041c0400341c03a04c1003545081110a100721003154101840c0400d8a40b100e0b940c20400b80500050380416120740e4900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982426600 1250 982425350 982425377
    0x4020d12021b1525120305150117010b09010c020d0b09062d0612030a080a1b02101805070b0d270201030f02040b0a05090301230703021305090412 64
    0xf0505104280302401c00601d080c0068000280c400d0b81c111401c0100f1050440c804003182e013100890200d41e40a4402250510300300b1282404001c0c000c00050520400010702c211180328070010a0656220410466484003000c0059840701c1854a00a52201c00014401c081220070103905020b2414101284c81c291100480d00b900300c00c200407140000000d03800f414a41e102144040c0b03811000141030603101001400109081d42d104c40c0117140407580c60000d0000c0b849003481000121301800b00c0040768824608002503c55104002c1040490f0310f842c03a0496105d148102004c2d140d134031408a40d2201d43d07410a41080e41c000c0000101120b28140c0c481d410300349101c6100c46400004824003811001942c019001000d60000302c004907642032102064003d6210010b207920321458032010740b2214010704140c00e565800c070030680580d607420f40b132612040002c40c20940016540c02c01503100c884244017800e81260540c040c9510540714028001800000704100020354130b01d40c0c0d001e4082e8031a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982427850 1250 982426600 982426609
    0x20d020c0105010504020702060d0911090f090f24100503010507110c0102071202090901090c120c080c0319150c050d1406030304060c050f0307050d080a0612060504020d12021b 77
    0x11f9030006508201c040000e803590b5242a44021506841608517079000114200482c40d00701003154507854600040040c846082c2c02000007030740c4501c00000425008001d010219948500f095040c0608a00c0f034022034099500208013030042c240c054020001450440001080d1806c40f00c010595402101c10310710f44c9510100704601640c24000d00c1540e252160360038480c0c05000100b114125560307034032411000034207255101e002003000d0640384003442c140342444600d107a465803000c400c66000c5000c0d0405a01e004c50840c000b10304140700020786212500b0902e01400c0c9407400081d8851400d5150400e04e0381100103000010060b8004101e050400c64a248102d2010707a45a03a055100388810410144100d08191080b40b007001a144020700030058145150400c05046845e500040300c0c1e2182076074080980c1c0d07488030030028140051460480d80702d031885003016014125540f10800075041d5110243c0c14560203034002c102118805075058004e45565944141c051316803050030707102c0da9a02e030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982429100 1250 982427850 982427857
    0x702150c0a0809010e0d0b01051504261609050103060b03010903090e18010e0d17070507150230060103020906120618010602030c0d09150f0909020d020c010501050402 73
    0x141008018000081d100c0500b590400c1d60403604022500c0c02c821115140c95458400d424451201e17500a0f5041c80200400300450203861011404140700c200101420400d0105c6841030000c000441700402140140c00c08904281c07444500111b0000016881003c0d032205041380e0041208100c8441c2d0001014203031500040c3c00350020740c40700c5d4203000501503040c0c1c440d0401464031078482c28502c01c0100c1825034481d00d000c4011600300c000d0150b56181c101c0009000303807054101c6403c9900e000b02c409006ca0040c05009400e031000d00250050740c8100354110356a44010000c1440008003c803071451448200e10a182100c408000c0441c3c207a502074000d8030000040102041d040040b030000d074008000006150b642d000d011311843c84030001d03842c0e541c0c502910a55029550320140a07404518240c1e01803440c4c010461304000c03c0005016401040c08503030601d142180902c00d542e4012a02610f507500701c0f0008034400650b900d00817205500800a00d0100d01c000d210b140e90f502c1c1000200d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982430350 1250 982429100 982429117
    0x4060903090b221232010f02091516030e0114030123040c05070201080c090603070503070f0903080901030203070e030106090e070b090a030210121509180201120c0909020708070215 79
    0x142590302841c183c4c2a400d04405c001e80d10321040110704d00c200c440c42d130030b45000002c0205c449500051120050034841640031100f501144114500580d049041c101100001409802c02101d6400b44035030340e10404d182552480301c0c5039016200d507115070b6004c40d614900300d00342a068880e2420820a0306143c028038030b007407181c2d848203030400c04681c0054440c203200800c0420514010842400d89541e001c0255004200c41d644d000c2d228500460003401d0003002e07404400a1011307100f0704000103030b00002103a9a030602032801685a0300c580400f941e03103400e20b13200c107545135091a101061000f00c60340300412540c07100084540755651984810b801d84146000107403c030600c19818000350a00b440490800501485c1041c01c078102da11011007200e102c80c210a4200c14a5001004914000d00847c40281c550094101011901c0e5002030a4000200d6110084c15200c00c281c0c44001d008070784010081122003815903a402981c600183c05e68400402248146410741861502c2011402640c1969 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982431600 1250 982430350 982430363
    0x21005040c0b070309030212010b190b0301090b06270310110a11030c01061409010e07210e03030405060703060e040c051c1b03030906031404060903090b2212 69
    0x503801c20b8038022041d8406641982032000a003000001030f01c901d009600200500000001c043c080d032410040b004004c1e040d00d101034101d001060015100f00c8007240c2c1100c0c4600e5001500c8121a0041049401814094900b80f450400400032400010340314541c401800c030140c0d49100110201c08045550fa00a400700c91807082c4074a40055005107011255100c6031011031382403900c7c890403213080d01d0440c1c103c881c00c0490f01013261040c0c1070001c0f0060150140c0003803c105071902000003000341089107408404245501d0750f080740030b8595400080e880444a064990761301d01410481e682d0071094991000203850071000003484c800441c2505d015950003000130660601d4081040350810384080e1780d01d104c00719244103c0000d004030081200042101100021080c5103050161003105030f42d0040060506086083e500c0c2101104025402a0320a1000074204c03c24141103904003070300d4000c019142000141d406039820211002d5070f0052000170300705040394a4600004640c081d403080102803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982432850 1250 982431600 982431623
    0x6040204031a0705040812070606120305030703240e04050c03060912130e1e010603112a0d080f010f0506041403010f020d090b0a0e03040e0a0906050103060c02100504 73
    0x201e112085550064450b1034450301781a201d609041c1010b030004100042d942c00010250304004090152070010410726081402800315600c002d0114440140701000701643ca144031605080c42c41c1c079034110071140007520f2800d19250070307210014481c155801e0350b59104a40d0646898940010400c1c8030728100005049000112950b07070400d5003014000c444440b14171080800c1c1140c006519900c244258070000240840c1c0c80507420040c441078120f0020103040900081e41c0d040d1010450f0420311101d001d010042100c0301c4114545240d01c0b80544282c05100c030030140301540407810341d00400845240048070b982c3d810034140c506446202c1c054204006000411820b403515400c1c070703d038210140c0003003a020640c40501e0105d0703000b0145d40089580e01c0000d41c0601c41000e040c25444404d0210030010400b820310741ea0b81c0d90095208110b4494400000104402110741125802983c41803080c07019584903d8580013501345c10b00704c840103100d600a82645103415000e901c2c05140c0003031510b000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982434100 1250 982432850 982432883
    0xd0b010602010609061509051e040c0c29070e030f030706061a120f06031e060a0b1c0f1509060b01271a040f0803090102010c05040317030417070c0e0604020403 70
    0x89c1d40b14054681511011107000c094544841c0603c1170312042c20380e20b007030380d50801d40380070314490008080228181c4902c080100030302d41d21189590b04010107080801c40701800b200000e24210100000000902010600708200807035500200c05a41340360a4005081e540191200028040c100e008001580e400012480427080c04101d0350304804041e050301e0300c003455039030003c203e2200c01c003400045502c41002c00c0b42e0b0a685109040320020700311120300007940e00304022052640d4810b0060403103a00180d08008024412419030038100c0351200c21322000c080b03418401d000704031116026000c1f500394820300c00c04100d80c0130f0008004c4034000c05040320301e0034041e0000700c1040401c0c2850410b6001c0001188500d43d504141c401400d865006665031068100020b00356480c543d203d0050000a20092000622a803a040d6503001f464541d15265a11810140042c2440d915500d4031b8410000d640414004801c5000e410750b090784866005685542041c00120b01c5984006411901c3c518500720 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982435350 1250 982434100 982434109
    0x6090c09041101030f0f0e0f0d1103040e090f070b1207050f19110f030c0c030a2a21050c010e0d020f030a0602031303080106140412020d0b01060201060906150905 71
    0x544220349282c0000d06d2450301900081118410008040ca641c003181c00c1403120101001542d841084915000e400d00d4502d080c0b80703590380118044c0d0460a044e440015121507020000c180780d60441400300c0d104640e0796907681c04030390b00c0251014801741548000445244c02401103c861015090131b00740b41044c4035000780b0b4001112051003040100c04c0301d0b21001b0107010840c040004078050081c555132440c0c40391441c80d0a54228440d8002d030400120380c00800c0005040440610940032074641810255424080300303055601710304103200c10000c81c42c1aa020404410280034801c1c401c8407150218100150382c0c40c0c1e241c00c41070b640071035502c07410710040c1062508515000c41c098121850401d040d0789202c00c0c0d802c00c1380e00701503001d101c96428086c10340c00041280100210704082c480c8a50740103801c8102d1046000b0321111000454807207046444040c94400820340044807107591f03584641e40240600340521903815101e0402c40c0c04104030348484860702c8002066191824914504010710 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982436600 1250 982435350 982435361
    0xb040e04030c110301060b0d0e011a100905030a0308041101111207081201030803070210050f01031e140106080f07050a050405071209111f0c080d0204090e06090c0904110103 76
    0x80b54042c3c0f4500d00008591424010100504403c11505445058440040080350007403915201284c4c1445010b42c009002010004108581507400c800125043d100545035000c840c0d00c0395425100d00300714681450b50002c0c400380658481c1381c0ca80000340b07014004462240c1c1103600d00a40d82c112840c00d014682d42d400c02882034a100f201c038182007079007021524135400801d0340f0a4070090700010030805c01c41d07814020249910300b404000c001038200303002c0c0b6002d000014000245200b990540408c544c21005010540d80d40d8001d503802c50f84082001e03214040c2100380f04401c0a4400c000041030300703540c0411110190b40c00036011008042c40c0c042004040d000c050450018440071a1011400070101e024465049005880001d52141d000c0e041c80715144d5030b04540010811880900b040d07082c0d000800c6400f10780c00c000143d44500945240c10001c0c49954070600c102440c0400054210f00702283c0d00340302d00722000544009103406000c3c0b0400500c00c41c0d00922280c05070120f004250f0099225 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982437850 1250 982436600 982436603
    0xc03100c020c0405100608060a030c1406040302060d09030f091a16080d1a060322020411070302071404113411040605120d050702180408130b040e04030c 67
    0x4448514440e48045001c40c0c50a8544174104003e02e0800e2001a8200800d65008042902c191a81600e15210010f0264183c080c1214401c7c400740c0405260b640c02003510090b5400070110356541e2540400d0391b0040ca04400c04901140240e0800405140940612000c480c641e200d2b8082c0d058040340c40261a5108595044840d4000c1a407d00490300c06000740034194016040007816681306140b1504a181d80c0d400a031140d1300400c104001e10040c2100400b41d0003030185410304081031480050701400c1d040200c0d048210001c030300f08040c5036002072003404450b134004c60303c944c10012005000584042c80480c40f8034203020466040c0130b0019180414110008001907521000304000014008010090a880301780701202d5080c4c1e9464584030b8400104021100e140320352011542041d240c960f1040d0810601401145082c20342d00d802c0c500e030020180228110f41d03546040d28008500350031141c2e5000750220400707400701c1c0c030580b0b0200701d40c00d8404600000701d1036565540d007190b901085010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982439100 1250 982437850 982437853
    0xc040b330f0403060f050402060712020a0b150a0b0c06010e0417030703020a0806040911040218060d20180d050a1703010512070b07110607050f060402120c03100c02 72
    0xa815845103000c40141c0351200d21815256581c52440c201481601d82d001c00c0d44050074a410144001681c1e040d003141d02c0d0075070026030781098030b01850f020789c1000400a170280000b82400204a03138044083e01001006404a40c00e0051940700d44201496000d0044c07122120340c040401400588440541e00f81d12610aa1000211840c0f8140410341d540082c2c80503000320b41c0114030707420055001802540e00420555040111500e161110f126249080c400c25004682c001066200180619045108000d0182480b6a00c01607007150900900c451115901528483c1501c41c49654480080340c081c116810786140c425154082000b081034080d0030122541d2140f0010400018004004803154004d08040207849601d41000c0c00200034003d04503c0e4185c00240c001d2200949c10402c0e20891b0742c2003007600711280840c4000c50903e104071040900248100303c0003000c00c0200017007035440303117100740c2d0300400b00d04c4034990060741c8481c500f2000c0c3e41a0041909041049803960180303061154510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982440350 1250 982439100 982439179
    0xc010f0515191e03060b010804030207031509020d0b060103050c07080a050d0b040f05160f091e05031b1806010c060b0f100c0b09071217070c12050c040b 67
    0x20b40b040000700386078801c5070350318103903c070030014400b840c82410890310007800c3c610842c3c901075900039180d030707514000204590f0800310b0401d140340d1a075004025060b80030b000300a9280150500c0320421100300c0701d0034002824080007910421089090b6103030164070021041c2050004a815107058120080d130750ba00b20f955454148195585005080f840d010138040014141010104c2c440da00461180c41d00a2050305034844003041e0748038580c0f01c111070358515030b94518a010500021800c5655005540c0f601c1500841c003080d481c400c00202029208031107141da121955507401c00442e008441040c04900165482d1020038450741080040c4080100707031380d07034107103c00c00010400d406020000c030015102e110740c0c00030006401100f44d007000d0604000e14005140be540c11011009011008082c200c0001d10b41e103ca49c615010f50701c4566010403001003c5032100341c441405041144162254807840b90ba1100c00e00701072040000e044409086080f600100c1e10035181e83e41704086085c6070044000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982441600 1250 982440350 982440359
    0x30a0c03021609020a1409010504061b0215030109060f0303050406180b0a020a060b0303070203070b0c0f030406031a1f0507022d01080f0c04060305040302100903050c010f051519 78
    0x4640000c3c1c40038690040e10788880030b10041c0041c005461100d00b41e24200a401c60700c3ea00141502d08541051825203082d140c0c0c000204080d0144120080d00204c50500341c8810b207042c4005541a54242001008a503a6a502414051a40e4030002c0c022800800050000303a100c0e13114401044a103440840c0141d680d000c00c901703103a000c5c10041c0d006820004107141008140c2c040c1c081b010341c2c00c600035400c0c071006400080e141d13107543c0700e07030140c000b000180290794210920005941d1202d400030781c2c0e02c880c2c0d11a00900607002e69001c0010440001c841c00080e403078000c000ca540ca813510350020f05201000c10080c0c900c0d51103606c2c02d907030288510b800104001600e0741092401660303121601c0000c0b940c08000341400d10301070001d250b43d5003640c0422040644d448140c1c0c048036000e10700440c0e1a115414240d040a150211624805040204a1003456004001801001d500e0f5000f0418242040414801c03200191502146e42c3c000401e92004d6107040c54088400081038a42c0b05d9405a55 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982442850 1250 982441600 982441633
    0xa0e07020a0c03030504050a060e10210f1505011d04020d020d02070525060c0209040311150f0c2d040b03010303091404050114120c061204050618030a0c0302 69
    0xc6900132000180001814001801c1c1005940c004140d18244030035040b4841000030f0b04040140040820400201030410743c101075442e0211084000704400c0180c216070024840240c60700140304082c2130b922110000f02540310380c0d400c10f43c3c00b540c080d8118800f129081000040e61013030042d013641503001e00c4180220800ea10040100300d1241c0e00a1070022401464074401d00804900141c072408007030b00401055070442c2009501950466411006599038a015241b48900b22099452442030320340314040e984148030041c0c040e00f107100401e00703299a009144111303440b43c1c044500040c01d49074201e20342e0802d801d00c0c44c01c042a804285074240790300d50801c1e0348a500709900a41c00100615020003038483c0b0785071004c3e106441518140820360518890349503c3d80041403450084c0c43e0bc9207041070804007480850b08069000340300e41d9842000c19019410000195015540c0f4051100410010700410580c542001c00d444040c5090140c1914252050084004180c055020702c400c0f0b085110b18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982444100 1250 982442850 982442873
    0x7020906270a050a0204030c14041104030f051c020712020301021209031c0209090609060307030c060e01020715090e04050316060603050607020604020108130206070f0807021005090a0e07020a 84
    0x241600311030780d0310344010300300e050f2580034207138038070340341c410441480410492017101d8190380042845c110324402d0140464010503604001c41d44503c004a00482045650040e403801c586c000c104490b015406084000b503402169040100035a014600400c403011125180d0314105000a0006003003400001104c1801a001c4912401c66040004c1425807030145507c5038401c4030b2030035021420500035102090600307a01034200da100341c07006c000003044d1740d9040090801841e032100e00e00c20b149903100e90280111220108590140c081c440c40842c2c00101d0203e090000c1001b0b90b1154000d506d040034002c2c04d4030014000342c42d0f1340800c0006450715080390300d8000c41507210f010005202c6255041850034550007626071411034024200307000c0542e2b400201e031030700192485110300d0b0b00000743c400102c0030b1080000042c4103482c500c4500060141e940050301e0a58003e8840700c00c85103040004507058407135842099805004100d050000d000300d840703680d6000b2850300440d00a000103071150807a555 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982445350 1250 982444100 982444159
    0x20f010e101b1a0702101103070507260306010909051003080901200610170d032d02040509090703080f31090f020906070609022101050601200307020906 67
    0x8501e0501a0300ca6041002802007280c401c0c2c100031100700c241f00440540300103010401002004540801404582056048030803a01c0d902071042d4160390400c812160411660640480c0e54410005291445805000c0c0b02d40c180904511000741035039500100c2da004954101e040104001c400c8076000054800412001c803800c0007051541b401c2901500d0300c5040c0d403c6164040d4400610300e030f100e8000a198180c000250a01144c0b2550316003941060701070614016402d26003001c2505400c02103540200207440b001d50388450300b65184202991340d03058070310001303102030010820308010010340405000076031414500d50307a542418210341240c0001105a40742c0c103030f8000a08101c1101c03980305d01d041d0817820400660419a51600217001d50182990252145844484100465840d1860581d00c0264041a000c1e0070060a10040c020402140d1942c0400d500c18603c5404c040840c40c1c2c00381a206240055251101d15070034441c80d00710162406800c000c0ba00743e610304424114040c0c16290 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982446600 1250 982445350 982445393
    0x1e090702011b1106041202030d11130e040515040f1403031e2a0f1c0f02040e04121202030910060f03170a0c02030102070c03020f010e101b 61
    0x5180c0c0c06900c00705400940481083c018145001c40710f114011608a9200e600051501561903040600f42d0039072064904184204d4a008100c1c001034009802500d1102c824103a00c62003541c03602e00d5090b5201c01a540505140e103c200021000c013884854290701c07030700c00d0354201003010150b07039680058000044281155000481000500c9000741c100b00f2491041c0110342c0f40f542004661201d200c030680002d0410100b030142c0c020600391040701191590011111116580c82165810480499801c80e0710b111050405244010811060082e1401d071140109480c0e02c82e2a99520100156821402d00090004152410107034082a1015520915591014080c140200c3c04003104a0300140c009000c83c0844032424000305014035018134400200b50b0005a40d401d4481d0255403090881c10001d5156000144800c10001a00102c02c116032003913030010021004a4015641042c4269000c0c2e04621041004400b0a202d020001e031300781c1d14003a10203105080c6454841e49070058410941c8807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982447850 1250 982446600 982446611
    0x3100f12060e0d09050103020a090f0312020708030a0e040e0f010903050315060c0a1416450f1112010e1e0f0408190e10020c090103021e09070201 64
    0x1030003807a0141d80314a51940c0e0103015545090480642452014012107040581c0428001d06642c0614618006040208140880c09a6906d04042e200d1140080c0400600070740e00005111a800029242c200340e050311044012101002804000e00110b030313588546125184541c030301440c0a105100019000e170f514035a4070700d020041c03d102041b02d9140301c1c0c00703208100301d00715403505d0108115074000d42c05001c0c04030550400300d00c00e00e02913441c00c0030361100d9111000040c1008117903000c503282a6105020b4103502c07407145805540600c184405001300c45844001d50aa250954401a00400c0d04840046d106d4201050200541c2125034041c41c004140c90052140c1406080042d0b03100c460108100a00600c11098040e03c8002401075001507100c030020904010f0301805071603500da07841145a641e40110300700200080340c040b100c98010392a441d03d40784594404079102003c00340c040e002503a56440c0d0342c01e0064590180c4404021280f00038807680c103d41e65801d00502480c03030b660000c00c1d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982449100 1250 982447850 982447853
    0x2060402011404030b0f15030f0c03060106080702210c01090c1a0901050409020f09181f080a170d1506020c09060f010c0317010801061703031b03100f12 67
    0x140c24810307840c1c1c2e601034014402040002c0c0d0010100350300982c009507506054982c1c0d4401c3c90944a03c03290b941e0b060090005041004100041c0802259401c034112804c0c0e1b680e4000030b840230b000588040300180c100361501c0c2080c0d4100342085e0014810290818640300b0f4101742582107d02d0740c2e804946800300c02c402049010f004142003900e541c034201e81586850003e600203007092080c1d10518201039004181030100300350741c1d01600c4910501410222441c41203480162103290100c801c08403640301e4031320b4540c4800d0f19a140c40301f40c5050000914118a107901da00c1c3c80c0c1480700790303054950750040100c01151810340c040c0c090743d01c0341c902d01400f0050070500f01a062080c442849801445404100301117039491002c4500f5000c1f013030a044020034641c2c10304855403001d6014101d030354500180001817600d0150310803401c440b091000080011200b5940a44030b11003030b682c04451100c640c190f505901c0c9120021600700004502c00b407900fa9460a41100041da41c0c2d01142220002100520 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982450350 1250 982449100 982449107
    0x40317040818011713170301080601120f080406050d0f0c0203090609040e0304030b0915060a0902250503030a0c080402030a030806060d05010303020718020c07060e040b0405090f1213052e0206040201 87
    0xc2d211b40858204034110743c10441101d650f82814480c10403103400d87c0600d0002e000002c3c000c4c0403166008001a43c0d15926a00c000e41260701903403103108164034000341400600d2103441090400702d0743d5030281d864810500108082c03078004043d4543d05c150740348017801e40590100000c01c000c0d403082a1074117a5103850000700d4103040800c40750408000318071b8104010b603914010741500780d035207043d4010307250b408805011229a840024880c190540664911301384540000030310b100361912042401806030046080f11290000e890080d0594409420b80000034014a030311030303001d40081d0200f4284410f18120106941c0c081c4d106a02581016105000d0301510541400700d01142c00c0096160507141400c6503540d03840341c0b06480410005d8901c15490740d48680051401400c0103000780210704190100030344030054a50030006611818000d60099101c1d0350540e1894a2020401c20f01c0625090a001266141c1803940c407041001d400a0810200c5101072580000c0c640c1d802050705203454400507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982451600 1250 982450350 982450373
    0x240f1b0c0a0e010609180209060c0705120c0d06270602040e06090112060c031d0c09070c0b04150b0a0e070908061605070804050315040317040818011713 67
    0x341e02d1404000e0042c030845401c294983c00701c070000c1e160a0b003001499140800280640780170268468070019001704044d8001a8200a0391011249004480d000b1104295150340480c0f8843c2c022206900c0e1101240e601d5120404a4a0080849584035860401c00f01c00212540b01103034410b0f4041760074414042c0d40c45c14203600000a0b04c054846506140702d481d09141c0c085401021143c64480b200082403190f000240c41c690302c6804460854191090b49489080626486006942880000b40ca440c4070300071b5001220340050b0110b01d60703200c0d0344032614091481410100040e4440c1803121072364031030412000040050314600c038070905150000404900059116445550101050001600c1007160020303040b001ca0600715900c0b500c9140c0780119019540c09540c0c140140441889149441c204d0503100318800d540d410610ba041d00404400c465060764041d000c0c0b01c0030700c0032008031800e1508050821005042c108648440b85190031106242210b200404100d10b280c020700f00249203408 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982452850 1250 982451600 982451609
    0xa260a080a050c03190c0e06030c0a020c0a2108220311041b0e15040803040501081303020316060b0306090d2d080403201605240f1b0c0a 60
    0x43c80c3c0b850810400c10303015451810f130800145591409404801400741205503800d44000c1c00054407031900001d0816950080d510840160040400300b51039840c040c10008146d80e070300078260700c400d04094a00360084040380d208840c42c11041110002e0003201825040800042c0c00301115018203600d456807032000000301103401a03007890f00c40384074031013800001d501209140c80d14000301002800000e0280204150707540c41c0000001300811807031008401881074910a881d40c2000fa1260218401c82014035100600140c10901c0354902d0f41c40f80d14040c0340c2880c000c04010809052041c001fa00b0305600f03a440c0d841c0c0754480056621940e4000c0c00d071603602208000b024000315880f14006202203100c40b481402c1104880000341058042c420201200300c3d900c2000a0300984031641c2a518440604140c00b480300c4084000341034900b44200407074104040c030b00c5604d44812001d00c50000e400c10001ca10301604140180740300003a0074000002035521640c000e00290480030140142d20185820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982454100 1250 982452850 982452871
    0xf060302130b0306030a0f120f020a030f032d0c030b0609091603020f0703030c17010803120601020c03190b100303080106080705040f0b09090f090a260a080a05 70
    0x1000e4200c103601e108040403181030304400c80ea41d9498800107418000c410100500c814640f41184007800b21220040d007000a0035143e1100711412071400783e9540c03940365001800100e031143c220403003034443d170401a0307210000c06920545140d100c035019800c41c0050009051180d58982d82982941e0501900c040070030103030390003440d000141c03000c60300c9644000c09480c0c0d014507403440030008a10076411540e009402051494840b821403074000e0180c210315403500d00003250007505000c000e410342c090604031a030f000000d5240c481409600c104461005012605500641101c89040c2c0c03020f1082c00e841c4ca00440401030302103028902048011406042440c0d820b01c0342c0300a0000940140f191810f40c0c0c4e481c00c0003051645c81c1c40c011a25849150420000311410707900004029000c4000740800c958100d0319105140e44c2d12007a1140d0380b604445d001c3d003a0b03001e00031b4140855440b000042c40c69800e510903000c68a8a10314205e5182d00c008507200c00a100d42e02002004003035845119002180a40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982455350 1250 982454100 982454107
    0xf02010902102c0d0611041a041d0f01060c11061305150922060b0f040611010504020f130615080117061b0327010b1206100e041b03050102040f060302 66
    0xf0041000c0f4040c0200003805160740b407240602c80300059060301e005040400300c10f11a00384900c001d0b1241d030000d10604405240c00b245400e0984d01c8024420303c14011802080b030940e113051400c03545510520800e943c0d0b448004594240ca45608006100000d40300b01c6c4401602d240500703102c110060b8400f03502080e17106101c0c03100c00d96141c0c10004207441c4a550304c003c80c29480c008440080840f50300070b0480c404001841c006140491015000b1101c407520b6080d03580300b03484003440c2601c3c005c88000390702051888203681035140c00559022a880d840100140d01c5894685a51a01030210641c601155801004004004450180301c040ca08a2800b83c940c03801c0005104580d2985207440d01c840c0400400010354500304d00f51060300c4820241d98448401c00e0700c207051030080c0400040207001d8208990050488100080c2e0a801080a54108501280380c905810100d10018004075140c0e4140140d41410003013544203a005540500300059880d860400e402200c107803681d010b14181030060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982456600 1250 982455350 982455437
    0x1a1806031e070801020c010b011409093c04050c1023070b10030c0f03110d02040b0a0308130603060b0a21060e1006030209060a0f0201090210 62
    0x204042142050140300001d1882a42440c5810008290401045580301007041000690150820200c9600070b80390300d1080800c04804c801e4510580c500107800c6140e07000864402d070005180e501c40c48455484410802c0c42c80114205030070151200e820301500d08030305200a0040501c21030710184d000300d481184101e0301c400b028021a01201100d00000d80c9100c162041310a05012140d0f4542d0100c01e0442514002c503411200d207546000131354825145510100b4002c1540c1104810390760880168165034a5540401421801c14907040780c00c40d886805082254880030300d82006140305004107034550781d440c003451206840591104040ad1309002040203a07c0002d0111014490103143c041c000c5900b0a21031220740d81010300143c000b905d842400605080e42a04803800dc4400968041304a5a2000101d040c0e0250000865001508001d034000050046c0070180000700e0500011500d4003054001030200c6491504040c0496440850183e1600c2d29004065031b16099041c04070302c101c940c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982457850 1250 982456600 982456603
    0x190c03050f0640120e0a08070b2a0703050d02281a130201091e0b0d09080703050304020f01110303180709090302030405330307121a180603 61
    0x1204152400403040c58850b600380b00050b000e0741441840c10800044400c07603450310032001030700c01d4203130300020b250795903001c0b001e240920040c000c80700b0400081c4220360502003115196072082c10740b0404041c060026074600c80c110200f40035030f420004042e095651947c213001c1d003054041100082150403041c9410b80c050034100c01600d06a8a032092414059802c0c80d001e511000c82070041503101d0180360801c040409405101225a803003a40e80740a00d07507072200804490100d1480310840307650341840c2400301c01c44503005010240540304002c200a42c503611140e01c1c6a11a403070070f400040300001004250b05040722100c2c0c10300002c0c60b100280d1070b108800c440c0c80c0d001c05040c801a1107a00801c0071018013040069801074480c0f650100480c4500b0318001c2c4d47c0b5441071041034018150b400949040a40c00040d000c80d450752141001d2160702600543c80c2e19030300003000c07107090003d040140c840d5040d040c0304809200c0e010100d8425943c0b000003c000201d040701407010b0801030900c040050300e0700c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982459100 1250 982457850 982457881
    0x10603060f12140f06150301090b060402030c13030c0905150a0b032e03060c080906150a031a1b0c1902030f2415030c12190c03050f06 59
    0x50340c079402c4540600d2405880d1801d1034003404605204030801c00356103800220701d103402119441030001911200d0410300d400e07140030500c0a040718410030005511810076400456014282c0c201c42403404114207598055400300b600b06a07140c442002c400d00000246210b540c0e045071010500300400041c2000082d680002801001e01e074100100100300101903511000c102c1401201c004440d6000f000d220342000d40c1c16101c2512441d00b8550b800c40d1f06400f4100903402581310348054159030341c40c6400144407141c429442c41e00205880c400202180202d420710031098030600b804149404c5c078500d00d4540510b10340311780500300030400040361480e0000506240c00d0b5a51701c00100480d00600001b41001e110142c0144103000303140e500d60b0b464440340c2210110b203640340035140150300c8141540840210503041c0d150503074400441c0f80c3d41842e10a036504c0480354540f0840d040c81143c2144a10400f22161040706c440c0e0300c007181402008803e00902414000c480014440c03860101c031150408030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982460350 1250 982459100 982459109
    0x605150a03051f060f080c03190308011422021306050309030706050a02040905180124051e0a060507030305091203040b070e030a0803250207140402091203040e010603060f 75
    0x404004815026194513003181005240f40034864408580d0f804500e601c44034003001c0981f0a029003008050340c02080306003041d101c1c1e01aa83d24030035a0a0441e20245207407042d09150303112003100c200c8140c11003542201442c00740d101c2c40140c1c9618201c001c502c0b4160080c5c200300113000d0309200304000d40e4800010b494003141c01480205e025101c18020ba002803182e81c000040860802c81001100028051503000026580001f00614041e038582040b41d61045201541a00ca0f001c10803c034501d0500d40d561103070641c0580d91048080d00d9400150884030f41c1e072280020034800315074030040c96090300c0303250ba0040c2c244d0054110541c2000300000207100040004040c111035a001c250010700c50b6091040d0400b005d81250b415841508104100350012200c440042418041036010030340e03440300184035052680c00500c040343c14111000004ea80e00d144d0340d504242c0c24030908c0c040341d803450340c40440f00400340d0140d6591810640303031254125050700500b00745030400c001000030040360300c489000c5a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 982461600 1250 982460350 982460383
    0x1a030703030e0f0f0306070c03140f04030f02030c030d0f030f1802010302070c092a0e09040b09120d1b0f090501030c0c080d05370b01050708070605150a0305 69
    0x21824800051900d03e901130a0580620401c0d0402000c241c00c281b44c1d40d0014080d071120000c07286d184038460144d10480c0d80300b1a03403480502080000691845d140c503003562008042d10310791a060000f103444c02055040680014240304001c03604030790917100b1021a1518100184040d44580340750504400310854024100b680c006480424043e80d80c600c0c5004e000b08050901201c1180f0f1a54250014110440b8200b400311056041035a802001c0082030b101010304894296601c5032510710a8680040c0824943d014802060000380d54110003400514403091002802045802180981c481a865448240508030a03110005600844034000700caa00740b0340031807484035110341165410b21402c001042c0301c5001c64031306807410a580001b8414803011401c5040004040e001401c680076403138489031014010134800c0c510701400e070043c4090300d4040c10801c1c901030700c9551711303a01c590050605a0780280d40f84240b040c41200ca1040c100c100400712110b0701c006045445d01512540ca11004843e01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 982462850 1250 982461600 982461619
    0x3061303021f091205090904020f13020a17060a050603130501020d0509031c02160f060207140a06050609061018080d090515030405120315040207061a030703030e 71
    0x2003510802c10034075a2001a259031041c68010728600300a001d0400b41159000f59407114040c004d03100b4400d9800282c0001c203504407544558082c0181035848003a40c68120526000450700d581d040d000134241d43d609691041080d0344903000417090850b028085911500000f101008503030b45900c113407a0014034880d80420301410034030f840c03070091060040c02d003c12428401001504080807010b0051500070f80d03606d260060001c50b05000f24030905095804504a01e15081d02040d06100400c510f00c2c031a040c01031030605a03484850607228540d0800744190b20961640c0308000340c40c081c20703400601c1070320070699600308000000c3d03560070b5241c181c00400000045403405443d10307510030002485808203441604009079002080d00c0343c00d005850098078948200e4404840b0102202c0c0300c0c94001c005051442c5603a40c4841841c4d1000d03102c2c100484089902c084517560f240300801c60903204000024540c1d840202265030014a4070b103840c425040414200003003504030304081c00000d41181e41010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 982464100 1250 982462850 982462853
    0xa0b010c02010f0309170304150b10050d0605030a0615081c11010b0904140c010e0f06070305040b03090606010e0409020f12070b07110f100e010311090303070f0212070302030613 78
    0x400d000c3e40d02804400300c0b1b0b9107000305151290021406207004810b500c00e2a4811001042910907202e8116000307101410b0b00c840c41131041001d00360f0f0f544200c0d00424440d0b50b5500082c500b460445090390069550070a19501e520038050000040441030f020317000400c00c02112102d00f03400d001c1e140701070041c038840c608500e84080d401042c4001008007003104d14100703400e18000b54520524484003a116402c40e0070700546c0500c120300a2300f02c00910038804001000700740300207508a020103c007848420300005c00d000c080400603600c250080c40040800d8500319000601c41c01d06a54603a000743c4c5003410160150b00c560400707101d003003010340e10301c1d405d92040303c95103151010950100c036482002045400800c90344200880b204003040f12342c0d40b45200c3e19003c00071038402060b80000401e4480504a0a6500a401c544410904410824142603085000c039003141d01000044800f038400714408011460324184048181c0d00403001001c2d000d01f15400b09940d41c202500103402d45c20071004500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 982465350 1250 982464100 982464107
    0xb0405100206070512100518043f050c0316030201060b03060f0909030f0c01021b1c2706030207051006080a030e15041d28020a031415090a0b010c02010f 67
    0x40101f00c0a0094003040408402ca0303001140155001c94041d030f11004800380e45a191800384401c0751801c00c5503032000c0140701003906050007108001d0140030081c00280c2003c00c06101918481030000b0755060b011902d460000d00b103842581040000303200a000b8410711351501d00e4160340d0607605a500e001103440307042802c0e10710301540140b02d214001c00114103002ca50190060300300d0b1145411710b5038404c69031070b0030140c8803404071044500c062900b00700080818414801042200c00c15401d107002d2058034aa110341c0103610750070820210f0340010300103080110811210071407141e0b0f03040400907135050034003040d21001d03088005010010703103240111099a540049928000301140c80039601d940c0c030400b81c2e40c00d000e440001c00075101c0180005900d403001d176000280c2041d0142840c01150807011050300290007010b004000c055407140c0400500c003000354181d00400c56140300e10216007891080165040d80282843c01d12420591034058607600400c1a600442d03090801902002c44090200c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 982466600 1250 982465350 982465381
    0x2070b0d1503021513050301060b07021306031a150108071b080919030b0108010216020108090309030a2103140a050721061401021908090a0e010b0405100206070512 72
    0x196102d070044200141394010078006002440c656010f20b2030555480c2c040601b00e070b10512803040b01c41020003d4000601d8101011a0841c5003c2e400168058036034690152000c2c1b03404891026501610a04c0340007055454501d10340c0380c091910651a18004000402480303403007189148064031f00f03426804000c550340940380e040354080d2444004004005050009000d00d01c415142d100f01c080c00407070702c0d030410300031182800300c00103205105030300d03607030046603030b220020310100b034500081c080a44240d60600000c61401d00401e86440300444001c1da904044031031042e01c50034549403000c0c60000c200120b68003a405003102d800010959260b25041d1a40100007042e00030f2003984c80c1c0d003541083c07115400a8190741d452811518004201001640e03502d4442400441c2103402c20700b03640c00510203900400b0b9588014002c50106503441c1f1091003860001c0c0c00854a0b20000f25092044d424103004840c01070110348010501d604000c480a8018400d000801c00c4503d0054005429451400c040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 982467850 1250 982466600 982466603
    0x1a22020c10090b072610091409010c050703081f0503070e0106090b03060f1e030a03020c1305100e060d0206160c050402040521161e0602070b0d1503 65
    0x103035003414070315003100002003201070b100322400d003402d90105426900c6844465429480e0780444402170345500c0009080040080c00e24006215034880411036224078001d007104032001c094450440d040c10b04a1a0035100100c400c02c0420000b0711101c008240c2c0041265000300c00200764000c811401c81041d913005a198000a030548200040040c0344088501480d04952144d80d40503116901d6040c100600d1105851140d0b000381581205d962a20301410040740e900d040780700c5955100900404a81060b0040c102a005600039000c07e60390703400c203070403920302455807e1020081c506d02400f04400340c00050251303200c40805140040c010740c131110180b840268006103c0c0b920b8154201d1406080c0c10400001c451354416600002a90b0070117001f96003d98000501602d03000c80682040c11072515035000e40310951141c0340d5801880d440f0425420090300201c140b4100c803400002c00c1e0b005000c1c50360700031421076208007010040802488141c9103610492030b4003080100c6846100c1d200700e40184c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 982469100 1250 982467850 982467853
    0x120b0a031205040305010c1404030b191d0106080604020307030b13230f1203010605090105090d05010905151b0f0d06060801230607030c020d0b07080a1a22020c 70
    0x4a1401e0aa0028042c200b1a0310a80c000e01c500d5510703950407075007642c01115a81d0781700701c1072100f40b00161000d40c042d41d0294200c420504004c607044a12025219501d100d08030442c04403510700c81c65002030003a003001d02250ba000701040c1c2050360104c5c2d036a4602d07110244c0541c001401050f020500d072002c2900a41d0842c0407100c6490a00314400007800c9040b011901500c42e0145400040402107030300d6400c10149582282581c1c41e115050b19039501039444141049810003642245a441c0e021a503403176405603000081c0040e140c82c0c12450200c3d82c030111501039032400100490516080b051501c060b680f0303030380a52500101228003030b20b030182000403500da9061560204500e0b0380643c00604a88040356a01c180c0e8420341c01554400d060003528036000f940801203140464080d80d98a05075510250a10024442945540d8003c11054881c4400900c10800b03000c000c9495000c0c022520200c1e203100040c507194a400a0100d6004002c820b02c2d1441d00c4011194615070b42e0b040d60716240f900d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 982470350 1250 982469100 982469123
    0x3081209100c050d060e070c081606020c01090c0b03010308190c021002060405100213050906030705120d091d0a0e010216050a0212030f0d020705120d0509010f020a120b0a03 76
    0x301c024083c0c0c0c0094103220f044915010002030107003000240940244083d45903020303404400c2e02c903a0b075240e0040d001c1c010b0717441446d945070001136420310060480081c8580001403000541c03030129001d01c01c030340c860707d4246401e00060000c2000c180459120b561041642d620ec806170318401e0311581410003000c2d40c483d0600008500007600030504501c00c9100700c0c2900c0700c000ca2445848200d0003000600d200380740030030800344140d090103c030094001d4801400c0780d80082c0c0d24000983c0c40c0706041c0309402c00d074010066603980d0030380000140000d40701d82002808a0100b0406030ba410020040c940880c1a8590040f0f80b03041000703504650035a8009070403801c2c0c0704058288595501c40343e5100301c2c0a00703010046043c020202100351a061025041e0052400d09685001c10103500010025a958062000714a180c07111040080c4140116105c000c580c03860150142c81c00c541c928654000d240b03004102c0d40420310760103148055500342120000400106e108045a1403c0117034000814050414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 982471600 1250 982470350 982470371
    0x30a06050904051b031c11030d090c290901120906060b0c060c0405180a0f0203270c03060c0d0914031c140a020a120516030b0a0308120910 61
    0xf042c0c0340138034465126401e0300542c0c20800c1c190703503581c0c1400d800303040510300078070f404218801c0300d2580c1d4180d03419003100d00701191010040304071112401e080740c9a000c50501000080075040460710712420f030f1001d44130a01030402d00400d00380f2070003e00c02d04119006504003242040c83e84644034080d049902003184c16200c551602c1c8540c0070005041a81c8241c40c00030360011110743c100d030196840500007546400400c21130f040c90480c06801c8403166921b4001c002000009840510310601c151078510041c0c04010540b85d02c48080c0602150071a007104c41c55105640380029480c0c0c11803440c0c102180d41302903801d100c1006083c45076000746048800703402e41d100900c00201070901d40c4109001c03422140007a402c1c05048034000c440742c1d00c10354100c50008002e415182c0c00340582801a041030001100e0700440c43e8221801118034020858aa003099150158944110740720146c00b580d10450300c03815621540b00e54050403031140401c600810000d04622000d02003004080c4010000b880409580c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 982472850 1250 982471600 982471603
    0xf0e062701050f0619210f0617030c070e060303040e010e040c21030309060209120601090509010b130b011e030501030204110301181a0d050114100303090b030a0605090405 75
    0x207102c0c05120304030001404010b031802c50708840101c00c00700380a800d17006480e241034444c01c4028241d92000d008103410030844045900400c072154042d07810004e206410040c40600e4202c08404469a030340c401d1003c148511000101d46040c1c0e0140c040e8103850b0b17170351400002d107107125075000300c04108216400050203907034140c2420700503803244071005021615490240d4841c2800440c0816a0030849803030408280658007510380c45000705000762500000c0b5003c01d4202c500c08640400590010004103c402d842d4883c0311781100f5000000d00502c00402c001039061001031081d0750241c5e40d514400c4026a0150030704422601004000c02c0d0001c03d200320207001010240300c2070740600d09000d18112054841c4046a041c1e9a40188011185020075550b00052400d808080ba620f0150101078801d40d4510010088042c0328000104811101800440b80d015019250607482503240034184000b80c1c00c010f085040d40c070800c43c0c1071b440355187c079808406091745034010b81e000000c42040c003003407000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 982474100 1250 982472850 982472929
    0x20c2e020105160c0312110918060103050a0c1403060d05070b04030303180b0705090a211b0e010608090111070c0303020d0c0c090b040207081b0706090f0e06 69
    0x2203a612010701d01403d104280d030480345015008001a40c2162200100004e0364042044040c2a4952034180102400801c040c00c501034801d00750b80030b403078080001541e8907006a944c822141c0c01d0502c03580d0042030003c0c014203602c00072507212442c0400011015218000300c60000d41c2c125040790000c60f6580403040c5698010f0105600080c10035008010581c0041804c0c4803055008602d601c80b0b03920403070110b415070400000f46602020403640003507003040382d0380f20b0081d03000080c80700c0880c1d02692038980030340005e10303180000e040c01d181e00402170214002212030448940e400e00320385aa50b40c00085006000c255510040c8040200300c5405111104c0170100a492181d02103030204d00d1880010740b81c40650503401400c0c00d00314407040c01240100e0300560010140508050306000c03840c0d417250403540000c11001140342d685501c502c01d01c801044903038000e2641e800c00310b1a00341052003400c80030800d03000d245001e00c40d6501092240e10b81042c4400c1b012454140d1403086100700750369000f000c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 982475350 1250 982474100 982474111
    0x9110d111e090a020a0504050f040f05011401030608010e03190c1a102112031509090b010b03090606012d0201060e090f0a14011d0c0916020c2e020105 66
    0x4080e40020391010952003110b400200329141c0c28149440c020400448100c49c2e4911b40e001a00e81100110001c1035005850180c00d0032a21001c0440c005e8000500300c400351340c4050301503810103110942c00503000c01103c0586051114404040c01d41100a464801d1094802048400051010030400360f14500c2c0c075008840391070b0a5007555070b403280c0300440200c50b501139214002c1c1e98a141d10001e0145108036111071068280030810300760381c041420040010350700001e8029151040d0104006c01980c0b8180586507103c2d01a0a50a01002550343d4840007003490703040c44124041142150000340341040c8032400d8010884610300c103400c2c0203000e8038851081582940c0e01c2408070f44075000208213001709549000003020b00343c5071504e03410034418660100ca4219581d961110004440d8805100708040f81400201481007a07902071000c2500010100e5181e400303080085280c1b82d038080354010800504980201d0300441c0444110940c0b1004c2500c03038403031034003484501d138400d4041d0802032044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 982476600 1250 982475350 982475359
    0x120112081e0c010b090f0f0907170f010b030102120103140715050c07060e10080c0d020301031a0c0406140d0f0e0708010515060f030705090a030f0204050a09110d111e 73
    0x26034200240019a8000d61b2503024075101000010500e01c5c2840386250710a8560046400c4540d4a07505000c0c10021040003c840ba001085200c0f281c107024058145414402e500851400224000744040c901d0706003c0285030f906401d40c8114405c2c030401940300500400301000008106811380608550f002ca11a42c42c14001d07140c0001d1888e00a40210b00c00c2e000241081c0c03031102a101003124103c20080c0b03220040ba4090045011214aa201640c0030f144568298103041d070607503000aa0008000300040c00b00e040030407003400314541c0014164036400c90501080d0311500600344200c050b281d224146a5814685141100807210008031842200d905070001c011607103c2100b80fa0154048035906500030302d00f00001800b081b00200250752228a40c03902a0401041600140c19007203654402ea07450441c010030307002949007500c0b806811805103031081001da0040e685403200c01c0381a03440203100c2e15444000c501030003000101a000848000c01040c1501d00140205550b06481080113006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 982477850 1250 982476600 982476611
    0xb03100b04200f0702130e0703050f0304050f120a06090305181203090603041a090d0f030c02120a1403180c09070503060d0804080a0c05030111120112081e0c01 70
    0xc580a8500260b011203018001900e440450401600b4030303070004000f01d0700010340050306843d01c0f40502c104158400106d000d40f4000745035003400741c98489034031160000c540080008100ea0360f58280d000300603540541b14014528401929a400c003508204040c11140c14140d4010130150b0000c01000140c1000006148032065036040c0a0000d10000060703203198000c001001d000c5ca0050702840c2e001d44039186500030600c4847d8110980002079071001402c0d8408181d00610395041000381401090a01d07081102a0030340d14001d40c1c4208551100e4003040000440254443c860b250003140220341b809031540d40d0602000407812090007010050050251041440d00b514000c075000c2d008400960780c940c116150001081a23140b401301c82200c003410b04010010f203004043c440100300d86d01400065000d18a048141030949108414500000c04104461030362a202c1c0030351241943d005240d9106a00398a2038030164610a0800011202450300a48c40000a01c1001000010001c000074060b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 982479100 1250 982477850 982477871
    0xc0606081c0f051303141609021c050702030d0f0605060f0409050c04180b061207020303060f100c060203060d0219030501180818040f0c2604120807030b03100b04 71
    0x229030256044d00f05140000310b40c108081003042000c0c80d065807502c8183c844112113000e445158210395440070300c04c9600840d5010b4010820f801c52102900e140406005034500071100035224400c001c0901211580c0b600080c090751410750051015120160000c1c1e592114103041d031210344c01520410701c3c89818680060710203401203007643c04540501a03942010000e01030002c02402c0c1c0341ca20280c100405000c108054282c10a105018540c0c0380c002d565241405030500c010004100002402515500d8854450719400305590480a80100d00103031282c0718440081d4143c920450f019500901c5e84030110f041d2500020240c046034070800c000c03c4403203002c160b4a58071411104000e050024240802403000441c0426400403a000500000d4000c642180030b00444006d44030b4500010440b0400309082c40c4a811140c450015803041c501080c0360613560100000d00396021902001850004203003114003d41000489007030040075540c0052141460384001d00c0101c0781c8611445c100f003a0040e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 982480350 1250 982479100 982479107
    0x4121a180f010608031c0b060f1b0f12090a08150f07031b0c110a031b05060f0a0e01110601030b07030513020d06050c07020411090306060901060e010c0606081c0f 71
    0x1141e0020005d0341c00e16020703070b00c0d644010340400364000f070340e070703151944841d05a440c480107000c152880c41000740c070780c4c04c0b03417001055000c036018240900341e10061210710081e10000e81c4040b0800270b41b64455840340070a0114813680400e90000544c1c0c424111a00300a050200c17400d03214011410144c4025500c40c0003c034265101c101e10040200c44800c00d041c82e840c4649007070b500d000d000e030b005466940d80e044046904041594019601c00c082245c4060300c03000060401401403000321086420b0814841002c560303481b494003214203118442c03e140e0f185034025681e481e40400442c0a0703c035290b80d071b4101540400001c80700c800002c0d2902000442100d4000c00e11114190054018200e210085e903801d4000d00c40a840c207012080103004100040e40c0b580640ca910402075402075442e0b6003035206152816001401092080360941c005024840d070000030468040001d20703011011075083e04144000700036640054009010342000140888a5540da0000d03101250340c134040074a2a18000b02c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 982481600 1250 982480350 982480361
    0xe030904092306040c290307210204210f14012703050a080903161a010b0403020913060906092405070207051e040203010f0618030804121a180f01 64
    0x2012400795080502068071031180d0340b207007807407544000c826110b0554840c3c001c1f9081268420300040440381c6804510842e110300c00b8a5089124040d82054141070070188007001c24082e0b50550501e40c05410248805680c1c0c605034190040802c0c81c07480e401c404c105001c4e1401c0141d00344613285400c94003202c00c62414070140b215405549203400c04c00c0e0030f8021503003540040d003032184900c420f01c20440900031440e5a8041c142c0301d442d100c0402e1304201580300d0288016482590040810702c01003001d41c5803c0000340d40104201d44201843c0c0035031501400030400941c0184c980c500e0710107450200a212461980e1004090504141c0300d41103440c036005490003181c200005801c000003c11190803c086e012510755840540c4021912034280460100d800c05d13400850f46000e202070410034181c1122a80082e1450b50000c03003102800c4d41c03681d007090b10642c4039140301c8003d00200041807011454803c0c1e441c3c4400220300700c80f824289060100c034840d402c90b40c0c125000700c1d80b094007a020144190b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 982482850 1250 982481600 982481603
    0x1808120f0c0901081032120d18091418010c02030d1806050a020322050c01050d150e01150903020d0201081e01060914010813060e03090409230604 64
    0x42807414910000440c0c041c4e2000e4102d0880140c1c4140204950305041036407103841e40c0000003043e07040d61103041e00301d9130307089428900c1c018441400009407503000443d600d036010865007030051603011242c0e03021180c8022030f030045080ca4070703001c20a66280c07444001940950102c000c007440001d26001e00e14203c81c0e964410401507841000046600700305500402402c1d416110352420140786500c1f01e00c01c0d24000c0b034200f6013540d8004204662110b01d0480070700300480103413190304581400c0c0d41c4d031543c407000c4600540c107000300031541407161030040c0c00141750065540d1480d0000f0795940d104e03100b8410300303010f880f404041501071141c07868031035007810080325001003605100820719001900c210306c2c080c101ca43c0c01c140c00264050058001d150607030080c4020f43d550b0181c83d10300f0503601c1740101c5041c2c0705810421150141f188039400946c940c5a1181c000b40c0010b606000385040c03c0c61403045111007a0810304200322501402550400001a00c410410034080806524170642d00c41100701d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 982484100 1250 982482850 982482871
    0x20a1505060f0f01091e05030f0304350f07050109170712020102030c0a05060f1b0a0f1809020403021504060f1d090108100c0801080a1103011808120f 66
    0x104081903d0441514510500181081c03000152101409031240c4601d44411141d004165800c1100b402c0400042046445407000786007403604000128100c422101c40f080c0c41c1040d030300030030360841c01e440b0038a0b101516210110f40c0c6074100012745507103986186c030a440c04155120000144803101c445401c89000c02e00d000b030100340342000000c0391521070441c03080e4110320040c800240a540700b0008811424080c40007400140ba241b00013032003000c00113000411003000c010314800840703052000c2c2c07001c032041401c00714201000da481c03c40e00070805240140640d881c60300b001520341c1c1170b60700900c1500d00940f090b42c44400c02c0c900452051142e40b00b40c2e800660407540039580c0a00c60b8072240d0452f0901c0b1020703060340d0b0301d40e000208141c1c0e080c2c102100d6a08050301c3c00303009010520a0310090899030416214a41c0b401c0685038507101400b50203000b20402d440d51400a40e02036100101c3c01980b255400d03480203841c1081c4210341c00010703002801c0c9c036030301020070300946010307100920405a030752 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 982485350 1250 982484100 982484119
    0xc03090904151113210b090a060203190605030705060f0a090b0d0f15050f1908010510180603020d1713030b190506060409150e0106020a150506 63
    0x910000c40001401658250411108003045030043d020303030102d05850f90503050b291303641c81c40b4191507520381d90700041030103181d0311000c0c02c485801140840c4e19904148004a990f0310820b4490904c421101c0040c820b03403000081110190004102c40350030b0614820401c40c850700c5206165070794060f070040d258807003c11f0003007011000b480c00080501e828280f6048482c55581c0ba00100369070044040c20304040c7d200c0421a2800d29140701d102c261380251501a4540c525090200c1c0d880007082035040c1c090115007511140080090040754000d201910003004685840e140b00c41040b801c42c0541108003d100701c1d01352040c0340602506060b2a002008007007110788030340d070300c0a44c41c1c94250011124102400001ca405041403a020700450082120441c5450035010350341b002d003103c5001c0c2001c0351038902413220725100c5005884c1a503e20100000703100000c02810140506940c0c001e800152070240085443c0e580450603141043c41b4000131200900b003013003503106a80045480640104510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 982486600 1250 982485350 982485367
    0xc061606020a120c08011814060f0f060d0b100908070605031302041415040e1f062601110c030307030b0604090f0203090d260402011e02060a0b01050c03 67
    0x40d8010310088070b1909103001d0811200c1009001d640782c4000d00e034081040320004001406100005091031001c1140c2004040100d0391005182d20003d0b003800d0254500b100910303003607141c81044005d0200300600303a0352654502e41080300500420040300c1c0c00790050001c2c001e409030041c03003920251950704000d0070480303003001012a0240c1000f80096001000c050800d005078840e1712444000050b6100c03603885516000d211800b00d060b89816043c0100c6c545031001203a607401090b050260002440300d140036100c2c0001050140c440351b00080b46645240c3c1034000211403440300051105040c4d4000e00580c1d04d07100000003180510600c2c01c80c1034000b000000c0101e0300c241c0c07004c0d010584c0100758070308081d201c0700c3d00da0413580821039040703915600105000500310b04001d007a20790646882c1c01c2440400140c0441d00342042c58800301400f00d16803001c241160300406580e107000581c3c0708000007000c07a051000390703a04003d0350000031583c540300010001354414400c6450405a1000842c50316100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 982487850 1250 982486600 982486613
    0x618051312170c031501020c2404050301050723090a0b0702030703081314040b0d031407241805030910110a0807021005160206390c0616 60
    0x62000440411460300040704000001001903402504400c190f103840e841c0c400e814821100c0307080c1d4914150352005000310815601c40c0b032460641080401c0f10710103800c2050450450340240e8011642c15406c2c181000802e40d8051200307005005100d4118640300600140d203c582d2081c16012904041d81400c28040701c040d40e40101701c1c040c07014040344d40080d0750751259082a0001128030403061450b050810280c05800942d9261690894017080445070f040c0000d044000100303002001c2c81000c0441d168110841c46c10f8408907900400907420302d003410a140c0b22a07012458102149520705002c0010803209103221482e2030782c1c0300d801146424070f190100105c1c000700603070300c000300000551003403440d980c180402000c95106140711901d8500340c0c41080783c86d18071b10440c0010171000f40507419100d01c41036580e0b65155010340c1c203581c0d10700c0c401e03a075650030055404440d815140300c2203516404c01c0d138805410400e0409281502c00c40720444c41007101d24840c3c0b031502103d03110380312002e4010584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 982489100 1250 982487850 982487873
    0xc050c0d140702040b0102190b010f050105040803041e081002041809050d200a0b0a1b020a301d0d2f0d030207060e10050a120b040f06180513 62
    0x505004450341c00141520300324101b501100210740c200f204034010840c211400bc0b0440142809080a504160828065950f207003e0303403040700c24044504d840400c0700081509108040c0080c0e00540301442c4030b07600704901a50040c400c042c01010381103815009010144144241c460b80880a0f02071440d400300700b00e91501d16903a102c103c0718030928401c03c2e00c45d810040c5220051140407481800d01c0c29888200484041e0f4400410305102d08802c0d525503a070204400a16031351062000c4500e01400010103007000e8030340d9030114070441e5904078002c0c058120156042c10001c41c1e0845040e8003142c0d0910610b200d510400070042103002c5110400c420081c43c0307040901d84c1c443c041e84012170744c00001070942402841d081d030158000711402d22903e5401000142101001e40c0c5010061010b55801810380c41880154800c0241441001408141640101c081117000800510040100003a410300030240d074811001404800d45088035054280d0140c10710605034003008a901d074101c1d03110783c102d030304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 982490350 1250 982489100 982489121
    0x1e091a01030f0b04020d05010515070308070c060915090c0b090105090f041b170603060c041e0e0703062d1701020706020d02040303300c120c050c0d14070204 69
    0x3501c86422200710313212403000d810a518503030004122945044113120550b1008110074081910030890140480d4214150725006096450702803820003003424540010070f071080000707040301e1011a070040c680c50a9000030202074042e001c80496a075035034a45408600c101c1e030009010076424817a40700702d4680150100c4065401410100e06007041c2014144106030204413003010494a102c4420100c41400d01564000307010341c0200700300d050461107012280204e1003511710049445d40700c8800035003400f25010007043e00760303101405c40c01c1c02c01c0054007402d428002c481012512a50080d101c041e404a1031850001c0c840708991414240721b00d403041c0c60308d046c1141c40c1310340d0200b20410020301c443c070082c011029600c400584a03415031800a2035540d0a8a91581a04c00300c60410310038941c04106181d40143c103240010074440324001545c3c9415000b21010f00940b82885210340381c0d0300900200048140c01081c0e405842e00280b040e2104089000a842d240700c1c01e120000040c14503900103034100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 982491600 1250 982490350 982490381
    0x70309060902280e060a03080a020c030f0601080d1404141804030302090a050303030f0601080916090204030311070f091107140f28020d020105090a1e091a0103 70
    0x6141c2500460b800c0c54107540c1c08400e403011608060758003021101c400016284803603140b007440c207000c0002450641980000350040000298001d0128000c110543c0100c00140035100790118400c06161102d03800d110f1045a8003030390001c40000c601c1800c0c0240001200c03c0050309040c02c00d031002100c80081d50095400c540709112000040c0401400584034500c665405a52005894117100e21002035a000d00e000394014024000c00312a1448002d43c440028a010f0343c0c3c594552800c0c1c0c0ca46801c5103003034030314101196804221440790f900181b003500c1c0a07803100c804401241c1c400544d1a9124400c0704055000c00101344680b11498201c0c070041448040181c1c100501c984036000058042d400000b00ca91002c248000e140c0d4042c4403031281e4509000120b00550a043c421045da035400303510003882141d4024403802160301520a495160001038500b0740d0554840b104242180c0b0044200d09588900c0345000800035001d015003e1041400040b4018440c5820b00540280184da030f07500001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 982492850 1250 982491600 982491611
    0x1401051e090f0904120c060f11070614010b0301120302072312063c070c050601080c15030601140c10200901050a180e16020d0807030906 60
    0x80a505000c40410410181100d079115411401c101054042a07007003400381c480d120401000c28499075044001d5400381c10000d942d052180307042c80003480c001c240300d0720445c81c0c609a040003a1000d0b01520019100c0c00081041080b40e000c3c4011000d4248100140b66404100510084041201c1e8040741d502c203004607032025468411081c241d09082c40d0007110070319101002c00e1540382044d000724044607440b01411103401c3c00c06201c5032a41842160782c0544c01146034141030802c0c0c4c1c1140740300d450b1624811401d541000600244070203038030790703003920248039403400810190307008102c4142594000b000340d8000320401c031054a0300c2d0401001079042c05600c00c600300426807140010700e2512843c4000c0c0c404089440c003008203c8034084c0d08806101480701001d000d0b0005841216110b14007402c0050322203d0380d11044401030034102561404462000c4c00140780280d018200b0b0007080724201507031f031400d0a018200e90b100c42c4503002500141c8844086401d450090b40444200e50185401040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 982494100 1250 982492850 982492867
    0x9020405040b040210030e100c022409060c09030c0409060902031f11040b071e06020c010c030c1b060b0109081501091b02070506160605070c051006060207140105 71
    0x120303402100c0030384644416104000031460700034000c803040c11642c14100091040e540f000c9a8540342240081c14507907407071001003200b43c000c101da041e00012401e11210803413610b80389801442c0d030994240013144140000718140c10044000e54001d481c0c050000c000d0740e00d0700b0741000040d00303410700d0a4480558174080702c40547c60038800090740031000c0e21110f14804080840358116100c1e41b003a0040721009010a0005440b03001c1125181c641081d64201c02d003d08460380d03c0044e12030b00f0010071407840024201400e42041d0020000785005403010450f0559440d4140c4104120003505005c07940702c082d40703000203100caa11054181c901850101d0800ea22a68014a0100403660a10042032941d00400c400c50141c024510440c0b0040d440c983e2501600720702030b40d120003901419128400100b80b0309a00c0c10155418444c40b43c00050900c518107080c00007503c04c20603000c05580b03030701a1144c613648070300c0180948c408a40c116401071405501d08100500072a1003450001e04200e420050945c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 982495350 1250 982494100 982494109
    0x621020d0203042d1e1a01030c05040b010504061b060e030c01020409060b040302010c0611090d060f050f090a031101020c0f1f0621020a0f0602280807150902 69
    0x14440c601c01c2c1c512a080800c4074490703c1350703a0411602c40c1c200c2030300c1e1144440002d80c08140301011140c40c054030f40442d0701c103161420b2010603082c042c0c00100c000d4400002848811703014075040301d10a440c03c102d0400c2070b034011540c51169002c1d580c0861205808490020750f1542c64000140c040c484c00600030f0503c030b900905541c481e00c1040620f03900828240190080c074860080180f11050407030380b82500d5680042d0000022400240109942d10507508039030000d0022580c0002004200c416441d03094684031001304a08800100e400e40392a00040142e034105001502508482e0700804004090365007c603610903010b00d5181080d5002d0211501d178440030040c0014984150b005003007003e100541040072900441c40c2440c144d41400c80401403c0c0441d2280364000040e260041a040c0749800400d0903925260712201e922400c0c60000605c160b40803803880c040840c0c070503103415004010a0030b04082d8440a502a1544e0010881d840000e0781c031401c3c041c0401c0f2503443c0460700c41130360340004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 982496600 1250 982495350 982495357
    0xb07020a09050a272a0f0306050106020c0316140402090a0b1c09030e01271503060b090303250c0b071707030905060a1701090213060206010621020d02 66
    0x716400d030780b56100c680d9420070201111001c00c1202c50310440d54405920744c0d840b82c40d03440e40c4841c2000c030320250803c6459540d0500c84054507514821b169590f9883c9002d0009080902c5140014055841d580200c3c4c9004103400344880100c8500c800280d0808020070b440c0e11641d504a984140d00308001348603504c5161a00b0010b0407507841c1c45403a2103110036500e842b0070441d101c0f4404a80f40440e9440040d81002480c60f51020a29242240e414a0641450041021071400b00448030b0308000060900810903010600c21195030280a200ea541341f0723105040c01000d4590368150000c0c08803200050201c210700145141d0446e00300400075240d1a84c1c001c804040d0888852903400154207414040440d041d6841d00c0c43e0300d91410320740045a00c004240714850b0140511030700d80011000207540c0b00701041e081d02510b4000070320301c65a5818110340294002e0705210312000d050f400c001f64884c004100c1c01d04032444c9884201160000c0020990210041800c00b03800c01d5013840740c00740c0c0c42c1061019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 982497850 1250 982496600 982496611
    0x142101080106030b07020d0c0b1e040b070f11030d0b0f0604030f03020106060905100806010212120421050d020309070902180906030102030907031e02040c170906010501090b07020a0905 81
    0x20080d0a5041078180c0c0d000040c101c20541d40074400d034001892303000c0c4480d82810b41055003032007a070700e8204150910340c00c40360080c4031000202d024082444181e140d40c0d03004280c3c1d926481d8080c02140c0048e50860910042030381300c0e800a002540040c40765030070000c140d142c02422005d48440110002d9001d41198100365224140c801e10102010f8091080b0405040c0c203040c40e0f405079281c0400111592210740920b4200424407012030340a90081000041c00d42c0d070002501d84030014003079200550007048405a80008036101250030844000d00c00740c0480799655111843c0480404a100195101400c1c400c01e0b803144034000219524903202411051501400c46540b2040b01020441c00f2107002d044148641d2040013846200c040c0002d21b94112a401b10300c0f1401a900902c03081119248024065046420000400c43c10340c4e00640003200e020043d03215080c82e894071010340d40e50701424011344ac00705215080500440b0090310241030007034401001954403a0f243c074800303416500c050b1407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 982499100 1250 982497850 982497853
    0x606031b0609050307050604090c03112106060703020312130506012714060d0602070804121509020108040f0206190e0f12030a0c0512070302031306030b0114210108 72
    0x400703220382035201003810024041140100a039600341000246984036510403442e0469848401c0c0c90020b003c0c1d0411040c20750311490031a1a200208843c5007404030005050b10002001c0e070008070b151502006640595815a000310700341300c01c404441e03014003000b0301800444060180c649000560800071305010b044140580b018841c0b4800840b5000300064a6070340b0003030b0500810012000580d120203620990403239020000820a0034004000e2142c040041d0000100013400f080e00d250900306a400b0381d110f03012400e04080b00d64501c40465451141c002e0014505030b000c1000701d03102c02e00071910b190009120f945089403102d88a0f180a511050b008040789520f200302c2a980351500e08000305007415a1a90036503100c1140c480d0700d901c41c0310401000d1003081e020981c180035042000b41680c4040b0302e80e040e82e030003207800c029580360044401406008040140461442d02ca8010804440d0060b1200e810713585802c410002150810340c0010300075449100d5200c0da03d4061017009000703217042d60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 982500350 1250 982499100 982499153
    0x702070305010c091a03093d05010e01061b0201030c170405010605100908120a020721021f1d1c08030a0c03060b03010b210a0506030708060c0904020304060603 70
    0x10311100c00c0006141117260944014800c024444102207010380c146c481e0340f007181c074004481510702c80805464150220304003c0701010f00200320381d16400b66050b41c0c1c1c1c0c8070503101c10b42e980303c0c1d00321114413841b00701401c0964410544001540613070000038024120b42454641e0b110103809004240000700e40a07a40740c2e4464504003c20706103c0b030032201e0322146141003e12a8200043c282d69200b40c0503007140c0b90000010702443c007600c01c0c0402d0020b00440550340201070740028003900c120301d410f1000e034403a01c0c2e1040d80320140c419503485a003c0c50407585034110400060807158107079410300003c0c0d40d0444000c10146d13851600c00800c00358207600c200107450712820b01030410421291a03d03040820326141500030700194003842c06490440c0c07000301e41c55513240807050074094508540b000c400d403800c100300c00f801202c01042e00003d02c1400141c3c12a102151ba44255a544860039916210303082c000f007007082400d04064005641c802d0281e480480c0c1c1958941c0d5440840915400101b404079400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 982501600 1250 982500350 982500359
    0x6050a0e120a170309070e04080702121b040b0f01081305060a0c030b0406060c1502120f09010e070e01090b0d0804080607110105040309420306080102120a050702070305010c09 77
    0xb900c50b03d002c00c3d941400c2e60652404a6126546203510301404103825140d00014040000030b2088a442c1a80030f0080611081e070f10021030b94901071252401d4440a0801b4045180c0c10144902c00d90311100420f00c0c6031782c5c403890700103541c030f1b140240102c0e0f45100121020004544108042802900c0320761000600110904c1d000302210340c5000d00500c82c070300345601000919408103034065200e0f00213020030300c1c48a44001c0c4000910a40e14045543c0c8508020040003820180c1369038412241d001c024040011403441e201c0d01c0707007290b0003203070000940d030b40042c442c41034543c0c4842843c101c003038003102d04100191a1481c3e20740181d4001c040c1da0380300e0401c00001c151310101d21414110004024421410316a80103402002907008440d860011140000300c11442400d4059680c0d803110000003020b00c4078170170a00040341c0b5080c81c10200e414840c0000758100144211448130081d20341402c90785c0c9624886030f000d80b8000e40303100110b126110001c00490002e100c2c200ca042c1c030a441d90032209141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 982502850 1250 982501600 982501613
    0x160305061605030c0d11070515010510080f0106140d1104050f1002030304020405040c03140a0b011a040513110406110601150c0308090f0a14060a020c030406050a0e120a 74
    0x10601c1282000380030b20a0050860840c13003030341c644042c004c030041000c05030150a50b4050140c080098500d200c6c040e03c00c12200700100d406c2d4140c0e0010f039034948070362110620a60314813500783d9803030303070080d0860004020f094030825200301c0302004154010310788000702d02042c0a840c40ca102081c3c4c8880001030030807c5103408003405810000035540c151400003100400707034072408000c00107801580c0780e01c00241082000b00514010b183e000990b60300540d8006409543c4102d459030032140c1801c0b8100202e00030b40140036102c1340c100200390302403409003003005005650310418144900c1686601480e800d0040c8440500302400c40c0d50b407102901142454800d150401c10f900c14107811140e4000c002d18160701501784203080303401d82841041c43d00c9410600e1b00c2c010113000300400340d0048600f04008c004190180e210101d140000b02e40c9141c450042601c01c0788110018840d04da40308000c02c1161501880140c44140d10701c3c200110a1040301003c1740d8658449031004201d03401c003201c1c5500b0001d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 982504100 1250 982502850 982502881
    0x311030c01021504110a12060c0f0e0d0201050c0a060e101109090f06130e0d020c04230912130816050f1e060703030204050a0602030f12070216030506 66
    0x10901c028800c5080c4103a00007201c49010304050702e00d5071170400d541c0d6291111036500e0700078070845015814070007040c00d100000303183e841c90040024440301050300e00340d40b1802120381030520050104403a40b11765801500d0a9101c4901029640030f41801039010403154404c04010360242009031180c0c14400500004455a01040e086240d106000c42ca070039484900995610a178034804880c100d46854001840103807100034180b030340508141500d00b4500300825110300a00c03681e0200c0384045445000c1100f940e0040d2002041c1c00030303e05e0210700344807800a006400598400079562400c0850f28108003503402180f1519250081c0a0208124481000220391005803185820002824500013030b406048141031b19100f410050700302000c80030940c00c03d440c00382c0018101d5690301c0c000d26000c0c1c040d4005110b0759208a54012001030001c1c004012954440c0c200c5201c0c42c80c100e901c442c9803052000140400f81144552254041c01035060806003000e180102c00030b00680c030b4520008800002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 982505350 1250 982504100 982504123
    0x9060912080c03060d0204091401061d010b0d0510080703030c021302131403160f0509010503061603200d060f050105070201090b030402030c0d0f0203240a0903020c0406031103 77
    0x16003007000340a04080c41a44c1d0030000846407072460054134000039002d4207401d00040c040303004d4640c0030f02542c0415802001140c003030b800120340494442c0b01e10200d00d00309115042c94603004001d0050160381d650303c020352085d10b580036059003079100e140d440c1c41d0505542044020034038544c4940198034100010038404403618070305514000350780e000c91a881e00d092090660285151107000c41c0c665080c0220310002041001c82000e05a8035034501c105242144119405208d405002003120306003c149203105106481202c10100d4043c0822801091990b0160a00702c1e05c0c18458101410050020080c2c00040c00c6d0100348542012240101c1103069400641400b50030130840c4c0060b42c104c00800c0485040d041e119443c0c0e070303460020030300740010b0b040c103ea8400421100c0b281040580c90310703641e401d402902111409002180d074684502a0725450580841000d0b00107034100300a07401003402d407886441514641b814440c08034003070780d0f0690403c07030799002601310f440140c0c10100280f1800d00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 982506600 1250 982505350 982505357
    0x80a0302060a1413240e0c040c020f030304080d0b120604050f061b03100503030a020319020a03050d0506010c150f1a06040612020c0d110c0a0509150d020409060912 72
    0x1420800c0700070b04c4c040b9078020014401306800140072589200341d00c1500043e900030000780600083c480c06240c0310300c41540c0c80c1c0c1c884c0d480c00b040503441c9031002034241550b000c910011407840d2196103515669400002c0b00211b0540c446261a03e031361141d016898910340c1c214010401c50074680740490800750454902140d0340d02c448104900e81d405030b0820800082075101171a500d03100e50700c0d135240030402c5030810b54040c07000003400110a0350002c010300c601070921030600d00940760160f00300d89460a04c030340503000503400d010500c103880e0790f03034015030b00038105061214404182e40e03500c0d03d40307000c0c214039216480d5031040400429070490245180c8a005000c8014551450500081c1240503900520040080c642840200d804181c3c0c11a8002184941115000c01c0c40707180042c401040240141203500821035003c4250030300e50a03007016210b00501c5024681e4a60081e40b518000c4a05030947c0f02001403081320150300e451058034000c038001d05011441c0c0f0900d04100e0b0010702201d4030035041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 982507850 1250 982506600 982506641
    0xb09010504080906070609061103070807090e010603020c0c030a080c0f010506060d091b080714060a17130c030627030903060b0d05030a090509060609011205040309080a0302060a 78
    0x10070b62811a5112442180d25503103802070707820400000c2200042c01070465107014142140c001d05480a548a142541e0314802150754590f412160311003a80f207940141ca10000c018040d16019401034500d064881040b54400700d000c00010785800c00c80f46050301d0109000a0a046407a4284023840c02400c4680081c0007600f48400881c64070321a401032a07070b41300c1c0d07151008002c11000100741c2000312100d10a44203c143c8a141c120703140c001c584a442c0181c555517148910f40d0404400383c5540320733216113541c4160f0a413030f40040d4081c3c80082c800180b45410000000000b2089000d80010354064100000e03d044480741c000e209020809100b807064021150a8001a600c5401882929845880460f0080b00c24002c1408000e03940c0c0014030502010a10138403880d4424002c10803200200c50040250700c3d40c0d0140160b40c41a003134190f00140340810349a074000282d420981e001446450561211543e03a07201904040c0380d8401140160002010b1007119aa2409008a150a41003108ac1c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 982509100 1250 982507850 982507853
    0x9060504060e010e040203030c030a0e0910050f041109060d0f0509191403190f0815101404081609050c180f041d0c18220f05010212040b09010504 64
    0x4051005104d03000c41544900002011520140f05039601100f6140c1101e0700c1c0d480c69203003d411112004882030103800e40b240000c00a01e0720145120445001070000804541001c0c240006001c25080e02d40308003004101705036680d100d00005098070660780e800080c014854101d04019624054841c845961001e5442c2040a0f10318184188003030348a00d540036190441d82e01e050650054150010320305420300340c0032500d540c00c625603044000480e61410344ca039565003080f008001c2c07042c140c1900001816007122581c1d000b24007281c458440351000c68200341d51070319045e1800b2195820404800341a200c20400101e40d8054590448040e1420b6810202e90540501540482520359481085141c9031400240c0b555407101e89885030451072000806030040020341d442040c198014040c074054024080d601700b51354806401800581c1c90ba4809440c3d1142002890540e1b00064036680c10410100300014000d1004102c1d000c0706031148030312032410381403051087c1c0c0000d01405441c0d041c00708110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 982510350 1250 982509100 982509119
    0x1203300705070629090f0705091e090108010e0601121a190501030c080d050c2d032d070f03050a0302090925110a03120f150906050406 59
    0x203920000624200751a078045080c400040c001510f10348140c2c01440c1c0c12040d15200792041d1804246055078180740680358822016400d9500702d80303140000310700340300750340c0c1307501c1d00c0c0341603254000c1f07100504510081c884000464010013a841402140c0d503d00000080f00700c00e1003624010700d0716910a01440b0443c2d11408222040122509a400d80e0600020900c040142030550103000050007081a5a100d1a148485020600441d00280324074801035105500c96002c42c3c8042046c0806006894071a4419074461260001082c11a03040d150140000394410800f400c244814920882d0081d0394000f0017100c90b0010394502080800d003048101c0c0443c07a011203940000d640340c84c146030b4030040103100b01d000340a000e01c03496006580f03500f0302001ca00100326601d040e00140b005490130041d440c8007503c1b0f141f104a01840d842c0c110500e2a00030a0052440c03410745042c100c4003082c071218014401c0c0858102a04031000ca030500342043c46044214401c0307201409003514200400380c1080d2072070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 982511600 1250 982510350 982510447
    0xc071a090a0801020310060f08070309150c030c02210403023304050f120d0e130606030902091012290f0f06010306142404030309181b0c0f021203 64
    0x105240d2290206c20400c0dc1341002080e4103440c00f0410030688051045c000c014207040300c003000040c802e031121190004c40030001c45600260ba2800f05291524540c00c0c00055000187d8004981e40c1d400084405812004000c04206212507050f983d00c0d4140020001e02410003014603010788112801d1482c0920001001d404030701080c00d1514103003100c5400039025a10340038200c2000c50504000140e140d805030400f05920384200c5620190399201d2542049222243c402c40c65032420300d0fa51000482c003001c100000c410390201c880640c810351242d140d00d003190140d80c200c03003d00c4107408001e00224011941a0400070910f0b060103424500a134080f1340764031a21040344203040100d013404868088030520b000c403c02c1c5d00301f8a61a1561b07803c01401d44510303485055800c021904a0000d1407075079124903c0d0011000d522101040340525045501207181d40007194510014041c1034096920542c1c1e004028407140e00865448052030094210b66905111040d650500c013a203007641c030030290001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 982512850 1250 982511600 982511611
    0x1208090409050f100f0e0c030c1201111602010807030902060301140319051509010e03040603021b1507020c04020c12070206041d040311030c071a090a0801020310060f08 74
    0x414101410b007051410b228035545005610300c109010341d038900345650007482c3c00f008505410810502c0000380103480300031000c80a07506802c0340d21484c81620340322480c500c0069122000003180e41082c0724900e026401107803280b4400a8008508003103691103481c07154494001d280500c074110349640401d40a020600403580c2d03060103100e608034180c800700200d05c08081c4802080791805203030f0034090b85501902d82c1608410f68180001166944140210200341e00d441008615240c40c0000c110001d40042801d43c01d070030300c00791240c0b20003c001c0001014601c00d01c1411001c60a01c440041c0c60104154841806940140304c505a241c0300464112803000c80d6406480d5076142c144005812071003141c0104005950b0085016103062804030803030300c920b110382c03210808482084002c55030782c0180c0101c40e0459020490900c03e1400d604007003800000b440120608225a640028003001c8160300400c203980e50100c03c01040c1102d900702c410046c040c506140c198603050150040038483c00528 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 982514100 1250 982512850 982512859
    0x20a03080c0903240405060106050301060903110a031203050a150803070b0423151806270a082a07060810030f0b0a0f0501150309080d140f01120809 65
    0x4007118a0340f01403200c03003400b0004615030329003803000f028901c1302c0f03440c2541c1c2514103218401c0086044c40c000c104880c162412500c034a58014950381e1541840c01c4180059a0002101d0000200141a10801082c10760303454401003810702d003c41014045070300410b0b4600000409000801c04d01101004450000e0303040703007852143d66a5421300b01c1e030006d211000320600601c40303006084004000714000e45d124015244501140d1901d01900c8444003050115000c00d40081022070f00c1e880c00f800313948030010b241e80030340741018220602441c28004005404d80d4a40b4000405c0e15090242d00c0083d801500c4419507a907000c00600e22040d6030b605a40100307000e019508000c510130b40d124460200040d5800414217102000c40d107013030480780e030b0700341c0380040800d040441d42a07002c401c2c1d00809041c2c070000449041c4209040381c044003e1b10002d41e003a102c25108005004044255004480001c40c0b02c403013909203414007115200c56401d05034401014454141e0b40c4000098980044408403581207c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 982515350 1250 982514100 982514107
    0xe010b100e0405270d17060915030c040f020a0908191707050109111306060e010c08210712090507121b08010b03070f03020d0212120a0c0210020a03080c 67
    0x201d208004041001d280020024180408812407134002000c0303840700b0300c5039665000140341510303404030400280c40341c40e8040c0d525800654214240c041c0e910548a0007810ac591a9008001003002c68009000d00c01a054000074001103090300140080c0090540f240104070f600c040840d0481200d685800080c013095000c044d12000703816410940d141036401a000700849600e500e45020030910f620000c0d80240040382039920100410705c2003104490f075548402042c060840011100078008100c1103800c08014400d00130980c0c88004440040000c0c3e040b15083d078144813902070040c540c408540c44805040448c0d80c00010808151602220b046400a0300f02943e00d10b0245042208184815001c0a04540000764072605412101201030242c0540d1075842d200c00303401751240c1c05404080c0d005441d80d2110307001800c1026090100030b000c581504c00703a281d40c40c0c03050b14a501c000866800103055034940003e601c1c080d691025040031070300040071040c103a80d4020b084c13038400401101d801d81020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 982516600 1250 982515350 982515361
    0x911041206051f2309090618151602060f0405071224050601031107110603150a0f050103060f061d03030f1209100c0815030106050904060e010b100e0405 67
    0x7071032142d0168442d00e03200003500e4813401c0340c18203840900108101031031500114002400d01380910340c041c5030080c02500841e03a81c000300e182600c80e45081c40209102d844100084802c92100305406000d40d83d41090406008083c003e1038408050043c60b0b200c00b9090611000610000c1c030007084030307102500707001440380701e040c20304598440300a900040d03540003c030001d040260750b10140c4121000d80307080081c04c00c2c68900c03a0403030041d030100030000005407080303140510308400590342c00002003002c0440d0444600c08240b600000340e0094510b50307501e00e8140025a010b01543c005010b09040182e0301d585020b0004003505464204005404c0750081c4545154900780100c84103101405502907030345c501d90420f0026000d0441c0c803c1c9041c029400100d03190004c070300400c141e0104507550080d0304d8842d00c1040701a10503802125625660300d410000d0140c441d007015503c114064000040c10040c00b0080b24203440d2800c1d90144103111408032141d40704c2e0001034440203000140c4000503e99210b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 982517850 1250 982516600 982516621
    0x605011e0f020304030c08010507111606051303020303042c1512120f0912010b010c030516061a040f0b031c0513030c0f09060b0f0a1b030801091104120605 68
    0x31a0405815030704080c6e004180003a0540285000310465a641c2a44e415603000e41616a0f04000c82c0749420b0224020400603248608054106106c540c0080703510f81d42c1e40e90000f03145900680c4000d40303816012700e00302c421401c4098101c50301d190401c0d00c5036180c0b4022006490b26000085c0d054400d05c110004005843c00420800c03640003c0700c8142d542da4106d140e000082c58110010302c511a541900124001240602840a40100c1a180c0340e400282c1035900761216001040444211140714a01002007807081c011240c089001d080b15030900e4070100c052000b43c03030b408030542000600f0824081c07071270388000602500b5646440c1c209100120b440e2000ca403a8440c5c000360b5020110b07108004420300c914035a8040840e44408400100150b03140320b1602691350500c1038000780e12091020107581c0d050701c0c008101c4a1802e10705040c2ca096140d485140400804c9404d400262810005000d294042d1040c181b280705890141c50a292034200e0070b1204441e2000010000d646802c00b20705140c02c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 982519100 1250 982517850 982517857
    0x1b1608100e060711150109150f03150917032a0703170901150e0708090715050d0b130501090e1b040c02070e0f160302070f030e030304170102070203010605011e0f0203 73
    0x1017007030000d10950792503004030301030082c02501c1394540c1e00d12003000901202c1b001860341200d620409003038030042903400f4a8000c000d00034056600c03920410008a2401114005520810030009221a0b01c0c4070001d050b5082102003e180c44511010011000400d412003400404585200103402280e41c90490b10b901502c179450316201039880040e0041411108440b04510401055442c4a4250b841010340c5995981611840c5000e800460b0500b00061080000740f0a90314001e1000c54007007800c1d4081204004546a03040426540f140140024072841c0588898410b030000240700c03002d410105208401460401d030741c8520707903840c81d1010b142d0080c0141801404201d510180a184c0b005421071520310403195014540102017907921305034020f1003074428080e00480c2c0507120148556080e42d0300c0d2401a001c80c0e15200620000604130f111314045260780d10f40400241c0c481c8203503c14503081d030b1015041903051004c1c9080d145909098202c82c424a18aa0b00d01280d000c480c840781030341940b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 982520350 1250 982519100 982519123
    0x3060a05100f080309040e030702100c0303060b031f0603110405041e0c0503090d171602010b06031602010501080c15070c120f050606090105060409021b1608100e060711 74
    0x42c900400080d83d041c0200160040400c2540c0a0204180b0101c0c02a1203110324040254405110500b504140380302da020640142d01c242000200c0503164038054a5a400440301080c1c403007034105846100392541181c1d94000d0410b401e082c001003d289441000300c0c060b6006650040340d480e00030016070301c0b03000c01442c5c40440544c0100310611030214004c00a91089079107254600c03812000040701351084014800080c03801c4206005510b481c04180440156036500303100319900c420000700342c0c0d07842800850254030111a26400000a4400603080d01c0d0141c4c4890304c03d0b085001740801540318800e107201005c40c1d1001c2142d50390400d10380044290b11a17044102c4401c1801c840104000d5240100c00605025604079502d584d80e52081000d441000d004007130b0000c078140f20400c010701d000e4028250802401420303641840c5180ba903189090f569280380408504422410044121f041c008852a16815601409030010301800c4a41e039102c00b501b15000c021006034815203044051210b1170106 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 982521600 1250 982520350 982520369
    0x718050607030f080112031707051207110709050f07030c1101050f040b0c09101b0f0b1b07051c1407060b04110a0c11060c070303030e011a03060a0510 66
    0x100502e0070300803c059190203440b03000c01d4850001042e002d00400340000c81950640da100d0f010f96a001c107aa540e0800074280c101404000c1c401d0200348a00040014480c8940b0307984d1005148101e480c40c1d04d070140a0740081402c5151230140440750710010134040d8051510308000c200040c000d04122001031942c801400d039540b03001d040c40018103001501a00943c003400c0244066222150303607624901c0b481904942c08520f0740c0e080c8504034020300c540000903160551918407040c0f50b03198414103907050f02080b0703095024a401c0160007210441d040304641da103903070071600301441e9030b4516984600d0107100307034030b0001200840300140e4450f148440c40fa80301e110515403101414038003540a0086940d03003510560810244100c1105521b0035a041c071500d175611544005030544400154105e969141508020100144005440c081004d48010751003a0f40008440c032a191103d030031209a00c0364070408510b80869605507540001d00240c103c1c0d0300d83c000185c60740700d411568601504a900200303c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 982522850 1250 982521600 982521607
    0xc010e0a211b0302010e01050307050a0309241e050103173a060501021908070503091518100f0f03240504051012140a2f01020d0807180506 61
    0x60210340c82071030102ca10071b0b01d07800301400d4a01c005440034003044a42400103601070009105d064030075006061001d0080c000e10914644440844050b40d1000030060290754a40c0ea11700f807144444101e503110303c021107000300080c1d41590b6503a18a0601840d211001e42d0000c554685180105520249050061002c1c1d40c5c01c0c00b090701d50f01c00408102c0c001a410b15180180019080d40041981143d4482c0302210500c402919900d040740da40000c801a0780360b10080c0031020703c0b0340f585040304565211240d005900ca031251030669030031094040100b0b0091404404011849030028200100b407446424002901e60200c1c204030010b1900062200a03c0c51941030544520042d103244d40654609035006d014640c2c4924001e0300540702d43c03191032408000400c240010680311034082d042a0b00030b1341514464605520f89242021003c0100300002c0070802441080020340e440340300790603100380060030745900300fa81c010b48400d9005103003d051003c12091034800741c0c407600c40c80000d0080100403c0c0c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 982524100 1250 982522850 982522883
    0xf0711041404052505010f0504080111040f08010e060406050402010215040b01090e01020711040905150901050a061401090501030e0c0303030405010209190b0901031503020418050c010e0a21 83
    0x60341001038a0941e8240213412804803c80d207802406401d000003100741101c068070300401126915800f107240020000c0c140004182c2d14028010300344400710000712180c5480c00c2c0154114101d0a941c450282c0344c1c90b029204206020205100ba405504070100280301d1f56540010b0381824040038220b0b00d41c9480c4d130104010480040b00550527a41003040800c140310050580500300d00c5541800ba1141118840160181c90306401a4200d1446201611000850f07004500d080d8400ee0b80c040781165110303000c001401c40f0354401c1d40700030030080303c84140740841803001a14022803805841d04250302c0390303e9481c00110400059184007006003c0b641d892034107080c80c0d4000d412100466105003461f070304034050a00b141000d601034420304110213240c190b183c0010342c024030213141401003942420300c0000241c2d80e01c1c4a81060740700c0c01601403064400743d280841c104001d0b072510a06000c03039400324680c0b44e1613141e160000d13100134200d0b0650026800c454800807000580000b8480140c0788074802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 982525350 1250 982524100 982524131
    0x30c0f020306070230030a09230d02060703090206190201180c080f0d02100c0c061409100509070303050906070623010603020403082d0a1d0301050108030f071104 71
    0x11724043c14050f840d030100350011603c01ca0007040e9210284203c806201240c01c012640c0d018003000e51013400c45a2031940104501c6550052646804419800005888502c990140103040e4021540e14003002030000c26070028030319025003a08142c0749100200003082d058001d500004031030340d0301e039a15158040e052800f80b42002d07107401466501d002e1401e604090000004508080e550107801a20049503141d00780c10003088040e400400700144600d00310081240340c030406002c021110780c5210361740f401180c03061074518510403a40e0740c01c0c5410100240c1000104100060700d42c94034049a46a01c0480000e280340510f070006003000345130140c0c584c518a41503440c1e40304140b400d244c1600c0c9aa03982c070103070708901aa10000d0014041000665240310703020000c0107000030b02019801d9542000260303580c10780c001060350070100382000c8140c00302d200003095a0054010460082c0020340c10018850b03124011151101c0b0561800305900041124040b094000c421000e002008003420300d107000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 982526600 1250 982525350 982525363
    0x5030d061a042402070521010b010c1e06060b1210090e0304122402090a1e1a1204060b0117040218090a0c08060901060b1204030c0f0203060702 63
    0x121003110101c4101d03440e110a605a9045500004404082400880c180c0040b6039000038440114002d004021829560f0210a05103d554101c075202040700c00d80c4038582110b040c1c0c3d1946d41804003403040c0070001410b4111501c0700e03440f0012250071001c80342c83e02c40090550398100003c0c41c0c0012a0124185c170444a40f40d209508030b04100c000556910300c0d410464400b06501d21094000704414405c208074490910307a40c078402c3da680500000b854521019071440e55103001145030300010030b4841817401d44081c0025040941040c080400c41c04100340c00d840341845849840041d8503a1110140340140644d0f10318498415691100e16261400800134280d0340034060101c4c1e4019500a4091000030f81144513540c05404a035208020450110704440010b21000035803141003449030000b10305122107002400524024400c90409882e81402d4450641000c0301021050107510201440c00d4019078100d41c06082481c08120319041c01d01c0c80c0c80c1880c0019400d8418001403194096000450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 982527850 1250 982526600 982526609
    0x1908030c03072a03110a0905090f0d0e090a11160803060118030f020906030c03101524030b03030904020f0a110c061b030d0507050418050f1f0305030d06 67
    0x1d409030340f030281c0c1c09280005025881d04590110b0400d0600002c1e848141c19000b260004084620f61a9110303c2201554811a08144950040391800c02c50b254100f2048902c0c1c6950b06015000180303800100d865500003e00054805440700424220400f89004550108402c8100050f0a81c03590400c986981c0c010344000d40003980b00c0c0292071440d000c7c00c03c3e600030b49910a10348401a807031602000546d104c064055949070160321050b0495642c00c10408812072843c50010030522043c41e150b4030791143c00c0d40b04103809024011007902482101d0200d62120103642800030f185080c02010900c0c601884880702d802034400500e10050880002c06800703010300329591a1071001200c45400d03213901082010540004060003880324503410b403201e0800d501c0100048a0400b03000300601ca003500c03026600e20000c5a00014140410ba0292804d5603041035040b00a1000b41000c0003100c10004c00200062000070340e08507209407205200c4c0c0b5410042d9004012284c0310031003141c52400402d854441d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 982529100 1250 982527850 982527863
    0xb1c05070519030f050724031404030507020d050c040c09091b08013b0402012d0e010c06110d062304090c0b030438061908030c0307 58
    0x300000c01d40741c42c00c00031036081030052820264619564520311904280c11003100c081c0030300e40d0040b411194545a40000c40041c034440c41c00150b0411011f02140c40f500c060607100d100e40010000442d8110046850740303641954808111642824840d0800c075240c4191640141440c80406c1c00b15440500e41080c0c840e0100700b0460b00041c480028503441c119002c80e800314081c100100064154003004483c1000b8080c0c1004510a40007181c03210350580f024480c0c07046070b81c20305000a5582c02104866071410540c08100c0b094000c01d15500c0400c40340000004025504201c500302d83d208605540100da40020280260303602d0785500c0045822261404c004ca030300e042c03800229414900080e40c6010a84d601040f1808031200034440501009142541c1c1d40e010751800044c03203100140150302c03a40c0203100c1000c050040300500c20786c0307501c110320070710109884104000c2141c2c6140840303600080d0442c0c1300003c15803c2681000b1050300340e40b0005d1540400700c0d02c03281c0030102100500b0114840c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 982530350 1250 982529100 982529113
    0x203070e04050f0910151a1306140f030402010c021201060e0a020a1d0607021009030b1605180103060909030215011d0c1e0406110c040b150d0b1c05 65
    0x415040d4100044800e010143e20200b0042041741c4158860402e10b0402c00040360010307152840410403190002c40001035140000e07020582d800c00f151050b02502007413411800d064008000e400300da00807820340383c001d120004040741c1168040d10404401d40d81c0540808000e01410082c1030007040203100e6000e5281c485400201c940d0b00e00c1c8210b406052080d20b0b018201184001001c3d400c02001942c980c000b03030b0402283c800341c1d5070300200404000301d0b80d80e086c00d140c2c1145010381e40752402801505405026441040c01c154010f804e95090901da00c0a0122003094a801240904020341c00710f10101d2402c480d400a03d54046003031110008001110244c03070760398448020f40b00d025110300a810741d111902044010356490014544207200054822141002d080c240d070301e541c0a03901180c00b08628140610411006115511840c1400c807010860499010081201c03038918140d11009420300040721984021a9070000300c010801410a00381c0318060005501d1702e13000408113860610504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 982531600 1250 982530350 982530361
    0x1180509030c030a0e0d020a0b0a020c060f0304150914010605150903280803160f09050f0f1305090a0b0a1b052107120b030111041203050d0203070e0405 67
    0x4200c071041035003030b40218038000c0303142c0040350200c110702409a846031006c90681d02596507040344401400820710301d96a00c1c261980043d24003407440794036500505007441119000300c101416031303030f2141d0406203001072083c44034004c100400324100c0081101c4451000405058015406001a502c05640f07040b030308240d0200d00f00d40c901814550590640c04804013030f0001c0790840c2503020507800c1d404a500188030a5403162019007003110b01400c1c906400106001e2158008a604070400c45400d000c40581d04080104034402030b509006d45c02100050900f0500747c0f100214804a4052800d0412040c2003624050781c850824020580703902c0010310110740441824880d80c100042a8047d9013001c041d1220b00303840541143e49044500c0003814010b07189502300c000c42c41d228100d40c0e611249450b401c5410241100d07504155180240c1c0340080002c05000309030101c5003070707403a0041c110540b00058a4111071074801c01c5c1700c290380ca81c0048144000107030803482500140c02c0859090040c2d42c0e44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 982532850 1250 982531600 982531603
    0x14030c090c0403020609010c060204151403100e0916030606050405161b020a051c02030f010c0804110a151d010314040f03111603061103011d0c1201180509 68
    0x299019030807003508210400040c50281c0041c1380c100010704080d41c0043d031589400c0100e8002e58803980b000004040500f0281c4c1d40140600c116140c040406030540c00c0c007045411000c1d0176400303401d164210301e8020500d41d6008000c0c5c0c04001c10004d01521032903403249841d1004c3c0034035216840c061030414020643c0307840c901c840d0002d2900195070300100209032480c603500e01d038034090041c0e800c1100c0100104064550048102501c00e03607418030000c24400d4818507280034022040c250301d0747d1404a90200890788001c2d1300742c01c0780d0850b110f090700558400004100d0115036000c400c1d40f80b181040c0c68840750b0004050085408049040d902c0c0110020040d01580d02d060144c12040003036000190000704022112101c5074085e160103a01c200c1001c603800d19003d05280030514207540e0040800800100340901c004050380c2c2111541594900028094110712841440c1aa50300b05400110009081c1003030b102e024100c0c0001200a5070b64030162442c01c9180d0868454107410400000d120070300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 982534100 1250 982532850 982532869
    0x606040c021b1f050705060709080c09060411032401050a360909051b030307020909010209030331060e0609010e03031206010216080607030b0102011514030c 69
    0xa8680203000c1065410000c8018007101c0c0c010643d1204100e075000080140442800410520300e8030f0321aa02c140e1410142d2605d00014840c03810030810320300510446030003050b411080321060701c3c02045501d80078002400f900328070b480c200203140040b04200d1400024494410003028046a41a81c01c04600045406104940840c80400c044144c81400c214142d040c0540c0284464540c01481c4c044a0310076540d10145da02501103551a450204103001051148000e8000318524030b04030a032103500400e80f24050303990064800c00587c00000d003a0743d820740403280300c2d210003030a50b955410b00145040c1c000707014809070b2403024840b507006205210b1b500c1d02c100c05e481c0c43d9103030002480c41d68810022560700c03100f030450410080015091003510b04201400508000e292448000d00c1c3c100e000914140a1100c0c1c4006201004801c1082c0b25011036200e8015140f80303004207c1120100050b13001d028400a8007046152452000410386a0806048a9004120b040e074001a544204101030503c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 982535350 1250 982534100 982534121
    0xc0d02010b13021e07021903080301051c0b0408160507120c0905091b0d08030c0d180308070c1110080f01121e0606030b19060608070c0f0201050d020c0f060604 70
    0x1212072880000d810840400303406690706c002d00d030050b201e007040565400c000741980101c82c0c146010006010300c1c07404c1c00c6010307905c205400c1e082d03914207940d84402d0140705014001410008002402d500a030f44125040016030f90094111020a503940c000d604201c203205805550304407511b82d002c541e82ca22800f41c1070080d980c6a0007070400e200d90f1640c0708108500c1b26070599122010b880020300284a61014503c12800301042584039100e4401c1c04080c1ca2950507c0013001400c29a100002500200c100360007680c0c44c54039408500c3c0c0c0745484c520024186030405d0340034444000c205580c070b44c0700e0a1a44241180486c910480c1d0303031502001690000d160004020114028803c0c0301c041106c02d010724414050400400c0c4182d42c0e0300c0d0740c1548070043d00e034100c00d551107104501400090303001d00b000408042c42c0c000c00350314124000610520003850024055500d0240100030343e80f040040d00c02c0440404001c65071804010509a61810074400c01022030041d480000c40601d0280725544900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 982536600 1250 982535350 982535377
    0x601030c110616050c0d0c14030a051206030a02040609020c010b0a180e191406061507241109090916170106031707050c04060503210c0d02010b1302 65
    0x2603da504401c05440300c4101c4050801000744500241600c0421468200300ca1680322440070100ca401d207171501041551038941103601c00c0004801031a4807801700e900d98018003058880715201c000010741480300c41c000c065481030400201194140156004000c48000d00008200d45d04803041404488211480764a0036031455000000450482c4e800c0401404060016034a0170000380018402e8005200030a0f914001d004090b081040d508004068004c9400c90b820103044401741884149840366400040c40201c000f001e549058511f0400c241c042c10343c1240622101d6401880200c55400c003414541c4240c2451000c500044004035450613640c0d030701c400c03107440e0302c0c01e1020410b004821400078401c69941c2e200d001001c40d055000c04800800b102004666400460a0003850802c0f0380b2003a501c1686040800c101c1540e0000785101c2e05801c6000a1003107a60910110b10b190080100400403070082121a4000c194198000030b14503000300d0f01c5d50b1200e401d12400790200c2c080c584000040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 982537850 1250 982536600 982536613
    0x120e160e1602100e0a020306010e180312040201030c260a150305030a23040602030a0306060806010c060b040b0d11010f2613060207110306010510020a0b04020103060b120601030c11 79
    0x8414640c4c0111801074030000407210074401d15030101e45000400d80c000e240b00307090f81c1c0078031030080b6000301c6085020032404020350410101e8940d0f0308031602c021303100a05161780d411240e40860700404002c02c50b52003516003c16803080c00201203a444004944403265107207030078517210071041002e18a80c240d0303811400071410183e1310a4203580d5040342d0200b116100180c034040c450300c081103000070800b0f85019030281d500d07041d07072440103400e56646030418010700420108000c0c0070799100d1188050981c002d0310110f0b428a052000c078006010109895400085490a12040c000c0b03030900500d40007000e0307a6000301051003020888410001ca4450f58149a1004d01c03242c00f04081002a80c100e90350b40000ca0012210303035070b00c1c4100c0e480800100e0f1541c401c164041100d2406100301801803c090710200b011103052480251030300c03007124005004aa0301383c046410369200c0e0344414041d00601e180c1d01c0e92985407a8421268000031104140001d04104401d51160310410b5800e1504c0950402001c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 982539100 1250 982537850 982537873
    0x460b0c0d09061b0803040507050a0308070c0603090807030807030b030318090f070c0803150d110406060e060f030c070215181f081e07110c041b120e160e1602 69
    0x135581e0002d841943ca0348a61280451250342e0a00e12100544c030504d1030560b1803402c0d15003010304d00e0640d405a814946402003490102c1e5070a411100041d60610300715480303564001040d0007e00318152480e4044c400840e600c1c0403069141120613030b0355000c59803002240da60044a0109090480d448000105012000400182c400c0301440c3c006048401ca03400c0902030101080400d60401400d480b0641030651125071402c2520603440038018038a425403141c5a540c2c0410302c3d612880d2007082150301e0020010f1321032501e01003038810581d03004000344002e03154030808040903041501d5029000b81c0c0c40300c101c0f40c1450441240550901d0411030075550609006060380c500c1c50080900b841d460006425403813580c5402660f900c12100764030b4083c41d003080d10700da462828090103561409940350200c2c00e00400391864407400382e1551440c10303400d2600341b580b0000c0a400703803008a40461245952240807481403080080c10b40e106024803840c40d686070f1000000c0f00340001c80c01000b58014100c4a034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982540350 1250 982539100 982539113
    0x4240c0305070302240f0f0702120a11190b090a0c0306050a09060f06090e030f0702150c01060807060f0c0b062b050c460b0c0d09061b 59
    0x5040c0c040e0055034010510f15901c02d041000302540045006a04406c0001041d5040c1d09640c00404010b0b030321903d441c2c2000081e40e64410403500c8105150f001c00c240504608ca44c03001c8101600a40560780b00c002203401800451480000885072030b180d0b03c00282d200e081c00210304038815000b40d00c100c13111f450b5032580001048080c1940c00c8858603035407218007140d140c4c0115041005142d400140091402c02e11034100c0e90a07407443c03443c0b502704101d461044038001d02074070b80240e01107076003400b814074000f01c0e10442d1103962103401403035080c10070000d0300d10404550303441152110703190307581310903041c3c18116048502c500008042e80e9200000c04c101d81480d03c42c0388044034903000301c4c09201c80e41c108082c00707541c5828400c035842c1c0e0060030001c142d0b0038031010b1400340401c03144110307140c40901001c031141280d035a41c40e0040700c45503034000100c042e60110382d0002400c443d0180c03652041000c03141d40c5c41d050400c00c40d40125004810000710309204080c0d40321600c2c0007541590700340e81c03035039242d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982541600 1250 982540350 982540357
    0x50319020d17240603100e10050a0302100c050619060501210c0e030f0a1104051902030915150306010e0c1c090c0806010609050619032f04240c0305 65
    0x82000012050f01c030741d40c58484c01140112066043d480b583c41c500803480b00c0d1140018200c083d1038121a0080095458111002c002d4aa040360712442c140d00c44e10701180c01800500b8042c3c034520a160500440f04811842c0340c84203800c0c080140b0200c3d849800640346495080401054008a2849104260010752180c0c19621441c9400341c7c00d10100e40009152404003d4800401d81191550f241080200700a00340050000c0d941440980340000e13203611860701125143c450950000002a1200410700201155140c1003061081c41d003090b401400c412030700151407501134841c0c8000800d1a5203000a020b20820402c4501482c00840031001040b034035180174dca011090312800e05500044050031142d000d000f101004002c50b41c07404600400360005d540c400c9014450400204007032501019100c030226803241070100b42c48060114185c049001c107a10748910b2140c0035210070182131041c0c000c20854941c0e1404000d5000c00103205001d00d40c0d016243c101092002e038104000900030b4004d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982542850 1250 982541600 982541641
    0x181104060c120c0c09140a200c010b190302091807050f0d05120a020d110604030e0f10032c060115050c120319020a020709020f07050319020d17 63
    0x1860f1070b0802c1e91a000180020381101010603201c038001040e842c01d44050a41c0401c032403030709100c2c1e001805171034500140e151028000840000909420022007500649613440020f400c4411091018009111600c2c41e80070403445100a5400715955550b421094840e10003241d0240c10b1700c51a0500f040034081ca1120003c1d00700c40c12404240101e5821f0203140c0307040300a600e405a5030818040000e0078840c3d021050414850701020b1807410b0a00004c2c20359206034541802142e140f4a8000141c0704850002c000c1d912262558112040740d40c160400c2200c040441c0190103105115400514220389440b9800100d502c0a401001110301c454481110107415081c050314141c2c82022180c10000c0300c0701c0101107070000100f03200d00040400c03074030303003048806c0d0f81c007142040c805010081d21203031507200b01c402664010541003070030f041100031201c64070342c2301c2d0840b039039150381d141070764031a06a03412408058065100b50b0a441c50007902c810354a14520b90000c000790784d50102ca2192400407904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982544100 1250 982542850 982542857
    0x614060108152e17041505060a1503090309060c05060c0d0b030712020307091b0e01021608060a0e0d0807050703050d110306100207180906020f04181104060c12 70
    0x3074080710103500903c401110052010180401c0c116040034081401c140d120b009801d84540410001c600d68822881a40c45140000320390b6440340c40010342c0708251601b15111281001c4802d90500ea05a8010000e19110b5254407401d240c1d9500d0a484a00520344c0140c0300f034201400040910940c0c034010318000c030300c42600159540440300801c0c5024001e801070074803e1000c12000f025440d08100c004002d284c210418041500c803107462501c4c10b0317918140f10040c418194400d44440e070080c0710b40718105400c0010800440c2d0380d4004039960b11401d494841742c0920704031034144191004540c1f42291000d40d15211165110b494044406921054042d000c001c1d00b480300411100060080100203031030034091948034107107801045141000c1022690565015400030000c410700b0444002c43c10702c400703200081d180d40034240200070340300301710040ccc02600002a010446241c182001042d907080e00c8000c03c0140402e074100d0a0318031940c0103d601141640d1000400102c40a020609008540c40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982545350 1250 982544100 982544119
    0x7050f040504063b0303060d0f02010e0301020315010905150f070813170f06040308180a1506150e0a030204020705030c0703060e010b0307180e1c0c061406010815 71
    0x200c00300c9810105040285140b1042d00c1104104c283c0c0c0508508280c1042c0041c5280d401d00344000b501c100c114540042080388030740d1480c8156805000100c0c4107401c050020365032032415041401401003044025804502903200c00b0805040484110b510f03c04960b01a502d41034034458070789625004404115a48103080000e0b41d60030b8510000f0300c00400d07001d04506844564080160700b010100244003e1644c0420704000219500c0510030350080e01002c51040c11981300702e40d8030b080c00520f0b00090583d21070b201243c02c10a8465005070210703020240080840c8903421030441e21000803901b0341d40e0104140c4c0060000d4134156008248a5214404491070444c403605044d04041042c0d08c1610a00d50316000e426000400f80903100c10b00008030041d00c0603605000b40e04510340900c03440c0c450340e203585040300d4001500800c1038081e0b40884440302124a10302c188010460b0b0f80c0e0b00300403145a03003446510001c1004150304107000d030105071620140759840c1d406005103003100310704040c0c0c401003d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982546600 1250 982545350 982545371
    0x60302220303030c03050a140a1107050129010c0503030601050a0c0f0302060a06210b060111120408102903100204090b040b060304030206040b070903020901090c09050307050f04050406 81
    0x1000240000e5120f03880101e21a0300010380034089a0008020303031071207030910201156000300881180d601c01c0b441c0f07a00042214003c0444d203600e006000006020350301c0c3c8844c0d018460303294081484851800071405c00c544260000450b414001d062006206600510110300258003038400782051480a24080a180c5c4040d00c0364030070f2042e40b100030340250b0003020074010350820074000c0502400054400684400e201000c11449142c0318074003400000c50301001c50400da109003160f10852260b80211108081c0c8010050f0895201d48600d004610422080f200300b2540c5020351610120100c3d00360744550400300d192101c4022400c01c0652601611541c07010300ea1452000d07001502100d100040e040b210f2409100468980020711b92044105100b00f200003540040c24585c0b00f0303030002e211001d030b4541e01c805a51280b0280c00c0203500c032200d0320004c1482e80c1241c0c06160405015521400b842da510303c18951203081030b004054111490454400f900d062a0300a079401c54400d0340c0002d6900720b01c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982547850 1250 982546600 982546657
    0x7080304030e031213060503040204152403150608040201030f0509030c2505060f070203030708071505040305031315060305030a17190b01020a060e0106060f050309030301060302 78
    0x440381100442c501000007040c030f040400000364030154041503586017014035110400ca0b24283d2040b1410800000002002c540300d0b0f400409210000040c00d03060356031910640c422110300c52800310801c210003203001c0f1034240310f4002c3c4000c2c05001181034480c01c1c2081c0341107400f568000c1c0240d0515403074184030902d2049a11420340710714810800b45480f44101e1100e43e09025040700c400045071442250020191854071110307049035401c4070707040c2c1c0e1811502d0914906024246029515020100c0d0b54005c0c4400c00005001031440380b40b50301003c1400c2e503076260031035200b56400390006000380002200204650000030009015a46030f1800313564108601c0103940c2c0c00e030411102604007141a100c4960064501011510343c080c05800b00d1410500c2869503a81e1006189011034644401d5a400d900a000b0748143c0ca401c0f480901c54185000c0841b40a00314a22407900000c94011010030580d2040095900626085015600d035900e000c070201d01a4000c1030308400e00c08515660720712035110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982549100 1250 982547850 982547857
    0x606011d0604050d0201031d0f0c041a010507050a17030105040e0303270a02031b010f050a1d040605060a0c05061602060f1b0703080106120204032a0f03060906050a02090a0306110708 80
    0x2403e030002c14208902d100c442d03003030114211500d170185013043c1455144cc2003c0b0300203a400b24003840c2c01d9441d05034608190703140041c441800790a640c0d1002c045401406000010f5050b1881500c1c1408110312030280755549220803100d140c0e20440091005a20451104140070b0800a0104840210210750006420059041c03040c008059100c00140c1c11545c0182100200007011704000381010440c41c000340410350520005680e03a5001e08000d5a60703513407a40150080c00b005880140c451000c04c0b80681407403d5a001907c01d80700d0180020f020900d6110b9801c0c51441302d40c060007540d1203480c00008401e0b00030380740c4080808083c015482844450015260f804d00035038801c800e0b545048400b40420308400010003207d8010803050001ca0500c4400206144001810f048034050040c809040c0403e00e401034410754070080f030300200703211680d04240b4110340200d00410640d2980c0300008100d2250185a41d0080c0c00d07401b040010030044da0044680c0c50305156520f00d048000e03500c0d48816072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982550350 1250 982549100 982549151
    0xf07031817010e06072c0411040b0d1b050a3203040b06100c03082701060305330c09060d050901051608150f120606011d0604050d020103 60
    0x3e41d1540712055010b410000c0b140c1000d00360800c0d12080081c21090a80308401c1943c0305401c07403082e03501340440d4681d079110608044403012041d03110754940120013030a511000000c0c00316401e114811030100081e801c01c420f0000d40d5150940b41407000207003035548800d0f6111183c500d40500c0e0404444140100020074504405840d07140c1d24605454072210103240506454040c44904040c0c01989030481074400003183c16081041c0240c1c3e4190022122001c004034a44039403054900342109100150003803029070f032282e815111144c07440080120120401e8075986200b0401e0744c41c1358031501c0b2003d51203400c000c50907500351034100403101040e502d900614000c10b03895621020000740790420311903190000311184044242481402c0002d200d4400030340052100401880e104401c6c0c0d844030012051444007501c01c94000040d182e03810b445003403c0700c400c0c0c04224607850305401b401d400380041ca120f21004100504250401c014000b1a01d6408422814940e44000c0003110488048a48203c10b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982551600 1250 982550350 982550353
    0x305030712121112040f051c2309060705070806070512010501050c340b0406020111030919060f050a052a190e130e120f07031817 57
    0x5545007100204282000010080000d150008960360005440c0c2194041d103501640da40a40d22541000ca06444603a1070040c80c6220744804091011000607582140d200f860711a03040c180d0741400f10400b441700c58401041800b03c1000841c210307160010180080c01d000e0070032900f032030b511048040c0c40c1010649081c0023007140400c040540f9031403405518054102807801508050040000c00d0344ca490070282c000c0100304210040f180340301d01c40e940c02110f05042c84080320580e6164144005684240941c40042d4201511001d0072080242224017843c4070740b00070864451000c0040d1194854040c0444a89440380303042203104246000312402680c148500255038181145007130821200800401010881e54000c000e40769081002c3c2d81c4c0c45540c03400c8004001c101854104c034449441e40481354461010301c4002da64102d02c0c0c1c030500890700110112540d0300c1c614541c030003003409411185601d040041100c00c00207403003111074020f88000350844000d161b03140c1c5580040b642d01c00c50300481e903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982552850 1250 982551600 982551623
    0xa09140616051602040902121b0301060504052205030904020f1206010806011407080c0102130905010b030c0703053f0a27030e061201260705130603050307 68
    0x8401c1d07600044030003035150410b549440e81c40070031441985030f02d20b006881980e550380c0d20340564903441c00b80a02c0c002581d0540b80700320710548280d00c0082001113142d000c9d6203020408225414644290b40c05415410750000788408005040482c0c00c11601040724503000911030580d01e0385a50002d010200b00f10190039460300030802c0100322113070380180000d0410040700705020307145e6008194403241c07143d5400819503a10850030710b030100c0c2c07150345400b508079840002d407800380842c2c1c18000401d603410344000380140d0b40d031004441c005000c01e60704031080120800c501c01c0001d02480c01488682019001c44450f0040303440805e0301714920302c1e4540ca00990074012000c1e030a50400009500180300d88040007541c14407140786d80f150801c00f07520200c84102d2801c102c24075020700000903429400404440c1d50700e0fa000c210407044035082c820480c0d01245111001a0311b0915600c41e000c0b03d0220004103412031400b000c00030702400c1051800040381c1e45010200220300c0900c02080042d0107001e100d0701 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982553956 1106 982552850 982552861
    0x1030c02011517071214060c093a0c06020f010615080702160308040e22060515031b0f0105040617150301020d0b090a09020312030a091406 61
    0x224440241040b0100540307002c04c9010f11b81c0702d03015903d0b5911340c561050b02d240103d4200395401910051425811003a405040e880e40d208035401a504000010a01c0c0309035002c01c0c0d040d98440c0c2010010f11065804010006030760f0413480081148916001c4200100040140302204204c02100418003c42c4204414824844202952000140c0d070349086038032940148a40151142c4042c00034550300ba0a0224001a40d829201e616850703041d0750720b8100501d03000308031200b0039600c0403002030a46c80801183c0005c0521042508442c0c0d8038004100d1002c0300c0a004a040040400c0b0900101e984201301e80704408c5000d02d541129240e000c3d950496580500400350190302c0850f88410940a0303820103a6102403d8801c2d04054842040250944160a1020b50103610000394600d10501e03c1c2c00459000780d00c1c1900040c1c0c5c2c038045d80c0714080640940d11450700340c3d0001d4241314 = true := by decide +kernel

theorem cover : BRFrame.Cov 982374100 982553956 := by
  have h0 := BRFrame.cov_init 982374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982374100 ≤ n) (h2 : n < 982553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
