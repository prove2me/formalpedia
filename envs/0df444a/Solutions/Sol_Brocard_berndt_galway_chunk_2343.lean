-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:27.159234+00:00
-- url     : https://prove2.me/submissions/15aa8781-462b-4497-8155-58ce0cc57813

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421223021 ≤ n < 421402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421224271 1250 421223021 421223029
    0x20a0b011d1003030f18080a0303020316081605090d050613050d030209010518060d09050c03070f182406170a2315041a0406170a1704080d020703060506 67
    0x200c1104c2d050f440d500100600144119903180610740b060404110804c00014906020003400200601070b81c0c0060303c9007030895a94621050006aa004001040c014000b404c4d01000c6c80c0d5074042e12b05d0400c5540d036050311020501011000c040030b015405a070702001a82d02038002c001207140d205a05684095405410540407070040b0039001c4d0015a0074041c074110351202a0b4400e080c003400524090809215031808002d840781141c003120075030446408040c0c50305007005803802404070340e80c1e502082030516000d1400c8180c83d4910360412a216492400c0c16080c0c4141c00320300d92605c1800e4401d064440201030180301c0310038104401c070307100c81c2c0015000d116070f44a1b6103034424980480c0e01501a001003c20700440d0b004c1d20048141c0d000c0c21100342c40f95150b1040208626840d000510f030140c09408000849541d9400003540303007117582000c20380110102e88204421390095100058410b421580d0250303020399000a903540c81520300040c0215000221017040381d01c255014041c42d50390341c02740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421225521 1250 421224271 421224301
    0xa060f060f0906050d09020316031104331505040602060a1803030b0604090c08040203100207030206180a0807140c060a0509091e131104091e03020a0b011d 68
    0x1040080d0b4a00418400a8465001400d4046441c500030a081115800007402c094440d100c40c090040c0042d0100300b080391401c0c0c6065810307802c07141084a03c2201403800641080c1d01c492440a00e0300310030103541c20030025000380c003501004041203a094a03a01e0b0240090b4064050140581300350340008040078480c3c002c0c204000d06d42c100c0541200050790b019000340200c0200268810824400854100d0203449001c044841c00d07035505480d4103060040c1030810802d030460300060760042100d2008244c0009100c3d411000f0801098013141e8608407650500804040061041c400061001c0501280841c020310807031200e42901c08540348102004003500c03404401c3c401180041c02a155145004034550703910042c0c18102000d041a407490315188881d00711054441610749a100c901070000b81483c0c401403400a071800c011403e0662210408052490b0748582d0803100c01c950241014802e003d004c840315840052440256124200010324200700301081115010600008814100036420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421226771 1250 421225521 421225547
    0x4030812061e190306110a0306080c010503180109050105042301060807090f0209211501050d06180210020601060e09061e031f0c08070309110906030c0402030a060f06 73
    0x7010100e909140107000051041c9400f0442600c1074660000208100340a4a83e05480307080c4099a290346144000c3c04464954005070680c0d40144515107403641c003d0210384c1c0040003408040c3d104030304d45004501610062000038011350810003071100300f051702e0401401c14544100100002906448450b088403024828407000354000e01040001061650041040034880340016190041c068042503903908040f100c407800d201d503645448101403041c0100c0040c00d029007482103442d450540000d800e0b9280840141945030342d2100c0d03078580501c41c1d12146400b5805402e98500c503512031030103902d58070244030f1640412094071741c001861800103c02441403d005205e45203011424011035104005031202c01e405201d05c1442c1000300d61000f000c0d014441c40c0321008035551a6540e002008081d01174400c109060800070000001024044d460081c0341c4240d4081444d60b6450700001c1c82d144ca018203546d00584004103004224485401070410307100c000800307821080d0780b564216800490454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421228021 1250 421226771 421226809
    0x10218030606090a0c03180507090c05030c070201030c050c0115081606080c03060a12120905010323040303020904090f02040b060307080109050903040512060a0e1c050702040e01020403081206 84
    0x1a42c41c0400da4442c91759031030246000564490070100b14826428120425203281e80101c00400010049003e00b55400c170580c0351041c15814600c0317580c5458040c08200074141a00c41240340c85041c400c1003500c00c1c8180e540000d01c00007100b440c0108640c003244c0101c5020780a1103240040c1e078102400d803501110019034070360101c5d84e9070200e64000343d0005003207251b20a03003000d400914183c052841c040a03034080c5114210401801c0006010000590700c0141803504010101110015104240594072000042c00f0781c19038851804800038822400c40c0c543c02468808140b003880310f1180980d02051003070720100071a080d0002088490b000440d8200c3c00500150018040a40d450300140c0c0c100e032991049a0419071180c0c00615041ca158503002c416520140420000c560700e4018009034500e92005018108402c209000d07040d408865110b092050001d21402151aa41d2100340794500030720086458603120314103564190700c9149070794201d81010001c2491840c000000c500f01006540f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421229271 1250 421228021 421228039
    0x7110f0c15040b0a1806020601030f0303091a071701050913020d150216063e0c160608071803110f04090308012c0c0c0717010218030606 60
    0x4810419181e200e400c041d042440103000003e905410b42015094100302601c4200c4010480e00b920540700360107a00c04421540504010804603820000041c180d035094070300400c03182074504115a9040030240c500340c070044001c0030000c40a9004007141c80c1c1c982c54090503032581c1d9981c001c01224200c00d91ba494142c81150b2455001481c11502001581e0b20480d00d203c102030300d41e015041240c2002211207405611000c11504100040c800d000304c50800280760020310f4503000840382e6501040100034000920070010041528414040d2282c1254003000c40c0c2d44000281b48550009000b4460540800c00d03070400308041a02560148c0180c0f4555802000c40310b20f581c407005141d8001c0703903016410101101f40035101e41c5441c05481001c9003e611a502954901210400d00d8903101c40326000342004518002030404803082c500b84c025544001058880102c5101d00703040000c0c035840006012466503803084c0a840640141110080700e940f03821601080800f4551221000c0b90384540c004080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421230521 1250 421229271 421229293
    0x43804030504260d050c100207080301050406060c03081503010e06130c0e0c07022202030901050910020c0a0f080c060403020f0106091b0f0509030d020a0b060607030c030f03140a020307110f 83
    0x1c1d601a101140b0f0034002c8401c01201444400c040f680709c0e003c1500c1000b00000180b00c0b030705050045400804d110f140c09900344801da180101800b001030113a034002500202d04140c9a0303000d4000c0094000d00a00303071303451802d0044500c45c04510b0000308803900b21204000068208000004d1842400d810614915128841e8208010b42410f80e442510b08011941d585400c08850710140d84565005000040c1d142880e5001034900351040c41e44500c41c03401002055a015408210112a103502803910406101245004d2005005140220041c0d03c500020002459400038552000074041c900801910380c032006101c09441800c040000b580c1d030709042c3c0c0b40c5000e10550180c1d00c460414a015420804104002801c14803c100b0020040c0d02030f0040105010301d40615580242d801c03a032031441e200c40c0d40e501903c0030f406200040c0c00d0140886551180c18025084450000d00100801d4003615040d00800c00940050790003000084013902454005540000d00529041284009080340001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421231771 1250 421230521 421230527
    0x109180803190603050c010e040606050906070602041a180904200a0503010c030f052d090a06021b0c2e1b0b011a03043804030504260d 59
    0x8007412089901e802001c807450b0000c1d907403040502a5110b03401030704444100782c0005118168054460b8403540c40c10804201d000c0d0004202c0e806174006580651701d036411401c000000340255401811903a029200a80014602c24010090145103101c01d824100c40c03101030040303c1000720b40c0100620b0310000003400380c064035650036107803d20040403000a19103810100e401c1d40c2c5a000b200c0c004c07036240c2d07a012404040718060b00360302000017480c4180240e4410341a18020718a94038240000030b1361404219010003c0c0040e114040c1c002600f55502e00d4000140103070b0804240da01c54103400350400c05000d40c83c041c0707202c170075840080d03c9850803054110170003002d00d83e00304400001d004520b80108603100d45c2c1040205c0d002d004481d08281036240074404e41c2174410701c00410300400c0b020800c10000426221003107081e80074601800e601c56264510130303948150a100c4100c803040382c2c40100010103502c54000c0c1f064034844e5004204984049407461402031148102240e6608644110005184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421233021 1250 421231771 421231777
    0x10c0503070e0d0f0804061205040807030807050f030f041707030e101206030b070e0a0b1c060909200307080712020a030b0708090d08010b0a2f0303060901091808 71
    0x500103140948100980d130300c04503012915002100e440704007150130807a8a40041b0509013844140d442070050389825901d400c142c2c070034004028180034400012541c4284580d06540040007102c0c0c0c20780da241481400c403840404220b808841da030303806410b100b00300c491070001e845180341c0c5504c038182201042c0341080000340e0041a44002c01c40d568960601c03d29050088000443c025031244009041400c1f0080c40c082814800074012000d450b81048441a0309044030150380e0403100e82a024149008044090003441e03020180b01c5061012180501ca00444624040c403202e4003401c45401e142c90030700da1510041c2c81001c207541c000000c01c0000c10700d0071805d40c031100d20080004001315120303a51a610b4000640e40440051180401c002d0080790400c411045240a030815400c9076142980d89403003840352005100400c0101180c00d41558085c46c44101c880780b240c400047d41000c41464285e598100302c40f00361003103140400001310742801e40300b1a400e401c10509580d15400312130312440701581c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421234271 1250 421233021 421233047
    0x3050a061532031209040c0f2106050d0503180a080304180e03160b071403130203120a030f050112020a21020316030203010e01060807260316050f010c050307 69
    0x4461018280402d5405000400d007030803131901095180c0c41600c00344021510052109018081c64411400c4030304c1d0054076402e542c690300024450711001c4103603a074019103c550b01094101d0782113204c4800b001400b001a201e40c005449100907200c05a04c10030090010a104060041e00100303c240b1260002c150300e01c034480d264190100c0c040380c500b03088074915071000302e14090a0036260802c03010011050040c076001a40e91800c403480100314640e00619210107001d40c0b903002c0e0800521002c40d02c0c10b00104011003103401e100ca40710f400900c0081c0161441001c0c0010040c40c1030004502584549142ca50a64010b4a00d200c0f0a0911002101ca0860020000c440071003929040c401030790104442a040341e14040c0010540d032662051500395103250102000716414400c003804041d400103586030031508a0229040c0540c0159103038100310b02400000f02c4580030000e003104801ca815510058000e1260044a1130722a031980f049003250306001184001450800200b6001c03481010405115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421235521 1250 421234271 421234349
    0xf032d081c06030f050601051e09060f0d051204080f1603030c0f06021c05060925050f0c010c110a030e0f0f0301050a09020a08070308030402040c03110403050a0615 72
    0x1054503621080400c09501c00105c4141d48240c00501241c2020400080803c20b070072902020b4154940005204540c020b0201e070046240403501c0289076142c00e199808980c100068444200e44081011143e074454000c000c524415000f018002c4000003d05444d50005070b201c0920242c00c0d40e8080300c0d43da01e003c100761a21700c0113010400100f11248000e0030803186c00380e12080c0104002c40c12a084c0c0d100284a2446494040c08200c90000315400e45412005940c1d40303a0a4645c05c884140c0b41070144004001c00d004c000300780e428142c041580b101980cac1d081c42d1243c00d00001d031480c241c0e80d40c14000c44000c00250840307c1da104a030401c40411117843d8002050031010103180310100e82120800c441440d0016203600d0b4140550400a0404018016804c0030b08040707411a19041c61611024100a002da5a10b66030524100c0c41b96100c0170b14110402140c40d0340740c0c0d42c3d0811940c6d17401c03458815118680703041c4015407840007450300c840460300d040304101600680591490311034a1074003200045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421236771 1250 421235521 421235531
    0xc0306010203221503090f26070c140402040803221205150105030319050c160b0a26010302130b041518091112070f032d081c 55
    0x6042105659038845200f4030103011654a491001450020285802c0d02070514080000001c103441144215a80e40c0209065040c0c100c07450721a0440908400b20811040d000b00d15a0300f0025403642c0041207807a1f03030b902034030f51050200c100b004a104a02c203034542503000704400003030a685c40903400031209050061101c1c5603039420941c01c100807107410460f60f0317802c4045640501c410825005024040c180e004605110541d2412911501c516241405000d00828540c900510030030007002502c034030003000c40072207944644043c41c2d0307000781c1e071540042214a86024140c4146203d0044846000089100540d2a5030240000e00090503005103007282c4a440b91001610b47d8000e5403d071300c0480c04a80c10591400c0382030041c02d804072007460b103054201000b000c0131414006ca440c001d1001151024810b00c0301d0380c80c00e4500b000c0c5074404400b00b0b0380c440c0004280186c60050603e83c4014101d4124a40c640e030000c840d02e1032607202c00400341c0c1014070000c01d04855022018200906001e40061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421238021 1250 421236771 421236787
    0x4030f03051c020316030b0102100f0902060a09080f010c0806090a0f1e0605040e06010504020c150906040c06021603150b030f070302010e011b020d020a0b03130311150c0306010203 79
    0x84140908990030308083d00042800610f040b10b084c1200ca105044c901006041c5803040001c2d1075001d440880d101c890f03125038140060000c19807010400c1640203004c0d03552489a40c030041c00c024058811504103018900d5403c3d45900c040c008c40700440d0055a602c81140e55080410403502c00140c00500600d40d01c4800b07105850a80c4030ba6a420301403040c402c0036900003060400291a165000f4074003503402c01c825a0f4003d0000a401d5040d1941294050385442041912a03c0d112080d8909100011200c0070f00a5000c00451661300581c000d06a044403951280e40c140e9032483d0a1040003000c5040040400226203107800c5444881c10340340c070100d541842310300002d02d4034903000096159074100e24020401c660b0440041c12000c0b1003801c00040d8903210301050034803001d502c1c0c8003a0064080c0e514150031541e8081a03c00940340c810320240c8c903401c0c81d070349880440011100440214074444010004036000080070f200300c00d124441ea2000f680d030f640c010f100c542c00c050318460552009000e890 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421239271 1250 421238021 421238047
    0x207081215100f0503010e060f0a0902030403030515100f05190e030f120712030906110c010c030605031207020d05070b120a09080a0e010210180303050f060604030f0305 74
    0x107406201e001d4a09114011000c0801c24641c21070300032001405002200100f2580d080002e40741115071225030b4203c6560b42030302042100d203c1c843c0650b8441c995107804150050243e02031400b482c0a99401c02c4217980701043c0702c43e805070136141143d0103070440d03469100c200d114032030b85030119110b4a4a41e00341688030343c65a1494442d1400380e40410500c0880c502c0c03604040101e00300c4c0f103400c0b0004208045100713000001038402c00070054803030680980090845070080c0c010680c034aa1002d170405c00741960b0854010075400100c9404225401d1220041c00716100b80150170030303140010003070a80c1c004580803041082c0c0c09404202d0300301e14841068808140c007440303400d005005210301c1a03620808940182c2c1c005d80018007240c4890703e001e0b900380200d08003c042e40c421758010f003080344102c00780300300507171034600a042e0b165911401c103e444001022004180e0201c03501c0b91302e060086494594200d0302c0034078110f80ca160018014441007000c94000c01c14500294006d080a0f071070070309515410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421240521 1250 421239271 421239307
    0x4350a08041809021f120209150c01020c031314010f021002130e040b0402100f0906050c1507020f010b010912020603070c06020f300a050907090f050a050708040f06020708 75
    0xc0100c00600c908840da0b0103410004407071404206ea0401c5140107401000034411745140d81030b141e0744010200d60260910803d5040712494608142102c0e111001f600700d108402c107050080d850426810310344016254015982d4801c155015009800b454418000a0b0000c0d0003404081c00c2001c0031030000a80c0c1c00c0d00403080d0740128024100d802c184d25041c0140610b20012880f14420041c481d480014941da100719840161425131800c02c0c0d585d03015200c40c3e86000070003000c86040b407425106100340c032900080c901a03207041c510000d0050144030307001035403140003d03c00d52a054440d4515a001480c007080156440f2a0900348045e0144054560358101c3c1c0008683c03141d0241c0005000854601303e500b080550032908100c1c1c1121280f207200b0444070784001d8041e1402c0d80e01e47d070200307488070310601443e030240072003d00030802000402c1d000c0e8007030501551a075962074505408100e450b07115400745403286400502c003078180c4502e651264001c0d07011450030340300c25000b0b00a00f1402a00d41c004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421241771 1250 421240521 421240549
    0x7200d020a0b0a030b030a0804050f010e03160303030c050405010e040e0a05030301031505010f141002120f071a1b09040b09130c1707060e030304350a0804180902 71
    0x8003503154440803078054211945c030115035220340c2c05601040002000030b1b00311000e0352026581400c90080840050b40d00260b540304242e03050150a1041004c013801c0f00400c02143d006c0d40e014070070403600344401c0c2c8062083d07026140c0007130707450b0b000e00c065814a50400d008009003901150618020360301c0340e50440d0000c3c1c04c21210540c0d11001090f40d0300a50240f2405410031000f100700c142d103011031042c00c00d80c0500c612406520307441045680e00340207200903017a142e540309860b03990b03601c4015101c44552147800c0849004600c03601140100c001c4401c0c2610070501001c0b03445081000c64010405904510f03901a840b5486880c5110607448000d5983c0c040c0c0010103c1000da940d035171525110ba004c1c1c64019040d042003800001d0780c207007800188a400c450042c1400c0e10941d04a1000c83d080d4413654005003c0d607045c5525a6424000e000510142020304c81d000c0e4680e80f10129009480b41000c03400a40809001d0001748100320504440c1908451442400520301c6d841e0b0340411254603000c12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421243021 1250 421241771 421241789
    0xb09071b0f1406041b32040507020c0420090108190f090204050a0c050322060e0d180b03180f070b09040c031404060908131410030207200d020a 63
    0x4d1000b00590080e80801202c10070f0b488003402d13818074940c1c80e0b480c0d5051005a00601c188081c140514841081c0c2c8101d01d400944180706614050340007a41d00d43c000c4e11001d00451400c4104000002240302150700000b404408a10b07054251004640c0110003400d03640e600d101070828000c5200e4140b10784074068052040c041440300c040c0c01000300f2948014644018642001507401e9442c0d4064100c95001205415400351802d800940c1e40d41c03030306c0400000f092941b500c0500c001d5000000390007007051216035a081c070900030001c141050300c01c89228400e5072040904c08625800840090f8002482c103040c01c0341c030400300c0d104880740341445580c0324240d0301c070780010a650f03142080d0049420002640c2010b0101903005c3e15003841a070401800504225038a114110030480d008049500f414040400507001c142c884005100003900c07000701501ca4508490200c140074041d0098501f07854020503040c0140010100e222915140e1400c8c1582c041504e050798001a565404000c0c00ba0071211 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421244271 1250 421243021 421243033
    0x51204050a0303050117060105011103070507030606090b061c052203090602100b06040e07020a0c0f06080106030903051902070504020a03050906070507050d030b0402091507060b09071b0f14 83
    0xc1000f4084a10681011019000404007803901e01c200144141c1146c10a1030101c0c036414042c102e06080d401440e800820074040c001c000824840720390410001e4035020a01044414050341c10010701d44643c2d0702004051180c007080348076421080e440581c2c4070321140608442c0c655008450900900d642d02c00b00c01152445005000342d50781040801645044606c040000340c0800f00000c403980900d01c40d82c04500e10100005030304905c20311010321140d03406000380c41d48544504048004220038007500002440321360002448031301c00d019041ca10764240e15000e1408440041030350709036028036101401e52040e02030000312601d83e40700601d10b0804030395000171142400000e0300d08202028051000304801840110f010500200d2070b00050031450400184280301000450007900030072407401c0e40840f0040090301c0d0420348000500f9128402c03041003003000003a504000306402e003030312600300284215132862a83c1f6051100c418070f05010b10000c1030001031a41c0c0d000d2502d201b83d00000740c1c5030848 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421245521 1250 421244271 421244273
    0x130803030708070e0a12050c0319060b0d1a101e050f09042a0504090b070305100326071b03120f050d021602040f0623030c040903051204050a 62
    0x81000e403c41c00f50300d0508403035028100080c50350f15032405036080445401d4043c208100040102c28a05ca00140603104001a12814405040c003003010030385241b414200b0040c170901d0414400000b16a010800d0ba240c0408089036900845c40104814614503c0140200d0010502a084d484040006110003010350614050040017544030840c1c2c0e020b0000001803000040f04000001346001c2440104000445d1030003140c20203800c1c651181d908030345041c80000c01d10100c0900c081c4520040d4505200c1500c0d5400f500c03d2010b0203100c090082c00d4529050340c10034042003041ca40108201602c3d074141412034641c100591000c1c000340380040554a000c1041018006031034000003001d003072011300b035064004050514452808001038441c1c0c0004c000004203594400c1406494000c0d204010207140b080495000705010f01074003460a0104001c419a12270095210032204005000741680001480500015040c00a0101c041c04014403103e48201d02203540544218003d100420700031200b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421246771 1250 421245521 421245527
    0x6020309010e0a2a0b0c0d08010b1614070e01170c03030a08071412041b05060405130f020412120f0e03060609060316090905010b0109050a1205031308030307 69
    0x100380380d94000c3d42101c0b034010081040030309042c00341c40c070001c1c0e0800400e010b01400d18000405401c88440542c020030400c00121002800125000c15511000f00300d03602c90f020040c45019004500600c510005403410008401c014200d071041c1c00c10302203400c40c540351103001130050b07000d801003442d03450141e12001400350204002d0704074000030fa01542c039010041c480141400700c0108880c00b841000c19020001b08825070860380c6c01c0b00b10b520000c04a003050f01e002daa8440304c00d50b2200c001102c50340d01042c079191000c00c1310202d9200074084540311003400300c450040d240c1c008615407601d42c24030001540500c96079a00101b207120f6055030034400200d48001e4011b001034003081040011403d140f143c4c07a103001540c9901300204803070008880c0d1710200000d1a0121107a200b9980c040b070110f000802010513004482041c0c0700e04002e0060751880f400454100c00e85110305640015004401c0040c00500550000380358040c00a80746000284031440396568103980c800381c02544000104600168 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421248021 1250 421246771 421246781
    0x60c051b060304121b030203070201090b0c03181203071b0e010b120901090c060e120d020606120f070f0608060a0302030706030b03030903010c0908160e0c180405040602030901 77
    0x3042404880280e03590601040300d6000090000f031043d80c2490400c40c48074010507481e02010880c0e000030303c59202d01d160083d101e40211034200d020035002c030b4022603081096000d0340c0d10540f295005504000850b807880c0c100b210800415604000c4046111001d400b041c0001c100d0b45020340000c1406100c034108440885016a001c0b03400350f11840010b02030003170884219100140c0d689040c0003213807500001d0130b005048016009002c152580c03800540d480e00032107252660b80081700c000c40b0070200e40c521540c588820303410369401070b089107000541c40e14081d510707590b4165128080307943c1c000c100300c81180341800e00d82040221220040302080b503103601c880300075841074003580d00d85001499a03021903a248a140506024141c99451141403030b101002a07a021140c01002400295188030001c2d1410740035015480da00e0150244c9620403240f1601244212034401e03641035000d540b403020f20304540c0c00c05010075404020003000f40d00b03030707554a008842c0264040d44005079a401c1002d0f590342164 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421249271 1250 421248021 421248043
    0xf0d030504050a02060a020c040e1e0c0d0b0717070203190201181221020d0e1c080a06091a1e0f1905030f0312010e190c02100204060c05 60
    0x1600300001c00c00040c0e0b020580a0070b066054401545a49a0b0741d8180c2c00c1c51001c002d5260060b1620440d11304042d00001c01c40c203d540c2140004074400d034101c00ca01d85498188101540110005800d4000604851321440d032020085c681195481748600030700031200783c15a240c0c0d006900c0440c803024003002c540d100481c491490f00080105414555803c0104543e0481c09480046103a414040d000c5c000c40c00c15140d04403448015604501540454000350440f11a001155181142144212000044202c81440381c003205201603003000300c080b500d61400070b04490b4500d031150320000305c254a074020300c83c1340c2104c1c1c406038440e5419001442600ba10300380407154092007080d01c0c0070040d218170f501011442c20681e1507412029900392640e4201e039555200c6600761103041001d030f0207100c010015108403d14191421240c0e6a50580025010400e03184429003460552500005507081d278405030488411303005440b04410351020303100c00c980065003c1e0300440c070300c0000c1c0010001c06101e6000b40ea = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421250521 1250 421249271 421249277
    0x41404060b04050c03190509100906050405060a09020a0b03150d03021c050a120207082503110c0a050405060a050a0807030501051b1c0212010308040509130b060613080f0f0d 76
    0x1d0314000c10204007401c00401b02c030303080c3d81d5505d0100f01c5410381407200b4804009403c03000d2080c02990721b8200010702c8200d8095a0074040c03040403030902c1c1c0f03050240280c2c403034004080d09842420300840b880705074405000140060854118160f650715000e0304815242c1c0243c0240054094860660100214048a075010040e080200303001582e0030034000d44501055901c01612140985050b000e00d1040319006c1d41444c0e44d610b51034501840802c20889402d03c29900e2083e445910b460b0306a950480c2c22146034009200d80741031101e4100303940180d5001c1002800c0c0d000003541d0f01c1c040f0b0800d407019000008a5082040c0c240144402401078a1704420a20f0303680780908000c3d03081d140c65009240880000c200040c001c1e0810541d60780507585a25254112040c3d03950392841d20483d00d902078401c03940120400360010790039255090b020741748160840040d02c1c80d69a0f280070020540e0004510280444483c81c0220340303550100940403801d101e0b40d000304200c0c3d00c145512031520307000602078020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421251771 1250 421250521 421250527
    0xc09011d18041a040b0726010b0c070603020405010507121e021e0a122105070309060c0f020703030e0a0f1701140702030f0a0302040e13060b2409041404060b04050c 72
    0x1400314503446600c201c691820b100610310114104d80c0100741c0d5221f0001441ca03503c00481c0100412000b0300d200c00400d01120311442d135812064080e40628402d05010490610107030380850540c068003001c503640f5141218901c0c1c12a0000e9070300c080200751540059002400081c801840f0080d040b14840103c001003413500140d956061041040c216448100034241040700c41c80410301c000c0003904d454100b0244800e18002000a00034070106100b170f140b003402d1441e004011402105c0c0e425035280294042d2081d2410b50320185c071008140f14a140d00705c0740c020000034542c0064500103025160390002500c0c541d0349200030070b09481e1125800c040d82c01d0407600340010a5000000c40f1042010940d2240d101e409088098000340190391210300640350000400c8200d039495001d9140c5240b20b448200181b982036410301585000c511564030407a0f1200c250a0b004140000203048034040c01040032405804d440a003540003001510120744ca1070702d4203100b00040c9018001c0d0384c0e00c0300c000303160142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421253021 1250 421251771 421251773
    0xb06220c021e0c1318030c02030d03020414010806010504080718060e01060207060e03070f080d02010f020c0a08090d0f1401060e04030f0c030c050f0708070b030c09011d18041a04 78
    0x1854001ca01000c82c451940c2204400c0c4490340c07070b04148030089428030404032442d00c5c0d00f0003410304800118103c1c4240151030031890a40e009100361807e480708408004900000e10006445003800900740d1414040d06000014403064100840c0b00a80506041036110300030080850040d0390300f40c3c010408104500c80180805c96000a070721003258014a0510b114003040400f02e8202401174000d140c21b14099000420b81a20004002076069081d5008100c01c1d400403403000308902621250f107035682c200c83e03400ea001c102d14602400166800030000740c2d12203941d42e00c60080700012001168515012010701c16045001e208a4005100c10844800c0d02d1621b5035001b060484414414000d21090b0303810079041c5889980b00c070080c154040100c491411143d00450340e070384224450401103214083e07011940d0911355055074003c260203100b00e070901001c200191101d021a4090600e41c5421011a0f90243d4404100740412100c40495003c0d03400e050822860003c4000b800c0d540340c1c0c052005000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421254271 1250 421253021 421253023
    0x10204150201181e06020408060103030f0f0906090b070503190c1403030105091314010608100b0307080a02090c3a0504030c06052e060f1701030b06220c021e 69
    0xd010030000150404c81c4184502d00f400c000c0c001d42d00b068036035100b1500040708254000c03081107559091919550b201205000080b140c2c11000d01a050000360440001c011034100d00000d040030310301c07c1d03041c7c9041c07007402c1440300801342c80122220000703204402080140030303003001c40300003001c403140140d45550305003400700d4003140c0c014004402c494201e4400c00103220308290703920b00000c0100003e1041035a03400d012581c820041222104840c58010224018680064034a0481396110040c01e240c00040e020003451940041c407142d41d01c00100026441d04110300d40c41da087e10100030294103041441c0da0913242d07200b50014000389181c503086c24400400d40051303a000030a540484045946d903501c0700680c10407490f1141c00300542651407118074031101407511200a4698a41c0c0e2200c0c2c00310788000469901840342c000e18800800c0b88018030200d10b0f16203007590720601c050f0455100340042d00e00b40501c2c500090101c1412603030390802c0742c0402d0707060111000340b00d9044100c0740c031010341140513 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421255521 1250 421254271 421254293
    0xa02090f0f0c07060e0109110f0a0303091715070c0b0109060602100b0f1008060f18070309060b0d060c11060610030b040b090f0907080109031e0e0301020415020118 72
    0x40b09592001090070380402403d07400204200d0b40f0200240401c94440c5440c6c0081b258180c2e01d54030a041c40200d40707440c0d0403c030001c5400c81790560707141e0031300a20307090640722004018600c4041a000b0280221050000245042d0007100195681a451002403c010b4240c0f14183c110051940c2044410801542e0004881c40c09441540000404902c0800011924a038603112542c1001220090301b10090700450507600c250026076002d0780b8680c800e0308101d00c10036068100740202c28120082084144642d000c400c0c0944550340015104043c40001024504a444111400394840c584089407592040e9101040145031009240707504008001404d08a031550000040542e1500e410301595103542003209200c0c2d001e016164241082c801002e070b40c2804030707414402c6100310300d80001d501505200301030060360590755041d0340e0010f107480d03161440c802c1310081c000c108101100020b5641c0030b1008000030811808203910b0580d0040010703095803035030284013040c2c4104000c030b5030220b8104c00803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421256771 1250 421255521 421255531
    0x170f07060804120216121e02030a031416060902030d0c080418060e01060324030803060d020d05010e0c030705060306310e030a0909020903070902160605090a02090f0f 73
    0xb442c843c0040300d8000f249000c482e00c40c1e50f009081d0050000070345034648020300d40640d0198124038034800c03001c0c031440100110100025051340c082c81c201d602092092142c038a021210954881c5003140c80c912039a000c0c2e020040c259810f6643c0c0c0c80349421440c080007240c045403101d0034107242200700b5885510050080f4450800b04403140326411017071440c1c41c0e0043c406040c50781d1825240b561285801001003110700381c003200c04409550421030610b8005000821079500c60840e031f1450b510324052103000640074900301d80042c070701c50002e40000c500b0302030564500c0d09007006040185100b03042520704100d545c00940200420018040303d038880c001d94142500513113001d100c102e00c500d4000d00091104426440100e803030452245180744022001700000344403079035000321308c40d25605018101d1003004034083e41580142010407081500e074016102e11907020650f40384c040038076152207065440031950030295401400d0980210700d056018560000b0f42e0078a103104510b80303a50491003504000d40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421258021 1250 421256771 421256783
    0x1d01030b0c0403020d080301050109241808010f1b0e130903141615110a0315180519050c0301090b130f0f050603010b03030d051906170f07060804 64
    0x11003110070101220002d5a01034420140b204c1c0f00e040805454000f80169400a01e02e03003000100703a0380c510000c0ca509051000c54020b0199488026100c11018201e00c00800b55580b60000e110b40003072080c48500c0000007030100700d01c402e841140e030f019200000c514050003440c0610341825200c04041e0703094105a400f001030607c9041c00c041d540301c0c85a4030211515000080c00d844880710010051322107510820301c0b881408582086039058901c00c20711030104400034070403000200c0c400e1308007052a403020880030003210b0310342c1c2000400d13401402580034610744480c18450300c48c03052202400d08181c841d10400c49424400c0d5180c1c1d481c8010b104200d440c0352190340c000c0481d40c44411f07402d256603800804021181d42006070402404101c0c1105802514003000110541010b0082c001e080e800140a9440c02600100303800090038060721202030b40c0d80d03842c25803001c00d181d072145501600c10420f5002c00c800d40c02c0d08151520261a100c00780b43e410139981040340c1c40e001070b0541e40041d4860 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421259271 1250 421258021 421258043
    0x9050607170316020705010c02090c070c0f230307030803040807060e010216110904150f090f0b0f0705040302030606010f111c020c0103020c0303160c050706020c01091d0103 76
    0x10404004041109406101c81c0c1400818040f900c070050048100743e5200d5003c0d2001240d540005540c996076409003c0e42242c03080001031000c0f04040024000d040c4078200e02d038038181d250103424440500e0368100c1d4a0301258552400483c2c52228609481c142c002c4008003000c50940e66036079541e000150006000c083c003c80c4003401c001da00d4200381c22121202c4001c64603620340061a8104040090003910545448441180356040c1105118415a00010307107aa111850b4021040145802e4443d1051942e852901c040002c042680c481c5500d0701885000d21503051450108121000103002201408400c1108100680b00460f2040c0d019100b402c0c07100c0e1101d010081602e1000d0441c903e8122800760b15082ca5229401c0300c10f0b41100031180d8200c81030f90300d0003c015030407803241010104a5070b10a10000b07001003d200c2ca480301080042c40e001594843e01e6644520384100b6400107005a00909011092941e001111000900e4050b80640c0380c110741c4014209403000601010740041020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421260521 1250 421259271 421259273
    0x72c15060f040b0304060506040e0f0604030e01110a060c18060e010c08091801090614060417070506180103050c0a1704030306080a030203090f040621060f0204080102090a0501020d09050607 83
    0x140142d030014000100040d079240380520b1301c0401400300301d1701688240d18051480d0451034000480400c0113a0410041c02a0b40396500e041d04d0400a2048503410081d50b41c10007141c0c07107420b028a5150307904c13807440854415119803000e0003501d0021040c9008142c0c44104009030740c3d1000b00038174804020709080310000302500785020f036481342c00c1059070401c003800440e42002641d0340e85941201d8820408104d1561212440c03001c000e0045506a4040401d02c01840b50b41d40d601003100d000710106085035001541d40f008110560002c0f44032500d200d0107444180700c03d5801d400317a9640003917040080ea03c1d004400c1d40141122034450000c000d800c3e2148002420907000f83d2141d0040c08a07802280c2c03400d001c070701d07000f0b689030b111420190007203160149801c01410240180700a60707020030060510301040908012003074a21030411780d480703900d03850004011000c910044c4050004000056035031883d000034080c21400c603a21190441d840305041c42c2c032480c0c4c40100181901d4040302d00d82d83c0d980c03031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421261771 1250 421260521 421260547
    0x1e0c01020307060f15080a0203010509010c0e0f040f14010906060c030c411203040c030201050307050f0a0c0b1b0a05130302180f09030a021914072c1506 67
    0x3405e0301170b500016190086100c000c0011480c401074401c5009024a03598540c000d401d0350030401d19180401e1010741902020302c4c040511a03103400c4040c0c070000c0c014040b4000c0d5401c2e134201440d0410104081c3e00180a00d000602030b0501400660070b180c0300b950b00c5560020160019404080c001e44000d0303511031855070a001e89a0f254010a48101307190303000849040c02106011070306007070903220f420000608103c0b84003d80c0d2107550402124413816144d41c0055490380c1c0018408005c10800300034020841d0300c00e60107010003500311340c0c80d2100c00c0102e1070018001d0f01f004c0c0041c03110000c205001c020045101d411507841410520b00280c90304401d03400e4482c1d80c50300c0e400082d4007c0f41c08108007401801400e01903c100c80640d00b41c40a500c4003500d040d1240300b9071001c0d100581018020301d4145110700f074104d0301d00c0e2152016030b00354451280f81e20304002940d080b08034411039056607040341c20302405004078807000904200040303040440b03c0040710303200458120702603c0d021800d42d0500c0c1e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421263021 1250 421261771 421261781
    0xa14150714060412020c09100504230f010608060d0f0303150806090c090112080405190302131e0e150604060e0a020702100507080315040b03010c021e0c01020307060f 73
    0x807580442d4200c2c00d00303240003181400406080340042c464031004140c245040c500d13143c00b07540d030410032100aa0421041c400a400d00c1e0007000c0343d0002a45544107800950840c051140319811080345043d41488001011100702409807440381e80d00c3c61900d004a604c011421202c0d03941414000346071000111004140403059004150030302500c006c02c08221000b08024446d80d1045605048603a00ea50f1624404240c0c1c0700c0103002124144801c1c0700e80e0401c41d41ca001d405480c1140b001000d0b5681d40043c0c2443c250030124041d454a80c0311559139520402c0d0281d5280c1100c40080c084c1006007040325070b40c0c1e80c00e40c200c05101011500071070740c241c8595000a02421040340004460701d41200050b001c1d60040754124091001c00d101d8020180c420020340b6940c07680106120300c0d42e00c84030194540820312890710759010740e0312a107a55880d41e09100d252800f004039000750002c40c4a455103c583c1e4184035000c044103800c880b94800d035581e800300866041950054001509201c800b2000000348 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421264271 1250 421263021 421263053
    0x3050d03021c2a11061605071104090f080a0e010e062a01230f010b03010603050405010615020a0b01050d02030a080a05070204061d0702010c0f1d04090308060a141507 73
    0x144103c070442044035800300503a0071001208044400a44442203060750424070f804440001038024442900061a185000f402003c00204040b5041d00c45403250807080400210849280710000340c080c28454028507643c904035002d00380310000400714008540c8a22a0768001c001d09829440342d9500d0921040003040a51b0f4203a0007042000703900040481c0c2c0030301c507025040c49425101c00203035041d0520701e01c05060341ca241c402039007564a00070b0b0070f034083e04020f482141d00d03549925010408010412035841c0da4089a4000c204035a03d41c01c0c946d9403a94103070032442c02140c014150070090388000850300f61a0f64004903065a40b504094115550302429600039400760614400044048031040911101040d510302d0f0b041d82e480b805c000b030b400c94810444c54408242c6040d41450158058229440c4e00c41d03082d03c0c44c03480280600b0000f42202e408105c124042941e20b0107209060a15205500203000498040002d05085400140400340344041c402084000064980100646404481c4c091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421265521 1250 421264271 421264331
    0x8031b03130803070c1707030f03020307050a030915170609060d0614190e0d1227050f060103350c060906060a03020d080a2703050d03021c 61
    0x81e034031500700c251250701444007079503c04124072000c40c010808041d4078042a1950000b003450f80d140d40e40e0040107103603450080d000d40c0001e01042011072001d0100c138026a100341e4800841c641460589060324403525030b02070400003010324503a8080705403031080e50401d1084503401202c1e0396100000304910313002417000342401c0c01c02c01d0307401601084021443c0501c034805000c45c1c07821000f159410413030b41000c9080d50650b1146c140c2d011031b41e004125039401070003000e8000c9080807840084040f000c410480145500c4040a00e18081c000144119200400d607500136040e194595155545105002c1c2c25401e58022508208440482c80f2419990082840e45115807105403005440d07865640480d03c01c0554042c01001a2580ca0940644400ea0368010310100070703602c4c179880b42c01c1c1d60f8003c8152101801140030390402594800c6242544041c0752200c00385800d81145801c2c0e0518003401250001d0500601c4054901600c10700c449202c562120070000300b000300c2043d0946c00d5012030101c5009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421266771 1250 421265521 421265557
    0x80417070f030501020309190b04060902150c0c03160807060f020c15030f060a1809020301020721090b040e0411010c2f0d0f03201f0507080108031b03 66
    0x100f20040d00914443c00942042d91161400705600c66142d460702c10004084624001c00100050840c0c1d1100b11250b0004e88404800c0304d404407034030021b40c000c02c2141243c2e84800400e18151404001562840c0008051121031528090101d56036a665001d4881884050303140c01210510030803140c2d04d0042e00601001c0260322500130070189a0050b81d40303c07070b400007000004031641085034114040701c50844840c18a2030303052112000a000c600c0c806c9078155000c01410012942140805440e0300c04420b140502d181d59400142c4400b000e54000711459200344020003410285a8825038041d4022418420780ea000d4001200e0264190b40c0042051230149090319592920360220020521841e900841849001c0208140030440d21001811001c49401c1d0600080c0f14202a480030200c894007030007007035012a0040e003410791454403d02d25141103103400c45110440d0040e29003061160801c8006541480d06c2152240315924115901c610304000c4410403000803c21101200380c1c950070051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421268021 1250 421266771 421266773
    0x102041a0f042d1401030b01210b12010903020102030601020d080426210703060605040503101107050f06070f0309020120070b0f180901060c110f06030403020105010807080703080417070f03 83
    0x201d1301441e80c070f040780003c3c90315040e50f40d61f500070078411035003210620711128080321f4a9041c4000c0e0800948003600800c10121036000f892017406441c001030320940000d6100c1c81e02e000024030f4040c1e21081c0104000d104ca0074040800c59412010010503400806512804500c843c3e0744094441c04c441d12003600c0e9a402a80030300246940400d0192801d942c087c8022a40ea9504442c58040c9000f01a8913400c60144074041c0c600581c8003070040c40402e0501030400c0001d40722241400e001c801800240c1d00807100304840716520074040340c909485401d081100075820f400080c0040c00d802580b40908158810814040c041000728100600d8000e04050340d59641038262815134100b00d190120200c0c2d040c10103445c6140032030440703058400d160343d000042c038815264850801d600c2d00070705400260318025088680c480100440c4264000d80000c43c2c81d5262100580ca411070980c4041941d8000321014800600044e00303da085441402c906502c11028983d614208429640001d40724212050004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421269271 1250 421268021 421268039
    0x50408160b0601020f01020c07050d0218010b0a0801171504050c0d15052211040204030c031b08120a0305060f09010305060a0506010f0917100e0102041a0f042d 70
    0x140b0652003a800da030303240c3c0d490092440c03c0c3c0c0201003c50740b9940041c0300030711040c10002e02403d80030780011f0000c11080c02080000c02c845000b80c2004410200000d011f0b03c4080c0c014a250740100f81c1c0c070340e095030781030b080b1407a10361079950010305c0010404025005c50107022040124604004005041c625547d04c54a0215a011021103112404908140024514a50711f10701c4407c00500034411880180e555902c10482c4a940b110496005600b0701010010404864220020b944100048880a54001d035080c032528030726801a04968401c0ca00d810880c844c0e042a5841040e042c1004505030b124038000900340c88513524095002203010740000b05200000990602406000108200545801b001143d40c000040c40420100d00c0c850420401c450483d240a6845205002500d2000d039274011300200b5206810005040c0d69000f160501030260304070300104034030009500c4185032079a2980e10929501503803140126464a4004400721070303003022071100049000340d41442d07140392141045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421270521 1250 421269271 421269293
    0xd0605150d1512020105030a06030803160e100518040b090411120a080f030c13030c15031a09180307080a08090f1b24030a0b0603010b0a0305040816 65
    0x90850941030400c0d003210b16241154200948450303000f02d4103400120340040d034540e48040d0017820001d50706d1b8000000b0501e441c001e18041d1100c50700d4000e004000c007800908074401400031720701c10761850031031024164001d000c039400c03610740001e4030b8100381c000d0001500804880001e19004544038003000304005146590075801c860407204a2107220607440d00960760700e4004c10003001c2c42c2007048662141d030340b013001550780701c604000300c9031425481c49801209106640d00031070303ca41600304280803d000422241e10111000c1c60200286010f80025600d000f0310303185258051303400703a404641d5244010300740d10703601078600080701d40e030704003900c0d145400787d00c9000540006000000414080280810001c0c40b8034080f1008000c2d1407007011802400310504d82c0d41030391010f041516070148481441010310541d8500741d81135224a0f0050744e1100380c03154000784510680c0108014889103401c10142c4011020910300010b45544034900311020b4450f20426611440c0440082d404019102c1c3c42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421271771 1250 421270521 421270537
    0x10306060b13031104091b0f06140f090d02031b10050306010f0810051008040b07020a0c1a070605091f05061011073f0807020103020d060515 62
    0x41008180d94690301c000c2140248020b204005940500c1000803070300030a6080d0b9041002440003441e02c0c42913454459040d42228552a01420b07044104010107030709640f40001c05071801c20903031410b281e1019408a204580804ca00c0302c3d004501380219868020100e40301550141c1203e46c5035801d489100c68480703107010428400c169100402076101d1040c0243d0380101c004ae15105101795101405850704040240794400c0d41c6202800002c041e41d03034105400b500c00540e11307248018140f600b0b1101884038000c240b401952300c10b0100d0300003d8510300a900c1114801d000400000d200307403025003c90300c20034a004c1c05490410043c80009440170550418420312102e9510301461440703904010380300c1c00c44010f0340c000c0c16140d0110700300e80103800d19104182242c041c0d40416032a62042c038048107542800c0960200c0081c1c0396075a020702c80c602d00d20682c600f805001141d624a545261304d52040d07500003810550080381050040c480c0da04050080c0c40000d00f001a4006815100c90054100050f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421273021 1250 421271771 421271783
    0xb1c050307050d20070b090409110418020a051507200901090b190f09020a0207050603090a12020307080406030f02130b0d11030907060807020f0d02010501060908240721050103 77
    0x40a40c0140c10021760f507030450b20102c421314100400c281c1040010300440c1000e440e61460840131030500e40e9281f0900c040c074918048441c42101c0240140042c1e040c40d9040740e030040640c0d025140e90100f10000b5500b8066100088132100c01c9038501822444101e003254a82001551340040780c00d6256070054500c52205440b07440c03154103159521039049109124400050260400602000e88160001c28080c079590040740c0015550340041030050348120ba41d00c42a401c080140c00401c00e406d0302208010b105803000703504100e8030791100a140c0c45948580c005041d6103404c2d00c0070b01110b9030107452241c00c048a850081d03582d035100280581c0e00c0403105040862400707401c91640c060b210281da000e40e0701c02000700000b50414030b0076180564040d0a0000b54450b608507403000c0358042010b01c2280c40316500114080d40b50036000351603d41d658100c2030907034018502144403800340c1140b080c1c0084d08503a104015455181d07082e590000704c0804107100b450000d400c0203140c030356604039078101c9220303107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421274271 1250 421273021 421273067
    0xa05011a13020901140a0309020a1823060f0f0306070201050403121503080d0617160509040503030a1a032407020307030507031211040312030f0b1c050307050d 70
    0x3601100491083c2c0080d1400700b00c005180a00000da00b03006800310210504000035403040310b070001070711506250310204007241c00b070403021402001c0c2c0c0204055284183c1648e610b0106c400d1989110000041c40f890160254036810801551002c0307580c4007221000d4142e454034240300304024047c00d4111350030740c0401c00d84250400010541e10408498200c6420064034017400c40d07840115951020400c60100e94481e8004207007811482d1211480200d510001d003201040048a07000fa0340c40e076403143d0302c1195548100030108801004a070352008448030001900d0400d0001d07444800e2440100d15010300c030b00e01c490f0b40202c400002d0a07410b03400314448500b0716601d00780101d07038078460140f00a00003602404003500090240e1f00303d004044501e40003140e0714084410b800d62580203540103843d903103039900d408101ca07600751040c4010030302419028040401c1d8103000c201c103545120070703050700c807c00d42c101e10083c017000380161404c15901a040d1003c3c01c0004100038403c400c103003119104605c0320 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421275521 1250 421274271 421274299
    0x2010b0108070c020d080d110d060902250609051f0605060c070b0a020f011109042004050d06110703020c1201090c0b030601031805030417010b060313050a05011a 71
    0x22220307240b00e540e1558856019110750360034410030f58016034080ba40c840c02400b01a40b0005540245442d84094044907078031b030841021100b0580364203a00504000c0d104000d944401782e80b41440300c0c40d06254540c0c036082c1c23014a1406400030a20f02a01800314025928500110300100e0107030050345070810414846241c40d40d080040d240702d081c500034016408080c082245064150160503405a2801540c6410b5007501d105425180800100d290001c07001880c106a8902403007014520384c8034040b03004001d650b603815454036200d42e0103070511440c201640d04040140c503400000304c0d240f040306891f450303014910b4042d559642856080f8440c414419030303a40600300503c10781045035000307585030725a1803600c3c08916150340043c0a81c1d04041d1030f1014484001d9144c09104071851081d4011a5106e24140f800035020740306220740845a4102164a40d56aa40300c0580e41c00108804c81e21003c101c036403401d24581030450740f0050055013041880e0308514007008160f07400c8502542d4070b042907920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421276771 1250 421275521 421275527
    0x130b19050c06070e03210301090f02090d02090903040b0d0507020f0609070e19091b1403071503060e07030504051203070827030f3103110a120b0702010b01 68
    0x252880386500c81d4080d000144520b84160202105000082d00740d03019207650440804041c42d10b104d52000b41b0f84004010440b0601038807402d045842c042c0344c01c50038484100e00080fa03e5084840203441543c0c2e132004903000c41001d200f190300a0980c1d0091a030340c1c03020501c1040140808031000c8016001d16942c2c030303102c81404146c0174801c0d220500503100741405c1446442d510300003e4440a81d51030a403210586090782c5129203000c25000f0003070070000d0350804120025982a40d000710410003000c80c003009094400113a1302056030044009182c03a404010011002482c00d03500c84500c1f840d01000b0711181c560194403884c007440c060001e80d4400420780d002105544030554407034000542550018000d103400040c8004509141d11880089000c0e5220035441c1d034001c8412443e0354980040c09641e00b0100d410807400480f502c501c012070807040780103940005403280c40042c05041507805280400d61301c16401c0009440c00e240c203001c3c082e545d41410040c100e41202c0e071601562074205000d5035980 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421278021 1250 421276771 421276777
    0xf02010f06170705011716020102090409030e150a0203070311100c051c020325030e07091e05070813030c0c0e04030e030105041e0f12051c0c08040314130b1905 70
    0x41c0303440107841b0b59141d4000003004480da60034602d04555007440312040c16a01e0307010b03055082e1700a590700c1c2044401081001548142050302c0f08026004000138100c1039004815500801d40504021113604010a1744034100805980e203151020301d002c04016840380c10102920721b60903020b40212030710485808a00882c401600d950007490700a07440c3d48014804040c42c234190040a107004101a20030402d40380ca04a0160804403480b6260495070b5452214449594045002210f040c442d5041000d4041c12112000e840e1200c809000f001010a02d80a9003485841a5100d400140c5c0159200641041d03640140c904070005600314603070b554289030501486014680000f818403001e42210401745124406400450340c41c01d00c0c025190100300c843c1c900c0b5130b4041191300c03103070355602c600c14400e448248103034508605145410355080d10140e00002c016480b03941810009290041300d81c1c4192203000d080fa00325401ca0401c1004151011914007900003800c000c901400724041c917120035103e41c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421279271 1250 421278021 421278047
    0x10203090c100314191404022b0807080307080108010b09151309081207020307050d300e12040e0402190f0b030402030c0d020603070f02010f0617070501 67
    0x5481681164094038280d00b400c051400c4600f00040c500150302d115507000d41c0704980c1c950f405d82c0c0e110b160f41202d0040d40900c8500800d000c070301c4201480e00e980054494101901d0b181c5e03405480c1d426031043d4a400b060b544032815000085552111510b1600414540c0111108400105c00754000030b402041400b0700c1003240002021508580d85609007200194a481d56031030340270401f1040303941004080c0c0700e82c102d001e00401c40c4560f94007104408180341030010b00210304540c020071104020460128940207005807034944481300d5080c5081c188400d203841d010034044128400c1c11455040e60342d40c01030f95082c070300c001541c0542071003644824142c0503130b00c54800b2013440030b40001d006189c6542d0568002407940d01e0b04606c10b8403101c82010351003c542001c0f0f41410000705020031352030200840340d1564400c584241410380c003a404500140400742805080c001d2041c01203403458004e4203e10b0b1410036812042003204c0d030781c6c03031b00c0e029062100c0031010756030080c1f071400b140039441020044140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421280521 1250 421279271 421279273
    0x42001110a0b150433030203120702030a0209160f020d091404020c0313060e04022a0a02040e031e090d1209030b0709090c080601021f06050a090e06070201020309 71
    0x640040c1c6568003029002018003c02040e54001c080c0c1a03130b5248071301009800001380c1d13000221100001c1d2000c100718041941c030302c11084001040103070340014400e5120400050700503102c07125440402d01c7c1040307a40c4020f6105502d42e00f0003800441079044011842d20a9a4025504402d24400e82c0c131140382c0e445817800200700123018040004500b00d440b804a001620042c6080840c44025007142c02c024044042c40451400c104581c40c0c0c0500e06070080d40d011182185001101d6041d426035031003080c841d080b0501c01e9100038039a1413050150440302c5401620034051000110420703926035100c2e018821380c500c840f440c0300083c01c5c05481910a441d0001d00395140d072614580722003652110804d03016040004860000c0001040050182e004d070031103481d071404250801d402c0a00f0f03503000d45150020402d0036420442182e0f400100c5200b528000340c001d4545840000c54440544084d400468209541d40ca002600041c0342d84000d03010009072098450b5612010400c90a0703103c04e9a1850007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 421281771 1250 421280521 421280533
    0x60d0308011e0803130602101a040c0c06111c0e070e09030714030d29190914090d0914040c051c0608010f0924110304200111 55
    0x209181d0b400d103402c1100c501c140c9806465610071035603103158842c64460a901d0b01503c800c01c2499010403400d41008485e50043c001d10484922040340d01c1443e035181446152a6144490541d0152008140079500040280600c0c02c84c65240402544414101c0c0d0031150403c88020040c5858400c183c011004440940003075440c1070b000ca4141c04020303000a0aa01013000342c1c60008003125031181d04801000095030300d84043c25045022594401450400c8010354484a10140800c881480240000300e07130f581040002e1000686442c81c0725080756070100d01c0c1090b098114132544402c14480c2168000702d03020100900750480321030065228401180003008110140c92030320350081d100c00b1405203002800d040c903d40000c109211400034408601d540c0310018010f005087c0503001203400c410070180031040da541c1e290b00d000c0415a00c0700c0807040e906001a0010b4240c0d401441c0000c034609185904c900749400c0400e001240c0c0120310501d1800c070000c540c107a50083c40c0401017001084080c1c51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 421283021 1250 421281771 421281779
    0x6060f03060406050c0f120106090b04061b141f180b0103030c030c02180702060f0106051e0d021c0b180a18020a15021213120f020603010902030f060d030801 69
    0x1004e03000241510f01100301c20b00c074610b03540d2080400380844201400c1d191050754541200039110014580003d00c4200c41000f0600507160010844428503480300900c038640445820030414041030140e42c20b03414000d52540510103111480e110780c2d50079407981d0412401c02105158580b80040480040c41c04041000404c003290203002e8904035103000c2d05042c1c000001c1c582c0050031800d034481c01c41b516861600180289103504000307082c0c0c440021110b5802d154103280c406407150041c03040c003030301c414400001c0d19040119101a214800000203013076403103040c260044483c40f4152442c9550700c500c1c10240e60304d980f80a00c00580803525405c0344c0da4407601c0300183c00c0003034202d8642c00a641d01d400d581500058884000241c0140701184191a285140a02c02801c1010350b285202d010131051040d644400100425030048030082c01207a03007089890b242c0000d542180d842e000c1d5000310040000603482026800440c850700800d03800c82015510300040088020041102034005140c4000502c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 421284271 1250 421283021 421283033
    0x90c020c010e0303040807120f0204060e07030b010c030816030915050412021b042309060a0609090206121e0705090a05040515040203070e0310151d0412050412110306060f030604 78
    0x1882070f401641e46e21005404ac0d0041010b843c60342e8003800310081d1f00d0003000541c0780c0c14481d98542aa01f483c0c10314600144e034400070700d0b104001d408407010051030507200309840d0180c1e000c1545540e00407141d2114402c499200d2005000440c1c007030f0b60b8400c00740b4425004510200d0302e900b4281c3c3d140d441d0f01500314000140002490f00c488450b00941c4444905100390194500e907a10880c0420000c0130f031446c0c40c4907000140c4026078800204036040c03500c03200060345ca0005480200184616281d280d640380d4100d1560108007120071b040c080c0312403040c418200e502034001d15801005803144482695070740c041c40100c0300d084403060205500706d4440300712480d00d9001150000303907529140400c40c404000090070302902070a01315003159252000611107082440c1d402c01004030366042d003140341582040300342c280c1d4010801000c1c0c2114a0081d45040d0142d020b980c081c0900c0041084280b0080c0b40c050408600625124820310655002603903e28003400c601154a502401603c0c050302c0c0c1303039030340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 421285521 1250 421284271 421284299
    0x80c03160e0a090f152306100203160302030a09230f060f040603020301030b15152508130f120b041e0503070606060e0d0b060a090c020c010e0303040807 67
    0x2e011603031142c0b00315012030022203620030414026450721080000c0e891080d400c03121000c281c3e50440e42d002810005001020540550102c002c0e0b82c420004081c07038000b2400d41c814000031012110f01d0703446030800d044e80040681401400f0303442c0c01509035101d446448030110610107418012030904083d8003141400c03800103c0c4410064903203030410702000c421008a0b0019000500000d40c00f0004005008805200503044274031407070020400d40444021603500d4403640c2d02c0e124200d20001d03212241210146036080103403039684071810180c105103001d031000d501164030448841142c3c040811007180c1c1c240705400326000c03003021000800c8180d4900c00c03040002002540c0e03203881c0d046404510900c500403422514490005150344040a02d400b1045555076082203040018a000001c400e480d407042039406160000541d45044c1e8465002420440d50303900b01140f03d50424065248064002400004d150803d032a18181607602c841419030744d010350f104050703450307009003003c02c000c000d92403030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 421286771 1250 421285521 421285531
    0x50f2203140a0c1502091503130501090303140a060f060c0c080304090b01140702011b020f1002030c2e0e0f07080307020906060316032d06080c03160e 66
    0x40794511211a00c41e00d031003074010320340107408901e45111040402042004181e4411809003045003010b0108001c629008042e400021400c2c000002140441d41490303106030086074002c000388400455460020007800d0702d81030f9900768114610201d400281c1c580200415200d0741c11070360208602d40f26040303034040349148081c0c074400203140d03002c100c0c201c0a00c01040540803403880400e09040307090004140103094140e414440d0014403007540180c5e80240c56503903002681c0c2c0b1106141800380001200502010000b540c40340d400c480040c9031a8021000e01240e4003800e0a440c6102051040e2100b5a8403803044030070304240410b550920201d0580c002c02d6039014a50455160340030b0200001d00d022400c1d003100600744d201140400c2146001460300ba40081c040d0348036400c5007041490b40a002d40b14101d0141455201e40561029507030310205205903405404240b1790410310060010700415003800780311054025040004844d06000841e200700168600903c50f10a00d04001c03245103a00182c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 421288021 1250 421286771 421286777
    0x3030402031203130c03050307030f0f21110703090e150d080714060c040e130f060e01150e090d1107090908070b070509030c01021c1d190801050f2203 66
    0x4c4402084291511a0180d03100388003c6a0303580aa05000d000d40c04041122004c001d581500781a036158407100403004940603600301c80400d070f04a1503100c040c00300d041580c0c040f840086040c07000c4c59070100301c11045811a50f07070290141c40f55000c40c0360400000d415160850351442d81b400001e402000105003560007408900d4903030380c0c0c0b010034604241050f50817003800740c40070406001d2011240c10464100a604800680070a16a5100c2e4003c1e880710740041c000c51740e1840c0f5410003030000c0d00402c00c000040340c288294030b07441ea0105c5003a000c06541d00e030384510032007403600700030350007526082c4030700001c40020b144951a01c04031101600544d001101c61240c107000c0e00000681d6600344030b004028a40f83e55031030300c000e0802c1c14034040c1800320701c904541c4a10042d809891902c6075018241c145480d04500c105c0034080d1112200c0302c51f00c500c40e0001e010a0030701c3c02c00d80c5081450380582e04400b00a1120f511a900030006031070040c0c81d41c1004c0381100355001824522861081c08441c4281 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 421289271 1250 421288021 421288051
    0x101511241506030c04061d0a060f020606190b070c0e0712060801111b100f0209031606050f0c030f070303090b0c0c0706050307021006081f050f160c0f06020d0b0303030402031203 78
    0x140c023264030060b240e84080c2c08a040c2c1084040c40d580c041c89140d0740003900781e03080c1858003524002c5040c411036031302c00c140c240300000501c1414006074034641c401900c4101d42005503804c0c82c620090119140040e4401c4041c500b031000f10f82080180141c00420300301500c9641403064900d82032a8184040c00e8035186445410303610155802540103e20395001c2424005032954000c005040c1403214103013075502c60342c0c14071600b40010384d0442c0948100425440c03455485544150210707185204505640401c0d0002142103800c240c3c2c16003100c1821482100c3c070150a13255401c660b1458082c280301440f064016004c01d01000b4420000780d0740c0300e034481c030454070451840c1800c03d00f280c210b80c014020300e0304211540d01008805ca000c4102e980d158100412a501e0070304940110b0403005032031506050303810754026048500c68002c1680240e000000ea810441e403603d000c10095101ca156024030702d08206c030204c1c652a0200640e4495600680640031140c52602c0034101c5510041c403001c00c407018070b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 421290521 1250 421289271 421289327
    0xf0109180606091407020c0907030b010c1e110316050103020708070b0a0504141b09060604080d0f0e06090d060f020c0106031a101511241506030c0406 66
    0x94002e45008055003d0b000a0084042d2412450b04200800b40d1003554490691070040e622041420b0350f0000e070901d0000b40609030f460040b03a4010740a44003601650148500ca5103044c42d045100c40c0183c40342520b0140169102d06042d12070200e1110703101d9a507503c0f18204001e501a800810005100d581f1745482c018103a55691818a002d0b07440c505100c0d07540c0d0800040008681c2c046400b412400c0061030500161000042d81c50310b013440d0640900c01c0c4101082c0c1d9030300e44205130707030140070440e00b41d0b06907801002c07008149620b00c0342d0181c0012001660421641000c400300c420f440710240c580c00c032018090b101c01c00500f2002c544214066420000c00d101c840c000c0c031403070014521407003510120042110801203c0c038405054500001d001e18410403400d80701c001f580079401c607503050104141002e0500c1300d051004020010410102c000d040c1400f4000f803030450b510402c440014000f4440e525000c0c464140401c40300340700d520008010900c1601c2c0920907074403c0c3c7c455032105001c50108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 421291771 1250 421290521 421290533
    0x15060804080a030f0504080c07050a1802090a17031e030421020c03120909010f141005070b0f071220070c0b0c0a0b010902130312050d050c040504140f010918 69
    0x4803010348800f400441e03100c8c640d07030040c41580c0003480d0031114448418100400c29140ca9844010240c410741d0025070740f075480d181d074441c4100500c0e214400d600c01c00e2560660a4807907202d00052036410f08600c410f60340c1c07800c03082c054030f010b2500001d80884801c04030f41610301e0701121407a0380c019807244012848082e502002041e00141c8440612074440751500280103901c0410703000320100c031542710300c10b20486410390112045514120b40c844414041c44105031018410700501402131244c0b07070104150409881202c0d4040c2585a9500d46240101c100e400d044030450f08590701d00b1802d035100c1c0d400c2c100d9a24081c042c5240196448a0869980d603001007440d80300054a40caa034101d0000c1100340703c1c140c21398070300604c50f003c400c0d0f141050414010228000d14080103144800c1c2c00030346000d15200301c0640c0c801e1121814100460b0a03d00b14000d0a6049032281c90721481c1030100c850280c0074640d12a078021008036000040603406d005842d0050600b658000f130f520590054a4801700300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 421293021 1250 421291771 421291781
    0xa02030708011e0504151104031a04110102012c070902030108010605040605120d0819020d06051f0206010b0a0c0c090603050c0109030201020c1306090c080a15060804080a030f 77
    0x607010300000d0300450114905140c85221181000450f20700010400440c815840300c8502c2c200d441c00c000744e81240c3d086500d0080c0926000606145201c0030048500d02d03010310400d010b140150030030442501114012405d95006040420301d40030b0120403000c07211b507014100070019082409907495141c41c1c0c801401282c00c241c2c030036411a9101d8070200010704003407103204050101a00c0b0f20100342d00e035400b0b456480092203159070400c41c0c8140092141000040500d020f4030120800b95030304c03824907038480082d00c80703401414030407841504441d511110b070002540d0100e180ba00030340950381c81c1215401c00703a0048917142042c4000c00407040700040700304060382e0140c002007000050300c6045060407450403074500e890324144400b000003400542c2e00003400340d81c401c004441010701101019070300c4000e0040b03503000f03055581c200340450340444d800804152040c855401c04108500443d1000140c1c00194892100803e908501040205242c0c0d0f00520380001035090104500884803011000c880d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 421294271 1250 421293021 421293029
    0x6050d0209071209050606090709151404171507030216060e0c0a0e0709050103050c12060d02031204060e0303040f0335030a0c0e13020c0c0901060c02180c070201050306030a020307 79
    0x34104004200305480c1141e12580c00c44180e2414482143c18171002f1001c441c401e6050505214805488d2000d5013520b0382280c0180c42d43c100900b1341a805060360954500b2625210300c206404000000c00941c424402d40f00241d00c3d9401401e2444010707201d1000802c0e07046242041d50060000500c595102d40940300001c041c0c00581543e14546441d005103010400d4000504040c1403109101200303e10788161002d1114800c00c083c02511a4000220240b1207820700a406004d4606104508440407014104480d95078894103440402002010b81760304c19402881c0c06d0502002042c004a41840b11150a05841c0c803030301c0c40071a1003102c81d040c0d0744078202508860940c000040010940355405002100d0f420703403c081300700300300c590b00140c481c1e9000c1c040c40480b41e81c0480c0f000c0741a2400c0200b14000c0c40c01402001031075844540c001d124602045040c0e000f4280c0121032810101d5400c02e4500c9a0060003c075030424159034011070b9a40c0c00a04525811310485c1c0034000942c0d41444210014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 421295521 1250 421294271 421294273
    0x9031e12050907060206010e0c12060f040603060b010201110403171b122a28060e0609070b0315010309080c03160b18250e0a0903030f06050d020907120905 68
    0x8a1600c84000e1406c2c0d0160448160b0340c0c03040c418011480000020341f110340d00086402c8503203a41e08008209014105500c03140d0003410000d0010500c1110752000c01541400e900a002c2d81c0304e44404003980348242e00c0300404c50520042c880022500c3e010103401d141804017090101d103010103408514220001c00e224200c60000a4a01d6180004250395145101445a5803501581006180780c0f1155146c2e61030f103000c00d00c14891300c04280000080d074a41035104004202c000200e0f0982966120100e41105d62441042800f10f0504414002d0f20301c500364022980401c0c03003850700114040d0100b0351084070304000c04d00080107146000d0002d443c56070141840c120807138080b407d240240080140008200001e400550190301001141e0119003500221110503103c1c144051445000380c254412002003001303506000701c1c8111600300740e0100c2d000c0e50f003c2c44000c1c444002c41e030440d07000340300d50355100c80c40c106c3d41d000505091900c030341c2c0b10440d818240c0062404424903019682c26071000c070341d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 421296771 1250 421295521 421295533
    0x1221050f07080315090c12060102030903070306050402102f0c0a0305010b18060d0809061605060906010f0e07030e121308160815090a0210031e09031e120509 69
    0x4c100200150404e0150304941c00c02c098100b02e03110138a1031241710340c12804e040001002411f964002c100712201010050100c40c4150365904002c00108410b4404034418040d006609035210311905840488545a0418040d4540040c1c000410900c85003001051402244c069510698502802c50f0040d40984004617100001e441001030707841510222489005441050000c280c4034000c0100d80c0b15840700e1079a696440b001c0010340c00e030003000580310701c2c0c0e44a548014100080440e4140c0900c0b80502115071a0b600c8101c403250246040c003914030149206400a00030520030381040c0b0300d488008007a11030546440c42e00c045103501885000c807410300c0415041005040411440d00c2070403040c075020001e02d0500549944881c030846480715089039075004101d8600b000d01000486642c000c200100003684070340007034060310b02c455203214464901507080c0800000c9001c0d280c00140e00d669a80f00c551700e4001174081c030b011105009000c203c614240016100c0c0d2038800c0340d0003002020002d01e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 421298021 1250 421296771 421296781
    0x1202090f10090e070f0e0103140105041509021b16030f02090a0e0f0106080c03010204050d061d030403050d0906020a0b040b07090806130203070602120d050612030d090c1221050f070803 81
    0x3c00c80c86d040c4501810145400303016100c60030200b600303c1c1550811540401d00c100a890180c003010416003000c0e0f8424400140801b02200b09814084d582c0c05010a40310342d0b40b00e410360501c4078040b0384000f0340501b02c09c00a07000189040a0710903884040e5440000300c50340c4d084500da162413603c07013444d280c0da95107020a000783d0004018404d1200b030102c009501d03060a18000c102007001c035203001030101c6e4440c1d40310702c0b0224210001441544030102200d480d10b42d241825a03445c0b0034407000002190020101081c0036102103600592940c101e4480c011684441c1e03030b1174100100080c041010855200404a17040d0000c5c8100c502031811103400842c030110a0042504160913030f800f020666010102804007044e00310143d8444a4103114009079990300c54001c0340c41081c0101981e6480e0100217044145c000007030b844001c0c01e80c0214040040941c03a0741d152031040b8050300004d44000c0312400394156420001c07508900e040c00c40d20b0201d00b00351400d00045082d41040c1c0301240c480c040442044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 421299271 1250 421298021 421298027
    0xf03111b1504080c060c1c03020a170705122a07060609020a090308070c0b04030f05070b0a1403180f0604050f0a030509010c0f0804090c1202090f10090e070f 69
    0x9907850140c035524162501c2200c42d681e50903107445501504012401c0701c00c2031810700414001c0ba0000c600d0000003003660304000d000398030800c410030201d1210071401034660031400c4540c0c81b03042281c0304c603440c102ca45000300c0c0948000500b000e0041e40c90156800c90b0313010b080e45004400d4000790401c7d407a000356140040079141c140c2c20100c0c56600c180701804d102030740002400c007143e820018140c0d80306807070309100ca65601a41c0025210160000340081006203131111040030601410554205546844038804141f080510620006100316003048032000102c0085400070344010b451440411a12442403d120b800c18401c04160407200800c424001c05000c0741c6070001c0070402801c05050156001340560140c030610504120b9000e13030003010090003501401d00640c102c00302544850341d03804110054040400700c01c000411344a42040d00f4030f410b00a40305800f500511039262008040c0a0101007080c2d10409020400c942e40300080c500703071030880c541c000c8000380d481d480152910140a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 421300521 1250 421299271 421299289
    0x110a020703020f0d0c1802070b10060e030d050405012703030503100609030309030303020f0919050102100b09010302060705120a03021801051e030c041d0412090f030f03111b 76
    0x201e0b0080f00404c4480c4005166031070503006803580d40f108100e015540b40401c40082c01083e034001e001c044036000303214141c07009800120446906544405a051501081c140ca4807407a41800300420014803042c0019805001100b01d24206142941170003501400c000003004696803040c0e0219400005101800c81400041c070090100e0b41000100c1c246540e4004144d802c180c403000d420158080ac9070380d0140020411605416001004840b04001d2803c82942404081c440d45000d8840c205028070080400c3c020a55500310003802020280c0c6142c00740a20340e441800c0496003402010b1020b25900700c40b0000c0e001403c01942c0058444042c12141f2075940e6800d0300030303414020f060203880e0880600f0001718070103120f04c1c1c00580d206e0315105003002450266401c0b502448160344140381d0101c0c070360031041303100d04d0140020741d03952592240140c8041406008180340140401000c1c00880d14091140020900c02e11f4220030500c280c3c4000e500701940f00b42440c00072910f1507281c0405203800c40380 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 421301771 1250 421300521 421300549
    0x106140a0506040e010302040b0a081c030501140a120f02090c090a0e010506070f0302010b060d0e060a02090d0b040c050916030e120702090405070b0703120c0f09120204110a02070302 80
    0xb00c929050030b043d041580c600c1c2c1480b00a01c200c0d2559041e00e55522941e0385940240602d104407070411009000c0d0390780d00c9082031001400139142c40000140b10722a20342000f0441e8001d0600c40c204c50038410520030248038610113450f00e40b02c0325950001030711500038480c481c0786001c0880740c58002d900c04001d41f00c80c1681c4601e008140510040c0040d660300c1003200c501c03c0d4440e000f814680521316050b405020b91a01e0654840c2010800c0610100b031038021041041c40703802076a21503524000c1520803401006001504060060305041c002030410180e160054041c1c052940103541e2900081e08250045513042d00100e188003040b6030480e01405036000710000d072405000701c66407248080209014894000e0b20070030360403010909004060291902a014407540c0790b41d900c010741000360882039000000c40040e45403020241c4401c1c03190748034165544656481c4100726140a590401d145a902001d0740c0c040d540d103a0355000d54803001c2c020120702d901900608405440e600401100c481d483c20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 421303021 1250 421301771 421301779
    0xc03010f080d05030f0411100e091b03041401020c1f050a0c08150a030803042603010506030a0c11100f0c0306080705120a0b07021606021c031d0106140a05 68
    0x102000c015080070a480d07006201590000b601c6d9111706052020f207a08044994001ca40200d002c40d411f980182e0b41c90014038148d072080a243c440d000b600c02003000d4241c21880c012402c0c00801d0001d4070401c03400a00c00c1c1c0540001d4185064510070b28103160780540d02117858407005031010b00807142409807a5110000c0b8008104000b2070000c041c11944c0001c0c440b44d070b5120030034080c44c5503607110900e503c0990b4021103c2512031030300340741c900e042e00d00d480700c08004520014403100d64bc1400400300d0341641d074090140790941d00c5102288025259000020301800308544a00c03145c0d50f0300f0065003007031f00321801d0080b840c3d0307601241c44412680350706840c80c209070410100b8800603200285010031075406030383c1c00e01c291400c40e80c00d604011066070000c00d07807091041403090781540020703209043c0f56401708092030141c0d10f603000e0342e030b079580403210716001080c5030315640b03849000713034080180041d066910740c80d44000440c9460868070745030022071a081245480315142c4c00c200d26a500a400c05036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 421304271 1250 421303021 421303033
    0x280e041a0112020a050408070f0305011404050c0405073f06140909120d02040807050108040b070809031603050301091a0603010e06060708040b030f0a0c0f1101090503030c03010f08 79
    0xa1600d03205540c402c180d42c0e000240248054490002c60740100b44a005644c026910350f07008042c001c82c0d0340300661f03440d820003415048008040801502943e480360040c41c4074a401d0003032002404e00204410b044c0180480c60040340c0308c1207180712050b9484038680c40c1c0c8503100d445012110f954141154001f85150010031f1200b900840300c0d50b481036904550101080e0f840b031010620340b21111741001400100840c400d036510880c3d8000d00281c0741d6250a4412164441004441801085a02078200001c103000709408a00450019411110160a03280307888904003c510154000901c12000188000010000c000640c4281e150748200c40801502c0d07418243c000a034240018091020580c02c4c0001240842c0d48100071105581e5111583c103071540d64580e2070408a030000c0f100c6215110402c000110280110710545207940440d441d18a101090140220740c1a0f07680c2030a10071641d43c1e52840c001060342017011390b204130340c11403000742c0e690f042c03400d84101595268400701c0198814 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 421305521 1250 421304271 421304321
    0x10609050412080f090a0b040809030106030c06140f250b070f08060d0b040308090106150f080a0e060a0b0d0813030210020607050a0e01030212100f1a090105280e04 72
    0x13280c045d550541100780807d107070319a814100f20602c20880d04c603038558a0104000f04101c01d032040b81c0119040d42d111490032540054000c481445000c40362680028100241005450200302044d024601c40303030035090800c0d507550360380414041030303a900c03020540161061a1950b403015040343e00031000e031240103c2c920f040d45c0750605180003038401400d100c0440d0000d181c6500961100303004229441188045207109680a081d90129403070b01c100140010001820b550102d0107103001203c01040101606c1d51384070107140081469844807540700000c01c00d40c402203442840544403003000c1201080005141d0f1040001c44002c0c4400c000035500040d0400c151b0942180c1514814005410719405444040c0b004030004e10640390007a400d00301410034841c6080c4a4115001030750100350400589945130018140c014a0240030300600307440400004031706510441c090b01c1564610404500b00810700ca8040000c18480a400350000f4607000513040c2d24500b5004076041010501004100c016203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 421306771 1250 421305521 421305523
    0xb190b030c0f2205010e01050904050d050f07020604080c040518030316050c01020c2107020a3005010f050a14062809060510030e1509010609050412080f09 68
    0x30051081e4070030359941010012544030308605506000d410198200207a80d040249401410203000303102e001c107a0f020002c6428148400c0c220301030703504000281095800e05104640e41d0780000784070000c403801880346200603220b1101410103000c4842c054001060685c003400100c440003000303120906c840c164900341c019030200403a0340141c1e14000c01126188600e8003545c0520403804003d2007988002040e5074004d201003031050389600d180221959103c24224018414051400042d501030f00740342e810011100140450b20425440000725110305107901211405110782c000155074694485060581c0d5041e05d228403580110982000c0200590306960350f04a801c00500c1e10b4040c00c1c00782217402400b0040c4151041202c02c006030210a69282e015080144c42c2e14400d95020707640d003058a416150084c06413111030300710700c401401d98039541e02c1c01d003c05410107000c140043d540d13880040f4004045014552056004100c4540c491040340c3e0b008061540c0106031007130818800c2d040c0585910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 421308021 1250 421306771 421306783
    0x18010204150207210b190207080307121a03030f09131d2a0904140f0c030f0a0816081620040903020606010e01050412111f0801030311190b190b03 64
    0x114211b1400390881100d1544000344103030a000ba00d0040c1c0401000072195010039409907180070754000b44081c800700d1904414030b000c500300a030740c50f410900810300721014001c00b03041a041c0041003000028002c4441c2c604031840004c10a0b4041045020904007840400907050542c224480c2800c01902d00007180d01088403d00d5114481e81030304000c02c06110680d002540d5501300c0d0010764401c110340c130540598501c40000210f002c0d02030035000b101410b9000c00c811190581021307083c0d247c5022620401a400e214460454201c81e06008403216030765185907108505110b52010b480c52034046207240f40484002c940c4920031800c0c58a00000254045a441e030820f0742800c202c8145a00000144c0741c6010740d801c62000950000300b010240944100f00c401101e80640e05259800706056034003a02803c11400500403030380c907800420000384541c0036a50a09410416a90140308410811800092034401501ca50203414284864100240c80c40b070101e10303071700d45c0800c00d1014000219443d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 421309271 1250 421308021 421308031
    0x606040b030406091a06040e060930180a14010c0303020a12020c070e0903040311010f09180e010b0a0305070306020f190309060c1718010204150207210b 67
    0x50300c08404101004241e030461a240350703000400762154000300c400225010001c0301c02034426428040701500403030000c6080c80c00307400890081d150140c0030a5583c584846084980a080355044107e840d50705130203000f070080314008515000ea0b1541500800000710f031030790080034000c0c1219600c1109603811040c011400c0384e26003800f58a5089101064071100c0351726031054900340c0001050001c4075400705402040c0e44464440f10b1440c2c079030307a070740b0355582c020b50100a018480c864180c06296014000a00351030740c0914003011030315150324072042e06600584030b5035609511103461400d150400c0c027034501055400d5a1000c0c03540c0c61510703025910300043c80b01802155002485080401c0c1a03000c0314446007111b014081c0c40070302400000c0041c6540b040c00d8807030904e000e40c0d4000503807084000c00c403e654221101007140d1525031004c00032100d4001031103aa99803c0100090035984c0380e9070405290001d07009804800d1802090541254440950079010b2483c060404000380b403488040e9005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 421310521 1250 421309271 421309289
    0x120b12060a02070b25210606030e0601060302070c03060e0127120315060305040f05010504030810050a03120f110d0e030f010b0922060203040807050c01030501060203090d021c0506011a03060604 85
    0x44d040d4284006c1c540101000140d034000d040c000c2c0810055096048020f42a090608441803a07a8807141101207000f00c4c00c0c001d240e01d0b0f12200401c0412019084050703501401000001d00340b100c1e29031214038080e68178500d2490880c0d094040c0500c8210201c03070076160a503007800e0060400217070015035050040d004010516554001140a100406040103038099020008205a08043c14082c1c500041110885400c41c01800c01244a0a1130400c50044175032108003035014248400090711032001c0203840c0d004001d4007880080b2250003c1001e0b68209000b5100c12040c80c00c0f6a09050424903040e60450705a8181191003049443d86610300390b2010368410585810303007000310341c0ba0803400b5004000d001d4900200602050011200050410381d100c1c00454010240820054080d01da091040c900503800500c40030340e1500b0640c81c1000b038103100404942070f1a0b0f0200181400384600c180035103559002000600c0352440e2518000a1103d6540c02030b421407a01c000010402d200d980516910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 421311771 1250 421310521 421310537
    0x9090a0c0f0810091d1005060307060f090b0906070506070f03110421020a08030a0203270a05040e0109050a150e070f261b01030615120b12060a02070b25 67
    0x211005d52500c0590b84001c0c8810307903142c541c100c00070001405095400b68841d0041800026001c0e0003040200403004890300ca8091991528441070b00c56004542410b801107020842c1c0b4000a03402c0c40081e00c5480c40382c031b444030450320038070000b001c44104555a02448138104400e01801124648192581402e1680704010712210b10100340070007959806840740e8400403850a24042d0040003904e04403511011188500101c216000300d81c4000c81d84036501305100e04018010750900e070300b0580a40a210700089a4404540d03102e43c5842060101958091100504600b40e60118064a8541c2d4840002020140e0405940c581100500e11a0000000e05054400e080d111100d101000f20300e0740d0740640341e0441c0482860340c82c0f14500b0072a5800030b0300d0020082074082940381401da58180341e548441310401960f20300710040c41351040c620307440100342c41d1005850004001c200d00c5464000e10250702e6562038034249455a00c0904002c9902900320404911045e034010481e051420070701d82841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 421313021 1250 421311771 421311791
    0x30b01091a0303030702010902010210050103032c0a030f150e12030a090f0f0b0a051005060f04050307180f0204050f01080604090203120c0c03030c070506070809090a0c0f081009 78
    0x71810500c4514603825003c00b0080160700c030f0701948170104441c000c0c0c007070750a540b5804403064100c4400340002400700b010901c40c070368421a003080700e5a1210b80c60307162000103100480001c060240642c82203815203039200e00d020400c1003d03401020f09000c800c07030034003215a0f8004aa511420700509004070b504000c00042c40c02051740e0001000e80b60010f040b00038130100d0341407800aa0100170703030941c1c1e1013036880042141103200c0c0c411644561030880c86a1401400c1104002055114040c4410441c10620000c1240d40e02881100c00414184040798082d01c4501c150074181d404600c0f40c1e10003540305000800058441c240c000400c2d440c04d03e00f00d0200e954020005004107c03962003e074040c45800c412888603080c01004050821000088a45614042c1c04060307491182c00004c80c4950841c1c181040503003030000190240e14030424105041c440001c003c20f102c4581154041040c44e11821140c007400d070007442003070310603046d0310b807940c654a88600c1c103a00201c3d00388541d88485030b4407035180c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 421314271 1250 421313021 421313051
    0x180519050a290f07170702100e09060607080d1d10060308070311011d03130f050333040f200901230603040506060103050c1306081302031c031104030b0109 68
    0xc1d507045c0d4002c189038005611310644040d190842d0008900a08801900c4001c8600480c20912410030047c001c02c030702c2d9554800c0c131a5a8104800441341d848040c0405075540340713a0b00400c0400c405c82241c40444100304481c00d840c01d44040c904c4440303d803400d0401e201040d07001084500c0c09400d800c007503007100c82c40c0d11402d00402c6450503d00b04407400b00e619880b070120200080900f12010b042c5440d1041e2103400111101c081e52294942c0f41d4400101c840002201014641300c0d90240866080c483d03102d0051104900011079045852204203c3c22004100d007031460092821000860b002da41e0000c80086203511006000300e400000301500309241e450030000f84000b011401819241d100e0606103012560f41c2015203410b070100313003404005040b514204d01074a00344241d032803d0110380380c42c240050303401c0ea0029080700d40080051010b1000b50b2030411943c0130b85444162080c81c84010302400030112a08104030304240a41000300f0030114100c030f104281906c240000000d0101c816030268 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 421315521 1250 421314271 421314277
    0xa030c170702070302012a0b0a0617100f0c0f030902030309030102120f0105040203240319050303040c082d1908070b0c0304080307180519050a290f 65
    0x4060380c190391020840c0301607000c030700301040f07138800c1c1c803461203920310000345100700c4c01c40c2d509400315980e00140410101e013420b10080d80205a0050001303140e611882c0303114440701d0380c8508900030ba001021207140703c0618800c82c011210b01702d10070001103020010003803000b40b041000c0e4082540365000401075503000d00031a20b108400400856a61074035490f00b086c111412140c0942044074103000045500f42030089a1240d9002d41592803c0109114502f0501100703007203041d0180b098400680030403d04400c0c0c140014012402540c1383d11700f5260112052019406c5000130f40c0042a41c3c143c0c0b201c81070014a940300000b0301c2100c80030050343c03049251a0140d804a010300501c4000f00007448240b0004244582c06a00c407991103503500400b100161105540040a43d4030800000e042d0902c280e5210b4030070280306050101c0030b950b6074001111000c0e118601c1882c8a0f41e4042007245140c106200c90060929460380b542610050b144030421021000c524210640c00081b44504402d82d0340072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 421316771 1250 421315521 421315547
    0x70f17060f041b1d100c0f06020412080702031b13020f0d090c080d17040209091f05160e060a0509060c0106090204032904110103090b0f0609010506030103080a030c 72
    0x126603400c2c0b41154004d201e540c100712403c0700c10242c102c01882506001c0803001c0c490700c19441d103001e8030b011556880c02d007820701e450980c0d08507424400416000101c401440b2440d0250101584911117401054100001160024014590040e201c3d9458403a8000740181d800351020060701c2d098580030f102d0152203015180341103640341800d65402c100c0c03400300c0902030301c28603000c40d00030301078010056408c1c2810b1030460125201c03640000d8010300d00b00c0c095940c096425020340b5a01100107803a81d902e26003400ca8a404c19880d002006518100d00c11410801c010714600440202002c03001300d030031803180c60070600c00c200c000075011580f44c4458048070700c500c000700006c00a9581d151420b20007504580811610640586802c0446000f154040300c0701d8a9020113501e40782e2100d999801d80c5201c29000c0c1070505480d03210038004240c80018080c820801e81002c3d03140c0349031403401c101841505811891090700184010320207c0c0c2c0240956141d581141400982c0000c3e5030415a11007600c420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 421318021 1250 421316771 421316801
    0x111070f030b040605010602031602101e08060f060a0e04051005100c050d030603051e0115090510151205040804030209040525050303090411130608070f17060f04 71
    0x280000c00c102d02c01d902c162280b809008208420303600c80c1c00403030300d92250241d4803111054105109016280140789aa61003007a42880008910f1a1008001080288080602045a460030003013241052880003094003401c0303907098900464148042e0a200701440001d000b6541c90000650344030000340800043d100c000c00c00311041d9036220b0010706142400741c04540310700510f03000500d0a0b019018040a0326403120103004625105d10030040100312480801c9621f42d251030480348120810210500074129200c804106454012480c3e03c01d16003613440565074110007110104040d0344042c01e1880003218101c0030920b501c03581042e04c80d5001380e82001c0d60060000c0c0c1840b0030404001042024006a07154880c5035100c2ca40e0a07804070341d801d00c00c00ba0990401c21001c800c030301c0e02d58040e00082800d000c0383c900340f1000c440c1007403800b10341e40c1104000c0b0b00b00009020f41180c12207010003c0d50442c0c40d1030f4800c03005880c10740c820301c40050410b90180e410800181c64030303a6150000c55002003070074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 421319271 1250 421318021 421318049
    0x506120613090516090b0f120705130921050f0309032106280603020d06090c0e03190804030f030509030f1608070e011202060c070e0a0e1506011107 65
    0x1041035520f40056840b12025a1140d13580003a4140850180040c240e400074910000380700030030180300d2581b401107001c1701c060144020110b1240c0c0c8850801a043d0360f46500010001c03a540f030b100112810446503000b030b0414411600800d1540107044a11030b00380854507940360307150304140f00c0c5036016000781d9150300342400000c121440c0306120707014860001222104072136055400c01140740c03655404d644038004405441841958000d030000c00303640124100002c2c40035680c507002c5080b10002203420000a94070511080c0d50710f4100030480852a01d0b008075151071280c6d65403286a48507910004000390f1190780ea00d810705000d8030686102880207004d0340c0f0360141416403103460f2030280101c1c0c8071030000140040340c000e100207829410b035103d011003603441d80d08200c6081c080c0806c019040b684110700300584000c4001c02e2011070002c004200311248981049407091040e00c0307084100e003029902c8050004403903510100d500f0740048081c200200009910b8034900c1c01e11800380c00c07003102a082d01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 421320521 1250 421319271 421319273
    0x90301061a07140f060106081e070e090718080a05061b07120c0204020c0703061b02150907080a0b0703060b090f091b181302031b1614160906050612061309 68
    0x1400c0c80e4440c50341144240d202c185100c13a005000300040c2c2b40b841c00201c04481200e158140070241680250313071404e04880e1000402c04059035407071a50001138454112450704010011300300002a0044841104803001d0070410b04030380d20300d029544000c0e101c0800141040a050b000d450341044454002e8001d41d9a00c40d014000c6944030501d100031112540741040410b00206a40e10000c91440b481d405424080909031040034100006040100207005203100084c050b0700030050320040340e00c916000149440d14420180841e40954080301c600b04040001c035410707030303074003204100b40000c04c64400e0010b40b01e41341d0f589004906a004e651b90002d001411150718000d201c12004502022102030314003800031001c0400b680403c2e64880d400d41900c2c9446008907268102038408540c2900444002c071946490311988503107d8a27802408d0b800c81515000d1507880a109200070b002c050b00103204140c90030f80803503c0d512035200d1581100008501044c46565010940701f0990300d0b0a1050254a150b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 421321771 1250 421320521 421320527
    0x16050307030330051806061e131d150919061e450b28060302130e0303010501050d020408120301050909010504170304021c08090301061a07140f060106 66
    0x500c00400b4914840c08000501d00c3c034006250711002200a9070626039040180300b03000a509da0751000341d1a4a40320044290f22211060b01d101205d52500020500e010009101c8105514080c00345100e81e000001640d45107a5845041e504403944440300142c89030145200203401c11005400001d45c6080041c01d104010307039182d540d050307240a880b0b0104c010803a04124400c0d00144664510314040105601e8041602c1880c42030f4842840c00341c3c200d8041128030960792007070440214101440c0d4076602401941007100070080c40310060780d82040b07880c65a9203490b699002c140300301410800b000826407a80c100306d0701070f5401441c1e000100c865a01000310f1007140c6404c02d000d224000c070415400696550360500509001e590024944805a00f2458000010f548003c10581e04882041e402d800c80074005541c45005134010300e030f802d8480642100305402e546541e8071070002c00f002c0840498200500314105c400305940240490000301042039000c1c10b0a6010600c0c50550042100004640350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 421323021 1250 421321771 421321801
    0x10b09010e011701020304120804031704050105070e03010e0c10050c010e010630060c0c050d0806040515010816030e0319030615020d0311090409051605030703033005 73
    0x30142440e281c4198003d6080d0708034001240d000d05114600c051440719240100c5140b50014003c1c030300801403494040b000310106400740d504032920382d0b5410411009030762010220013040d404400034401207000d503003215a121070b6001d0f200d125400002410041038092411203050b0050503000780510200d010409009040511400185d0a04c42e8070788680300021000b4444c0500d9003680a03d21040141c07982d0000740703050b85404090200100f1002c0100300c041280c081040c20b160345612041c07a000e0240010364401074452036110201440311812aa00000141d5100300780b541110405640350382e080380503181e00f041d101e816002c0040c42000d503400c8a040d83d40c6004ea01d44040c031031691b849041a40c948011120000181c00081d040d403006032180d00000e21520b401d40540b802d0444200010782140c410307500890383c0354040548450101100b11000e0300401044010f01101c61640d18068440001c41e00c164800d40203503641d109501c006800030480c40b09110a0410103498004a4450401c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 421324271 1250 421323021 421323029
    0x190903020f06030402090c0a050f040306020309011a0607080309010f0204060c0317070e060306010306030605070e0117010303090b070317010e09150c09060903071a090a080d140903010b09010e01 85
    0x5840c07a1541c0900703059089901640d0b0250034081030340d886e0604542d044d00801100340821004009034100001c12101030409907000d824010b13a28146100d8890840f010606080c003c00d01c3e03034011100c0c1da40e850050b1000c064100c0015a502c0e03903030806207801805c00c1c150324262144003080100d0300c0d5611a482c440010300c40e40300c1e000b00480001030130050040c04c89602c070014100c00f0341c5034103606000f4065504010103040104d1120b4403a900e181c240d66040350000000394513400d420740a90380c480030008080d0f4449a400c1400c1d411510014030000440c090711904000000c3c0b00c10426201e05860240f501c150070b0020450351b1500c80301283d80c0c0c0300b600d107020a40b16040c3c0e548030449070450071a020b69001c043e580e1800c9140000d0018980025180310f80c140191000000d0f80241c1e00b081140718410040845d0303607020400d0420a80b0985074012a20950005081040140e001540705c45101c0716501040d807510100c00000c2c1c0503040c0040361079001106400005008005500e02038140c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 421325521 1250 421324271 421324279
    0x50a0c02060f060307090924051b0f0915040f0306050105040b0301050907060f021011300a020f040302100c0201030605100915020114040f050613240219090302 70
    0x1915a45240c540d03448050340c1d200e134141c1045004001490240e800303154a68400c0c02d070402018560000c4401960100507a00440740d1076004009030752a010f000c02c910390f103801c0c06503424960380351260fa4050050041103401201209000002900d00ea41030303a00400320045840640382d100d00c1c040e0060705081c030906001c1c070b05001920700b40345010301850340b00307503d00c1c0010000d075413526400b185c000318000980720940c003980c000300480c4030b402d0080c4a50603180064032582d802800d50311002c100a8000344445103035600e000345003080b401200064101c41c400c40007607110b20010075148901d00c00d50784000d41c41020074140e046000e41294440f80798034001d807400c1289070307501e80510600c102c89083c240300103164000305004004a02c40c910203080c00c50310000030242800602c043e26468259415100203001b05c4444003003090412944d588180c4039440b508110400e50b84580c045128100f03000f00c601440362078814040020f5040c1e6001064509507003600d42003410029080c01d1085c00141d002e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 421326771 1250 421325521 421325533
    0xf050a0b0f01051e060f040e160206041e030509090a0902041406030d03050a0902041806050907060f030e010905101401080d0c150b1009061701030203030412080d050a0c02 75
    0x1d611075a02101d4101c03400902012007020200040121101501c0b0a0366406a0244000c0100d03100041c0030f000a040c950b05424030f18100101c1d405e0b5030080f402c407884e0441d4031083c1088005141c81c0d4814000c070419084504208030b0500d01a1840d00800103100d80000c03c050400103001e40c01d030800c200f0140240c80400203d901c03948111080d00c0c2c00c4030810b401d5400003140d030340624480d0313020582c00103d010b0001800c088607030004055480008100303c40c0680510382905200184c031580f500aa1201300800360a46043d201501455400031100b040c507540e58011803c0a0080d001b01a4aa0b0701c038095403509400d5106400003400b04800c0709107004020340c004107076844001105800c00c41c1a844210312000240d8490000124958403201075070f40b0741d1044009501d41413a07048041501d600c481e50300c2410b204d40107200f4070500d030b9901d506244c500010030158a000c0308880c207443c49450f0800e034590182c10003d455100300d02841d01c2d00d43c58101007100351001d1707620501034440c00e41d09a5030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 421328021 1250 421326771 421326781
    0x192c072015070c08040e070305162a022403090d0306050612040f0602040b030a0f050f040b070311040b040501020c3705030a15060605071515030f050a0b 67
    0x1540740c05100d40100310303569000100d60854010032204400394814210b06203095204e10707100740c0b800d0042d100031002c00e460704280700940c0c0000100c001d0100c0146020b15110a514080ea055801d801080e843e06002c0c0c055181d0664554840507498042c0b0300385240c400c090303005a02d051304d03401221506034600541d02d0014415104e80692002c0392001040380341042032881d004240c1c500040c000301c803155a910242d070006085e5001520080614840d65503c2c0c1c03504941039000d45401d87d801e80346035840c0804001954100c918805e8016800240c02446540c40c41800d400034404290301c1000c00c2c202240000d4107071090030040042c0c17034003a0309031940c8051369802c1c4113000c030111605a40d0040c05030f507076401000c408c10282c201c1c440d181d9040c602559583c00440d06207149104191203204122120301c607111447e029200c0100403a182a524000300c0b40c90300c0c03030b610402032007a011583c2c0f41c150207001d91244100301c8010b56000070003407002c5410b501d842c83c0d50796608402100d8990101d00000c13 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 421329271 1250 421328021 421328023
    0xe030703050717010b181b04150309020310180212010c0518030307060606050306031615180312091a0a050405062124192c0720 56
    0x8000c990348103005100060904080700c1680c3ca400039640c02d10340d41c07907080c1c80c0c99507180c1818019003500101150100d040481c103012052842d101190601c1c001080700308840040b88845550042c141c0c90000380c666058400282400401580d20000301e0174010300650300c120700354013225620302c21240402554450042e00303007669003900d54440841c001b0300580b01048040884540c0d0014000c00740c0740307006203030f595210031181c1e44d420210011360701004102180c2810400c0b040308060218042030a82e10700640701c44a08400700f002e10810140c0148240054903e1341800c0c0a143d22810005108000c0c20700184001c2c1d4521810408403124001580c042c1c014404480700c15502c2c0d52035924140c2003800b80101540700c0b40d11042021101007200d4a0501070f9407807580100c050400500305684095011001100495202480750241d098200e4600b08000700e200d088070b240c254201e01c803281e000340107011880b44000f81461820040e080040030780e441443d901600842645031820103039400551 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 421330521 1250 421329271 421329283
    0x8011b030f0b1f0302040b032e0e0105010c0507030203100e06010906060806270702010c020c0402090904060e0a060213030b09161806030503180a1a03010e041a1005010e03 75
    0x110f0700300000490030100002820110030300100c007400c0140c5495039964080751540d0084401001340ea0039182c151200706541d81075883e03d0701d212803c1c0c3c0000e5041010031651f806041c401d09062001d280f48030010008207011000041d6002400e650b40c1d03d04071000c05018110310000403d00303020304070020400c0945446031505842440d92082400e548000078000c0448402120480d4044102103c040910110303581a20030007042d80086501019038001038039240f40f0707030701984c4a179005018500180e181c078103005902517082100460f424100651031030030f00c03a01300c4019150741d000041c20007090684011203002c580c803d995205440e9a85218140c88804260120114400c410000c12024810b10f2000d150740c0d006403000554190780e9030f5190300e10ba0012102a6400101070310007510351a119141000030403030200d4a5152244002c590581880140075145e0301442e8a000b2500b8407801214104003c2c000889051b004c0c2010b5541c18401c03c41c502c501e070300085c45c401d25007030319080100b52 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 421331771 1250 421330521 421330541
    0x6010e1c30050f0a171e0703060b0313030c0503281103070b04020a18050109050c0304121805040f0b0a080f151308030106051b01060f0501050d0608011b030f 69
    0x6140c03e1031100051601c0542c044103030f140400c4065a0701198986070048494012032145c0c240c3e400c8007138105400c550806000307146401b030616010080203104808400c4030741c041600d0841c13800c11529850151004114110050454072002c039019286480d903410300b01e038200005102d601702e8456060201c0d5400000c0d6042c1016070814040140015100c1107010740041c0b00408000a203903c40f407248d0141c3c1c06039510003040075110350041141112605c100350304241048000361861500341c45441c00141d40640764001c01c44c18055110300500c54018401c080d02d801801030020703070680700c40903000e0001120300900c03030700d028036001580340b00024107590150741500250202101030940c0d20600b400041070400727001c201c2d000281c001110400114007030031040d21100d0704c1320790220141c21035402c48404800f842e8540761090000e03c071081107460480b482444e00d00d5882101906e03040140c030303903a48100019820603801d03641400c0440c11740340302d1a00b540d03810010050700340c0c010020749881e100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 421333021 1250 421331771 421331777
    0x306060915050f0307030b0a022214010c051c03090618030801050f0105091801030b010f0b0f09040e010915140c070303090302150106091a03040b06010e1c30 69
    0x7410000307030514000500100100134191404507503241c031440b1841404070307000e40c2507036800103032551404c0d10161011002041c60440341c090314101451002109010004507044c8008180807204000080080e80851090445007030021007490754090701409109504035122418102400062800506c14491654140d07603803010f02d074030b004184080344203001d19150401c5001c01562000791a00c1220845030700c850300000e031803507156040100c0f8403201038020614444040d1020009880740c81c00341c80c900c412004003155262007800c0080d0040c000d90843c29810b508100c60802030000a81c00c00d001c5141c204000d102d443c0d1405a01c4801490460300d14442a00a01080000ca4842e80c00f41d112144030780101c6481080c03d06560303490b140c3c01d07404240000e102c00c070203020414400f0f40e843d0904000c1114141141050f17900c14461000040103641080b0304450340452564a02030b00c00c079038619014480b110004c241c1003c0800084840303c1c000e1140c1d480c900c600d0550320001804182d040ca5a0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 421334271 1250 421333021 421333061
    0x7030e1606030e030f03010e100512060f060406030b1303030f06181505060d09121b0303050613020c030d05130209150112060b090f010203190c0c150903060609 70
    0x620182c00602e5000f403200074501c414070407034003504244c0c4d000390f0107444c00d040541c6075031801c83c500001040d59500180d020314a002d500000240d0005181500701c10641e403120416516030001c82c00520581d4030151680c0707105010320801c080010003510f21580070f940c0c02d01101c5242003968060341c0c0b55100360307192601107100c0841b0a1300b06520007044200ba00e41d84100150707860000820603002000034043c6540d81d001c0342004c00040f4070ba960214203030b50030106401a030980c00c9100704100c04001609140d1110002051552000445862002002005c5489007042a10190f8a40000035480c0c8800d01c3d101c0400c1d01900b100e20480b0303000b640140603401039658001d03481410070800c1c0041c0c0c1400f00201c4052a180324601071003020f0041003106584805a60003042171350a0030180c510306641040211400c0380c4040801c41078526101c0c02c0c0340003411894a0080703590002c5c1c3d03000785d0124510103448683d10754401280e100720307800b40005000041d00c0f61031480840e10101c06a03c0c0c24031040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 421335521 1250 421334271 421334279
    0xb1608090a08030405011508070618060c0b060a082401080f060c0d0216030302191403160c060c03050f0117060105120c0d11010909050c04030f021309030807030e16 72
    0x30400540c0e02c05d120707800210ba0b140d4580c10441800e41c81d81c00010054120741e8040c004554003811820700114148030703810300c651801d080070b0284000c42001a103142d169000081440e2140303905140100000e008680003442c00b004808080e20100ca042500507030300c1030002943c04000541d68182c510381c540030303101944449072100e00c1c503400404901074154003482040c1c00c03000080e05611400d40241c4000d81e5940100189076102d100103885902480710740380811112241020a584e8042c5a144070f582030324843c0d0005664000c0c20003001440d603400c009118014a5040d0080390050304070501254581c1d032101c2952100c188081060b01007070b41709100410882c40c10400740504040701c4000c0c1c480000d1072a000c11496218240b09481000e130f280040d554950b44a0300041c024680d070b0300100031506010000d080c0ca48964840600790507142d00a401c1950303108580c044c92600504000c0003e04502e240c007401d15001103820388040b1303142910320300c2c400e01c0115035065041d140540070000c131810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 421336771 1250 421335521 421335533
    0x609030d0c020a0b0406091103011a060315150c01061a0a140d0c030b1c03080f0601050c0706020a03031401050904030804080408010c0306050f10050f071104090b1608090a 75
    0x344540411441800ea4141c082004c00403024002c0c2d0250070040703050801c5080ca41410380d05450aa0f00981c1350500000d40380540c004000603511048581136601c2d200d0507900c900e01040c8003241540461004080c500c016240402050701c0300c61800240036081e03540c7c0d03541e00710b00121506224401810040118682d200d14200c0103540c1d83d00e40c845080202500d0750340104d074550f40200c0e001c00d9030b603a40301006142035403048500030504000002e1020300780e60001d0660720080c100ca2410043e02010404903801082581c06600c1d2400482d2685a642c9600940d513495000e416400700e89030511884040c081c0c40c203e20b0603144050038455007600c9513601100c10aa0041c801d0310710380c60074000810744403803c0c060381c101600035590105085040100308007420200c0c2d60072510545030101741c82000340c1c0100c103540708040c0d4810003c1e15584581071075403141189a10499000d03251500e01d0f02088012061903019200340003810454002c2c02c8015a4003e20641e40520140c5c4401c542d1000550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 421338021 1250 421336771 421336781
    0x170c0609010503010e040804030b090a050106050906060d0f180305040e01121101050c0c0405090d120603110d03020a050102030f1909030905121903050309100203060907030e031c060f080609030d 85
    0xc0300d10301b0030389495664ac0ba846401c80c01a0384c030034002e402c426400f4090100034041ca1014100403030712603a040c200f6000262103885183d9a04070300781e807103060b01e0740c01e861540d02c10600c1c0820400803540054180c6401006d951182c002c10000c0c201c11000428115807015501107100d600140c4044000e040000564081c1c00c80d003c07200c031605c0f581980e100e2030b44450180314020080c3c0c000a1199481e110405810121050503184205180c6202000415040204031000c50320548086100348102e0030100d090000b10350703024180750b00000921680d10800d094403403003568440c540d086840d10b04951101030702d0a600001c2d00080341c0c000107005e545400540101048031707400827660850f03412404410b07003805030201500030030004010408805402c1c080b051010314010401c51440c5003840004840a4014004004041e95174040c00424a01003003100c195121200650501c044298002d8011744458041c080c075071304150b040002d4800c00040d40034064003180d0301a509007511100000c000381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 421339271 1250 421338021 421338023
    0x2070e07021f0b1c050102030108010b040506090403180905010f061e020604060c050705010f1a030a0c060e180a0504260301030f0f140d020d110606010c030216170c0609010503010e04 80
    0x20700071344e0010f10500c50007908101c03440c07040001680303a40c034000000742141c0302031a512307004600709410803610f50782e194580d07540142d01d42000b810040407c2ea445c2e00800035500326006003440d120011039803120301041141140c1495650017200c480d00382001000590180491001da448000840c0018499820261700c02c4964500b00e4101601c40d00c1d864256180d0343c425084e00340e5580c00c1011070001c0391a1100070404154028510021181e585094068042c03203510100224000f10310020381c0c4007801d8a944c11003551104ca1141004090740c0b00400050300d040341c4450900d1007841c401c0542402c460100c0d105440400c0c2145c1c81c0d03458440500d03100f21800c446400c11700c0f0010b40055855142a42554004401052002013000d00070f498041094400f0090208901a0300700e5841c2c0010002d600510a103018030003924203150a91801540c01c118fd00029600c00001c690080014482024000d0403011134082c800304038184540341c46011300042c00180108014040580454406a007107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 421340521 1250 421339271 421339279
    0x403080705131d0a0b0604090c02010212071706011125030501050c040905150604090c11060106050c070b04050d02010507110d0b0405011b08060112110a02070e07021f0b 74
    0x11020ba4242562010034070b41080b9520340800c3c500895021036601119031006102401704201d1000000103055801148501882c0e19240c0341c018580368804e4042d2224000d40d6000e00e02c607814040400342c09140b8135010b00803002c90030300000b0f034650300c03840c00a0100380740340f40940780300315800ba2403c03d0300d00d00019168003000f280c2000030000e40240b080a220300043d500d920780f80c40c203000364541502c0014100d204040410825045290b6400085a040710140700c00060140741c9980e0075960383c140043c00c0c0c0149d0090000005035643c001e0020312034180c40b04142c400458642c0c030203803c0c0703000b10f0044a8004030034030219401540200002d0114030300801d03804a1912071b140008110145081c811075050000300140b204022003402901424007910b10718504035098100c00500c00c00d0b000b01070a040108546003d034041c0e1540d440240e04020301148569100880b04c80a540ea010710b1042201035440d0f90009810188042041d13014842c815440144a94296051001820301c42000e582e00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 421341771 1250 421340521 421340527
    0xa0302030609010b031c05040e04111905270112140102030709050a060201090308071d0603090102131d0606130801150e070c0f020d06110304030203071211060403080705 74
    0x56a010880301e48118450400401e07400070f1002814100000c51160598102e100c100c507941094100084e10280ca005040705000c80e03940707080941c0c500e00500409608a02c50f500301450081141c0c3d091016200140c0302407100007450751003110f00104000c1c3d8004e2404401005215982c6881c0c0d501c242e0b00d0082c55a1114110180c90050072a8020764401000c5214600c0400c011b04100390032200030440c90008000520141d2800350800d03900030501810014030f031f413007180158a1400040a4400081c101c02d07104e03d40640007074000e511110182286004000000600e404401402000160000305038480c0742c81300824032900340c00000b441c10411803100ea010414401c00d2140003580000380304003024451608400b0407407481c002e48440100007003c964000803910031801000c0781541951412140c00390341c140007000b400340d209a940118000410701080c154000060094580512440e024400d05403e050794401c031038589100b1541c00002c00100864050b2850741d0340a1714074181030b49 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 421343021 1250 421341771 421341773
    0x10207050d0c0203070902040305060f091e060406050a0c0507080d0617060609070f1409060706021b0f0703030804060903020f0303091f0e190f060518060912180a03 72
    0x82060100507140002444260300081985000c000400090140c100704614150039526030a485480c010146c0f25800e0010700410700d0180100100403125950910740f44024110f24a010b4940b0001e940a82c0c07002c0c107100c086410085103226101c90f12080d51540e6103802d58950b1022000d4020894407109299114000500040f5440d01c1c0b400710040c0c007003d00b8013440d0401c1003000b18035000e0802d9081080407039100074019080180d400c50003981200840d1241411000601d20b07100e9000c00070681400070810742c8008044d40064581c2c3c101060a82d500200c4203120965111a81d20000d40040d100da408140482c2d00e0b940b04901c558000e20641e52030b12602140c00e8590380c400da800642c294024951030108858046940340c0110052205010a001e68210b0f1680c0b5909082165030408409040704200840024100b69490744010140524035100e0784022101c80780001c00005402030f070000074820480030480420f00d000e8410281c1c10841e9801302180390445818247c0d030007840c5010084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 421344271 1250 421343021 421343023
    0x3040e060a06022812030501031b080c0607020a26071703030c16050a03020f0d110c010f02101518090213020a020f030315100807080f0c090414060a0f03020d06020c01020705 76
    0x100c00211b07200801c1c554994070300501e02d0950020a81c072262807140090110700d00105289501750411640d86807034001d5070000461606144d0300800640c10440b040355402c4010500059140d1444003c0e00c49142e51140410318040310700ca02d0b88200e820800c0000c0d05c4a401d40040c0c89240c00d9a1a01036480b400b55031142d00d005004001540541e0161140ca80c00190030040038458500600d800000703d100d0307101203035413070034041742260500051042900c3c0203403082000d034040050303d15043c40b101c4250001201e091044c1d0041c3c032114140071840401084541c00f03614400d5502402c0308110200300013003031009400500c0028214000c140c2d43d280b0383d0100304041c5004100320031554140342ca00b80b0402c800105620703805000d00440004000c0026001600d450b071145250a128446655030481c00c0002c2c8901c0c81c025520500d840314603080c0d810000700246c031402d02a524031b6002c036120184100300301694031000f51b004446504e8000010025000307482441640d1b000036007020340c5d82d0b40321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 421345521 1250 421344271 421344293
    0x30a06120317010902040e0103120e0307290901020303062b060e011a060f0a020106030c06110c0406120303020f070605010b190309030c030f02160803040e060a060228 73
    0x150002800424101c03080d240810910f030040806003801c502d403519061654050490500c80a400140c0d42c51700c1c0c0c02c0440c012340340c1801840e0000c0540303007020b0715910242d0b07000300039120f000344240c9844100c0818009000c112100e41c1e00503001182036903580f80c2000014517408084403180e50300d501c1316884905c41440d48040783c52040c0303404910b00901508050031100a01130840319008401c0c151582a203030340003141c1146910b091240d60f80d09000c00241c1c058099544001c0030320070310b41400a15281e000011b400b48611107020b5034000d114020030001640e003240501d000000d0888103841c0064029030003400c070500d42284041c03c00c0000e40782d0a08440e4240d00955006d50002032070718401e59110200702c043c100600b410411400715450080c030300780a451004050080c580d025806440c000c2107405c0f0380302102c0710301d15035094407084110b4581e0001e206030440d0030070010100305145072203030740007060742c10942c0141482107201c00101412007070031408034180080300700c403403000c12044061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 421346771 1250 421345521 421345523
    0x16021e0a0302011109060a200d030207120f121d0a0302010209090c03040f082a03300f10090c020a03080a1a091b0c01050f010b0a080705030a0612 64
    0x1a121184640c2406400e54051311840241d03c8030400c21101070b90b442c0c0040d01d052440a1819013400e440e8809903611440b81059141c00c10710507280350200003503054000b0003c140c03103440c05d0400c0700342e10542901c00f049203000c840d0100d140b800f00007192011543c00701d03042c019000340440748480c1c140b00003800e10307251070025070060f500050240f12031708001041a400c541c68030840c03840c2d45400d44031043c5500e41084000d24a500000d20000c5500300e02c4603244d03148100d800350110b0b40360581c004560300d5000e19111a00054124046400307900709280e0b54501021000204010b039440040405036404000c214451410743e464002c03819166502c85c14035204010340060181e28054140030745801d000a0403012100c3c1098200d52004408401203d40280d0907101c21420761241c2c061016803030a42811000039060204d07002c415240150800343c06003d05e040485240e98840f14030102e944035038a0810003242c180008544614850f1008550101303540500294246c0c40d0b0042010390b00000300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 421348021 1250 421346771 421346773
    0xc0e0405090f0f1209191d040c090b0f0d03030905030304030c030306090501180e24040b010603050c1605030f0703120b010f09050f0a05060403081806040e16021e 71
    0x180c000600b079002c01240260a8202004040040c2d24140000d00c03886422400c42c00741c001c05184650056420003804090b107a800c0c0321805941c60100007078004041101c082e1004202010001580010341c4a083c20181c0e0103000c40382d04042c594244400c10140a01c12002c050781c440d5003c0c0031035414000b56015a1184d034601c0020b00343c86c10001c040d00c1c050b4110040203480c10b401045049089801200907100a5101041e540b0484001070b00b841e2002e071114028400c1070030441050480c0c04e000500c520700c540d138910000d9803604000c508032001102d136001114000c0141038400c000c00c2540d0030356548a2412246880414010081e0319040101d00300c0c003140d003c0003404d620014600945092031028038051503030310313017900303008120b00b07c14840c26008440e00082904140ca9040c4580003a01380685502c0e559996403a040c00702c0da00161540700d0546400100c0c64040c80c003181160110342c12802003d043e9100e408204a40a0100c0c01580035841000209260740d10007042c1e0408807401c0310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 421349271 1250 421348021 421348033
    0x24062115040b09010e04030306051207050a080303332707020f1c0302090a06050301050a12050c06160c0f080c0103020301081e1e0d170f010501030c0e040509 69
    0x45002080a0341500d0614030403418400020b107942c4a60718494110340010310b8042113030703e4500b016030040c91b05410164002c407600300c8010070300600090f9181121000d650800300595503041d1a031320380c002a02d400c4409681d205030100440105440a207404500c0c11500103280142800900c00000ea180005441442e035a060300e80132081315001580200e040c0090002103105213841c6842e40d80901003200140340002008120910030303810303500030070320140c041e00000d926000080c01c070790024030139548290f0141c0c0300441c03102652404c10303132800e92100c0203040c01e0340c544041013540e411080884028000810200000c00d07600d6170504010a8498081c00810f41000c1d41d032420404020043c606241c0104010808010005080c0701e030100c140c001940751809130817016003030400c0d448000d05c0c4030702c014060030359403d00810b404106411603191f4001c0d604034012900d00490045039084226100d00300108842d50094000c403171001c1e00d6180c014090140000010304560040e220851998000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 421350521 1250 421349271 421349281
    0x21c0903060b010e0108220f1b0f030c05040b01050918070e15040e091f0506100f0e090604180f050c030703050d050c070b030718060305240621 63
    0xe10030950100c8003840c0c4501c112403d440007030600c000c080c040c0409401221001c6521f00c0c103c43c040140f83d079100001080c480f2040c10060403903540c07008290a924030a840008015480c03c880714116680034890114075442d080400c40141401d02000d03047c0002000100c015994000c6d40300288078004480002da400c00b44e100a1261030285151401445e10b041810b050b581c500003580c08036007130001420302d5683c0c1c000b2400d04040490f0101140a00489030210009100303400c200d2041000f504d0484048030340c80c4003250303050340380703841123012680601c4940c110342000d1100c2c41c1c4c4688064004108804030280c10234881000c0c9400342c2c0e003140031201c800e0820000340241420380c0c0c2c00720010025a421500da182e100c01c00d0540c94030500030000740c09505420180301020061a40901c0c440d282c0c50301c0480030f0901d031409288001544a0300c2c1c0c010030f007a400303803007200e00482c3c0c0c05003480d0351014070f070880144018000010316400b040c144059603c1c0b103186000310544403044605a0319070300340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 421351771 1250 421350521 421350533
    0x142d090103150f06050a03080d0f0509060a1b0507030305060a080d050408150c030f070c06021314180c070804030c0906051507030c0809190b131e09090201021c0903 72
    0xa414840c1e03209401d1241c01c10507030b5034080c1040141d03238110700d0700c0750344020030b01c801d200600c1421b04a0382c1080c109000c01200603c0400e105110b031071070780d90a00200c4615100540162404120840418400d000311030101c1d2090b0301c03943d423002c005008002d0700da48448417039103400c01008000780044c1c00000c0910003285e091005140c80071810360303900c209050481110010340401000080807081040010f44c055108051181e0f21641001d0110b54074400440d034001481c100b80200050f0005080c1c1c40c8042c0e05252208442c00c81e4420010710b0b1641711a41800c80c0e50303011003401c3d40c02030014407002c0080342c241484030005000c04a000211285010140718146555000221030401c1c2131116070046500720104254040d072090703003541e81e50401c0300000e21a42c0380d03414414030035a00c1c400c00b00f90110300b8001854842c244c40204071510741d403480150000d0768200e003680002c4800c0c81040003250410b820507170300684140150b50340300780c21602d0901046207902c00c890008058520070028400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 421353021 1250 421351771 421351781
    0xb190e15011818021927180b07230c0607090f0608010302210d0e09100515030c07081207030c030203010312120b1203030907142d09010315 61
    0x20303004005001c00ca07910f5480d656940c40203000039020704660303400c840c4001006210440a080720304d2203001107010303010710f100d60156a10703022424107140401c19240c400040c4299002c2641c00040c4038101d0340c0b0b5a0003210f80070f0514240c2c5101c207101c00c48807450b02000750702402c00c40700a074008024501c1e040c1c000602d10f0070346604c10040c0b90f48003007041c0611948400c20b40c1c1501d80540c1c000080800b14514030b1170b103a400303100074200740c01401c3c0700304c0745140d1080c240f000d8200e04481034030043c0c07126000c030351021030325104050f4000051400c0420f040311800c095a070120360301c0d581074140202a11940c5082d0720090b2802407140e2030b07804015009c0c2d0940725005450100d450300314103641c19540d138000750b146914110410712900d028000000d020799001010f940380007401480e2805a07004202d5940e400640320000305001301c130300108400407503200d1050207200041c2403c040c1d200e5040c9000c80c5500c500c0c01081280301d1800381200ca0340310001d00c04e00075031103241c04041c0d03002c1010029080350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 421354271 1250 421353021 421353059
    0xc080a0f06060f0602100209030304051302030601020c01051c050606090a03030f080907061215170a030909140705071110091d0921090409060212090a0b190e1501 71
    0x10002e050f0510209a0020702940401c1500d5001170b0780c0d0301040d000a2440c025a4401da9004042d00300d5000c51100c541c010307501135142a000c41d00f03040401c2e0b0054665014006c1400421801c586c02ea6031101601d41003030350002e40241500c0e15014080000c00c24549094000390041510854294001e0360b004c03a126612011b40780191281c9401c0c40c90080411180c0d544100304a074494510302d2903a880f90000360004c1c41c021127611001e03c900c0500b503454603051b41040d03001c5000e100d0009014110b50062151421014420714425a02e00c03800380d4041d003001a0558450710303000c1803421940c0341c03030301e880e4409070090321a030301c4151030f00609034200d0b0702a0401c1070305101e4800c288000c08000044040031181811980f955124451446441078002d80c2c00d2180d0207800c18981002344503041d801000704003041b6000900d41e40c3d94584060741c0c1c50300c644004102c44104000202049844511601c2400b00e210000c160002011340b9a45000e1414101c0c0d02001c100000410000d0f601c4540d41420b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 421355521 1250 421354271 421354289
    0x9020d0f0309090b0f0d03051327090213021c0e1b0102030c060609090a0503030a02030603070609150810030503030702010c0e0a0b04031209050d0309030b1b160c080a0f0606 76
    0x20711021310104482010040c011030140c18444000ca0030035025a098070725519499610040d103a0352080304655003800b42c1c502a05002c09100010358617a201d0080a901741e0b0003400d03070b003100b04541c1c060320000d5000704c072001d2000c001031900c040781c1761f1203018402440442c1c200510510501c0004840410859203241d410341d4400c1106014103000898a41ea1224048420000d69500c0032010b90403c481c0034401002e030301000081100030045d50780550b0007100d0541c21552015156074040d036046c0034a006241a907400f0110841040f44244d4078107510000140310100090350341c4d55520300d941c2041c1d8058003d46d45a41404441031f900802040c841c001c200c4450209614203113015561f81f0a902028044150f03800644042c540240209030080c08080c0544141d042a0705005043c41c5140c0070456140c0000300c0030400c421540701c003400e08001480241032a081c20100d5661072440d03551411100e450a1080001c6d00c1c0d0014006a031300ca1340600c045034000126403030070008540080c0c00200344 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 421356771 1250 421355521 421355531
    0x1c0306081b060f0a0314010504050405070b070201050403020919140127020c1609050901020f041503090b01062304031a100b16050d0f020d0c0609020d0f030909 70
    0x10060001400d00010500031405524074040c500860702d94454480e400308240c5001949602580d4186e00405610130241024000c071390b2100b0030130042d1007090b40c02074503540c17007501d044c0110340445000307002007841410918274080d41c1c2c3d808554035440480304400d29018142d10464600300368081c182e13690703003414641e50080d030404440120440c035122010710103942c4a8141041b0079081d604598403841160201c4c0c1e0480c450307030107084564050b40142540c0da424100401c880314014001d442d0b680e544440e01504040c1025204030103078003200c0200c410191140510800716050608460103090207540700002d01583d500302c22030b0a101d00d025220001410401003010696054110042ca065606001c0454941c8108910780c0c20301c0380c21001e01184000399101d50301c0d0744030003d921514070400036100148504401aa215440300d0300e510b02517003040c0c3c0c502ea500351207000f00d41003480c440d260000f1b8520f12500482c40c3c1d4041d02c00111484d0301c91682503000d050b00a038600b0000c021580c01480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 421358021 1250 421356771 421356779
    0xb01020c0f0603070c1509060b2e050c010f06090b0109060c02030d200712031209020a182703110303190c0903051f0b0307120b0903040f081c0306 64
    0x1100d10005061004001d00c810a180030451071000081046150b15030501c009405400c0034001407d00c0a001c62145944102e0700301c201850784106002040c2b0781d03290b5410110f609505503040d90006800c40241d5584544280700461584280000340030b0101001803107002600014010000ba50028001c8c030590140c03440050341c00080300d0902d46260302d400c0703524a0000644146130b200e504071201c07440c0601500821030010942d4500340d028003a0f46c0c1c0400d0781080c4074032401254003480f00650040703102c4100384040e40d10790b00403403c1000c405500091b010740841d1418804612150807008581d0105509001d06a022a90310020318a500103989103082404a01903801d10607800a4001910740e4800c618182c015043c401c011600401943c00100c8103204a0203c80342000600c4181460b015508105007030006000c03082d0f45c80503030100080d403580d44800c01c8001004200585609c0208000705604820101b4180246070790030051000d1007a400d1030300058412421170008161910700100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 421359271 1250 421358021 421358029
    0x10c1406040203070b1c020d0605061908060402090d020907091a0306090106030c0c030c020d08030c131a27031203090615130c12020c0c1806060406110a0b04060b01020c0f 75
    0x71b104400c0d50b43c01a51045003e420790007500441d80a1603214201040c1751414a14030609071650340c0240e0303a0300465039a1841000100d000b007010042d00440903c02603401802c00c140603d0700846113007031499085a07551f2241203071619950080d4440035000c428040c4608021003101d0140025040600c10809001001000081403440203410080c521403a0300c2551074445a03441c22540080c0c40c1a580d103481c0300c03c114140d00c055003a1149030300344480001c490003035a003030a41c20349007141c040b4900307549a1000511545800711059400c0c141007054011580c042101c03803110a010700003151645440018103040200041014a010b0344908601d00c1d666501807800c0d1442c80080c0001131104c038658001c4407030401188091017010303c00611034045035000609212444c0781107441c0030765000a000d040100101c2550601d400560901c002d11045000e10360ba80d40a030804000c46d0801540d0361581c0101d02400c1d9404c0c0c80043ea02c0d0031030308407960706022002c1c0d5607006841039108916180049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421360521 1250 421359271 421359307
    0xe0105011413060b040605040810200c03040b0c0a02090a050402010c0b07051308101514060901020307080d021b060f0103140c060d0f06060c0c05040b010c1406040203070b 75
    0x146215071181d1126040b04515035001c10080e040001070b8540f01d5488010291503070340b04c2d01507001b1511a01822610b0b8900700e000b020801d40c0000d4500070a5002e884c40084650008000c00201d80002e010104810340000c016000f01c04001c0010b08040450307005101c075020001d03061201035800d28041002503604030500300c1c05182c6c0503040081c0f03681c4129041b030741400385aa9603d1038115140000440540004144504000010301001640c0700415900e030300d00034511a0201c6800c1506000070710380b034260081c0c02082c10600540e85003188036a00c100559020300000380345980e001c51110101100d07041e0309030100c19008024259402c00050013100c818051000a200001940c2c0f81860080d060290040300760340900400c0d11100c24800d054003501c03140001d1100146404400200380e846500d606040701e42100f440c04d8450b051806000191030307100846030501c0b154202c0000020b0840601031040c00c0940003401e0355007031a104050400d41c1e0b6a00140c0f10190034000d41c140c01601100c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421361771 1250 421360521 421360559
    0xc0504150503100228170c041d0105151204200616050d03050c0904050901110408010906110405100503070c0b130b091c0e030a02060408070608070207031104020a0c020405070302040501030e010501 86
    0x10a01e1990b1102e50581d0f0380e02c08c035009103076000b0030b401211040c0c203155081c16060712002c80c0e103203400001d1465944201d000b1030503035580307451030034001c035004c52a0840480000d061003d150580005448003140484d8002c11404002000170303035030081803010a1100329000303038041c507051007981010b10051101d4083c5c9807100340704980d20000b0079500030702503000c6c00c600300c1c42c11851070f00c0300e6031440ba0500820004c070050340c41c1030a0016007502407186400b20340a5503001040c2020b640c484c0c007000c4803a904020b0408080c00b015540c01d40100340070511040c400c2c07103c0002e0740c813104540e140c8009486809840c1c0e02480e03010201458000d541c0740d0507000303903000518240340001d0b1078400080c544610f40304080e4100700c3c001004141ca03180803441c0c100f0f0f074800e600c5800b402e480306041260754440c40c3c840030303051280c1e002103400c0030b1600c0c2c1c00070315003500c0794030b40354940124075000101247e00c15106000442da0000d0100260350300b50007149514504807000b04070710341c5040701e1814124403c40b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421363021 1250 421361771 421361807
    0x3040f09150305010c05070302070e01060503070f050c0106180f060b090409061d0105040c08030313230d0201020c190803130206070501020304200d0c0504150503100228 74
    0x2450400e10700c0140310100210780003002805440c810200c00350071580880810350041c003401c04003217200d02e1036410b1076040301c07031965615165a03500c600486001c003ca040a00400130f0030030a01c4000002405420080e101200300704003c4101d0380090070440311b4001d02e0b20440760404200b004000c1800c01a200e461a01742c80202d803600c00d0303103825030040c0848004402070f00040640043c0c02a015171085128610590860410f1502d401c50903940e030004642c1d207250440d42105000005100a080089034900c3e103128180d15220b2041241c10b228a0003001070060b076001c110112403860411048191120b012944030409071243c455850600c4001c1c505c10622042903060b00440d2941e10840b0200364000000315100e003410f1406500d0f079800c0c081c00a1031565001807208444c80c1c0014203400d401e500010076030700c003403030f080c18080901450800d003411a405c18000082c9510280022201d00214400044c0e50f000d61000808690b0540c4811862140281503e583c149030040503018480c2c410700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421364271 1250 421363021 421363031
    0x101407090311120709060806070503010b0d092909070b0a02030f0306031908040609050f010e01082805060306071b03050913021801351003080f0c0c010203040f09 71
    0x180100743d91449080003818a84192500000c50b0410b80d40712000381c600307040c10742d0f03c01e88074a6011a01e0340400e01480b00c049108002c1c6200304400c9500201d43e05204620041c0000c0701c21031845002c00c03040400b081641c45580030040240c006220440103050a003099500b81814000c0003952030088400104541d0000004030300e05503801c10041680c0b8004290b5080fa6000515000b00c1980140c0f2031040454a1148003048070b1034450889840107006a41e2050400356100044611102c003034a8040d80c0d40110011841c3e11215144079144000c00c1080071805003044d000345441e115004214004100380d018030485554001114400c61503014508152140c3d0490001070b102d01c000c5c8560740e00030340300103034a2083c030741c038200142407100b4242c88049101080808068860302c1100208540601c48040c0700c040120020b0196089800c0144050400d51640d40303036606648000410000350b400401c584414003410815030a4448003031010b107040a15009001814048070f02442070426203074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421365521 1250 421364271 421364303
    0xa051509090406022209050601020607210b060a0e120a020a060f022505030607030501033305070c12020f06060105030c07020a0311010905030604120503040813081014070903 76
    0x2d50181c50317100c0381000d118010b000c034110762881c00c0b40c103501c03c1498031820030300090260f41c0040307140c9120740c082e51940c2074003120109c0114000d894800d02d1070b000700d6a03020760700b10649030000602054010764690460401c031200810009080e62428144a40d2140441d440140c58070043e0340115140c2d400e0046141c0100d0300140d0070b040004001c2c000000000000800710f81078655030341c1c00c035a03040e0300380c5000c0e0b141c00d6801c07800da44003404060108008400c10805070100e2205284541c00500c0088041d407561403442410b8400c2915190300144482e403d6000344101c52540707a00250f4940003e08050700b1082d902512600028042414402c1c040002001002400c01310b42c02150300400b840072041d12481c00001d4507100315403c0e80050301c24540885c440c10001942d9000d5500500072200c8845400d90890721540300800c100c80d0003e0600035401140e1900400e10041c12262016221803c110801403040303850305001c0e2040c50211034280503c4540144881041e0ba401c00c000ca0701074104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421366771 1250 421365521 421365533
    0xf030c030f070c0e0a0c17040521040e0c07060c0206070801090908070f05071a0c031c0e0304030b1f150e27150105120f040c0909080304020a0515090904 67
    0xd56404000300520404c20089810540e03031200807101d00a40784c405902d001c0d60401c440b02181118000c0c5550711940300c0b4145440708814100056400d070b2007a924003502d4468800f2001002e903518040401e02052910410401c0e02503c5280e44152000700b8003480c20f500014803071403041c4540200345a8451081003404100303001c0302d000c03e0700940705210b0760000385482c5507120014440c04801c1082c00d0305040384924600308540300800100011070030408203d18540300c01c5034012a18648075034070000d41c5400442400500020b50080e00480224074144420303003050415a400744810500001c020f111a64030070014009800d21403604158502098010812866901d141f0904101c036820401c85060348c5600301911400b2030b0b0b1407002244801c940156141d000b1681e03141c80306480d4600251805c510000d600790300c640a02c3c441c00305c003640c40305004100ea003881402d8520040c004200300c10b60a0514905000300b40549109045c01d80014106501c1e0117a40407d5206111440c085018809 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421368021 1250 421366771 421366793
    0x40209010c060c032a0e240f0712020601080c0a0e0408182d0409080a111203070504030201080603060606090d0f060c020f100e07031104021210080f030c030f07 70
    0x1440f000507290300143c0b180102005406105c2c02c07400590121480821170800301501401440c0c0f200390840b400c2007480c503000035500054561008800305010000100304001548500000c0301d4000c2d101e03035410656500e0400031001c40311801790031078a008000399000040101e620540111040da1a6005500c1000c07a11811680d041d6004191070916a122000c480101b0321400121840d06525214101407100b941c45002c006050ba000034000358958602807041740b842100048241c07140c02c0850350740c02d03042d070700f041d40c80c20001203000c0f6043c811541c10682654114404400511980c0b800000180302c40c03064a4015000d5030b011154001007140f039130101d800c02507014400b80300e46010007100035606d400b0380c1c1174404a841984800315140303d0030301c170745040c045d0f07031101900f41c0c58151780314450034070200034206810550800607803c2120813290018014500c84001301030b0703103180c444258035000c200c00710078034680c00811490341c100b0000030072240058203400c1150740344d8203241400200c0700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421369271 1250 421368021 421368041
    0x1c0303020904091b1d0105040e030c030406030b04050a18030f030e0f0a03321c0f0b01030e0106060c0219150203090910030203151b0406120b040209010c060c03 70
    0x75041129800410080410b00e0881c01c00d1109140303101c5540e14514036080781c0300c019140700e040701174005001307a01b8590841d80c00400c2083c1224a06420030b0000c40c515032045d07010b080004d650310007440c3e0328500350240981242c0242d0041c41240e003805000300e41d14000d04402403d005210500c05405da002e60050384400420320241d43c4043c00402c19552a40d401c2e50003100007518003d9050791140030a0314071140c030f100e1000000c10f81030040745007003102d45c00541d92181c418031100d0802c4200090f4002c05404041c244000b02d501800f07800050300743c40413041003100740d904004050091642c4102d805043c9901283c0f16400d420200091242c0c03c0b10b2500101458134051102c50410f603000801052004c900391524039a690b2a0896144074048034000254140c01650000f40813050040b40d194114040100c031510074050540d400c1c28aa204d03905c07190100c2c02d030b162500c0403624513100b9104c1c4028165419490f1903807030000200f10224418000307012036a581400c0f0f00c250320a41c0308039242 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421370521 1250 421369271 421369279
    0x30c020106120501321603110a030b03060f070e0f0402070203010912180311040c090f14240a0c050102040f0b0714070e0c09040e060c04031a01051c03030209 69
    0x1101850500901800305a502030079138070180c2c1502d104003190807100a403042d210708040c0040351030f160400c240c1d428121110400701350711103a52182016423500100481020390701e0002e2500c952605050400b1001803125104c03240007810003517441e8105901c801e0301c0c002251126604000340340010020f009000b0041d4056107443d28000801c640d21220b407404003100c1e124410100075191005400700081e000c010003071a48101c480c0308504054000c60340c4102103080c0070411a482e0354542400c08501d9008076081650000c60581e00c1c1864070f0740210301c80100c0240c00d10030200c151210310910425018408004604c4801000e203e4294182c5010b0a15005030303480345542c0703007500d80c141e07080002c050340c001e002210444a4840005200b900300c400b811900d48990f52a50070366119031b044203000940050311124400000103003031011314402d42810a40e00d85480c2142400250052909100000450740d240180081d503101040329201901503000151502a01d00c0e0032000ba0260400c000d0700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421371771 1250 421370521 421370549
    0x207030807020f16090b010309120305010501171014011211071205070c1a0706091b05330d0c0314070c0b0c0306010e12010f050f0610030c020106 64
    0x1059032100400d80216110303803ca950300ca00d604180d50b01d034441c01c18405944800900108411011504000180e034014180050b000e0032075103401100c8248144c1150000b039850300140021340c0c0044d0141ca4456481222507038034030380200300c1e008078407c03400344200c0f101c0a2031295400760703c10b0701c0910f108000c0300c40c240074005601c0d0b1510340316009984111400311152007401a040e1140050f59100c80d004040c00703004900c1d0024000e86c00101c405815608102042200041400d80c011898583c0c400d41d0b8101001101c500451142d01881d0400b621810031100b00482c000015011510882c920602d81c58124000010440d07251140101c070400040c00c0c409040c40d07550b011741c400c0c41c0c480381c04d4600c02940c1c0d4950100303c5804141500c006d01a6170075502041303191103c10061580070710181042c1603107000601c0083c940240300d03210701745143c0d121040c0f60901d03016170152640140144050440c1da00702440000d008501180c00101090790b5074041c102101e100350000d000401e000403900c41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421373021 1250 421371771 421371773
    0x6040b1e0c0604030210020708161713050f0f1e0301090c060c0302061b0703050903011104030c090b090712051f2d21050102090924010f0906140c010207 67
    0x180b1602c0444003a405070040103603411005009000701c2e1255035104000c40d14002216401440001d5004000d4500c81284e511034141202c5010040c005041e40074003d41100b858881000004800c02c1c0301e01d4001d000525005c441500d95105d2040d1700c1344180c1080e52110b1003903001c42e00522292a0181980c0628040020a51707040f01c1040f0000c3d00942c00d0396640e1303603468141c260100356100b1100a1010400c49800860310450240030583c0c0005d0000c40e205424540d001e050342c01641003591a600e42c548104094030361f40c41582c4026409468417a10707464070318005030981d80840d0485803142d80342c400090165000070f01da040c030308508411032124152030318052068400c2c0520181c1c40c0c0c1840d8044441203e880c2031940040740c81500c20321708020048101c11014100208044400d59000e0000140b240d40350480603216082503541001c04849013070b03410f050b80110320f4640313050103081a0800300c1c10348c0c4400c1103002d50ba040c3c103040da60000ca40303644850b40e11500096403800d51000c141d000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421374271 1250 421373021 421373023
    0x121c1202040311041805061308040306110310080703020102030a20010608010b011205010302060306150f030c1c02030417031806100303020d08011d0c070503071101120b06040b1e0c 79
    0x2480e5800305135010882e86501c601c407154007541c46100904164000c5000503041220302c1045208a0720503440c0034100307983e0743d0391441512514109840b2500c0c0c04810080d482c0d54405000c4018855440100b50003461500080d44071702c140b0494800300090001003082403050111240c0041d08404000c101c003907a120107060003010210341d61400035141e040096034911060141e00e041e42e8008107214559144c960400140c07016111080441f03e0007848040c8505c440100079501c00c9004151080e030700d14119002c003000c541887d070924081841031091001090715641e40040c0c0282203124143e4035201c09444850400c040d0039052600d100d40400c000c584540b6030352840840740301350200c0b00050b03001241030782c00c0d102c00d0248682c00a8140a910b490304100c000352a0444000b206c40d900e4182c0c50340710305095910411040e01c2448088010300035070b5034040caa44a45102032031042001124000004c1e02c00d00c168030408030914008030743e440d840355040740e190300d8110269158980d101c01034400d0f5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421375521 1250 421374271 421374293
    0x504180b0a0b0315150c1b030f0d080a20031303020c1e030f0307150c0c29100602030409090812270a020904061d010203010803120105121c12020403 65
    0x201d17000d0384030080320740003c2a07907400303944070002404d01506000424003031a0720071994014989034144600941c500c0c11b801c007404113002c0c90903244d03180320307240c0382c220080c009845012005501103101001d50a0034882c00d00107a07900070140c0302c10008414a00c0c20124a0702d1005107030158407a10b00c0011070040c0480ca2001d10701001c06405039980f001c0c00c0c11210392603001714400079004103001c0ba0302c4c2c500382401350b00c110020406407c1c00d004801054030f032007025107500c0002901940c1030b188441000160110440c0d40b0000b40403400d13044600b032002c02502ca0150388180410252134049103000c05c403061066401c5110f07520b0701c03ca0b0758a03084a16041504000e065614020225002d030580a4004554440050380141c05114282c07200e60b54580245103a031031420400380b1920641c5a5508203000840c000c1c8480b50095446045e1b05920003184c1030107074409442074426847d0360f8a11500800c0d118003a030401c40c00460a40402002545c3c505202401c040040e8400140402001031309644 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421376771 1250 421375521 421375561
    0x8060a0c200c0111030d02030a020a1808030406110c0301050a02070c0b130b030a3b060108060103030522240507050a1403070f0b04120504180b0a0b03 66
    0x90581c181d0410601450400104200c540302038106650140e61035000342080742038041810101c9240c0f41040010108030f0300140c0d00000e5094001419141480d40020300b02d8a42c2400c2070308014440c9010701840e901d00c5171784100c6007401a002c4e04503040100500103030101c40c4000d4000e2286280030401c1000940c0015400c0f20ba60181150100746102d498003560302e030708805c0100150007401c1843e19201c3e80c00081031912125101c0c0506801c1d880300e8411120109100403801c21421181ca10400d64075201c0c2420a0640d4002001000b90b0700303000901c14110381d0981440d035a00c018051170700f060088140e451495007a403100000075101c01d507a151240100580841c44c501c0740408804880c20710034003002900703075440f90005102007803030315035422454621101100d00d49010340d034810415000b101310a82e490514101080140041301d10901c1c400e01080c0761051400d420030405111102d20081d01c044c1496403800c00758040e4031036004c2d03070014103401d842d031036102d10340403502444001d10080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421378021 1250 421376771 421376777
    0x215010f1517150409060c03151d0f04030e06071a010b0703020c12100f090b09010203070215041502031906272003010305030304140c0906090702010608060a0c 70
    0x8400d800144078041841d503842214000a28507224401c40b0800c3c4100a0009a800780e9205119000580c940c42507000c3c1c0030b82e589001c0b4503100140000300d00b4845503030103500d40d42c032140070f008050181080b0160340310891101725601a1034504045480d02d0443c010203410400006218051003004026202d0361004c54603031143c00d80e00d03030803003100324020050001c0140e400b21000000d140383c070540c1d4210b818040002c907808071501880500c1503034084043c3e50f000d9a50323080740d0018040c01c412136542c4031081d200290715601301582c0007541c0d210307100c0c1d410079820126408101007002d0384692400c1101e1004041d510b0b07003010840403040c00325210039001141c3c40e11a00040000d94401c00c0c100039001a42e2420340b500a03054903801802c683c80b81c0d007900e164104500d100340030083d00954040c41c000c0380115164517081c58504029175104121074050362091000510f1039440704c9585130b001c40240c1d0780356500e485094050340500300c076800c03580c45402801d04201e4101195130041040c00055030f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421379271 1250 421378021 421378049
    0xc0501060621020307111b01021209180903070f06021209060601270801020a0509180f0112140a051c050f09010e0d08030403051314010e010f0215010f 66
    0x20029102c40240407456500380300354a494104034180e580c00396600940f507007800b90422003415019800e20f1300001d80100c400304c0030420f04c01c040d64100031700c00d01c5081c203507806403070a030f17001c0005103226800b0100220003055240020f0501c803c14010345007515070051001000c025030f0700d462406908100080b0008030701c1c5400241d80d82c980012143c1c010310040e10f8000d08400d008202e04048028031103072601500794a18000b54049092009254001c000e964003621907100608200c51110700071030a10078400f51005000407a0000c5540a044030b0710320400000410f010310307003220b103c00c9000003004d00303000e5102403074180070000c07030000d1600400651707401101d15295000d4440740140c03007000c4002c0d84140211020365001742d0350b803021380000400c111910f0203290b4443c2d2499108071001c4000075408181d8400004c0c1f180201800341c0104c1c044010a030040b030300001c0107034880341c0201d03040181d1070041b4213013240240900141026081c14020042d82c40c0c00c00300050f03584038800e64200300704030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421380521 1250 421379271 421379279
    0x81312110612040b070c080f0d1b0207150311120411060c03030109150b07050d0e27041104090c0302030c040203060904080703140a21020f040603020c0109050106060c050106 76
    0x1110100003800780318480b00e40382c030340715240320080040141d400d101001c0c0e03402010508040140c141072803a0003050742e50310322014000042d03540502c0500d4501406464999101d500820150241e03011504042705252070b10340b0450103004403091018007078500003160f0381400440701501e413050703008540301c0e8052011081403040c036105111070b485081c1c20900042c4004103854208851101c03900391440403007603c8a244015591209200b2a01070f807045035902c68094101c81500c03241ca40850f41c1104051502c1d6064200f40da0840344900300141e5180028108415086210040304024204121981c83c919192550070b0840c081640300703100703451140c2c0e52454207000b164418500030b02900c0300c40e22155154012600211811000d029000418210b120340801c0074100c44280c69440c02d8841941c041c044003c92a944268949a4010041c0104401d03050003101c003110b1161400607a00e0030083c41144c01071010080c02000e5508002c0002003695200201031400c41c00fa800810000b956 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421381771 1250 421380521 421380529
    0x201080108030a1215030605100f0617070825030f0f06080316080d0f0c2c011b0b09010914010204051503060f030d12150810020708131211 61
    0x40c450320f00700142c12030080c0c03110104107400000601e26242981400c241c2c0301c0da907d0054440480e911b02c843d400d90b8808101e602c155000c0040185828182400d1140c100f85401017040c00051400042c042914003090920302084544000c0c4100200c101d070800c21911402001b41c0008503e220106040c1603c0d11003d05491042d88101c03103014009500c1d08801c0c034030102d40f04a400740243d4000c0818003003a0b0801045020301e842d2414003410025030010348400c0941041e4403500202d0301c5086c0d042405444030000c2c81d0b051046030013401c003607c1c501c2c01864180340524181d18010a060002700a00000c90815000305010511a0241c0d40e0000400072100d400c0b03001d40d1007015480745018101c60000c0c00b101c0d00640e003100c00609504035000e02e200109203003444030420360380010040104049508000e110740e4500420918120707000500e4050301545c7ca6080346090001c4607030000d408410000024120380301c0080701a843c403281c0380c0d240c440d003251190816050358940c0c0c20f004c4004940c50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421383021 1250 421381771 421381777
    0xa0210091802131406070c0905010501030f1e0b03030c100e06012301030b0f0d03110c060a090506130305070b090a1212030e1018020316030302070b2a0109020108010803 74
    0xc90f5040e420360380d281108421000020b00003058129808025041c0807441c00079594024100000340803070300e54035245c001022104031011a9040604d450b403095005c01ea55200c0d8580c400800c3c4011034000007031000a41144560440e1001e64401c031551440b070038140da00000030b886548000d860150780c6e500c9086041c0d4600400e80b01d100f154920312a51150300030380c044143c642c0040c00305000b450b6003e000c80c050070719403c0d00360701103840d4040c1081e40b03420401c101c95100e80f050360201e0070b241c40c1003400f6280c0c400d90b0240f00d1040002240c0703201e203203084150000003103420004403811aa80d400e98209242d0101481c0c03405410203410100e140d00140d48034181e40c5601c101c40e002e115001203c120010141d00901800d1805a401401900b030110701500080c16000d141004200b1100c2c8101480c00280800c281418140c0103420008039401082800488503690040b80d650340c01c1c180651806441070380c1803910b001c0080d1a004030084158024811540300380c0301c0000070790700d440c4880e81d240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421384271 1250 421383021 421383037
    0x1e0a05010c08041502010207140606040b060c0c04021e130303110d0905040911030d020304060e030105100513180f0201020d030e06010b07020d0b010605090306070801081e0a0210091802 81
    0x2c0010041008003110510700b0050303224040c0300050520029540e07031a2603804034003000b01940d12101c240001803902e8414405042e80c112640c9181a4140885540b650900c0107140d200700ea011614044800c49120300100060004020310703511100c151742c840c08490319000550000e0158000c4480c081300000701c1c004c00d51950b841c1c02e0b030003910741003c000190404803011030301e0115240321524640c4040252040544882e005141c9850400f8801070104403103481052107a07041a0910130780d484d01c2c042140540c4c1c01a20480140461a107800300174100080801800100b0701411100344001d800b0781c22030f090320076825948298903403207044050b00c2081c0a490304076000700e8010031070a03005100a050107480540850000009512550402032090f80f140c400b1074030000d20020141340c107206041c1d0007401c9040c0520301d9418100c0b15655460a107000400b0008001c0700f108203904100103148025900910803500803e45882c02010303070610b03106000451401001940d80c402480c002d440d410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421385521 1250 421384271 421384283
    0x50d08040c0911070b190e03090a050123040807031101030c0806281419030f02090402060d1a0306010906050102060412031104031a0f2a091e0a05010c 66
    0x709040c042550010b000c169480c058150042149900141080b030340c0900c2002c0369401d09207042c41c85020746c0d00341d0b958030802207100e0b0400c00c030156190399142c00c02e4007a52801e12700003c04004c040e41140f4910f10702c100c003095484003c20000341d00b00c0c1c00184501582d01c25400c04000c0c244000040d800d80313440551610100d07107078100107682414110010003021410780c802011001e07440c02c4201c85100c180c4c0101c821070307885403154286401c0010192111801c80f01c4109802403030740d2111104403c1100c0d00910401c243c00100d015940c0301d005407441e00340320360000c002d4510048984104102e03a054600d000c0d01410000280216130f070721a41049034410b030003802582d0b076907903107441116408911600515135658010300c582a100f0015001540c464048215440d007101c50300c48a03618000d00200340f48240000f00a5103001003110020f2188002c4000a584000d50980c0e0f040c0b40150941c0c9604040d40792242c218407521000340405404044e00c0f0a00700d56100c100460360386601500280c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421386771 1250 421385521 421385543
    0x110109231f0e0f030307080412020a052d04050c160c0e101e060f0c060e1b040b060a05030c0c011e1d0a12050703121503050d0804 57
    0x191031080380301800a900040016041103080390350320084500c1000c00030009500402c1260280c02e0112901c0c2511208134011420300302c0c80d41d60b0300072502c21030040702005845603844074110b45904802c2c00c0600301c02000500e000c024030012810341d004580090f08209552002d001c06030405100e102c2c00741721141d000c2031405813140340c6810625080d41c01140c46000740c5200044240200aa06028514400407900c820340741c04010b003480e0b021a0841d8001c403440345401c00025070003115980c45500b0761300b400c20b0a20160706004005202111915140740103a017500d48071b0799a452040b00c0300c594110b604000648494040c0407050003071040f010007081040010035003800c9814060440c1c050007000101d401040006000900c070004008c00ca542500c40500c41070510011441184a0340c2e0b10008000301c1c61907403a01040960018600c0080c040d0008010302498402c01c100140314152500a01c03a00d058810310060007165880b0541d0705c1d010340708910741d1007886800e65602841d000308140ca4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421388021 1250 421386771 421386809
    0x3050a1505040c05040503030406090303023304060e0d0e10020705030d03090f05010e010b040606080702060105040e070801020f0d0e061302040c1209060b010206060f09010e130f0807110109 83
    0x3d09481c1004000d004003480300041d955000c000400c058082a91050459890340c40e020749812801c0c440c0030002900d40800c01d07641101858083e4808102d4215840d4131344550400000810170200c6c900346074020200c00ea00ca580d0443c061803040e02d410b5541c46011900240c08031b032507941038050709905030007a400d0340e594148030750000e4035100e003c0c058403078130b0a0650b60795908403803960850900d26511041242600d10341841000020700240c1410072540c83c244000945070081401391612681e030301c03990b610b412002000b500018191000085555142440c0c1c04902d580203141325030a070a0804200c00181e200200e61140101894542e486074811075508102c080c001c031314103207010403407041e075006990b80e500d001e40c414181c01048002194015203000a00340704005107003034080c920708000b0580d10b4a500644a0440300102c1d00d030700c0b190f00c600d1a17210b400c808045010300070146008444050014400040034107230b104801450780040c480d00151011075040c4140b6030354000380344c9111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421389271 1250 421388021 421388029
    0x40923070906030c144603020f280303050405040c1b1401150905060907030506030307030305041a0127090317041505191d0706110f1c03050a1505 64
    0x1141000c3d005144440e003d821a1802c550fa562148a03080d010b580c2c80c24441d079100c00c48181c0c0c50b03000f0707094600c11051400e580110303901c02609d4070f006008950340c2810240c1142902d000101904d030a0886040095617820b0040c2550014040c40784280e2a0400c11100c041c0501c1000d60701044150345400b0b43c1416840c1c240c08400350b168286c2d602d540321468a550341030220b0414001d030017203540020319410b2120500c1411640100f058042c0361505c01401030a990020a550806034140340104040d40c46e0f1400e58100c0030103400c51101340c4ca006001240001148202000c150750003581e010703010b01e04180c2c00040e03425540010340451045504c02c206011524001580180980310205c000c8109074030001c1115000c650070b124220b41c1c0341164031400c09500501c00800d080004104600c2160107103540c903821944a80000e00040d6084240e84000c1800720381c080b404400151401c11803000d0461502180b000400f0000901d0200000e0403120300e03114100e841c0001804142c41c5905140600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421390521 1250 421389271 421389299
    0x91413120201020409020415020c090c0313020f1201050618100b03090f0a121107030215070201110f0d09080d12110d060902120121020609040923070906030c 69
    0xc102155000c000c04950380707071180020310040500070038080b02c42d41e0854000742010f0302c6080700c5205031600414080050000c00941c1d030440c1e0103007185000f034906440040d00b020b40b0140a0341c5c100100c3c05102c241c6a40650250384110300c1174030904070090b10005009601c2104584480300244802d03c14411900c40ca0091980440c51008640003a045441e82c98030b402c9101c04100c5032045000081078526500003060308007048004e004107a03840c1140d00107101c0303401c00d0030007018000020880b1001d6a2040610005001c1c070003040d00c51402e40c10440d1601c401112210801050780502e0005000f2000901c07510b160032503039110a200d84880d000e01c400382c15088803071750081c182400505c031038503d40d00c1580d0040401c9680141d5076458280600a000b005134420034800b0005000b07000100300c100202c0419942c110b0350300c1e0345c0c1c0040300c00041c01410402d00141c5600c03003006203015403401c6541e8100d2049104030880700c805694080c48001d960060100400e0070007a01d60810111132440301e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421391771 1250 421390521 421390553
    0xf0f04030903020405090a02120304180b040902060a030b100c050c0409050f1e120403020619090308210a0509190c03080a090e01150512040201090b0310091413 70
    0xd441c6030b607500000d0a84105440201240d04040849030031864440c1d104c0a000d841100507600b003502d441a800800a0115035030701d05180c98015060403507a4940c058a20181d0003030066403a0b021802c0010028001d94400a00841300680501038160240648441702c55100009000e0041d01d2000d101c054980002d0881c0c10740f01e109001000b10780103100c2071600726032020568400c1c4d00c4101c041c03131401d441d02c000011726150401003400541c403900c0483d280352140380c0c1221401000c07244201c510030340e581d002806c1c1080c00301300d82540e00203032840510180466200b088080d1a109051800c8031810340f405a07469002e44d030018440d0841025041a15008070a544450740d600d4483d66007950104a49074006610781c90306000d481124030300d0501508042400d0b490f1240d0b4268090002e00c501c20040003104021000141160310031042d0708054030700980c0c803d803070342040d02c41940c0310440c5009d05800c1600300380030b0180040c070300d103001c0344900c02800d80c00d02d2800068560000241107800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421393021 1250 421391771 421391777
    0x1a09070302071b06020114180703240507031e0c1b080d05041b0602030c150c0c10060f170312060102030c03030f010e2401050a03090c09050f010803030f0f0403 70
    0x320380d143c0d80c00040c8003840245003640010800956581940102801c01403480b04080b0f29400510421440011204203580e84200404000c4030702140d200d080c040348103580ca1002d03061004008038150f05422a00841a01010411f41030021071414401e844003800050000b2350705208050f00d01c0103580000710018050045c07985000c841c0340780c201c142c034407c44055810812442c0c0144e82d1030b080d81e001178000c6c00c0c1440030b58140607094a0064a4030340300101c0a151418032001b180310762403002c0c00c60321103802d01d00c22600318681d02d8200e14040c08561148000ca80310003100003c4610356000418181510030f00918507243c0240303401d00c000f44000c0d00041c1188014009162480400c100450090170300c118107102c60740c549030005070342820080c010703090b0740c4444e442c484560b8051007074070910078001d088c2140c0310380b40c000d41100144801040076090300654080007905032000e62166000b0355500e150307032420780e0702d070745406507a40710503140f107031481100c1c400003058581311240d0789410505ca89 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421394271 1250 421393021 421393043
    0xd02100909090602091002030c060f06010905061309050601030e120a020a0f06050f011a03061e13020415020304210c0b180325121406070207091a0907030207 69
    0x100100707007110b101030000c641c16035000800d2916072404825100c4428464402185481c4100d50550340f03c803805002210a00c6894010030a240e005429000191102411407a180c042400f0303035a00103500d0b40300e0752040e286400081081c070351180c02003005500d50180100360320035545506402940c454441ca00c21402a8040000051a10090004020700482000c6150301b13000c3d610400c03526040e8044003181307000341c0c0d4070340d01170300fa11054a0348414115081c0c2442c100645400c1c0708030880c40c40459010f411310414008044059010303005a03600118500300030381c245403069030380c0c0c445e900482009803141c1d000c0f41010b8001c0135080104901c10410b515101c1e80d1050001c40d150405801e881c2401c04484002c400c81c14104040c1e41c815810911800300f03401280480c0c042041d40c1d015031602150561103000a000c0007070304000116901908982080c68021002515081c5d076006c0d5654460500c60641800100d061a0241e010001428022582c84212081e002944400411105440d282c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421395521 1250 421394271 421394279
    0x22d0a0818060a050c01060b0702010c0f060f1e0509210d020d020703030c0216030b0c0c030909070809060a110a1b052a0303031003030c0305040816150e0d021009 71
    0x1450180c04400020b488003a160103c0c1c0b00300c1703429180c05410060000006114913000350307a0200c03081c4942c41d000f1a0044481816061000c0580f083e114000c402c9030800314424580c1c90414211110100400c0c800c04c990745505d030807540c5a000301104100025408035142143c005504020000507180b070100500d0f040c0080903600598202d0707181034020a94601300b1801341e6806000300b41f24240300102d500c02c0702e8150369400740e00705c00c007030702c03d080c20762020602001b0482c040003100c400c041c009084036424078000200400c1a101215254004d0080202045200070103028034014184030310141070416036044802c80c0d84a1040c040c011303120001e1003d07500490414008078000340e810074082103030140058075070007404a41c00321082c006c0d4810820031107419035003400c1e4000e4a0389840e00740180c040a04049400d405150880380d683d000d129800e590b91081e00102c3e001321143c51101580714406e080068a0642d2a0001d180c3c1045e00201c480300185811200c1d01138050580c1001e09641d0b0715 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421396771 1250 421395521 421395529
    0xd180b160e152101080619050402010c061817030a0c08040804060c0309121a090c01170604020910020109060f0b01080619090c110c090c0409020d110703022d0a0818 72
    0x282e00c001c529030016400d0040b002050003a081392211f102c0c4051005003410ba000801d288001b202c083d00e0740345e444e00b1100e40c8001c1c050401030019085281c0300c3ea40d080010b00340040c0d902c2a2498a00d0a00d40400c2c504100e02440d0f040b0320841d00079900d582403e14044041c2c45840400c4030840800c04002004601c0804004110400500428004d190840c0c0c44450f44010603014040c504158070007441d035131280e07a10100350388000c81c1e00329a901c030580341c0001090190088002c4568040b502207041c8100c1070381580441c82280c0102824013036a420b000300401168a00d1440d1800114402d00250342c9050000200d14070340000b01e441c41400343c0e20821030040f555a1441d08000420401c91071100313282c1084001076806044a041d2101e0038020402016481a40300f85610b0640118101030340031a1607110750980c40120140e1a034071022443c0c002c0d113481a0300b800d4400361302c901801800360101c50b8604403100c0c1c5144001c0003a9902501d85a07601d810100100c080313030707050079050082c94071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421398021 1250 421396771 421396837
    0xc0f0804030b0c0c011d0d12020702030a0818040203010b0306040509100f09050f030406050417030f03040c030201170f07030902030c04060303200f030403080d180b160e15 75
    0x1601c40300c00c1c2d46500a010110b42510401d05175502c00c01111b4440200318000031881c0540600300341020801d42c224904000043d00442c80040d505008500c05101030150f00c0d00201815486000a840020308410400080340001c0c003070443c0c490310520005840b07003090390007190400030260496a25020341c0540509403180100c100c2006500c3e60b654000700f00c81000181000300e40c080c0a1420a810302400400500851181265092280e0403201e4901e0701801140c4100310f411691555030302d041d00b080b00941c081407004a00141070b01c51600c0001006101c01401850044848921910340901c1200580650701c002d983c1409641c2c24a40d140e51644035072801103229403140d0f00903c0e642c07030040400320010590200c1e260024042d12a105102008950689034054429500c4141c42c1205c400207003d28040c5200d500000105c0c00e040c08004194684656100d074070822800c440c00c9421514070f00c4840700182c000e04020030300100502841c016090381c1d00700e0f40700090802d0070051001900b00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421399271 1250 421398021 421398031
    0x304050111101a0f1503160507050a0303021c09030207060807030b1e0301050606030f04080310182a051c111c0b04110a08100506040305101b0c0f0804030b 68
    0x101d140c0f01000030500b0086007040702c0003000c5910821000510700320908611004140007001c0b01d0040c50504c0c268003c400303684442d5000301c11a505c0e24003e00e0050000c1d03100403019225000180900c4e54240d0284c001e02442c0c0303916502810800386000c1c01900c0804d0003a207807000b4035441e40610f041c0d40e1210522030202d00800c12402c0070f5819418281401c544011388010301481c401c000300a011800c1390022908568000b001c00d0f03407a138a44601a604110a8004c1c03948070110801d0004038103003a0b04040702140b0340880e0926041140d0341c901103284140341182c0c1c04101c0c1030226511010f41586810700548000501080380080491030f18000d9100d003d03c08a40000c4082c0e016180ca05481820216507003a50108062542490b403803107030340a400110400c00048800140e8071129590b501d1008040140c40799896540301e280154980e003e00540303000707007881c02e1041610340112003550b203203061030358980c0d080024240e00c500f4298070341c42109498003801004004001400c010302c40d441a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421400521 1250 421399271 421399301
    0x60f030f0c161118011d010807060906050d06030212060f13030c11010c0506162c15040e0a0204031b0605030604020a020f0f0307030215010305030405011110 69
    0x29261504200c00c1054010300356480c200c000340441403800d010305000d50800b503000b911002c060807142002031680d4043c1c201182c1540300c80710000940c1c100350300c24284118061000724185a0b04d4011407692068688181800039001801c2003080c54003503001055525201340021031030b1526074000c90442000354442e25407a80c8020304200030b01d0314084806030007520900ba0250169083d4800410000301c1d00409000d180040c030b65000e075607006000d242513141c3c0c0710084d00c19524011170800c032a00101c0410101007070180c94002581a4030746407403100100d02499420015641e041440301c04a102224004164001c01000c20b070140300c480000d00c507561481001d80d0300c07402c40c0382000022034542c81842e21003000d000284400380c0c0120540340c0c04041501c0041c2c403940419022031030100a0290024240200010307054604400f00c01021814002e40840b0349045c1c0980d003100c4020001d200181071a0410b000c14400756105113000c400c05025041162103800181d418030003200e054242e6403e00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421401771 1250 421400521 421400527
    0xe0f04090f02031c08010f050f060a0c0515070e0604051e21010f06050607051f020d0615080f130305071416090b01020a0b0f040206040b0d09050712030c0605060a05060f 74
    0x5030f562010070f080c09800d00404087e041458100400c07803c00b90401c005109010110740401c49c18450001c852880b80c226007208c1001404913800801e01c1130a50f0a000090000c0410b2142814088100c80455170042d1504c0c40030601c1d046c0c601544030f5a6030030690702c0301000b6400c64100380076165405c81000008000200780550345104400c4075000d5002c02d000340810b0000340c0c0031901c045200744030179a06c80304884400c0074900c4800e00038411481da040d0000d14088010500741c01d000343c0c060152030b0a0300c40c5c00ea1a1201a003030040740504880e42201d40315a40d0034400009e11440192101c680f282d1040460102484644d03070500400000040c0c50010032682001680d02c940039206540000b030000d0040301e4000d44680c0040100188200072131650b5001250464803104229002004444c2320107448640c820340d081c01415030316005860398420344401140210040c8145541329500d5103a00c1d1404015554201c05890700030706060340002c2001c40040d498894500a00303800c3c0846910682d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421402877 1106 421401771 421401823
    0x19050403030615120506040204030c1a072109140f0f0f030303010608040c0515030604050a0e06072003070816080f13030605070e0f04090f0203 63
    0x80003086821540c440944e00101c00e555401c202501400252540d6081105074001c6002c05010341005400c10003900e144450700d00b240000e1452400d00b4207410f41c50b040340518101d1a20f9401d08a0620200030f050351064200024004406090041020400210720805000c02d0034500900d601d00c010041903480005000b12440003c1c00c4031303600e60b181c0b000140040390540d03046071600da002e20301003040d10348400312034140d5a60001084c21a80c1e07000411014100161807002c00c40e50711802828007513014012076201d60b1081d00c9400201a082444081502054500101ca5001403100c203000079529000c48240624095101c14070050f507051200702445401910b0391412070000e10100030b8410340800d00c04070f0307014000c100302c9a0ba81c054155100240c014095501040c2041e28a09618150b88134584007409040b4584440c1e601e580803a282450243c44d4640040798a400d000c = true := by decide +kernel

theorem cover : BRFrame.Cov 421223021 421402877 := by
  have h0 := BRFrame.cov_init 421223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421223021 ≤ n) (h2 : n < 421402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
