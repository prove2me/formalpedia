-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3584
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:04.47122+00:00
-- url     : https://prove2.me/submissions/49ff1782-260e-4ce4-8df4-c6413b2c851d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644424460 ≤ n < 644604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644425710 1250 644424460 644424479
    0xe16030b040501051c080424030c020d2a0506040326060a0e0c07120905030c01030207080708092e0e100e041a04061217040609180f180c 60
    0x28140d5001404105696142041150408490035406c58911504000120301450000d206452003400b82090412400c00c20307a001d410780303c440d02a281194420400d40503c42d0340f00503908440351540f026540300d160340309800700440d400d6030005031451183c402840304150b4003104840800d0070310400c0310900c241805081850020954610390b0101c4420000d102d40d24120450b03940011039a105980741200075510100020b91308545400884c03c0b40d03908201d9802c06105410808909180452a000055071640494042d0701400303001c0c80804154034490383c4aa11940700c080c0c40031070501d2a000f050000c02941c108800d400e8500107200c20700b594000c0c1c240000080c0015170551141c2050b00e5203001404010140101040f01030312424140900c03a403564450f6030003519500e800c0c03c412081a0802000901d516000b000143c0c0d030070002004816400f003a044141c0e42200500528400100f1030361001d0103990100fa00080d160803624152000c1040690300100c4c811109040c07102d56940101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644426960 1250 644425710 644425721
    0x9110316020a03021005070c15240b0d02210c13060f0c060e120c010608071205070303030908092706040506011b2a03061410120501060e16030b04 64
    0x80145c3d015154502c150302c1c103500702c55480340962510340e1000801d502c0e90441e82c1c0585111070703004d5070344d00094403200403c0d2048034149108100980000340c602100c01c401d51189030440320520383d0201e28540d21a0454040358040d21524500030000d0030020b250124aa000030011440b41452400c001441d50051200d030050704030175210529544180d0b182c21028100040b1105c8840c0240c0031030f11040304000c1c0180c20400c440c00b000082140c10060380034502201a0010100440600300e1031000841c00106032040c0e0f9410b01d40410200941d181041d003c1c0a90310b4200c0c2e0050b050313a204854101d0030a80c0032a403100f408a15451600c0e42010b0004071001136903060300040c0420005184408410060300034544503c5c0d201041b0030030603030f400070040204076056444003180b410030030038081d4500441c450b64200c00203030755040c10442c840c1c00720b801e858130803108030702c62130417110052107801c0d44120000c1800106d9080300703141c002c2101217512110044e100100f803a0520484803401c203880781 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644428210 1250 644426960 644426963
    0x903021c0201110417100c0302480a0609030507020f0109180902031e06060a0905010b19210c1101020319050c0d0c0509131a040c02030409110316020a 66
    0x11511301030408041d1000a0441ca81e0302d2100d204980e0300314000c20303552003041400b0400b682c00680391005491854100c5100c80700c1b1004030500c07890303080d0452260102500c001034100758800b500c601d1441039503080a64101004d05014034100c0c04005041d0008001c0107664400c441d10100d0503100d07401580e640400c0d0141d0501545d86080e10031001c5031039030054120600050480340e204118050740003240f8a000184d81f820380008040c00442d007018403104e0040c010101c01484250304104600d6100d0040c07440101e0001480303044108428003400303225080400b510000c010310007480380d04001806036038049500103291031f06004083c0318107100303a900a00f01007a100080000e03106182d400b03031101800c1c0019142d02040a00c0c84d0000620400d40b04000c6601c81503144c800100400010b01e1401810b40c00041c1000301540108114039001983d0240407900000c41c4400900304900e10b000350b03003124561910349001621030394442400f4620a94411424504509000c8000c0362a030681020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644429460 1250 644428210 644428241
    0x3120804120f1d0a0306020304061d03030c1909050402030a0c0206070516080a05091002010e01110412030f11030a020c1203040b070b1e0a02070516080d0c0501020d0903021c0201 78
    0x249070001c00f25020760006540d40100410790030303512502d0f8601240d00c15031b411540603903039544240b01d04250000082c0b103030268802031415450300c451030013050700c5a41002003044107d030009030364060090000c007000d4507000d40115140e28001e546940140740c0120668090712134040040c0b44c207481541100c49880300104558400052071b500d0382055040440704409210081c485040b0344e481d81c1103140183d00003a400414281d0001070316900b1102c0c1c0310380d0491a806d08000912049207030350016554180e15240c1034400c07900c025802c8581203004803043c1d07120302000075204085540000c0b141c0c5041c0c0e080b5039070300301d03c0302c0c1c20b00b89542c9106034496444071003018001c10002c0307445010001d034401c80d50080c01c000f0031580d003285044004215503000030b80d03a000c40c07908184807040001100104032000070700700c0c490810f032a03141c3e82c1c507000555604114556542404001082d01036502d000700301c200500803041c3c14a00030391680d140c2507450702d00890b00410384400d148140900900840b01c2d80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644430710 1250 644429460 644429477
    0x18082215080a1b02030a090f1a0702030c060310030c090501290c0303010f06031b0806040f0e0d020307120e090604090203031317070503011b050a0903120804120f 71
    0x8a0980da800c1004201c42d500c540d5803030a00358207000b20250140c0c01c0120340d000d19914000741401504442c500c1e00301c60099483d119081c020320070745005224044092002040d100c0c0381900c00070b80381034040c107045a0031440100c1400b100300440110641540d101e9800d80082503200c0c1c20340c90845000344111070211919058a030303000340288044d8880c3ca0100000545413183c0d0030b280c24910740c02a4080f105940300060108180e55040c402d104030b0007440c14100c1150100c0301c1c00140502d40181610344904e0b0349001c0100701d142c3d164001100b441d0700c2000d40345414031980c40a500c075005090241c94500e03200c2c336420740d070034450003034008000c80091002c0803e071207040502005140356401203826110800101d080c00c0e103c45c000780000d01d034903400c1550048041a10504040195000c1d074082d1381419444000b00401440d0500c411003d854185d441e1900e01d80c04403034a0505500181910440b680c00020150f131104e1840e201d28010b0010f03000d207886a50f411501642c0b00300040c4001500034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644431960 1250 644430710 644430749
    0x1050108091207120f030c08040b06120105013512130b0313230303040b0c0909041406100509060d03030f02040801020711040b01120f180822 62
    0xc1180c690003840500c210340d240d5800c00c0e90410103520802040d1407961220b400e116026902c503114410462030b524090001c80c0d140361014150100184c002020061403100080403500c4005001262481140c000c2c0300d1569a44000b441c4070a01c003905150410045072040c003c00100741c480b4000d079400324020031441c6000c80b990040c9400003020704403201c18680e0001004040b02c0302440c013690300d43d48100c1d000d0540d890a100c807045c000b0945130300841c2c10b00181403144404010b503540550005400a540d5a4035448100544101c6a1300360f4440400400e01c0180110040b0f900780c00e80001c01154410744a80058800e070086c01c1c422036a00005400c001640b500f000c00710f10305218440d08000c90f10200c004080780903a04513421490450b0f6001c120001440503c0031300707090400e000c0e82c0c200601560708000130501d00c9402040c02c021030311842100d00551860f07014a498a54104075404041e01e6450021980ea01044a401c1da10040308e00f104200b40701182058100c600b248a000f8881542 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644433210 1250 644431960 644431967
    0x20070204270b0a02120103030e10030c0e0105160602040620030f07030e040b0a140102120301061b03021009080306040b1e040902041116030906020105090a141e0705040b010302030f010501 82
    0x40c55441a9034003401521403465440c021706001c0c40c4070340c0700c03150004603500034058034102d020350b40800c044c1001e022251080c3c00070440c80c100403003807800720303a1541486207284004205000090401c2e20001d070001d00703581c1c081d0403442ea0511800d0016802541003000560301c0c0600d103107000703604000b0485400081e00032424280c0750003001e400030400003d014001a03c4481a134080d04652104800c1e0300c07419a4180904912050401401800d40d414440300609803a902d604220450503e8040d03441414020000382c02c1040e03007408280001c50044c5013041c10703030704180c034554050350918071030740c11924008560b01064115014460044a900c030200405070038225401e0360410341d21540280350441000042002558241b601b03464004a031030000c0000345994091811a40750209018800d00080345585502e508800d011002082e43c402582c20a000400a902c6002448200c40b14108020030100c0031100125000c0145c5400000158242d20045680009458043d001444150b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644434460 1250 644433210 644433233
    0x109090b04150609090c08090c01110f071e09050925030804080c0f010206010b0703120b0310090b0112030e040c0c020907020a422007020427 62
    0x2002400450808907241403841c2c1501581c01c501e00245210348103200840250185084c0a103803031800e0700300b0349405907c40751217008000805041190580001c081d081c4100722500d03030240d805003941d10380b0744d60f842e038040e07080003805002c280d44c0800a0300084105041c810b1300e2040381060041c0403420a481d40c00b0246049501000d02540c0b40340f80c1c0840420740c12005040034012030402000a017500070208001182d4041d00c0794112361005006101d0169400c0c20f481c0620352506141498144440490003e800f000c1c6030681c152160455040742a500758000e2071040d8095040810166220158a1940c0e040c111015020921122900b00c41d400e00740c2c40b90001a001349800c9070080030960016030020307000d54001c40185c4c09a4007c6040c07014440b201d00710b80006407a45000c4280c07646020310b00f0000310081a01030b0483c0b0b44402c00d12402600021043c101c04051203650366004841d0703181b0750700000d109074015440e180e010b4400c3d68020b103100b001d2030484483c2c2c0080301c1d05a600d1080709074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644435710 1250 644434460 644434481
    0x602060708091e0a11040207080706020702040b09090307440708030c120907061b0303061e2102031e07030c090c02150c091c15150b0405010909 63
    0x4904840043e912051039621100640f00501030300d03411070b903410301d007070301c581e4000c00a40715a20400056000850070300840c0c01050740000e002d41c0700c071070030b00008008080c5000039039005011072081115050000c001807401d05c3c85400320702202241c460303d56252884040000c0f07480014083c01d03130460030781c000f00d000009645108080c64144280c0da866000d40095402400c3c0217404544d0481d402518a00282d104070720300010070340c03240782c440300034203079a4200a103c2c18540440d6040047c584070350001c601411441082c016280040800c9407a683c004d84101100032aa000e51500560400a075521070680c0060040c482c02c008040b83c0248a01418a125100c5c03091a070000002a03500c8180c500074140380c0800120903c294101a00386264482d000012350842800c00c00c0b02c201001c151807607400c041d20542c6000c04000e16494001200c0200600000c15101c0c1c105410082904078000e510000c40102019650780c48000c90540501d018140c003160f0f0f0840c041c45544130300d03802401c450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644436960 1250 644435710 644435713
    0x30c02011d0706210c1e050c0d0806180103050607030e01050c03371e1503080c070b030f090106050a06080a0c03110a090608060612060f01140406110c0a060206070809 73
    0x1c0c50000b55000454a0701040c0d07030081601d400501c4030140030910301c22050a41b40c184507142800c440c0300c81c1d44996404040400341311040f000b10310103481c1d400200305040e407501910352070303541c5905046588060440380c01001034108182c20281d1032040c01041d004041e024515405c685500c000b80103107400e103014041e04104250306110300300788801c2180c401d801c82644000b0f20030324503083c1004021460f2551600460800c510300c00a02c07170501090088a030008a0300c1d403280c0d840344c44035081040552040c51060401300500c4094031a40d1840f90003500b444c8020455a0b955409100202980788a0000881c0c0301d180002e014140c0da41045030005407914000400c0b9803491b1a03204d130740c0c200141d01000038102100c14001290000801a0400b5003101d080b81020141c070544000b072800201094003c41c06140302d1446a40903054494a13003d80c2e040042e251503e03014000d00b41d87c01c01c8808101881030401500700c50410b40d518070181d031543ea02500c40b0756035440c402d942070348000d4807880b000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644438210 1250 644436960 644437007
    0x30b0609041a1905070813021318030504090c0e1f03060509090313080f1902060d050408120718060c030e150d05061507150f0c030c02011d0706 63
    0x42c03044180e140d2060128010300b14408410312414422201c1c02017040c0c06120071141448500304c0202d2990002550460b41e1200c07248010f42100090031010310518400302a1002550030582c029015100344d80d6209420444403104a2045407071100d01e0018a400446010903141000b0039002e104d106103c40e0b0801166075981c41c40030680c1540116020807040d00042170500c280780c1d41460726001881014000c012a403004442c16464849440c40d070086900d06c20350034004c5480b4001500c80410a80004006d9840c2c182007011a540c8002426440c0341e04020008080500804103042000c0d560185515602e0a008043c1c4030704e84030000c26010f003e80e04215920396914800801441d20882c0a40f0703484442c072182d54130503101d02030b040c6403003510040c00d40d0034580001d100b91a4401d40007a14500d070750303142c0b4501500070040c400080010300d061000505959805800407030186c6040c1d4000c1101240115111280080c846900d02d003607005000c04000d40351282c1035a03560f0884000e2550314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644439460 1250 644438210 644438243
    0xf06020c0a03110616020303010603091e0602071401270609020409060c0207050d02301002180409020d0206250605090c0a0b03010b030c040509090c0415030b060904 72
    0xa846a00c1104400261008407120103d500901c401900718410041004400c07961a90180d107902050190908040c4d64010580034000c88030403900c04203180320340c000200245810490003070f6000100c2aa00745081c881c841200600504c030f404003001001c80c2c0b44c49a442e011a0040079800501d00c2520140d40b145003a80159469201d03443c85544980e0340011110412103000e03050a100d070340424800c02403070b02180050388480c44105540c0b5501c40f00004c0c6021220b00c0358820746104182c440c2144582080c00403403000550082424052610b072000b0440075140401080e01c400410080d001040b84072448010f040c02c10182070520080380e01a01c1401c075a0785501c110407a508070a403282516401806074040b02402580c0420070142c4016035601d0400003001e1a91206200e504e40c0c007040000020101d2841c013054030301904005041d070806081591925079a84079070035081d40310320710b814a008006180c246000f01100d03400000b691040d40c0324800c1019592004100b039440c80b400b0902d568 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644440710 1250 644439460 644439463
    0x41502060c16060f0f090c06050f0d020c0f1002071a0603100902040225020901050108040f0f030207050607150e0c0319060f02030c1801020601120b091005010b04141c0f06020c 77
    0x500d40c01107050021b00c00b0b4043c2883c00c0c20194580c084010700c03208101910015003110119100085001070141c0d6455140e00003a2501d001070440b250a40501c80041010700e00316001041031900800140e4a03032524020804035203901907038100e030315900c1410007000041c01d5800650103640010300050621032900c04030000c00e205644d1000e8201e08000d4150118940000c020b80540000e03e001c8241e45410b075503010264000d0200600121041038802040520030056100501800380c50740742c880f041071800d0a2400141c105014404d8200b418168240100003940340e101c00004004099a00881358500b20070740080340c0c241c0341d85444811101810355203000031030240301c2000f0081da81e407013146818034560404940b45030440d0014001084190080e1220b05c06250f00400c51240986481c04000d15046140958000741c0c1d0a00c8000140b20790003030094000c56110100b00c0070001100760070003421182a40c2800c41201c4000ca0306800303e50710340685caa115224500043c5402000b00495 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644441960 1250 644440710 644440721
    0x1202010e16050301060f03020a0b030a09020621060f090a150312080912030103170d0209030106060206100e0115080601050d021204060b060c0d12060f0b041502060c16060f 75
    0x2181d100500e50100b2103801d0911801c07001780b090011000c81c2c41d0940e400500300716960300c00c08120303120100104003058695401440307100e43c0240155500c20200715132100c10008241c9481106024400040b0703141003100d10240e00602c020426285a501d8112441c020030400d401c4440b03a08000d20701000044410302508105440740d282c0e241e40d8600002c000e1314100721041809402c00c0240010000280c2030010686222490400c0a40303d41d14025900028090400f44a0b45503090800000e00e950300449d5403400340081040d0100019150401200d40c12802e11550010003954a51400400d1080e1206c4d5041300c41403405501d462503403207803c01070380c2064080c0c1d8940c4c500c0b02c040c0070410449100e81c01c14508292030007420001d00100706602e44001d001e0f0074090103031488180c903000c19658010b138041c000c0c412564840130303110402c1d500190854000d1507000300020518078102c078000100f062041c07002c3c654051030600c181003c41001c030315940382114655102c0d170000701c51000c18080d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644443210 1250 644441960 644441983
    0x1b0303010816082a040b0d0609060e01020f25150b040b0a0e0613060f060e1005092b06020406020102090307150e0418020909060a271202010e 62
    0x8101ca090b40d44a0710700500300ba680030300900d50000c810a1030400310741041d030018040c98184010006040b4010501400c50351a090781c2c8020f070700980c1d0040044503800201200c2c000c003801c2056284a684a900b00d100348001017081d82c03000e00c40130f8030400510b00c84034181c0400e400c1548007101941e07141d1245000300c0c1f840d080302a85485001001d400c0601c44c074082c981c000c07200c5600b62840e0100b00b0031402380c050b158034000c03601d20f209000c2060180d040080205040003503041c503180e59000003001d191503018070620802e40346080c440502e20840c16a41100c2d001006014a140b210200310125801820003141100140c00d80402140d00c51014000070501900096911403c0c0c82c00c044c1481e58507040510507080b100e120308202a0302176282449035106680018030307101341c19020901d0448100c0f009521100320750130032441ca040400c51300d0043c4078100040c00700000c0511100d00c00c0e022a5030500140381d00f1543c0c00041030200880f00c080c0d481c14000003130880c2c0307140001400e0480c46080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644444460 1250 644443210 644443213
    0x216170306061b0c04020a090e1308030708060a1502070618080303190e01090303060e06030601081f020c03160314091f0c02041a030f0613030c03050f0a0305040b090f0c061b03030108 80
    0x80402c9549ca00400440e445202026105031100705607072403551078000a8001810080000002826a01c0e82c41c078860152110110b5a800741d44880402075540e5000c0c0155000640c6a20a001c00c107404440150f046e540018003941c00c60341d0714100c003010748441203000e4880a403640c0c3c0200b07045d60f081c410070351031a01a50b03010402c01d041403882c40c109080581858040d600c4100102f14004011410784a0b204e04035050703840d00e0b4034441800c000703406490030540046c00001407045504403181340c201c045a10a07103c5035103415071100c9490890064514054004c5c030150750703501c401142e2254824a002050074000122200c0360003145c00c03601c4044240c1e4240480c02e006045c00e18003000406111918240140000c0c03400d900405080c001c0a00020203016490030480100350150b005d8a44103488500143c0d21a262488010003500064805968004451003c12280000402c01e400c080002e034000344100101d010504c4182d602000c1199012864244014908117040c001940244103400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644445710 1250 644444460 644444477
    0x8120928032003060a1806020d0f0501120816021c05010921140d0e060f0403120c0516140312150a12080a020304090216170306061b0c04020a 62
    0x6080c0103600074504102082c1030709140385242d01d580029100381e20050b01c80303012a1070458203a02c02d00c05002180010308050001c10035040f4486654000840b40030212001e002d0f5980c0c0b4030b60201c5858200d5400b41a414040008021130740e2210342114500d031014100506114203400e07000d0000c00c2244085840c1e94441081d64240009991010100c10111104208851981d20080c141468200c0d030b00741000400f2030000030441d0706a11600c0700414210175140d03a8038001038504548a0700720b0b4203c3c08503217401c00d10300040382140300f08103e43c181c9494042c642028020013000070041904211004000c601a07080c0d81d000c07c0c0040d221031000d800781c0c40c1d01814541c020703402400386454407078042d05207250104602c00641e5440810540c100503096910281400304a0540c421500419543d5000080450700c8400143e94004854004c05901070ba100d0b511280040e18072065811a80c096028030031445910041c0074401d4200304001e046a0305030341d10202007403e0741c209145500211f0051b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644446960 1250 644445710 644445713
    0x709110a090b13060c06020c0601121e030801091a03010e0307020f04180f0f020301060f03050f0d0e130f0629190f11060108010204140405010812092803 67
    0x90264000b6214240b40d1a0910b80c907503d00e4041c2458074410042045001e00d014010b2140e241c0c1211070a0092a090b24030942e140c82000000c007074109401c507442388000600400d0560707040d900c50901e45d419512406240d180c03c000c0c10180c44c0309403100444180140c15071020b980c00340300b04050fa80809000d9070311880c4030300400c80c0941c500c800c0c10303005034140700b1003580c41548881d40340c040aa0060041802c10b599003808440020350500080d007661078a00041410711844403010200c91056088403d41e480a141541d00c81c00b138040490086050741e1001016894102400034400c883c000c00000d4008031107200000f03550303103076010040807060311185060821030010b803c03400c1e000594042e85000c0500e002812011114116031080002c0d82865040940c46521200300070038202048500650b104d81036103000f94071620428195810301c26190100307007400c0c011035040b124064050060703418519149045544299811540700c502c1e240381c5034801141030b41d80340500d03d10f148900d104c1b5065 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644448210 1250 644446960 644446967
    0x1a1807030b01150c021c0804030606180507020c010816021002030c030406060b03040b011415030a0e0f070b042d061e03141303050d09141204030309090c020709110a 72
    0x4144a0f142004851407540000da150601d4000e03804140040480c0500b007a800c2550b9180140d4100814050500f034000403129404604449408090042080543c80d0b12030103a03551541800702e10301040c800c40010740b4002c2117840c0d0b40c038081c1d91401658200314110620b0012030703004885a80710408040240004e01ca00ca22442015028256001d4034504207500c035105088014450b80510244158490011303442da1552504120a02602e0b6501c90a015507000064484401c60030203a216040e0000b80300100082d090b4103c4010f02c108500d07250070300c001109100c003040e05c0e140700d51034060000030f0400c03001c01d403040c01094140c2d5045400c40c0700400c02c80e80c6d8a00154001e041504103600e02d10903070b403200000d5402c62100701025044030a5850706640e80c2c0151004410170300d1038100c004040c0991039115040000c1e082e800e032410709082c0003990303505020303d00010700000d49140c81808944201e601c07004940c9060700403121130a64850324841500c000030760060210380007050a64a0540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644449460 1250 644448210 644448239
    0x102100903031a040e03030f06010c0614190501050a0501080c040f06110f06060609060d0b060307110606090705120411030703060603060e06070e01051e07080c060a091a1807030b01 79
    0x241100c09100d02c171002410030f6500c2c00080c018502000c4c40901140f1940e01803440c2e02c1d0f1241d80720382c00f0700c000c81d10101d907031445801c00c8a00444c102441d010200340c0d5403842c4110380c1079400083c001c0c450103050900440d554a03000b0034850320840300b080080340003985040c0d240020b240e02d80d10042c1004502e0041824500031801902c0e2a07072010003400244c0e9030341004d07902556816102c2984481c031002e040009071801c46000c54100348000144440e0307960180c1c51580e04080013040312241d813121428405541e60880d0a1300c0007030010300031020325101000e40c3c0b03a04117000d07920003a101c00c2c880c40001c2c107103e01944201c50260ba01c050400030000917004032006500701d480646910301d4130060103401e102031103189174100f0000003900c0d20708444c0200304a0070301c0b0301c500007903071141c1103883c0481c2c1c141d102c513020107150320442c000554002d4031401041c07a11a030161940c602c1d1110208410700804001d0610700b484204404200b000704010040c81c2c0085004030b10401d0b10f0b51410151030144c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644450710 1250 644449460 644449511
    0x71205070f0206030910060e0108070e01080c0f1906050a0801080c09040204050712020c030405040605060406090306051e070e092217040314010509100e0a0b06010210090303 76
    0x20144580c80106880255040034190142c8031a596940c0d240e4200b420190b1007484011a246405c80c08509400c2e10030060b410398040008480c1c0c1c0382d480d82011a8901003d1144148e540e1001d40d424010b41050b240c403c1e900f5502426008184c02c40c1044107a000355942c000d20000b41000c5092103040b03034422043c2d4010b1070741c040035040b01d82991000c10680c182c000e00c0640180d44800128900f00d1165500707d0401c00016011500c0d4030800115680381e520521805224030305090b00801c0c03e01c0d182040b00c0032100c23070f41c9885e035a962842e56103a0140500804d8000410b50074000703c00c01803504200703144190700f2959504d000040c200304000010a014021110b0380e1001400c149e1102c0240842d4400190018030080140f00504003141711480380350802001882d00031400300000b04150003550041c211340e0182c84c412a1088210300488000205020440d80200e40003008200d40003540d6811200c18810b4401440419800b4000d407100200c0c101c0000c0d07a150080c0b41d40d011981c04100406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644451960 1250 644450710 644450717
    0xe1207030e0406090c0e01031a031b04061e03060b030c2809020a0e0d05012403110d12081b03010b270d0308100816180c021b12060a020712 61
    0x1140d171450001e0201800c90a0181803641d64062050700014240790486a010b0060407680d8000c0b28003c0f200c2c00a000924060103241011070225442d65000311000a418110b0510341119186455080282900080164240c050408060303201e03115881c06000e043d0a80854527540c0312203040da80d058500c6540400701d01f91040c404c040129602c48000700301040304807403003011403a442c2400d074010308000440e644154984980110b111030844068130469006070441e0b03019088035400d218045c11008402080c500040c141d0189a0380030725559500302c8040030b070719a08102300c070140c011346d580203070030070084d8400c0880c00381e4211080f00c48264984a04880f800c104240d8070012884c403c2e202800101401841d00000c0c032a4118600c60f003004221a00468116001c80c80d9101c4204855000d000061403d0100f4040ac0152900a20f003210300f550340142020041448408103800d0f24444840d8016400000b4003413030042009402c0c00741055510040e81c44009150507590000a801c0007800d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644453210 1250 644451960 644451971
    0x30b1302120703151e0204030b04051911210f1c051606050403021507050d0c0503090601030b070e0d050d0207050a0e0a022505060925090e1207030e040609 68
    0x6440268a440648113128010414071000c8101c504c036020703101424a070071840031900000b804070403510305014600a4054030700ca10300d1021010f00c0301c1da07030b43e80240c0007001e40300d0550402c0c20103680c600c01c4bd01d030320300c00000c01071081d202441c1440703a01032040607141c0c4204888000200c02c10550181000c00d030403c50301e0058260308030502200c454401030301d1661382c1c5c000142814020300c03a07400080c0ca0b0351029981858001006800c070f400a090b1359444914004807501c10b54004d01c11a401128158000c042e0f680c65503454083c4031400038010300800c103201d0101b00ca25294041d1034948584650090700d5007640c820002851b01c03c031a88164480d40c5080c2c010404d4101010840ba00006506005a07442a25080e040c0b4a0b0030038120f81e503460644015800e051101c0480c0440c00780105c003048d20802c02117205102c3d11041c6c160303c04142d07401800b2040011120580c0002c2844065205a61400301140c0040d0690341200030107070301107154161a54018606846480003814628408010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644454460 1250 644453210 644453213
    0xf030b0a09020c070315020c010b1c02040f110d060e060108071b03200a0b0619140307080328020d0f0531030302060c0705150c04030b1302120703 64
    0x290032016100741c0800c5540014000031585051008901640d00409051068186552076200a501101001140c0d504e481b090707500b14540b44030715104040c0c00d454451341c02c2c0e2490302080010098916a030440a6441e04084128a2000f01a05456810040c00541149041204095140024a020b0404c8890410880755039080a00d40004905201c0158601880c501e41501c070002441c40e45e1001c3d054900460320207400014165821500c10a4100119150803090002c12601e420380c212204682900510103007040d04d000b43d294180080448292655502c15542560310006020404048a5183c8107201c50850000308042c012840189112956181d0080490031238a146808000c80081c4c0700c4283d03484580f03191428034100d100003d14100007440e41c0c02c0549103101c224054020170002454160103030090b80e03407268126028160600d00c0c10724040107a80300410b0807004620600003c0040340030a10801d00c6400400e001c2400162980104044500b0000180303141d07a100f03010500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644455710 1250 644454460 644454469
    0x91b080304380c010b0d02010806060a02010f1a010815151b07180f1104050906120604060606110f0d050a02011805030901110d05040b091c0f030f030b 66
    0x408a5510a100d2900340141c40c01c0e00d1511409000700c11248030001d00705446802ca241c006000d0300040000810403c8581800d204942484040180c0444e0501002600608101c4000c200450369440001001c4802c15500303021038494010342d1040191b66049074080b035030006a00382d08031403c030322007160702400c2400003000582080f2090740307500000701d1010035103003607500c40340c1c0e101300c00c2d100f40d4031840c2d21091700d145060942c101e0290003e082c0b01c0c0106103002c3c2c901c203244c030203c145005180b078a410103040c4018188090003940c0c0101c01005442c007404400d00400e401148103d5000c9140751030041c0042c60410b161004140d60341101c6504101c08500240c412002d8405003081c83e141c501d035100a80c01040b040b45000c680316a080c404e0010824040014a01c84400362075003002d4048100c02e0b03540c2c580c000e07901ca2012403030402c0300f0701c4103d0501019100d0240c006044410071655014115441d00d45148212040e04040d600682011b400c414444034403400b0789810014903084e040041d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644456960 1250 644455710 644455717
    0x506030d0215040f1112060901150302060702150723150c18030c04020703020601091527110f0a0f03051005093d0b0406090306021c060603091b0803 65
    0xa001d2101504e0802c100126020f1601c21a280201800d00c20f0307603002e0b040c40d124502264062000d519242501eaa0881e04900480c01d0f02c0d00503200500b0024141c0c00d12000d440403c610143c000814003400e0009035020501180080d00003200745000c0d03540c0d80d041480c103049005040e003001f5001c0300300082d001c108420b445021500700b29814203040ca09001c02e0401c00fa82440c6a002400028161b041c1a00044c02c503040f6100b501040120341e90b418082c000000d0103000700700030b100d40e0f0b850200c2c2c640d002800303119240608107000110b030303810402040700300d40c001041056909000700340350305000e80000400022080703d05050000703290050307100d070a410075401030521488000c0089200da1a51248406840040c680b4521800f42d07004910903a4403100541090b00302a29000030400380100402e940440395142c40d01c014203411a946c1c0e4010750041d00b6001c40c2010407950f00144aa068003544000b07041c1038500040c2c0a01c41e080c0203154415205000003c40c080326020400c116000049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644458210 1250 644456960 644456963
    0x80106120b0f12150f09070b03091c03050403121a060c010209040e070f290c0c150409060e0f0f220b01050a08011b03110408100506030d021504 63
    0x1e5075082050001d554100082009600a050103d0300e04102e4400a08851081c008400400f10b40c0d0380d030604c40840c070300202d412003095048140100718400c100b8020b5908000800152281d5500c41010a5241595002d10500003501c400c148814550000079007c203180302c50405100d58004001955400c5160410050083d000041d080901031000e50654581c0c0d0b40040060080ea85160302c1c2ca55034081c40e01071704a1642504100240e400403140c00106080042c0a2010070144800c42160107500303c02c4021070340d406800c10707026030359642c0800c0d0702c49000d044200b0347d191030500b2141e404441c80b035001440542041c1040c48187c00054445a5004200c40d81450556590810b039008041c00c459007030350034100c1001090304109512000c54141c40e015905000700716901d03124039003615044191000340001d03050090b442240301c1c2e00102c0c020f80c1c501d40010700e041e507141c002030310f0700841c4e03a46c402f205640e40c018130a0500c0c1c1407118946100e074501c0144018582c0004034651400040c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644459460 1250 644458210 644458247
    0x907020a081c02030a0905011d0c09040309030614071d1305130803090309010810031110020102040f0608041203050606030f1b0c06060111120409020711030109031d01080106 76
    0x760301c1c1d0320b400c0d00e407440c1941c10140312055440e410b0010b408000382860081c1103400e54240080c0c80b00110507012003000390740c80c0b0001000c0a4071140c0520260300c002600503420040b10000202c081212401017040707170669802c50004a1512040040040300240c12038100080200e89a43c416a240a01c03078101c01c500b038000280316101c0c200207071005c4441900c000e00d08071002c0204024580c0100150014801c207886054150b81c601400d15044840c2d03000040c0400c40b204926141404d129444100d60301c2ca500006284c00c0d103d030485001c20b107665100000041040f030401003000b104034090700002196042c20f12040c02c00c0c0b000240c460000401c00e00c06004124000703110b078540056540030080e140080295180507040c10184c41d0801110028045913290101242a6500060b8040b41b42e0643c02c40d5410507042803000e401030340c80f20009990002c0100e5821105540070311a00701554440e44684031040c4058a0034205180c52110f440d05100081e00100b08403038000000c80c0d100e4400d183c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 644460710 1250 644459460 644459467
    0x604030f0207081e071e03031d09070318061508190b0612011407051810120207020402071403040510080907060e010c0516170106051e011106040305070b060907020a08 73
    0x5445c604011580180880c81c0049950164000d0124050701580e0107982c0d203502c0030090701206070802c0e2007101c400c0c0e000b542e060001000c3d50310a0f070106840e408c10080074015078500e62954004c0c2c032100d18503000090381b0302030200500da404001040ca00030580341041110800c90700c0302c3c842400d0040040e0302482d00858180300700a030a600268183c0740c1c0f0202503a11b82080280100790b90440020110030040300c41941455103083c0c00b00421055440c0e4402c801c0b089805c0703020019410501c41243c2141c0c0074000c402c0041d952141c10100c50484000440c0c540e0714160030004024401040c90082c041034800b0301084000124a000503102d003810002c026a00c4200100c0e03550301d1416028011303004000c038071400500c00c0002d9208941e09200c121405c800b4000c0e0080c00c0310114822641e201c0c2080546500d50b00000407100d990120506103149000880035a041c1021700c11141140000c60000701c040c1003102508007590400701c10f0b0b8010480d4500054007960b6041c0400006d4004100071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 644461960 1250 644460710 644460763
    0x130b0307030215041211040c020f0703080f0c1902091e04020d0c23040e0f0c12070b07030203190912061e0c0903061b080109090606170604030f020708 66
    0x100d40081000c542455920070842c2048951b05c006c0c00c10152003039003812141c1455520016200d14040000e5014102da2451030fa50700e42c1e140c6c000e20b500c44213408180400541040b0921402c0020b000340264044054154410002c0c1d80383c000345616008044c20114011203059010724682c02603058840703200c1d010482c00c102000b6096a4804603400f15841c40c404145502c0c10882169490103880c00d0007059001c000c210380b11070b100780e410591a40314006840442c6040300495003a02100350646a0064172221000f1281d40040c81c10780c0940c0c000141100202141598008244050320309054a01e003007241c0e400a800c8110005000d4948541c01880e4502c403070040d01f014000030303490030000d0050484000d011144d80707101c10344800c0c1c500210b04108036140404401940450f55450002d40e091060000043c00c140805690719561000c010410030b0510314102030140f0014010803940c5424640100414000300c1c0c40b00c00c64000d000f0400c43c03464001900c05648203041000e42c21640b01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 644463210 1250 644461960 644461999
    0x309010f050f070e011701080c21030d0506060c030f04060e04090209010501081008070617010803030c1b031224030a0803070c0f02090106090608010f050f013b130b03070302 76
    0x4000e00780c0385101c0c1b40000140781c02d4005100d0845e213209696200021400161552220b0022800031090350820001c407240d1364102e0784580d83c0050f0040980741088c2d01c00c00914a140c105410500c003200c00001c05102032500006102000a803c88060240740c0071a80030540e00c04c0d041c0300302418414441701103256030404600000281c0249011103451030b541c1c08000785131504589900350142c880e48004940401c02004a9126a1110103201d14003190405801ca0004840c1d4424225000a0101c0c0c06d440340594002d500600003040e01204801c03207400040c209101d00d005051083d40100342d40000140c40c013007500c6d80701c405030400e11110111400e000e01498101c01d0001c3d40001c4030800401c59a821001d000c080d54616603400031640e884030380f40c5441044901500d5070010604d502c240b00c9e58428a0b2025048030030b29201e009000383e6403003002500150780f00eaa5229281d4038440080d5044c20390703d6107170901c4035482c1400b001d41280c021070b072204241e000c0603006803500c82002003003404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 644464460 1250 644463210 644463227
    0xb0a0905090a0e1f14090d08040201020f0f0604060f151e03060f0c03063303020c06130323220e0a0603110d0201052704110309010f050f070e01 63
    0x2d440c3c0135941414100c0e407002138068880c0c20b50706100c0b4906500c59003015030301d07583e0398860542070000b000c800c0080f0b80107441ca00b0004000303c0c1184a0281c1884030400207020345002d44500f10b00a10035401c003442d1034001c0c1e603105894100e40610b01881000c044e240d41c44100112150a00d849214203646240f100c24004640c20103088207003001c0502c0c001042e20790020405115560307041003c5a1a00707001121520160600c801c0407860200c1e8411480000036500c00c0e940c4981030041c5400c04c82d010a6080080440b01c08031500b0a02d01c4150500d07400100c1da10042c040e040000c03c2c0c19841e004c2114060046c1c561840600d6020448084a210031005000240a00486009082ca8003d8409024020342c0c001100c0c02e51200003d0100b40c101441c42001080c0d05031101400d184030a840000520b0554100d05c000c180c1150400420707480b14415072901101c2c698045d6500e107441004a405d5601007041c1005141c89c4c18200120302009004035030b003200705860100c000c1c50f140300040b200c014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 644465710 1250 644464460 644464481
    0x51503010e0a02090604140a020c030d052d090d0c06090f0b101401050a030c0c0c0f2102010516080405130e0105160f0309141509070b0a0905090a 64
    0x601c1c0c9040414400000188001d6261003115100007554402e41444195135012640b0341300c030354100006c1400045140c001c0d00e4000d5405003100c1c10300c04001c46050a4a40a03690803807406081000c0410900d00c002107a580105403100300c00f164204424216540e20010751090104024080000c08000d5650001c4080c41e030021403050003a5901d00b4282080300f0b050fa207269203001b480070001807814444004a0003000140c48031402d248448405401411032180000d0800040103203081c00556190562409080302511515816080502400c00c280510300c100071105400c04a0200503a0701030200e8900c41c8600890715445071451030128a14002d80d084181d00004050341800400f40701c0d4001300c1c40c124004002c1c8283e4842074007501008050301c030403c0000e0f103c5000c810309940680c01000c2074600c24290a207890201e8414035017031044002440401000070414048060400c210700005460f0340760000740f400c02480030180c0101031a104003401420400002209e616031130740040c8016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 644466960 1250 644465710 644465713
    0xf011a0c16090203070915080f06030f010e010209040c020a02130c140c0d0906030504020a091d011503020102060106021c030506150705060402100309050a061802060c0604120c050c0103051503 84
    0x1a616402c00c600039400864540c000034208000000750740d448183c03614104109034407080e4441d01c40c05986c40e11410024000c03074051040c848001c8070080244211040d030314141e0b0005031155600001c1009451440e044041154007800d030040250b034840001001d032500c1300c80000341c4600c294105482c01d10303c18441004450340451464008807000c02d5000340e6481a0390740c2c1c42c1103a10f500058003200d1083c0c9003c0e4110301c40c02c4003800b08054503880340c0301c482e108003140d18403075074915807240c02c0d1440e00e0046406842c01480420441d601006040d02522050000c2e08040c100c01c1d0801c0c03142150204030004051b1131340041484e645800c2e140070300a0101c10042d0750380d1045410a10390b10001900c00f02e000d400541d00781c0c0030301c231300c00d1158119899008000e4042040181c503044041c0c440102d8008400d4209a2464010782d1040c0c0206000034414020306594601070400031044510380800d481800f448120030390000d00d02048824842c1000d0074001100d8035103940c001d0312105180c0e5540d406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 644468210 1250 644466960 644467003
    0x6180114040510060b040e04150b030706030e0712030f0f230324212503060e030901050a0f11010c2a080a08040f1211060f011a0c 57
    0xa0080c00305807804403504043d000e110141c1e8900c4030200600c91841554401d4401c80c3c0481c00203550030045424014a284002c140150503100180c109809640560003080d41c071900c445100e00f06102104c000d08040c100c2d40c6003c00700f511f0103404060102d16250030402c50241c0030141c0e500940c0e1030303001e100301c3c400140c0349000c0000004019034001d841c41102d00309400b4030245c1e54402c8511024940d03001130b20741c1819014511880d5000700502c00c8101582c064003843c607107210324001c054082301036007012202c061465400c0a40131101080102c00098004011003000da9030888222400001c4914148181e0f00310440300310b0760803140307000d02151542808940d00c0103070740c02445541c0040785640b4508040010080f003e402c40100c0c64001e02035a4144090000c0502903107500c0d41c09801103c500e210030946a603842c0c41d52601c1940070307010a0866580c0358900c07200f00802c992116943c06043d10550501424030345030024107059000c03208001510325200703503081c0300300000141107003a80101d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 644469460 1250 644468210 644468213
    0x138030712050907081e0304050621090a080f0a0516111206010e011a2209060605030402090c0d0b0406121b1503020d11220b0406020618011404 63
    0xc000303203038400c0c1054103082201140104502107107000485e0710140c001d00c00c000b40e000310241000340c001780d40c220340e0100384800105a1240d000418040c00200d2040c50100c0021641c1072410401400007a490350100e088500041c60740300c00c403104c4c5035003000460348810490004481c035105a1f1180c2c048003660320368080810030503e128001c3c0c88401c5580c80500100350b4079450352044248102000b0041c0e04004110410740003212040c100c68641b200b610b400e801c4132a2590a07050305501100d070700352144042207214190b1052001420b0305240080c5103003041c0c0c00141301c41c41d01070f0000f00503c038001149071400342c1513401020400c002510a021650355260280d003000045201600c0b0004c02051a40440f0805c1282d6010f0720302280c00740a040252042c110002d4000c6135002914582c0e40101501e8240303c64080c1442c498000300042000c41001404070701c844495000601c018000d0009100d87c6401042c1d080c0d101100c140684e14184080420314090b00c203580c1c5504240d00203a09100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 644470710 1250 644469460 644469467
    0x304060c15090b100603020702011209020102070302030303010b0a02060f07020312090c0a0b0c0f01020a30020d0b2115130816110a1d040c03050601091a0901380307 72
    0x28403848000841341c0000c0e50f190b0b010790a0340704039000207000440000c40c20b0059005c9600042c00b8600610403201981e0b2640e021a14582c03081c0c10022103018007142d0700300007941c1080081c1c2d0225900303d801c01107061115002c1e50740c0c054100c40b0040c20a403040001d8a61904100c9503071421801045c02030a140d990070032103419440361801c100e9030f00414124020428050084411403102c83d03541450721444500114ac0444054480c0d01d0040d8881880650808a6001600c01114a5580050740d1300c40c4038200038165005282d40c842c201030303028200e525a40d0101e8184514140710920080a954203400425107500c140d000900325038011410302c0015051402c4106094811285190f14039940d5042040c501c810b0311890070080c1100782242400b06881c05031942181c410a080704030141c4030742d5214200a0241c00014100d0317039505144001071040c0e0300a045c03800e010380c1d2030718032541056503451500030911280310b68540c0524541d40c81955000d48400c0014100003021748038207010300001e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 644471960 1250 644470710 644470733
    0x7050f100f05060a060806061e1206091005090c130515030103021801260309030a0302010c171005060729010f0b0c0a0b06061303080403050601170304060c1509 70
    0x94401929001c000b039007504010720f1450585c0d0407500c0b04040c55407150200011035000380200310311000320104903d01c03100c800e0050041d011845400007001d240010034031986500c01030488800503241c1e071080007607407102c591194201c800c030031213696035180740010001210301d1a4070032034009815032140304042078060080d5060724400c0703c14030101c001958100e11100340a0082c0c0340e0f405100c40e01c40a080644200d0078204074544c40c02c0e6810a0b004200003800c0280107041513001d41d445403800030300150f0101c1c499000d004054180d5680d4240300c42c841c0740c0c5909034025240240c400241140a008007503050100080140d8803031007080038010312080e80014284504002d136031440c1c03800b00f416074000c402d982103406024014038000c0302c01c8c1c44041701c02740003501050b00414104681c40414558910040140d0301903031090ba81c2d0f40c510b103002490440c1c164002c0203429880030f4000380c0307c80048100d604072446480c09400016843c1401e202c516411b01560344000d00d460245020004a603200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 644473210 1250 644471960 644471981
    0x90405031305010908030405191e091808071130010b0d0b13031808030714060f0c0c011d0d090b03090d18080607050d150b090607050f10 60
    0x400340800d0390b8030010f41d0a940e107402508506d030018802807009041076003803004040100c1040d41c204a949810f40712502882442d44d04043c014241d0034004c1c85540d0182d00d5480f58500101c2c01d83c03030519296400f0a0007041001483d0719050308907a040d45d5110104240c1c1c04001201d18200101c140642d140b402d0074a111815040d405c0c01041c80c4e10386003400c10500e021b500020403c5466507072064440b5524680c50007201808100c1c0c06400c04606440883e502801001004550b18002418140144030407001d10b1801341c1d001d1002c20040440d035182c50303070b00720201500f2540c0303801081120038054591140b0091401354256040d000c04400058210349460342c9071030b1034501a071503d40d40e180b01d100c00ca424100603031050001a400d6446845458105100086070000007a00c1d882c0040c1800000d442032000504041800001f0b80402c2c030604202d0800c0d1144000e1703541c6083d440300c405000f04448903204003008528013080c44802d01044c3d035a100301d28103a0790f019540754001c00041011014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 644474460 1250 644473210 644473237
    0x30f010f060206040b0f09010f0606030b040f09080403120e0306040309050907020f3003041211010b030a06020d1b0801090c080c031f0e070903020405090303070e0603060f09040503 79
    0xc002414900200b0103502035604100d41c0440c0da0340d800d400020400000d40109520366035a090600801c01d548220009064503603404070f84e50000307400f004140d8003001c0b5001d0780a850b21510800043c0c0c44802c9904030382d07010103601055245412705031100d89032411340d940c25008040030002019400340d402400d41d402200c080c44c0c6034540c03400499465508610080f0b40b40d022008030915201c405103031f8010340c4401d1000c0c400c220008004404c00d501306a0b800c6820500413043c0818498200c290180c0c1c40c440c001c000c2250443e1000082e60347c80c4004005031145070b00040d203e0245440c0e030040640c014848983e052101c40811009110a0092107084240c602c0c0c0b001d510312a034803c8072618001d180c1203645e2802e50300c9082c2c2a01032426055503030aa07140f101030000072170311411880d440c070803203d0b074680c021030310301c0c1d40140400c0d103800030100d400d107400c20801c000d02c0c2a0013002d0180740410945415072240e0f2340c0404604c1c0f41d5020441c0d45ea125002008000030440000000d02d1010324120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 644475710 1250 644474460 644474489
    0x171006030f170703020a11060f0409020d0e03280509030a03350105060a0c14010e19050618030c0703050105160906090e0a0b0d080a030b0a050a03060f060803030f01 72
    0x5061080b5024841004005030410600369000c2940e0000750541608014845458401d28010501c45640030390300920019401040c220741c984103522401c580d0340c4000000c1c614000941c12540d000e404e031605e90b03204559032030381104811403044090b50410070024080361341141481c10058445982024010b514104800c1000c3c00c8040049401c55a5282c5804051642e401d000800c08950880014901088a445041c402060381110801d80c0983d0302c8000003604041c000f03400342000100c0d007903551030050790700741da0000450000d640c40d030202d4444625641c006c02d241c42c02e400e521034004000407911640f0008002d018040d40124050212020180010f0400c400e041d1180a0756100e1040410502c01e400c00c8440d0107150307413561000001e800060040c2031b107400211404000b240c142c038442c101041040e4866014400c00d0704030482220040105482c0000081605481d0f01005100360f440300200f05129440b0340111001e016804141c80d1a8542081141d2036003c1c00d105d400030703120505 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 644476960 1250 644475710 644475743
    0x91a0616020f12030f03060d0206040f030b061503011e17030d0e0c01020c100e0301150e0f0c19090b1b0d030204262d010608010b0a171006030f 63
    0x42042840d403c0030255091070200714542c2c1c20383e04000c000f0740d01721080e41c9605005956100042020309980704c1201d0199080d03003840903c4c0784c40280024001c124544d082c00c0e4400c202d0040c0c0341100c0828040b5840c00c7c0c074815203200620320070307407007c50f00f288009006d0300740700c0012010b0f000b0510b0404c010802c214030018031507540c1c5602c02000c1e01580107105084100c2c14046013070154180607081c42606902a1408a0702319204401540c03a4104c0d40041030001d1030814280307503081204400c02d40b000c0c1c104081401618031809140c0d191190700d410440610b18000c8041000401c5030b486c0c403e0b12a54603241c0140b014119490380c01f1640a054082a00c0a00910a990584070070419607260490354060542a000c00481c400c56207114000c64144140e84070038803c10740204c202c80c0040c6040d202c00c03405c0c0c03e4403002d4220300e07107903410203004002b261200500901100d40c0c21106100000c1d21803159410840800f40d0600a942441004428843c401d5104e20490348901d04682c02d00900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 644478210 1250 644476960 644476969
    0x4051e0c0f0a0302060904200a020303010e06040b03070b0a0c080f04050315090a0605040204020405281703030415110307030e1002070f1731080610091a0616020f 71
    0xd0f00000350b0000e0140031521640c117082d44490340080b034600c080c4511803810140e01c0a10b8015601d1000160b20010050294501d0744425a070003170001c2c2e50034845902160006a01c9010b54054a452000c0c08034003002094031400001e9006904028401d603500e90001980701c49500034080c1034001d20606180000551001240602c5411280060640c040b81d0360b0790000540b00180083c7d030301640a000214a543d1004201450640d4881070744031104038001c07100201c040c1640c40070540d0b5009196285a0f5a008011a075105501c09003042e42a04407896240040c40d03071040b90f00d440080842048000d41d010b034094203041584108840c1041003804001040c1e00c00d00130020414244c640814000620300075908040c401d55080c0241080c120404c5038401e04400312028403c4060540a00744092a4a0695000d0101d01000e8103a924207190707446c50103c018410310850303650780c4542202d4805240c24809560b007005010f00d40c4e0b0300b024030301041e41003095842030b03204441001403070005162 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 644479460 1250 644478210 644478229
    0x5012603040603111207050901031a18100f06050301032109090902030a0602271e1c02210105071e050c03070b0903040e0916090504051e0c0f 62
    0x44100214034140c20301d5001c9014000d01c02d40b11112600900903800f0060b007110201b4454640f560341c058449065100041c2541c141440d00c240e100704005075201d80d07803036951b500c07558030300f2410f210700785501e907541c0600006d0001e500c00c041440d0340140c007080060703000c2e00641c101da002d07103401012021800d000603400c0c4001000000840e4042804125026071900011801400202501c045150303d0700c80400741c0e80034802c030420301d1030203076094110920103014683c503001d400e85800140901c1110044003900e00c440c10300c0c0c401c500307400250b200e041d401c2101c42c068a9010b46044d64103000c00c3c141d88040040c1640b24000c0303500b00b9001681640c85110700950b400782130700340d80b90781102c1404146d5550784143c0e844211400100300d0355000c18804103001e4059040f5000855072585000410040640083d21041c02a0802903220801417420311384d1030152001d0020000c1c21f80c940b46059407420781c00e05228880c0556050a5404202000c10b0202d00a00143c03550b480010508003089103154 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 644480710 1250 644479460 644479529
    0xb160c030b011a1207110f010e030a12050105030c0d0215160309061d04020a12021c05010f0b070204050c090d1209050f150a141b58030501 61
    0xc541c8000074044605c030340d04840304800c1060503907d01c00700060801e82500c0d07141c11130a41e6a84001820080103500402d070750310070400310104001c41e50402c00026200c00c0002401072062b840104c10781c040d562540e080e00506410f43c030341c2990781c103003101401c00b0b60104030b0022b8000c510260800285180906610303100300e101c11004c6c0c0100c40e80201080025002114410100480400341c4d0840c2d401031f01c0280004610210305448000341c443d900010780e00142c001c04040320082d0810001030034903c0a07201107650460b0042003580e10b0342c41c0080d01d4050341940382d60041c8072580c90f405020800c0d8040e480c0546035550b1100c0c168651003885906041c80e07501c250005001007900700f2403090100504005040741c988642611000d400403086504805d91681d0001d1140b06030f05c148490030000360b01e036103908000c4410088a604d282940c010241103a001010b110348a850001c09034075546e02900c01c0b8100c401c0b100c410700044005000340310900a41c0030b032200d40080c105c00c0c803402d2500641d800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 644481960 1250 644480710 644480737
    0x140403170405070510020f060c040e0a200d09050c120a08031012081804050403090302010c050703021302041d0c190c0b0f06030c010e0a0b160c030b011a 67
    0x8810345100a2062000030002d0303400b40a11072022600381e131900a29110804154002c0111041c030000803410410085e06030410b00701c1c00c00040209010305600036a214007010700c00640142e0743c040c012039001101a0701c0c100c0d5040000c0c0707440201030680c04040001d00035001c403020440e1003401d02c02a80f40c03490240700c1c0c82d070002d08920300281c0b0101c0203580c8034040c050b072078080d160390f036168104045a01c82c003211030f4030012135003d82400c801d0340c550040e100111411707c400c1c00d154074003a0030702d11503010103810050441d14602c107012003040302c50000d65010308098280100580030400941050280403409400c11441703150780034100803941e004140100c8601e250110400504429503001c1d040c420a100c2100300071800b0a0410109610440442e1482c00c0b00b450002d00701804e2241c2082c0e03a6040c094000d42c0c00303074982c49071440e0760141e138003540400d641c50b206807003052254106200000d0280804640100c100000f8070300090480700480c05582e540d14080341126124028880880c194 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 644483210 1250 644481960 644481977
    0xf1c09060c0f08190608100b120606060702010309031b0825020612060a15021c0503070c1401150311181b03060f03190209070203040803160201110a05070504140403 72
    0x10082c42d5241e0040f004d04140c0005829994100c6541005d03810000c00082c255a0749000340e00b42402071070700300c01d00c9024025014618200c0e0010f4900e00602b00003a0425035240341103400c1500525a528242c0c01d5440311440c80030680c5800388040d840425102001080007800041e01c0343c03404020911180d00038031782802e0179298594042080ea0082200390b129048220005004289642d00200d030400c0358007a00c01c541e00c202403410680b086d4603200d030800c44100f04101203140d100f004a5200c40e40410030303001c000011568a400351214168107882580c42c0e1000008004441d0102d850450301500c1c11a0118002500a85550301c01c03240d81a0b0840818038408000411000031544080c0041c002028400c070400402d2a152032a002d01c0c20409451903010b040d07241c100b203150781c40300ca9440290f20706800c200c48203407030f80201840703800b0a40c07c07601300500f16070180d0910321425140400301e410b03079401410b106503150091310030203004601d4020030800b142e880500862107107401d900d0b0b0f03605 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 644484460 1250 644483210 644483221
    0x2040609090b15030f04020a0b040b0306130e1603150e0a06020c01020d140709170d0c05070506030709060f02151f05030f0a02030c0607020a05060f1c09060c0f08 71
    0x503086500c100c070b0744500c3d440401d40c5a4403603600030750300035083c1c0240055246464814080300b003416070011040144144000c0007000200c0e0102e907888001600d0400c0200100040300d405803040740010b899a000b202c42d8640c40100300f2410750300320390013034072802041c0d8a11001101202c681d029041c0326a0003811001c0086402500184148a418400145070408200c010340888d108881c12402140d940801d1040300c6a01014210250081c04911180315030348242c0180d40701c50000c1140180300703209260105100b804d10100000704000f6090702e960b0301d00080010802c007070764000c00000c650300c410000609031001800c10305204140354104095210329070120f08940a4881a9880407203045001c10b070b54506100060418800c42c2c0141140c4c078984c41010f080044000d515030240c4410301c5482e0250380d58000e10811280241c1e1043c0d80e901c200217092501723120f961452a2140e8682241c0d007000b86095208000050040c2410040f1b0081680110303040f01c440e0805d54002043c9402054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 644485710 1250 644484460 644484479
    0xc04060f0e0c0d0c0504080d030b1c0203100e0a050d0f050307050904150806060f041e021605190b06060309060a02030709051504210f030c020a03020d05060a0c020102040609 76
    0x42d0810141916681003400391000d403070a070782e0540b1076407000031408602004072150400a03014030f000c0c00e00b0107215421810300424102001410704030145407c0b5144681551020f201e030303145905215a05009021001c82c0c0c0781d548014100b4116002e1160404803225240700e40c9000d8040d17411a1b58075072868985000482d015000b0010542c2d11981c1c07210380d04030007a00d4034900c1c0700a09800d009010289040f10400c44040300c4d03840607a0065060402d05203460f85800a420740892a03c0700041c0c0780c841991000f242c4201510004007140f04040c004d40d0807a071048900f0700500d2080a021909680f0744050000c2c6020948110744207501c440d000c1014003201c0d40103981d00c1184c03483d00344d403500d40d10f03000103076147c1c441c1d1481480c0e910001800d000140814200640c046950711100303014001a40e1080300000d110400a030806c100090341404568805007000700070742e00107201402d4940d942c04c026441d4013050305c1520320980382500540c0020300600aa80444119443e00101e079858030f0700d0f10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 644486960 1250 644485710 644485739
    0x14090108040309050d05011508030c1e0102070f11030105070c0201080604091b090e0d050702060d05060f06030a2306010207060c26070309080105011a0705010e0f0f0c04060f 76
    0x8400f80000303c100030849480780340450381602d0141002260045561a0018a80540360080c1800fa0400c129101c0a0000004d08107070b40c0148401441c000c00b105002c0ca402401520001420300c50880b10640602c05001110800f91104800030021a15144030a60b503c85071800001e020070f41c803800081180ca040e9108020702070203280e600c40d450522400383e042400c100d800c46024596104951a6282001c01c4906a03020290901c2c603c2c100e1580c00140082c00395070151405541c6600c0090f8042d180d0b2040304110441c090445a102c1c14204170304e00c0a0016030304030328109480d070340081c40100010000c00307000c1c04c0180c001d00502d904200707044800084201c42a10410a003400d600c100c40c56100c1c02c0300c5894402d0112907299801890000c1c41451a9441030003e6030520b40140030305010101c1c01d40110380d011024079a50340ba140352480c00f40c1901c50031440c460180e9a8000e01240d008144210500220410358141030302610030007007254100c0c02a14101e4107081402d10030402c550b40346 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 644488210 1250 644486960 644486963
    0xf0e0601020f030a050a031407170709080d050a1205010e01150c0203070e1f0303050f090d0b0f06040b180103030309050f0105070504060f020c030c010e061c090c061409010804 77
    0x59500402d01c1c0441140340d948110b8500340003880000e415000c2d40d50600c0b420f03207112003034421549241402c00004149000d42170842000301444d4002c950880e008030f81800061035048207486007045441c0780648103400401000022880060b105200c41c2003a21840f810b803943c10001488503400c0000d6080810403006042041c06046560107000d070fa02040100010402c006000165240c0803941a04043c01c80c0901c0030701203111002407000030307000410342d1640c454cc0140e05807a02092000a005100041405056038171030f40d080c0001c1100301117030f09129500694041c44240315580911032a1a40d041c4192498800030380148002840b03a000400024010000c564001e0441a040d900b10b410645a401c0400c0000074100081a0020280403402c001c03400031303003003006c1c0000203c0d4480416102084c108440c3d020b2515065030340c8800d85010741800c1d080c1144520005901f02d0041c61440001d982002e082040000c240d4400d440c02c51341c5000000c0441d041035150700040d1007101000d8030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 644489460 1250 644488210 644488213
    0x917030a090c0b0702120d020703110105041d06030c030304050a05150f04060807120b01170a0e010212091b0a0b0706061d1501030509070324021309060f0f0e060102 72
    0xc9240120b4a4110007001070300c2a07408055036400644100324082c45201406502500075119501a140d000b187c3e01003204c0d00a0709803182c01800d040120b0f640d210380e03004be49000701000341e0150a4234921885c0761181c0015021140320344281c9040507601c0c0941d10480e81e1103045020140030504203011580c0c0610103808002d400c0c445113207102c42040d00b0035000300d4001800101085541544503182c1910100004c0e000c0001c0c00441c00003e11a140344441e1031394281600c40814640403003507102d00f4002e07840100842d103c640000d85244980402c0c1e5000d10103102d1032407800c40b036444a455a00000300c0c010000d4002914006414035180c00161003519401c0e919900002d1110080101611011091001c88100d14003565060030380325032043c1c141c3c10580b524040203501c00d000541d440540c0d8200702c481d0003045195041549943c21a000700c0c507558000b141b030700c15a40101c030075901522035920040c400ca13621b42d03d214031b680600e88614004840da0070030403c4400c5400c0c1210360032038010320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 644490710 1250 644489460 644489471
    0x9140a060b1c1d0d180f031203090203100e0708060105060a0215040501020903030a0c031b031d120a030c0c0806090d0c05190c05120703020915012003040314010917030a 74
    0x3d41c0103051415480350300700842d4508000800e82c501e0b100894014140d601c803050501c1d82507454501038a004c10039175005140c0d494400da01590340c00c0001034941e4450510034000f44c520480c403d038540807203204030030180c400e02002040502c0e002c003c0c0c540703c0381c1d9580200903c41480c1c0000a11210240c010b41d00d035542044000c8450318207100601c20b000c2c00383c40303614440c411842c00808820350601d10506210200503610006a40321510420b0b03008801510b8102d0600c0e000020300918505451824521403c0008001c164000c054442882c2c011b80ca1958010b60b43e407181a04c0c5c1c0c80c101e070040629001240004541401a100c00001a001e481207070602d03600c1240ba000f009000150589034415103c508121610b07182d0203204203c4070f031502070700c000703440c650104148110282006401c01c5117200c0c043d0300c60b4030496040346184109480c15400110a001d61920303a44140425100085018168107086105019000a907680301095001055140c440c1c001903800203000307681c0312900c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 644491960 1250 644490710 644490761
    0x108090c040b28061409030a0b0703140103060f050708100e040f060213080c1918110313030e04091101320d0507080c0f0a030609140a060b1c 62
    0x24409100b03a202c48100c2445840e00705840a0540b1100745c1260b016004100640503090301c0200d41c141c070240d80a254000305032a500001e401400c2c5121484120300b604e240004144011a040303504c560025110801c480e480306001100d0048003110000510815030008010400a00300e1481e44a8010101c0004ca414603a9500090740e112200c05020002083c82c1070000d450188205403040c02d003261100784800d0080e80e0302c3c000711481d105811104d41800000c0101d21140d8010401d200401c520269a920300100b6a10b2040d61820007900040e075607447c2c039a002d042c548100d11a00780c004905480300440c04004451412001180c0c8a010000840c0c1e42030700300d00031000b50789141fa00c20300d850302e4906000403072040b0b0308020160020000c080b4140a201c801c104211805c041c201740801d551240040760076005852650b1004e8407403450000650038140c40855943c0c0200e51101d000d200709903407001444010301542c41c04400010341700212036984004d82e4801c1e00d14020070715032800344a105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 644493210 1250 644491960 644491999
    0x304060b1305040c0f0f0b0309010906140403080a020f0304060203040c08010c05070317070903021e06030f0603010e0111030a0f241e03170928090b0108090c040b 71
    0x54807004400651a03109010810000030300020180c0411103210304128130b4500900702c0c0d406d0511442020320400004510149400c0d00702d04601d45d08084140080d0b070346110b9101e40b1101c11282500080c803c80003242d0268460300880d032102d00b6040c0001d003541c843c0d40b00d41c1c0003584013030401c45100d03070580f8001074684d4082c01601d62803131080d200c26480d8912802c0160481400480c41219610302c00200f14213141c2103600c06082d17a0301910103001c200c0d0b036289810005d8000d0502c950b0301440c007208000b0700701403040c0c0291007020300394028400c8500d1902d0325401d841044019208280b42480080e100050a41c018183c0ea0614100411010550040800d1300ca8541020ba4800c00d4048000d00c110581810110780c0c924000d0300400b0454995140c2c050119510090105008400550907500d65241d155940c07c5488800c2c884c08013aa26101c0482c400744c140c030503017200d64100020041c441d8001c409c5240320304804000380012181e2034007044000c0408203070855000d020100d031b0f041402d21 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 644494460 1250 644493210 644493229
    0x160212040302060a03390e0a031410020c0a030905010201020306031b0d020a03120f09060c03052a0c01023702040204031703070806121c030204050d0f0c0506041203050304060b 77
    0x122650515142c500f82c0c0485040700c086a020802485541b107250440c41c8c9800b1610021660000000d580c00413880000a051800c01440441514000f00d400030410b1404544a00c0320361017522403441896035940160700781d01080b14900c0c0e02d604040042054504d07040111407513110002c1c801c0d154515580d001035581d1003603070015503400c2160500c410f040d9403c54400a002111400c1c440c41591406034001c00c600d490600040c03c00c980800c44c58501400c554034558404a4980040b110700c982590399903459800040381c0d4010700c220751002c0002040d04500c680c100084074031021813058543c0c61318400c040b040740106c1c0c00540c204000800308003009100003842c0c02000d403e954a04000380014a03400c000381c5030034424449101c240307803030240000d11a0081ca000e00c1c421208003614490550080c09142d110682000181102178100030802482e8001107200348010454140c8800901c051805580191020500c800d1448000b10b130043c80030356442407007000040340750454003021601102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 644495710 1250 644494460 644494511
    0x305040303020f1206090606130303050f1e0c070b03012607090c08090f030313060f1104290f1b01240302030123070e030c030a0506160212040302060a03 67
    0x45880c002d001203031421380e442c07e130800c1084901c2410900315110b0014030101621000781071040000740e0a0910100a066615926250032000565182030700800351907800030800380c5290140d6a804a1046802000e4a041c0d0300354805001c1d003050030260b6044000c451103510600e030b104440700040c40c46000c0c001c5010941040d03489580d1420650b48242c0f90900740460200e26801c140200030301001e03a41c80140d1342035040000801c100e03040d16040c07401070000c503040090724500001d010441140c1a801d11301c1d030030b18008003146002c4200c0b600059a00400d200080042000c00c00b0100e80c030111544c061621782c0382e40000600400b00405601e90748984d4a5800c6030b0a46040b0800a41c074080c8111607c130a1111920158001440c0c860006544000c0103c024000d500f4030100486c0c800704003072000250003904640c8540111b06006503280d004135888a2010b8846070807400040c4007142880701149a04c41590400d801d5a0030000d00313410480d0780100305540c0b40481c2c103442015a401c41c4406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 644496960 1250 644495710 644495737
    0x303090b0d1506022b0804020d02060d0e06070905030a0f022e0e010306060f0e120c0312040e130305040b2818090218151b0708101406010305040303020f 67
    0x808119001c80300b90303681c80114504413150007a82c0700d45e168000008503802641140c00e03602c20b41e29840010001e0240302d41d00383c40c80d850124040068580020100d0041074540c45550274156904109551542030724030061410500004080041c18100c240c2100c411902c240f5902c0c0120305058007488541c0040c0c040d00080ca59809015903507054840d42c03025120714640080c50b0101c030300f006071481c0002c15446024042d480d010041517101800560b5200b0070081c260b99104001000e01a0700303400078098030b4040758200c000300704003103120401c200320f00d0762545505040ca0300d080d6460605030005213030080c0d203200440c120f109040d80326100901e4081281c0750702204104c403102240d0409455005248024410019888555001019070000c110304950550044114808054060042e410720300074003549840c850094802c041019810744124104032a0040441c0050fa0144c851040070304060750b0110012400c0365200e81c000d103502134043c1c20302514241b0f905400021a922004084551 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 644498210 1250 644496960 644496973
    0x29090d1b050a3303020c030f03040c0b36060a030c0e030127020f0603010b07060b041107060e07031415090f0606011d1305010503010b0108010303090b0d150602 70
    0x5501d82001c00340e001d03140c440040808203182c001c090f43c0c40d0a4020821020140180c52101014440e404543c4e10400c4601030f40d0710b80c40128546410f40d001910119041600007101090000349502910007000301d005a81c0703428401d480c00d040101c01303008000d644d4911800444142038440e080201264540b542d80082c0c081c002e8403009051002080c1d41612990400d03850390181080710240d4140941150821007040001b03100060342001e403822425040302000c000080d442d014140609116401b440742401480181c8003008200d859140e170503810300d40180064030200b501a0300c441859068141207480e0079071a03481c4c0c01c85610540c00003100baa88500600c150121040b07110582108e104001001d01020300400d0381c2e184d2400a04203410802844044011580e0210f0a0b003403900703000e403000c440700780c4612295028003000d01070a4007070340c02c010004240354418001103040f250181d031804d035160304003105c810032a84658000d560041d1910071017650000c040144000a240c5500200823 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 644499460 1250 644498210 644498219
    0x21250b0601180b09130b21150c030c160b100602070f120b09100207060212150a2106480f0c0b07020c0a29090d1b 50
    0x201011404001c001c6140d100b400c0205031103501c262400d0a5080b259118803c0b04158000000c211000788598408140880c9003610390040c0d40c2c4204415000c0c0c160341c2111a40503035801080e074203944402e02c0860400c001049076040c4c1d00901131503810400d280050840c56110f0501554007500d500c070360f0020990080007161b8040140100801e2000ca5002c0310300c1c03a003031485400380384911015204400707220001c2c000a50501241c13148000d403000464850356903060100c02034120503540303d00c1d1a602004a02000038021060000c02c4000300007800241c10b00d015941103181c40591158417a01c440d8085000500c0340c001c010044084100b0040d107414130386102402c0482a907900b000a10000e071950f00134019600c0801c0b0000520b003407040c080c03450207030f003106d2400407040c01400020400742031101c01a8045100703101d040040705d110290381e4546641c86108a001c1e445030f50b042c0070841200b000001114003420240f0801044120040380b00d80300c0714000e95805413020030001c1c20003400d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 644500710 1250 644499460 644499467
    0x80a0605010e18030d020c0f0304060f02070611100b010201290307210308100f06020d0206061504051e04140906150a1707180209011121250b0601 64
    0x1a4851982c007950030000c6000ba03d52a240d2003001800c10456030009040d18440404100d502910483d40d030860b5134440c3d907004001d01940c0080f895200601600c000012407500ca0360261a00c15020030103440d4a9100300f103600000d03c0d81011031419035403116040003203180141c28204038040703098281030180c1503030810141002800e070000300d0504040401404020703600816001350f0355060800d0942ea850300800700082c5000755003c02100001c42c4400301c2c00d00da0115441c40144415000c075022521604100045d01c205401d56141c500340900c0100240d01c0c14048046400900c140e80030b0360351800780b000c1000e1702c0403010520305e01c142481c00d001c11610204641035114041c884030106488031180094040070952280300141c401c03003c071813800b90405000d4013006100941c2d2513200ea00070b00003400e000e900100051404240c40c41502840f110000c00c851040540d090401001800a108a15519001543d82001c507400302b45010586400040340c14540c00c1c0614000b28491130b2000005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 644501960 1250 644500710 644500739
    0x2090603070b030412020a020310061508010e0a0c0e040e07030c060305010b0904050601120507030c020d020102030f06060a110106030f0b0a021e0a0c05070f08010c020d08130c080a060501 82
    0x680c081d900c003400c1000280c255205594019034003400040a004480d0012882c003101000003a5060142d64004502031603550702a100f01c031000340ca40b0911140c04402514042024840e140c0c030440e00000240c6c40710b829511545001250b07041c070460141a4a000c14126030820800b00d41d02c0d07002290900a000702944500014982450144110b41c145100d0030404d02840c0ca806004945440201c0c1c80d903070050070310000016450504000c1c0349442c40c0d000f000391294407400e00160148041135900c07a841030085030310500301d82d420304e14940c45070300030302c0a07907441061003a04002c2c220400614070360080c01140d00940c004c0404545140f581d00301652650380c00342c143e04005104010449140740301d034541c0e80000040100103038130340b0b810000540b0012900440100710b4040c140c808903485900781602400d40704080001c00040d090045d042e6920101803884001080b41e910004001c140d9202481c8620b511407d82d0b43c900c10341e03070300540d440c2410320b80313003115056107480050241e0a9016480b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 644503210 1250 644501960 644501971
    0x1805040606050d0c0b0a0306030b04050c13090519020604080a0803150109080619020408011d010f090201090b0904060f170d02070528030c0b0a03060905280b1c0209 72
    0x100c43d440c00c110707659070048240d90310500302206000f24400300100d0282c1e111313000075a00600c00307940300c4c5040e25101c0d4943c60400e400c40c1c450590200d082c00001804c1c4900551283d021004085104200002203000204c6103030499002c00704020208482009129031080144a8036201e5201d050850742010688000c066039410400e105108010503140010080d4000c4806d0b1883c25803040101c511001a105580040031190300700b0451140d0074642d031454070300001c0ca500c0200f041c20500010041621484000623002940c003400034400e00c0444401460191401031002400a64a101148090000b035110070000045126520002c1e0b00078841c0f4003650b0039a1010301611414200056041c00c0b18034004416140a4400064900c004074901d1001d550408100840140e58a0081256612040c1c205002074280040050308500501605d4000c01c80d811040a902d640501c00001d580c034400d2074000c40710345070301408519813950501c0700004180702103a034550807520b005104605902408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 644504460 1250 644503210 644503219
    0x60a0305160314150f06031011070515061503090118030903030f020d1b050120040611010b0a050405190c08072307140f07060e090f041218180504060605 67
    0x244104a1044a14802d60000070024490f03d1030721011b0200b4504103410a04a0285140c001c0494100300781e08007518100744180b0441e0300080810b41c180f0032418040c0c5081e07801a0541540001c43c01010001d15800004540001000d5000b5051010b111441090560100d959000c0510a15601020040d5821024001001e00c5031140500030300c0e445040c0203d40c46821000480d00c100f00d030070341001240440b000c805036840488105445100d038014401c45010404084001d809a6010f01546588a000804261050f4074000c2848041d001c010031640d40701c03051601d461a610818031a644040d40103a413105400c0c608080003410010045c2c259080c5c0f000c07142030011190805070100c403007403075005042d049001701c50380c400e40c50910344205d03070318950080070350128441d0341c40311400382119411035441c0d160b40c03140305040c10030130f01c240d8028100075054000f030400b060045040101005d507820f44141c5d026030350b01401c243e054080302c0968845854400344801e0003003a00583c006802e0895 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 644505710 1250 644504460 644504473
    0xd0b0d110405130602030906180a08031b04030209040f02101d2701080f15010510300e010c03050610080a14010602010903020d0e130203060a0305160314 67
    0x8a99000c01200320392400c0c440c5071540c000500420f4003100c5102100d502240c155102c2c00e0041c2807980b59030003141c0d140420088183d45042d0f84500058039407070b403608100080d10310b4841105444140e4149413500c007640d582040000010385a022209203d00d00420324610000050b01c10051060300110742c0d942007100c1c59844802c00c0410900070030203200121420540080059403049051025008001c000240c3c2070000940c0b1902054015480b1f201c44e094450301c001450000e03266041c20300800d03805c074180301d54203d041d5001d100c0550110100c00761038200b00302280300010340429400781913000181c0701c0485480c03e5000740260380d42006582030501051420703001003071400b500040601c04001220000c6090344019611281800c104400920525a1a031402902078280450220010300c40d0841c070404c2244552000c44a2407001008400014039038100d5001a401c09807103143d0000e140280000010300c10003804000d001c240422a000c01d16604154410001801e50441c054000c00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 644506960 1250 644505710 644505713
    0x3060c140c07090f1401080f0c0103021305060c01060e090c12011a010c030e0301060f080625030f0f06031a070801030305030450010605030703260f0d0b0d 68
    0x4103442c410b540440f01c000800c070014640000140c0444260000c2d10141c140001c61801808144444052280b5045070b041c0da03103070030044080388141d0f50326032200020000c040c420f901e850001000d860100500100341c42d612603540d030941403c207403014445a44964402c119600784006a20302203034545000700100c05e000c6c4003c400c0b40e03e8071090300303041122000035082050700480d088164003c0181c0200700f080d46810700c100205200c1e0140c2c4a281c854100014600f400381c4512940248610000484c080398903503054020f42003a8a24502c40d689810003d020b6205d81d10078407004501490340c100d00c0d02c075503540029001101800f50340400011b040184013294100d41181e4005074042d4402c07600e618400102010400a0322511044104141c1662076207585020040d43c00000c000140032203020032840c1354203d031101c3c490070303400d900000401c10100303002125460014030300049440b68140f12805a45959114400303110000001081c0c5070000c417424400e0860040d800d0320ac201c14901c55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 644508210 1250 644506960 644506963
    0x1815030111090d06091a0403020604030e1002150601050705101505010804120530070206070c03020a0f1403030109020d05010506070f0f0804180506040c0c0b07031a0a03060c140c 78
    0x240300c06080d1907100c425200c06c00100c0f81040900001030502c207403c03802d10345002500d600c01568258001021140c0c841058500303101c0a11816405400415624518120341a0701000040845051040c00e01212000c07407000d21416003540700e60580000c0d0030300e034148080c1e0f01c0900c2d6000386042204100821001450b032701d5904c145074100303041554a640700c112440d1800301c02142900f100790b50001c500484a520b2000d224087e0581d81c0a4506590311060201c0f8029003154003e07005900c444100000720b0746840311548454095600d42c214030044507a52403541e4000e038880700070640d002940c0006040c0c0c0c0d114107405084c0c1107558a2902d0352940302c4c144e020750305140107001c09440004000c200f09080d8211030003000110200c401c0c0428a60b000c0c001000125070003401141000c504800c1c86114601c5802c40550040754a83c4035103c1600883c020101403085000030369800310b000700696549089800218031900000c141c80f800c07908000c100c4401c494501c108a8400d20108095440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 644509460 1250 644508210 644508229
    0x80a0b0a0c0512131203020304020411032a0d0504030801080708010507051c0e070f0915030506240303040b07051b0130020706020318060c18181503011109 68
    0x850303803024054440f5403806140880102004048171482d64000100741c0d0581c000e144218001c039010030118015082d01020351000f100c44040b050107203001d28411001c2003a003c41030354001e141310740c108030002e071080f0200e40301070700c4c00c1c4c010840141c0100405c03041009024007408041c1c00a0005040840d4054800c0c011281d10b9248648507808451150b5845e41c488002e01c42e4803800c4610059640704084078440e640c0c000c44401504102e47d0808140c0a80a03010071030782c0c040010b041559800c04550741441508e001ca070070010400c20300780f40360303603041016001500d050456955600c50900e01240b0300144114900c0104004241c2d91030244e81001501480c80c0689040390300341c0301e104040781d0b0030fa0100e01451380d065102003842010312250780d000d144180c862484038000301a0300802d0030303a104021602c100103400b0410204080f8290344800d01c012500c09011030030641680c2401d080e1165044440351f10b080e80308002c0c484240b400740240c0c2e034000b1294180500d806413070310116502e0340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 644510710 1250 644509460 644509477
    0x40b1317160605070e1819020903030412030839130801020301031a0708100909020f04020304060504060b01050901020703080a051e0c01050f09060402010c060e07080a0b0a0c05 77
    0x20300c0801c5114408030801e40d1a04031542c07020301000310b460903c1001c1d0020040340d04080c01110408000c0000705900c02c000c40c01156105003111800c0320804280002e9071041d00c6807501400207100000c0c44404640880d91254403039256008a490410031101c102c88611081503c205140c5001c80c2507000c0f80c0560700940f103119007404d56600d45000c0380001800f40c0340e208988547c8000300020078420030711070707204607205000c40ca01201d84800404480c0600190b44030362500c02a200100320101840d80031950389480680211159441000041d0883e0407c98090380c545407103404000401c6010311450100b0002401e069080c84040d0b00001c1d900e041c02d00004100c0007000070051221401241991448620100403602742d42540e03100d06500d40103500481925800d24002c40d02461501000521440040c4020003455446800441d1100b01016055480781c4d643d05500e1005001844258090030385070000f00040b1041e85800d1030140e80050071040d03018039141e05403000c254000e040f40c0a59 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 644511960 1250 644510710 644510753
    0x2011b151d07180606180b09030a02061b0c150d0b0a050319030e0d030507150f060f0f0b0c0a02010f0509040615030e0a020105090103020f13030506040b13 68
    0x30101186207800c4403041403403401031240400002c1c012003401d25aa03d0409088014450716035034100c00d0b601c4000540070b070906159451410f2104030f030350301c0c058802c91000074101e520b52030042d00412a183d04c100c149662a14003004a19960b0104020199201030150390f0f0900507004043e100c900307401000c0ea0240326985445070042603030760300f0540f840500401010341c1c01802c202080034400d4011408110301280b443c2c15904220700d0886103c20300c2c4c1c2d4064442c01d00e03004040d5245900c0840d002880042160354003168524041d41e0303c546030241400c1d2640c1c5817128281440c21090112540c050851010f080011302104071380070400c281c02c0d55083c01c124002601100050342c07a4001e1070840d9400c94503102c0000782d2076049141000c032582c1c02d52800c003c020382c2c10301c541d40c0310b41d10154041d012400400000c03c05500c203900400b82805051582da040c0141307007281007070301c03c01e540c010785d0b090344007400380018004900a0582c03c01150780148030b6243d0305a60b86481710911110341c2480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 644513210 1250 644511960 644511971
    0x80a0c060f0203010605090307060207080c150c01050a061a18040c05040902031303031d0616030b150706111303060207030c02040c081009020a0503060f042702011b15 73
    0x300a2650421101c18641600c29034032036849900007000780e044190f1440c4280304540e000212107001203a01406d030f51a10014240c42040e500500014080034840901c000c241088002d8030102c0038441e41c0e0141c1a8100c021800030724280c0d003820301e01010151410100400c1104103810b200a00703941648840944000c44c0d10f042c298010764941c05560300c1950034038000410480c0c000141581b80003218480d072010043e0700507080382c0b8960702801d0f01c030f1003049071b10407008945c2c58803603061100703045c099901c0c2c0410400c18801c0418218032120303000343e41000010070804c00b000403502824140c03040c2c2c1881c40b401d000225002501c890300c03c0c8400360074203500054210605202c0e0341d8068415030042c200380815180400d000b010180105c0c0c03020301c81241800b0204e2100144d0088a403518044e5032030314119120001002400c1c0e40e49500b4561060741d0342d5007009100c4046c0961031000200702e0f50b0142d583e8040c0005041c2103a00038080b81c0300c1c11580e80040000b100400ba01c244c03541c043c50000b44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 644514460 1250 644513210 644513213
    0x915090c2202040b071a0f090312100f180e0109050d0e0402090d080901080901020f1e070b040c0807093e0d0228020a020111101401061b080a0c 63
    0x900c2250040b84180c000002d4000500c0700314141007856694071240d8903019030f40d8412189481d6010fa4031810607400c10060f146116001030702e81d0fa000f044202a622f0580e80c1c81140200301c841c56032219003282c0b280d00310030007140b9081c82040900d140640c001e01038a011560703803036100d941f81000710050000300281000c0c251140da041d21181c0d00f02628020601d4a50704105201e908030756481d42c0000e002c0b10000740d00d46018000d4070424840b01d1803681c01d004201ea0b107213540e881c4aa00181d0062400e01c9940003050444d100e05020300d024004031450701c0d04181100e030402c545900900d06290800124089400e007130044040d10b410f007620074048e848840000341c000340c80e4021400e0f6400b0340214001801d90311603030003403000a40c0c1d20302c01c03210008468841c100400c0303582c40500268000003d0907025500900d40d85a00c0d01200042d03d05484d441840b0b0b504039a0260f505083e803c0d403090052081c550454500807401c00c41c0702c00b501050310b0b240e603120a1031250001a04c104002c192180c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 644515710 1250 644514460 644514529
    0x1103040803030c0d0b01030605090c1e0318070f0f14030f0a05010501090612022407050303102111040237031805060a090206070b0915090c 61
    0x50280c40c150040d01d98074140050740ea01c1c26088a120031210501e41204003400750301030311a413070407180081c1000105ea0707610503d0005641000400b104804407003090754021080100003903115440c40082d2400d124001c6150a1801e5100d8102c4980c1c910b102609104c140081980b25007102c440c0105d03000301c401207401080c145040c0346200320440c4214a10202000410f400030340c1602d06410382004011760321520300909404001d4047d411555084070442c0f10600609040120800c60b002c0e0740c6002d0b01543e440345507900441d100c00c2040414103050006d10781180b03c44590180290396801e46c0042900d880900c4501d25401034070840d40012441031040c2080c000109069030000315840490790032403a001d000a0510079500000c4c508100d19030b038200c00b0781c50042102d8001c000ac202a82d42c01c1c0a01c0001e1040c08401e9a00400038400c1200040f0803841b018030410010010b0078900c20301c1e07410100c040d80c01a0148100350840d05000340075444a40a1403250300621010b0b0a103a1900781011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 644516960 1250 644515710 644515717
    0x90408120f01081018051c3c0e1c0b0606120f04020a0506042403020a080f22030f030506040216230610150c15022802010e0601120c03031103 62
    0x42260050b11f000450f680c000d01401e040765015a260b220101c81c0164412000149091901844610340f14003804200c00d00070040f402008142008280600c91100207005c40085070000c21315803440084074002c0180d50014243c204e00181c0394070341402a101c10700b03c0c04000041180b010844010001025940c5107030800004003006003049542c2c6071160b40c2000001040e005048408604100400c040c0344288200d661105280e035070820350381c41b070000c07000c005100600310880d180b5200d809054081c207041c2c00d00d0240b42c440d0300d44811074151401c010f020748000510043c82035205000d084000084150600c40035640a1a44000080d03c0078000781c00c40000c44d0480254031801007040f2200610b04800d00503618101e1403c80c01c0c14a03000d0071a22464246402000095034441030580811103401a02c0400c0c0945409218a24040b1064801c01c2da0b0340399450040c1c2d11881807046100b024407000f17000d400103a09000c10071017140c40c0c1200c2044944001010080c5485207522a01b006000340c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 644518210 1250 644516960 644516963
    0x9050d03141602090a0204030b061816021606120b010914061b0d091a03090d030509030909070201060f0909080f090105070b04030215010e16120b090408120f01081018 73
    0x2140d00c5c107210b020300000750031901084400201c3c810118903103250401078040c03c039122008603e035581d40c8600c1519458840c0b0a10f03c05e52040e40000704600042c9803d88019040070f80d10b03070882c4c0c0c6200b0400e1054030041c0c8042814000d0522040c008a4405001000a5802500c019544458842d030030061040030074010103545c000d5405100042d070784440140d04035004d02211180c0107400c4109154203101c143c40d018134950006618026a5010b500f142e41c0c080a241e05807800c00021401051001c60100d510b000180d44d980e80034048030b0490240c903809084a100c003080342c5000342d61151b00e14400c42c83c604208800225401825a1080040703c0d15150310400d400c0c4e003400d046c50040d50711862054420b121340f01d204d0020501000c05024503110b424080e91070313882e42c924180191180c0783c0c25400080c1d45611912203c640303444181440e40114402d403800c940d124601c98130b008000002501c1c9244071004071004209200000a084040c1140001c000a03102e404059046000000520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 644519460 1250 644518210 644518219
    0x2401710181e0605180303010302220510060206090c061606090c120203010c050c0604031206080f06100801020c030a030b2409040e0d050417100501030f0309050d03141602 75
    0x2c80000400c4010b1a030703612640301d00c9042c805038840f651300d80e15011010b41c0007030707043d0300c140010005450027035000030b0004102d407521886041c2019900b0191801105c40413a801c2ca0581c003041584e40c1049420f600091a0300075001c1011071000007202c6100d0f040c81012480340014440e010b01c84594064081254030100900f010b40c5c2d1603030201001252070405174400c2d460f005110f41031f9402780048428100021025200135a1566825a042e5001c1e2100406003a03840da00440d0040c810000caa10140340e4000034038042c502285801010700981c0c000c5009a401480f20500c070071000400c1e01d510000a080c04150003425a02080c0d8035081003011100c202d039144004011301e041400205860714003a5024000c000803041440e42da610215a0080059410001009180d4884003a12140f443c140251117800d85005050010741d07100b070304241d443c00301030101d1400701a0400d8031600200815038031160710050640b0098020400d18180b40c4006400180030741d005044440c031132441950041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 644520710 1250 644519460 644519483
    0x30a0b040903020703260d1a040203092d1515040906090b13030503061504080618070602060601080c1804110319020c0c01030240171018 60
    0x20b0003503452901c1d203c159911001100d40e0343c1140310240035440700d21581c0245e14581011555410020400500c603180014078410020039a40d0b11070008500607206034005100c56008100d20329511100d818140e12811404c441c410420240403884800719599545410590b9403220482006408690585a4054a0030b40403e04001e80c50f40181152406000c40404559820100c103c0f064144500600803440610010300c2d00d240113542000006955588681403580e2601020b28000003983d0010b4a041c0010710f00c161151304020000083c42c0501c01000b5a040480028060320405444082c4100c40024214140743e2402c0d416055020301401c00c00114406130b0155910380c009070780540b0f0501185048034050895402901c01034040d040c041c0c0500e8260b440190003c4d0310100b010404440d005a19030018980420481203000d5202c140901c502c0550050010706201600302070400b110008400c6501d940018680b407008202e0340300040e25682a40f2008410700d90349074010803408001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 644521960 1250 644520710 644520713
    0x20f1014041508010519030213090206030c0a030e07030c0513020f0c060103060b1e191805040614090303040f0c0b040603090c05040903140a03140f041a0c0f030a0b0409 74
    0x200d0a480c0402580d43d550495640c80f4402c10801c0d031100038003c24078010680003480540342c0245428030031301e6074500008a10889601007441d5400480300c0501c3c4480224071036413000d8141c0104500301d48808044c107a00707402c5949003100e8011901440b4051126000351003102c1006030704444c580101405c030346441d00b0840f101c503944d4030360074002180c08c0c0d03092001e038542074100090b00b4920b0070325080c03200c03844124032418850388610108001c4200c078800e000c00110005018400b54101100500100300792910f0b00300300060f83d070740c140c96190701d0f180042001620907001c8103803904958002c04000d5080744606222106c10000d400c15145800b00203000140c07240c16074405240584644c0003004042d50703480801c02100c86080780a8041407a401506100c200444000c2106040d58100005d070002444000c070ba01c40012600b035030141031298184814480c0c0c0d507010515401003011520183e2506192140782809841c8030311a80c040040082204002ca070707000f0b03034400c13000a84108142c610f00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 644523210 1250 644521960 644521979
    0xf0207050610051f1407060204181b0504050108040c0806090c032b0c14101a0906060d0f0905030a0819270204090606090e19020f101404 60
    0x81d12101c030350980b9050002003505104800c14500d107141c1c8006038441c110361809a0f200f00507180340b40c2480030100046000280c2620142020b04621400405950a038000c814100c0d0403072a808010842600351050600f6030140481d020f444080c41c00c1701464940f403400341c9506115402c030304141c3c02800100041090000760100e01c540040342150010144075120256030f40c807041c120400321520441d144106800b50031025692481003086851080c44125000c0c01c1464080809030411b44841d1701c0540d804600c10101030200f8210340100b898100351001668a1040c00e000001716515080700c9100b07107009910003000e094004083d01d6840083d1a801408080c00b1600f08141205182215120b2020340c8200843c0c3c0340440c40341d8650b00c261540540402c450554201e0f40103403143c40240000740300b0301480c8001c00742200d0110b22410394940391401c106a0061101e80b2958080c1c200015a403018501e11196000782d41c0083c0d00100d40a0450307142100070500c8020580015001841020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 644524460 1250 644523210 644523223
    0x10b030d030b090f13150203010f0504150611030d1a1228240c1e0801120201270815010308221d0f06061c0e010f020705 53
    0x108500351a4a410111415412180742d1401d05400449100016180340255901c80e0303041540d8109605407031626589074a00c00d96906032489500c2c0e0044010802500520300c0400907010490301448000851440544c48040600c00c23141000400c0c080000a0542482214101220904288034240702c00c01c1c50f01d41018070003074160054070a0301c032a06401e038002ca210f00f618034042901a0101070a00285804040240350030743c2d6000100101c01c4210705443c2c45000120030b912804145407101200148c080f100044c2100100c003454824a801c02d98091803480c103444044c0100e118070403040c00121091341d01071000c03200c0c440f1112103101c50403851281c2d200031940544129001c156a07590010f0070703104d0030301c0300401200301844100c6205401a450105401080f1404c1c994039070340319000002c0d00a4020b4404c2c003405008148410f15234240b00081c0c0c4681c0a6912615241c01d00e82440800001681c540300040d170303609402a20b000e82904898054140035605540b2080507081c440d84421 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 644525710 1250 644524460 644524481
    0x313030f0b0a02030c1c060503150612030c10090201020304090606110d0f0c08160b130c1d151210200c1c092c060d0b010501030b030c130c1b0506012705070201 70
    0x5507602ccd1425852100007084910903d083c5000c1c03c210407004080c580540080c003000c074154001440045203d18151213050002e1030300c0d0350342040d94500d038101e00703052116a00d000010000103c40c44500c807500705000c80012a403000c01c181c1c0d122901d2542800e91100240010a450421700500c00c1603041d41c184054150301900c0c181d40b410f690ac41c040e15509032040850380507542084c00080720380c2e040341c51440c00d280c006002d503000440c20050203810030503d030840303001c0903551302c2c04521083d01c02d0102c82044948043c2181c500f501c13a44a00b6583c01d40340c030f038a1411510a10b003213080d00c0d104243d18401010340084040000c045003031400181c0d00ca8011001d064049a00018103902d0002c2682d10b1144d08158240e00381d0342000c00440c041c100440e0210b4041c420300440840c4c6868242e211f0545034071144000440103070907080140440040d0404506254008404a0100c0c81c046082070444406101d02e407125160001030350403110b85400d003000b040d850711041042c0150190082003019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 644526960 1250 644525710 644525719
    0x50a020d050304030804021c020301050103080d0e0f21040f0803120a05040201210b0312040305070b07050d0305060a080a14060106032c0313030f0b0a02030c1c0605031506 75
    0x10410384411079040c0421240680061740800208000d810812051010960801d4483c612005d141e00803a0a5139004e034000c0350201c10008040c451078507544640c030380041500d800b038600c08001d001100c2da074194640c40910010089803401d070b460034084086030300030000300c0c0102c00080d03580e00a42d80c4941001031080e001c0c02c1ca81c00061550100c5216091003150705840710b844110f91703030000c602001d520246d03286005948074541003980e9020020611000f080324001f65441d800c51808501741011035010710444c1e242030107580300240e0041404040540c5c68500017520b0380d03418001410311880340d4020403c501a800b071142c02d2000f0711101840000781e2104a4180340d036030701c034210129040b4a82080b00c440180b04088080101074203c014807141c0e2004590510035165114000d281700c40e4400c50345040240c101004000701c2d014a207501000e504411411858030743c030040346030302c04c081d91a01201c00c2490400100300d025440113001e000c010f0103c40d28890030210100d841da0003607581c80e114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 644528210 1250 644526960 644526973
    0x2042a021c032904020c0106030f020f01020708030f090a050d06020d05010b09130b15121605130e04050a0605070f0201050c131203030f02130302041b0f210c050a02 72
    0x1070030b01a02030302414101c00b49204403038107100c55464400b610b06020450740f203034007000141300000090044002940c011010340340d8040d8588100221503032980441415904010400c01212070f010080d510780481904029544282c22000904510040e801156000150483c048140600c07507000c2c5c03000f80c20601d000c11103641c031b50402d42068043c0b0540700340c0c4000ea40c42500341172000380e0080c1010f94400b0708040b030942ea090340a440d1316007000d21488007202c1c8076020403207007a103076246403000c0d940b103810700c2c1d0b10703181d1850405040c4a070705020b1024660703500350101c0c0400000708903180c6843e412400412440c100540011f2080d1480540a0b0041d801e10003c11000f520f00d8085410b45600400040d0a1314a0542900d502210f0710600fa01415503039440701120400d9800180541d95451020060444c118410801295251050200001c0700ca020f44501c01c0e4121103280d01e01030a0b810700411420a40c0b542d05480c8901c0c8594204c0c0500700303200030150326005400b402c91100c80382c00f40c418 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644529460 1250 644528210 644528263
    0x1c091104090203030307120b0405040609020a0b0a090509060f090a0f0c1809050601180f09051e06090c1c05010f0506030705221710150b0702042a02 65
    0x35900c403414043c0d81a002000071443c03039070094200b2012607403e80004110b880e5254002030844904035410b841880d2111200b5045150682010b00a41a014052814480c00b46402040c91b80280185030040d000d120118a1030350310b100d20101203000080a6615a1030040341023400342c01c03070140e50300000e802c0c15440e414070b5029048240310b402d01441040721f40c0d894243d8000c050b03c40540514144000c00c0c02401c10710000442c00406081c00c5411410803a1900410004580c0014403d0503c00a812840807056a4101c0c08941002c002c071108030203a20351420640795841013200d8034482503030110f29014001d80540080b03048800c0e42c03905440a95540741404004c0c8011034114001031420440d038502c99011252950460580310b0030740303218540b1a2001540c3c401d25000344900343c0d010605000d0700680303c1c02040c038414101503c80c8003503443d00100200724000c0301d20081c800c90311140c0424425540f0180514014012502012480d000e0b640103910340303090100f82125103048048098 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 644530710 1250 644529460 644529469
    0x10b01020304180f0b030d080f0109020304030507061a2808010b010203040603180c060527060405010c062406030c0509090103080304060e1f0b040e060f0c1c0911 71
    0x201207843d4241c60000342d0410180680040c101d110091003a40c0d03540302003045545081002880121454450600604081c00403450240c0b05078002007826004004000000c0da0000a403520680d100101240c0780c41c046201000ea4520b070008150011502e01d81d01c84444241000135203142c0450109500c40c035210203500f4284d509071064540964410041042803034403032341c480d4851403154108110030940035030302c200150300d442d4003910010780701040c6201000c0001290f4a01c0729108018100750100e000301044290041d803007880c2c14840740d20480030070310245400040f04008040c000d6504001c00c51a00b1460303158502501c4006850980b4800304107020700200c9080d13400061550707039542e1039640d900b0035907030000700b040702c070140c0300c0c1c40d1038070800010004005202921059044025011140c0c0021504020b04e041d20039401c14032742078001140420076940100740610407982c20780c0e620b00070046e02d10541c114020345900350031860034424455800841c0251050130882c101c20211070820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 644531960 1250 644530710 644530717
    0x50c0403021c0c09020a0e010e1f180810020a18030c09090212061524030a020703090e09060618070f051b061305010c0908030708070303140a0905010b010203 69
    0x350001c41d401d481c1115058000c00181456100f15200820241c4401071142a60082c102040c00700b03032003c081654540e044074040030b00070003e81d5a85c0c0d400d0130380c0c403030a103070b140b00303a410ba5003031015204060000319565440d05020308950021107002c0c100519044000354002c191074400900c00c03c4180710001940301d40709003120b40040c08076185504010f00c00d002070811745012680b01050100840180b00140280c4d841034502942d21410840210280290341610184401c161601048203100c0e40d0101d4059a07008066100c0068640d50346207001d03142541103400c40e1410048142c1040a0080d000642521851081d1801c0c4801003540d22350120340c210982f400d0020440c0407803400c0013103100d0300242a10742d0551110154070607242d2056400c0c6401a0b4041c5000500744003640140310090082c00d0b02d04849180003410640340140301a00d0340600c00004201c02c80000c1c0c500c040c54401d8100380000c403240300780d0b007030f840c18800c080c10000c04070094101c46075400c201d521280b941c00070066 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 644533210 1250 644531960 644531963
    0x2130906081f0225120822080f0427110903100e0304030203030d1b14270a030f05010b01050304021012020f1606060b040b070209100b0f0a080112030c020603040c080f070603050c0403 80
    0x3c04040e110350361603075644c000c10100d54145106110021708015121808004c80825072006031440d40f6418032035040d914038403c03003000d010040dc403208003500d0005090400300684000010709040038446182184201e80c0060350511000c100480500f0301c550211320b429005155131000c0e4581d408044c0c0b00c000c800f40750550b41000620803c829940304000c0c0300e20f040000d00d001c501d20704500000440b0b864064005035403c8813a00c0c114400c01c078003481892442c1e1000d00b01746007580780c03650000341021000c0c140c0c40200701520704810140c14481e0140d8004c020070300b0500d40c41c1e50080815400084a4040684a40e801e2070700c00030f00c1e000102c1c102d80c107072401c0c0c0e00c0152802e4150380a10240c40b4001d45010000c0c1869500001da50310704a016241c400c0303450714581c0d603814061070020500303201a0044284983c4007104100000d41040c04e40d1021541942e00ca40c0b00c0d640e50070f1501503032855900508a5000e0781110a04200004c540c0c07006441003511700300002e48034015480510300030b5000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 644534460 1250 644533210 644533261
    0x6021501090c09051f02120306030c12010209060307170601090803030601030c0c0804030b07080f011412030c0f07090c08010b04090e030d02130906081f02251208 71
    0x5120031600754001000c03100c101c0c18100c0c00c0e81d0340e07000481d402003809440c0c2c4c00c00c40803141d0980000d0b076044c480c0005400380c0e9503000c0e04501388030300000d441da500359191034400c88088040003c142c00c20f4041d0380b41c0d03030401000d503601ca107004c0c0005000c3c648032200306251648900001200b641c01000741405541074000194115a2160010f400401e1401a1582030054200e410300004803510001e102a5204e0318024040782425080980b00900203003898521420810051240090076405001e601700b00720750b8000380d00c03a0016245e082d4880e9160b008418000c20340a01210900010445c1c01c8850000c4200613008164004440a4000b030003002a00d20041000308406d08558020001400300001a02d2a02001c200754001700d0b40003500c4101d5400510300300700300100035440b1703080003021030401400450448a0161a40c034143c0c00307404d1902d503030100d942150740c00e82024503514083c40b007502d5020766865003030684c0c1400100003564002503415002404110500081d40c0c1081441c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 644535710 1250 644534460 644534503
    0x415200d030516090e06031501230d1a0415020a0206060909030c120a020106080d03052505031b0c0706020c03061006080103030c030e06030a1b09060e060702030a12050d060602 77
    0x42c1021700240c805008158944510418410f2058019001a00900d40306004003c40d0080c50041201d03940400c050340d02c00c1511002c004007041d40341c054414030140c1d100c49140c242c0e48502d44040060b0f400c3c90060982440482c0398081660001a52401108211207450003503442000c603607540e104880302035205422200802d00c0c42500f880c003510501b141400082911611445034030300e000308410366400043e48500c144896019a58441c0c1f0031840701e0901600045200e041c09440c0d4070020340314196040d4060400c4080310340c134400341c0d001d112032942614241d40c3c1d00c5074029540e000200d0f1580c42406490045214003040140719421113110303440301c203250b078030f0340d20309a0301c00d1250b450540900c194069102e00d1a5204801113109a05440b0700090301481e2120302c100100d000459407041c800d050200b8002c90342c0208005e62100c100300d80c7c0395681d12881c030220341800040840206901e007031300700d403208054102c1c0140200c40c01c6041c040105950b2404100e036120400c40001c2203a0341eaa0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 644536960 1250 644535710 644535719
    0x11090604052704031709030a170406140910050603031206060a0903020405040c081e12070c050405040c08061006080f04022421010b0415200d03051609 66
    0x3618a50110000300448038011601e000c2800c0b01c00e08100c500b2400118150141c1c5900c01203d81d00c0b5820030781c240000c41c1400d100d000d02402c0d4031150a1210342c1840c800d4002000c221994101d00602031040740881c1c03650421200c640e5a4170403004000344090304000c001841400c00009a803541074080190b984a80c49d54014045542d0195030100208a106c440c04000b58a1704e010301c80c00307070b4801c1854040441c80d01048078140444440c8841c800308003041d0881c000000066420888445c80d11402d03640c0820340f0341100b0491155210b6600b29003003008000a11621404000881d000c40003500d10303035030b6600c0000e917030241d0074002d44000c1604078010032800408100c5065019102919100035800c4411002003420b1014444010a000015454140c91070200d02c800040b10a800e031007456505046224000d40204e00030f4005a41801040c1804548176940c0003800032590002e4100150b01204402c0d182c9a00b615900c0c04681010040703104003c13203241700c0c05038900d00d031b1f80d02d001c4d182013 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 644538210 1250 644536960 644536969
    0x709060c0b0103110a0e1611030903070e07110601140f0117070302030c041d060301150b07023a033b010e061317161401030f0c02060603011109060405 66
    0x80c2a5019041981c0c07a9000c40d1400b01952128054030f01c00d2801f141d1517885080c000c05010040d81e0900254209108040d0b0a4a0004081d0140c58000a088003a076681900440b100c0d48465003118440c492107000065112502c0000808800c00707890351115999240b00540b00e1241100c4a103240341c1c1d0440000344424840d60195411080300f945552606583e0361101c136a00303420344a1400e50b00390207000d1285603d000d1045a610b044408607000c5050324000440500340034002c80a400b07800c03035480b50300410402e6180c00d0016a0307200c07041800e000000183d0320315103078681c40031008138204030124000038001c41100850a803a42c620305038a400b02a600a0141d003002d4032041c10b001e0f0754040d903150341c1e88000190041e9090782c0d21480200703107040440d0190b0308000030080900d402410400d181884000c0d12031054580c040b81d110b0a40b80d034000102d004141d1403c03944805841c0c1003049a000d540816050b018041c1100244600c400c140510000d5205040741142d00039000c1204001c00d040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 644539460 1250 644538210 644538233
    0x6010503030a090b0c10090809130621050c03010e06040b151003090c03120309051b1008090f10090b090f0c040b04020409110705070b0f030f19060e0709060c0b0103 72
    0x85d860261440c0d0302c04000c2200c1540d045140459040c040031480b0f4203d42410780460017208082c50043c8030030b52400f001ca10302401151036514454500c0c900340d80c140041048038208000300640200800301c401c1e50100e442c2c00044d1000c582c00c1344d5040c00308060140f00440a002c011004140e81c4446002078416801040c0f065001c90f1404450b1100101041d00340400302100101a103020569400600d000303820710030301d100d2030382e60017504603030144498580740c5821502421506240d2003039100d00200070702d81000010550302500c102a00c1410b6081c40d5044540341c1c500c80d9603841d403580c03980c420b4a42c56294400c0030440951210009103070a18050300040e13880ca0002e00010724180c0c80d0f030500b00035030300c01920300002000001241001c1040030440f52004054680070b00d4100702c0600003d030083d100c050407010700080800d010070001d01c0d00701500800072050f9441009080c1d9107454214482c0000c89040740482e00720380000480501901401c2c0c1400d074440a8191075a08558580b680003a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644540710 1250 644539460 644539477
    0x13020d05010f0614150a0509150c100e0f0d050315030f0c0102060615070b0c160b0a051501090306050c130311030706110607111c0903020306010503030a090b 69
    0x145010500010400c280714803202e014070203501160007801c00c422107a01401c21038060380030300718505866000751448800d58146140d6803406540e0358822800180d002000028540b0700c0581c000f0302d000c1c01e148000741c01c0401c900080414406080d1038041e0036200c0a49051500300c0d9040301e01152040ca120700021a80b10560342401e0b400c0004c00008245031840d0300108040c80d40c040d40c85103049680411100354440b04c129624110340205000120240c020312900500018101010401c03800390792059810f010101c41c0800c044a07042c0c10000340c4400c098401503110f41c078040c0401d441042100c800314101a06845035860149955a510001c1c900108640c243c0c48061012800c0d81c0d0400545c00021400340540c45d171071480c110100350070164294801c000380087e0a4110308003040c0802c0c507aa00440c0380c2003120110701c59056807170800c0c40c20300c4503058128a0030080c100c4550841401c1e02528025811155982c0e00c0f1003d02d0f60724440d42d078078407011404500b010082442c1c40d82c02041c101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644541960 1250 644540710 644540719
    0x7060b09090a0f031e02070f0b0c1c17070c02040608061323070e0702010c0305010324091e0b010803070f140a0503131809020105190c080d14070905091302 68
    0x141000013088000c030a103485503170b0040c0c1040008110341821396a02d00050080009040c0c6840001070b80303556075003450503041d5242c4600101c0d00607803a00640c00804151502c040316200c40ca0b094000800c50012040c0881c4110f2400f04042112000010080e02c568010301c3c400d10b60200944540b0301a40e0f428004220300b85045180c4014000e0a10001b0002c194030782c02100c05040110019081d50074040000041500c4d09004101090700403010040e40300b21a000f0030000714016018001400e6000000340c142000c05003604480d02044150700003160003001c110001c1e980311181942c0f0382c4940e4002502d02d41c4503445044c040f031641c200c80290544118200c500c540c40d250394850075900041600d5140200c17050b4104500202c5525060403c144188100001002c550010740a0300801c40d44040c404030250080c072100b4082d200c000b4a584c0c00c81304c5282c459201d00b0912029240b10140c2e90720250360100403401040c0a4824403040c0c0304018070013a510b6139040e02c103044000340300005030380c80b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644543210 1250 644541960 644541977
    0x612060f01171615110c1c030e0d0c06030f2a0908161703121b09041d0106120c0b030a020f0a080612070e0105090c19020307060b09090a0f03 62
    0xd807003071609524000d0135115554000c007a105000907020701041c0620545039000342c8110b105e2551840c4035001401c42008044c1c0c9000024103048071f0381d6180351f107596002500c590301242071007400c1e48050120355031344d501881884103800d0a00107507540d180482482000f140d000740790040c00c0c45910480b0034006c3c0740440495a5480100c0e14140c01c82d4613113640326031030b100103004800c4507864801c3c11140c000015481c0061402c2d00e2820070390003e02c2c0050f0400d5062a038031450001100701c403a0a0302c000c009000840800e0488800107041e240441e20303d40c0b90803000500b0700082500d040901380c000c0c0c0c0c605040703846c1c104910b4007584000c100711616a42000044071aa140001519807605141e90ba03000a00e00401070160a0340c403000012130b160f100300303401c010989841c400a070540340d095540c60325549803486070225a00401c02211a01d00c040c210542001d41c3c008064a801405008107020484c20182170108000c030544801403aa04600c48482c013144404000e03d015911a252000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644544460 1250 644543210 644543233
    0x307080406050301150f051204032f0d110a080c160b09010906080c1b1e0d0806010f2708060a0204050f0303160b0c1306080612060f0117 60
    0x18158440c0d00030344042a80840140101410302c0f045001401941c20070000d01030305428058a00c0c01280808804910140c00040070107210b010340710710780300d103404044c000c1c0c1f2045182e610014046451544a03445419030000c040c0380300318038130035400c85800c0c007a00c0c03c8801078542286992002e41c0c1a0010702c2040040c1040429098404005019040040392030b24001d400051500c90103a211604001441090003c4985000112012481580301151004e424505c00c1800d066001c004521810300100803221500004642c07841007604954a100103035079004d00548030754480c16618800100d4404a9810700c402554050781c044019200ca900305075515502c1c41d09d00360301102c045a0031a00481c0c20041418034104a0500340c1040740594100140000ca92486000140340a0104407541021851011031102295400ea5600e0840c80d045921220b0103803150205413412405a0110300d4107500700707100441e0a034000c00c40c000c4000c0e00c0d0303480e00040d0b61011520f98103003880d0340034100c02c014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644545710 1250 644544460 644544473
    0x30f0f0302120a020403020315040b01090207020a030b070809190f03120f06140a05060c15070513030f170309100e011107110f1206040209070509040e0610081501170307 74
    0x621807120503c0150340c0d182503205050900c00041200c001c04400030301804000742202900745d065802d00c0f140103881d000a03000103512400180d001610740c800c03800c14031043c1381d03010000600c00e500c01c000300c5410703403020b5000c0803142d5030521000d45191a0a4800700002e441002c6264101c01105c00114003908001404421034200b40e0088100035010350721402c03c0d0401e840340c0d00060030102d64607805c203010070309075076125025a000c005541000000040041c1d0254042e1454090070708060525030740c4a1522441250500009440780e810b100e1049003401640c6040324420101e020103840381642466481001d00401040d400f002e54030703400c0501001c2c1414014115440c041c00810342d40c0710814084c802ca0700710307600c06d40c1d00602d120031011614001c0001c519401c40c0e0f05440051282d500e0f0001110304c0e01480c034505501034103281c01c1406032000014054004e1248030700411020395a00842c50b40c0b050800c5081c81c00e01c043d040108090b18400629521584480003580c0c600f030b0b01540c501 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644546960 1250 644545710 644545747
    0x903030714130803120718030201020a020d05031308010504051002090609010c0809040f0506101404032004050c0913272d150c090302040b220225030f0f0302 69
    0x40010400e0301e42001b0b095503107c0c5d2400c120110224080c2c03400d82c11600001c0d280e050103100030380228107000b40d1104102c1c04000b1142102c40210100307444580ba05a803c0c00b0f09403e40d0151050b118085101c080e038042482214504a4000c20f0503113407003040001940e0640030204260313401e8405001c04122516640124442c207420703a0304c0040c0c6441c0080070401c00741a00844081046541c6010070312440042d811102907a412074a8092421040f03948900c4a034001e45c20140c106062100340903660510f840a441480011200e039480c3d01e0351a08404102d4414444082c41c044a00c402101241440c4e40707940049401100d0385180c24043c903d15042400b00d100086030030550b02c54501090003a1201502e00f00f11007540c007807103a41c4001c01d000340f404000d400068803079940c2c1d01d030300949959427541003250a00b80041c005c0440c0d10a1020000940040340c0c02140c0080044422000c0a0a41041d101d03596040c0c82d40c074928250404121036003401f600000003415420806421940f41c0c2004030f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644548210 1250 644546960 644546977
    0x109080303150a1a0a120603120c060513050613030309021206160309050c092e06140c0607030e0304031e140d080c0a1211120903030714130803 63
    0x203420b200281d0074007a250409034086039204240804101c1c002d850003084801c41c000030700c1c140b415040360b240028010446a803004121100d041c900720700382d0350403421804800b40541410462650740c445924001501c0d160005d20640101d40060000b031800440d1a0b4414000d15002542036055800300d1a030000c2011000c01c41d90183d0100a030140300c140e0b6074a041180ea01d0240280c004980e162543c4070140ca40c9148500d04090020701c0c2c0709a600209104805610b40d60481038108040e552440c4075903000301000102c10504002514582104460901000713800810079643d4010044009240009034460140070030400000032030a00050340c0803018080c805200c9008440c6000b01c00600d400008a4840e0044104a060a5000111298444044005c071544c0d42d42e4000c00700c030340d0f107203a4840311580c81c40c010070707455a080300c0005080803519445480340d0a4503075202d21175803408103c45400028041c000a1030654075150080c0400842040117540f00075101d500550460704075040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644549460 1250 644548210 644548231
    0x60e010203010f06020a1203050402011e03050f06041503080d090f030905091006020a110a08010f052202062d03072c13021b011d070e060603040b060109080303 70
    0x42c031032040c2d0f0700c5002d0002d0070b0300c0c0000c0c03064a8079170b9283d1a920900c6807242080c0340c2e442000030b0039a4007802d01c0945800d4060340e0800c1c0381e200400042e00a080a0b03d5a100d5010407a0000300241014812803800032680a40d00f2041803650f0340c1d0044550109840c0c580380c0d40c135031012200040034554234414042c440e4907164145418030341400380c40400207103c1c0501e0b443c00c0c0d00030400c10343c01049240070341d600a2050405001280045244ca5103250711400300d661034030440282c01c0c01c0a80c00580200b04401c1904c40e0b403a4645400c0c0c9003aa19180040d50200b0300700443d407100b40c1c640f010300d0210700c00c80c0d281401407542c000c0032400b1500300721031101c080340b003007218000c1d408000502c40c08181c5c1c14100965004240300d0201c1c0701f012083c48a00160740d400101c0c0108105800e4400304d103640303608000c0c0060b20003030525551076039600c240035042d40305812000c515820301e054098481d00c0003801260a40e40da07525001d00305c00019201d2414099900d80210b10203000340001d510454200c078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644550710 1250 644549460 644549467
    0x15031608060604061520250b0403120809120d020703110601061b0203071a12010b0f190c0c0306230103050330070206010f050f030d1b060e0102 63
    0x3090282401001411140b00714505401071055041a2104c28904450303441c00e9400315038651086504051150014500c521441002076a410000221030390808800340305d03500c0301e070360f9040b10548900a500000300080b0590050703050440c451010603030b01c00441c0c07044400c1c100d54141c014070703c1c1c2d01030131041100300d4001400b2814160800d142c0e00403044a04002c01156141c02401030558201c05090b00020031140281d4003590f070100604030103001c025504c0c03403000381d400c00e60740603960109203114200d141c400000644a440070301030f501d81c03842e031011031440c0c00c40914100074000a44203800d400d0000079811400410302030302d034110245100d0b0b800081c500724041014041310328801c0704c640c00f05401c4001400054004030039229184041034a44807030300103540d92140104170075140802000080020000340d180e00080d901c4c1250400c1d40c0d6100384984800074001107000f00e003070711034240d401a0f046201c080c0c800c1c01c2081c0c140300c0618501d003038209590b4442040c0c030034049500f9916900070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644551960 1250 644550710 644550719
    0x601031808040e220b0c0f0f0f0405040c051602010f0504241b020102071e1d060a170d0f050d0c020304030b011e03080306041407030f0e030a050d0203150316 69
    0x864808851142408110340c044a5500c544017000c0042110428200c0842e020b8255200a0160307852040315401d00e9899040710090650141c20034403410388a40e0501c000f142405000f401281c01c04806c50702d400b41d00e60601e400558800e44180000801c21404200c00a8014101c20015000c4402c00010600701c1c2c15030100101228808030150301884420300704400140e0300042d003030b01141c02d862119003801c00c002c00040300720070321540866046580c0c1484030802480402c892031050783c0854080309800c1d00c8941c0c00c1203082c049040e41d040ca5020041c181c800c140280b102055544241c5046440e2a2040362502c055905901140025900210303040c41080300000dc840c4c0504044d03401041d90005d01002501d003443e191001a200c4c840c0000401c0c4651030f15000340c07006101054541c0d000e0300348403000600500141062001c0c5a280c11644e201ea08e0003c07044807584106585d80d18204034080f1441002540081e0041e9806488040464842d1303d0500105462032684510302c40018a003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644553210 1250 644551960 644551981
    0x18040524040b070f050406080603030c0d08100807051503090717070513020a08010314074115090103090c09151a070b2701020a03060506070b0601031808040e 69
    0xb904a009220643e401410600d40c040c061b0b41c00c40d0564900012541c403078002203415803058540a88036270086400f1400e00d1a003041003140200311003d03030040380e503a0b2500c0300c07902d81006004840c4d110781041020001a258071001e103400c00342140641f50300d81c0c0d032440c100000ba80b483d0386000003600440e40402281c90302c031380480c10345908002c0a40c5041d42c0004004c001c420140001072200c1014100c2a00007c810800400030b00344a064104d41c1703850358142d6450a03281c2545000300c1207407100495400c1242c00b000a40429000380103441440d60b44030070002c2a4000d0300c1041d040680d034950a50128005d90703c0b0000501c880703680001c040d640441036500c043c070250012100d480383d030f5140c5166112490f084840ba19000741c1107003c3c544941480c1003425901d2400c000450b00d41c100390700346114041d07004180341c90303098900301318003030f42c400502405004501c00980000170020009440754000d401c800c1210a00c040d0031401c20301607613106480303500300d5041250142c504404101c180f046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644554460 1250 644553210 644553233
    0xf0927160e0d120507060c032a120b040b0d0f0209010602070621180516080c0d120c2019030b04030e031006080f1009021804052404 58
    0x45440c0c2020300801a1010900480b60302100078060118072002040d428411801c0d10b0810760300140034080080d586000801501685400b01054041070f0761684482a007450700185a041c40c0c0c03201101506a501d040e40107003182ca504507082034440d0001111941c1d09800c03246001c2c4200380f42500c48010740184580c9450581008042d5401505c0601c0000d03002807040001040d000b50102064402400d00b8000d014280e0b600041000302d40f6420302080004030b486000c0745c51102405210301e503034031106a5a60b0920070344a4201c9000f411a60114076000301c0c41901c031082341000b58036082c482c0e8402000402c949000301401c060304124946503d020119000000914480c00c9440d50640e1a500e1140200ac0d00003030500c41d05000300502900c0c240890850310034960001c00610b40c1d08c01c44142c0703c081c00c940b452034274044e440400380c50700d00e248140001140c0181c42c0075a0007a8440083e009280c0c045c0040c0d0f0588502044102d01d07501c204140500c2d9000745600582a041501c0c0100c01e000c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644555710 1250 644554460 644554501
    0xf0f1b0423030d02070e0411091e0c030c0a11030403020a0f0f0b190309060e03030702010e0f0109080a08100e04081c27140307060b030618030f0927 65
    0x2040210f2002d445540040c6000503514421101e01c2030303071035614102095030001050b090f0000c05400820041411840300b07048202c04120304610b42d550380c40c603812b405102c200c40340c041030241840480e0001d841540301c0d40101550208803450a5140d40000f6040b080380c2e400b111050301541b40c24841146114640c00c02010b0980301d6509010140089e18900340c03003240305100305a5200d01820501001c1d411000c000880042500d5a90421140007400b0342824043e0a80e148240941c041c840c000501c208080540c10071146800c0100340d84007201c0f116405840703603100b8601144080350034000c0321165030049100e00440341d69104009604013000145058200e903ea1502e010720140366040c56089038849201e01e070480c462201c6103441003007103d4000b82820380c0d20001ca216020401d49511800160400320211212030752500c2d0f0864003900c0402c012802a0428040f16010041305400703098079040080880c800c985031403d4041102481c0200d52801d03500c01e0091148101a01001a60300d030b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644556960 1250 644555710 644555713
    0x11071703041502030406050f030a140421020f0309040c05040f0f0e0105030c130506031e0102130f12080d060b0c150114030303040213110a170a02030f0f1b042303 71
    0x1761070200301a1030360050000d50443c1010010000d8003e84250740400038540a034104902c0c0da0400741891482c0c0f1403041203864035100a0810303070a03118000aa512002a07043c4021440d0800490622020b0464181c403641401820701c0041004040100c0c0c3d6009030080254100c0b815160441140c1403000c186c0c815400307500090b51122003510303425050103030740c03c11450101c3d40340c84500c0030030320b0038181c3c1040d41500c0303066051030480c03c04190001d0a02102400b004a0350b01e0712850481c03805410342c40303804d44900c012220b5100140c80c0030007a000e4031802030b50000e903c0740d40303020040b490380c06400300035000c2d00800700201174510850009801740014502040d58800600080303545c03484040d1010303104070202c1418032048038072030b00400360461088035115242e0203d0003014040c00d0b542070500c55021244800a018411940b0a50703108910400d1011696250754102401c080360140034544907254000c818410380800e000208010020300b07031014580081c0882e940d00404205003803078802d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644558210 1250 644556960 644556967
    0x60503010506070f0231050105010e060a03090204110703200c01020d050d27060b090f0103060903020a02041109040501050409030507021005071205031f080d1107170304150203 77
    0x1a41c440400351481541c0c8081454042d00007400000d140c40e6020411000342e41c0c110310362002a90390b00a0840846c990032805020302d076203a800655520205034203154203c1801d0050350b4031130b48a90000300503140003410008100c0b0890051580c0d0b903002510540105900d00490051112640c1c0d04803441584900a0702c440c1019000003510b920700355060104200c0003080c05611104c1c00c5c0d120000c656030002441c05152056410040c480a11800c10396000d89051752681c00c50401905080c484d408120300199141e08503903501e40100803d04c0d0503021485042c00d4400140c5451052003402d510004849880b10159401c000035107505820042c0950b00340750701000007039004419602c0055046035030040c0080309501c105c40500690310040c00b030310342089251a4158100c4000c4d801100103030342c02d44129503170304c1d005040c040c01703481005442d9000e59901e02c071143c4111801d40e540c40710700c03040d02d1a981d84c400121030410390f480c01d80e401e55040041c003000101104200c14a0002c001d00140d400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644559460 1250 644558210 644558219
    0x3061005150a0504080601170714011227110307060512150d1e03082404110927160909090c03050607020a060501300203010e12120106050301 62
    0xe00c0791100003070360444240896140b00250003001510060200306045a040d580d44441c5243c603030003000b40c0c6040b0360066003404101c8109078550750a400300180c44100c0d40a00d00111400240020342c11310580080c0341015102c4d43e02e10f0405030410500641209651850b80c138101801d10256a00c8001448010490001c103c0c503640c0da01e0b68050785800c1c1c031900ca5800003010030595519000c0c01050300308180c0103183c42c29910390450811f1030003913440c2202680d5850100103411382414044003085145d82005041e8902600000081e0014256682c207001c240c0001c06e806e0040003042400c480c3c4e008803140381e0390700101120f680c0400f42c2040742d401c83c040558003802c03425503409144000ba48501581c070905c80c0c400141e0006652003421605180352440c3c1c02511740082c8802140c0c12800e20000085000381881801c3c03070001c242031034541004500440c110540c0c0318450803038041d501c52251200d1031030103004200d10202d18140c840d58541804450306000c00c016007000c07043c810140010710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644560710 1250 644559460 644559469
    0x1c030309020f030307051c0c12030501060f050301030f02130b040f1b0201020a0c060e070b07060506090612031c14130b0a02280315080d11060708040f0c08010603030e03061005 77
    0x4010b10400f041107c3c2c14404404503800712810070051704017440e81003040106503040d8011812103001e0307603a6085030404110212818402031201034202e03903091011102501e00210707407002500d041100000d1100d00130001c2800ea4514414014895546043c96100d2008800d8920415004da1000b1494070b034461601410070303c4c01d444042c14940d61800700d40c1d68000200049000f0700400b080464a1782070320314042000c2c000480d200c0c0d01680860f4041020760030500b20107019800840d014504050184000e40c880101074410340400540f82c11264188a54041e80d41d40540801038000074a8034040c1004d80c0d040c20b02500c84842c1a1040221107a1800d801251304000c5181c10100c0d4182d5200043c114041e00122012140b4820070940000f060740000401c1c00344800c1c20f46616041c0620b811038180c4a100444070035000c50042d0000800180c55600340c0d20b030311442610a84d20880e19502840c3c00c450305078208401107240600e1455603490200a074680c000c2c98402418062400d000c040f8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644561960 1250 644560710 644560723
    0x4050108010e010b071e080f1b0616031107080403260f090d050c100e0f010311090d05213105090c09190e0907060c111c030309020f03030705 62
    0x70305085000c6c050743c4260040c03880c03082442600544015142d07a448110101103a01890115042c45078800c58462200400314811b4818800e40c02000f101d801d0b4982d0903005000f00c0303101405400c5041142000050048025002860203071456040010480201c0686a055601d0400301a0804c2c021100c80e102a1801c9036003203201903440d203005010920b0060714000e2114101030780302e40c1d02c962503117426034406440c055418003111408440112000150101c40100b0380c07170100404200110045428100088154288100e0407a504640440412410301c41d9440c4028406080040d46c0018401c1045410008407202a50108600e020311f150100100d2035121721401407110300d00113620000d10000f44c900c141800b40900e000c400400301c400282403454043c0d0041e03115903102190010320002115425607090b81c80d00c0503024000c0d25140146020450460f40c450400b500d11b0350706400210195043c2c0c2c4c0700c1d0702c0110701c1035a14810082455441858607010364014001000810710001740d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644563210 1250 644561960 644561963
    0x120309070302130609020d05040309120f17130b0a09060f020d120617072301231c020d0c03050610120209060a0c0524340504050108010e010b07 63
    0x1001006038804001c8050203c562141c0085d51022400c0500c0c41e002c0e4112030312551181d51954013058030f07808003100d001520b42014140c0044141e11400094429502060050603260709504004003109030107071005413034100100420001c00c240e018543c0100c1d454000e04820700b0038400c0c810101c100255507803848014441004036111920038502e0007644504080d20090500c0a250468518600ea5500e00340c4904400d14898944005908402d001303542c180703040580d90250ba000704482d5080d007034000d41f1004e55242e03100708418406160148640243c0c81203190015849800c28101c0798110307051203000700103040c100303030412007155105140d00c0d40226881c100040322031a00b400b070100a010381410103400110011303028824903000301c0c07500216440385048400006c031140c5010b40400a14010110034076090380400e0a5070b207440c1e81c4a2184c000d07046088011000e943e01001030305083c2804402003080061f0a00c1696481720009000d00301d000c04504855145c101c0e8103080d4898a00c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644564460 1250 644563210 644563219
    0x1151d0103030f0e04090507120c17070b180910030218010819060f0533060304141c0e010f02060603070b0903070902040f05100806090f1305070801020c120309070302 73
    0x48040f4145d6039548101d0a00f40c10604442c400b94444407000495958840241c4001040d00000150007200300b07616040f0814540c0500140c0340342011400c02030308008684191340142d561351502c1a19880840c0388101141028004100e145006106841d00720544d40d0561040200040c0600840000c465502c0c5e018940b241904d003640e070500e4030044c801c54a000c001e560074181131101008100040902d0b410702c80075060040792a00c024481a840d4841d12507412120a03c0010003103800c41c9035040c0603003981e0040c0c2c0c21041064030700404400b14189164003049200946048550f0701116486022a090004010f1400c1203030000b0b03503071001446803401c0b0130b50001d0500242d40b0300f0b0060000400b46010255211511000c42004c084541d0046a00903c0340300484801c143c400c1940360300880018115448035210031017001c042d100b0060085041e01110240d48000460800003400141155000103032510703c00c1942d9820580c044504003002c3d0310510900410301404101ea4080fa54100c1c3c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644565710 1250 644564460 644564477
    0x9020705150702071205150709032001050d0c02011b0207050312131d0412030911090406020c0a0303020d0509010b031203071806030e0105061c06020c010b0301151d0103030f 76
    0x2c0e08a1409a00d60008500c0c081da802c4d49900b0020000340b035242c5c1d94803110f071180844c0c6e241c8100302e80103070304d42c800a0070200780b403010841060940c1e126016114410302d45030b4a40b00c00300c0c1f42c400c02d86900c410342e000140c1d52a207032840341244035a07040300740d00d40900c050191286840000383da210800d01000944030310001d400050043c84200c0d400c01001926101d85c1301e804c01c0760121010000445080c0d86406e803489610b08058440d105a488a5034007624403581b030080e110601a104000900440c0c0702c0c0e03070030480500541820045550158807039a000340c4d448075400125410341c2c4006d4001300903681042e0380494180d401141d05002861041103003526541d44403400c136104e0a0740a00c04d40d1024040c2004200c1aa1680059000040e1f08000b440691103500911401180050078690114002d90b10b01e40040d440790020515030ba40000045003110120300000d0848581126801400e1b18000e02085070840c0341c60804010281038101180a42c91510301500b0304800032a01c41c02c004158 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644566960 1250 644565710 644565721
    0x32703180f09091f020a05032403100b15040b0301180b0904030e0118051507050a05190210030b091914010b041e150f050d0f060f0902070515 62
    0x103284000c0000c0000d001c01801d042425056407149800380e500404040004c0f40140044513034000c070707540210340c2d035182c1d4915500c0c00703a2500a612944818084045282c6942c1c50076602002500c01200a0160004000c0d9000040100e100c150340d00c0700c018000180010007543c4154070036a81100c03046040981540c0c16070740108020800340d410382c3e900c4090f810500c414194071251a1550650030b0306d0b00e85000503602d00507030321106c1c00d109942d401012040c0d040780100703560018002813842a81107500c400700030340c2d0311030034422185501c04103060b095851400354039000c00d100000b4407490900700502da04140c0883c28480c0010002808454a481d0781007161220758403098585e18880107005040d6118061450070354410303c28181409003da8101c1e0b11081c0b0030f5441022607e50f54a034118240b403041059441c0c3c000540c0f420107000d401c0c4028003e0141900070581010254803000889500b400c0700740742540c050342c014007401803050040c0c90000704001541d855081d1201c10148440e582d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644568210 1250 644566960 644566969
    0xf0e04020607210c060b091006050a021011130b0a091e03050a060b042702090a270c09090213050912070609020a080a03090902090402090a060503270318 67
    0x5905800c845420043c541c5010340c010300c200d071094498030003440803d2901003040101e000550784001c060010303010802805008a005001d40c5110707006842d0b0fa11b6500d42500100c03201d01e00780710505040000c012483d904095001d1016203c200209070801d0510500107009242c03c3c051008869040e15010000420410180f4020340c0e0110440b0446001ba00c0d140010384403080302c0c1030041d4101081c1c411b4441c684840c08440c500740e2074082022107070325000c01c880c0040141034011380c0e82c0d0f03a14500d58014102080b038010a0320840d07000710f80c04891b15048100d200f540e80304032507552511104100595407448903134403810110001003415200e1a078400d050091510444144940c0050a60100241d03500007200c001d000b1200c0340c0d99503035a401101c2d15030118000050005441d0401400500c000b41d0140002160142005041502e008089140c601d00c0c0d130482c2005c80c0380407080215020b00303080043d540030304103a22001c500004c2c98007035642c3d00441e140c0b0304032004803084090b09602d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644569460 1250 644568210 644568233
    0x20d0207080408160503010b03280f120f02010515060a170a06030506060306010b12090c13050412021b0409050109021503100e090703030c08160302070f0f0e04020607 73
    0x100718a0203079803a90354180070382d510005903640382d003484a09840000c8600e410322680103071500250140c084c0c012803107200100a00c001c2000da850040c02c0c401c11004c0303001c484000c105d65205d203c0741c40d80212001350182800750700c40c003401d04580c10041040140d210201d0341e0f000000081c0da42d961078081140c02503071a0071180b14068440c008013003c1044600c070541110040340c1c01001680c40e01c1c0c07900020715886440034010001c540b0020800302030000041c00300c4a44c0328940c6000e03224078500742000990001d44d0b5121074030b2129100c2003800280212039000580c141c01e540010604110024020b04485062134403183c443c5a40381e80311418018290032000c0c2c030a90060903121401c0c10300642403450b410a688134107208104807404968000040a62405444600024040a0324540e000c0310440b01007901140e07881c070b00303105045100480106030046a44250040d0664905100502481c2e640c81e5011041d901c0100c0810003131501d40070b009030741180e016190719030754402c0c0d824060507400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644570710 1250 644569460 644569463
    0xa030e03150f01050a09140c030c070c060e09010909121107050406090c0e100503010506090409020607060b030d020a02130f2403120806100f110a29040503030a020d0207 74
    0x410810030019040c4160ba0440e050390b40c1140c400021a0311481040115a038980190300c4428807240801e00110040c409981d102d4000d9114600d041c02642c5d030700030343c8400396101c2008940844c50310f44261070b092070007a0141c082c5980410280000d40c07103400b1400144482c0301c0a0049000c01c4070400c0900b4804c1a000c2c100150050000c10b644d042c518005003c001078500002c0e030b40040d40c03005451302c900704000e40d200316601c2c2130441e4204020404140c1c00052125406a6518403810041e1079000252140b036014440002d21000303410181801c02c81c0c405075100442d08005411070040c0e070b6443c80001c4401080f100042c28101d2300706604002d1080034200804001c4001c010602e51500d44802030a0728800c1c080c143c0c2c0014264019224080c054429561164140c40525280751080d015000c684231907107006103142051043d207030b050101140703007901c104d8200e158103c803141c402c2c030b00da0030b0740c0101c14115402c038580390721940e4807408050621581c4903000121503072116200c1e01540d1405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644571960 1250 644570710 644570743
    0x41e0e0304080109080408061005030715020c04060b1c0b010f050d090c0308070303150b0a1b170a0e030a0b04290f010602010b100f031806050106020c01020f0c030a030e03 75
    0x135080c100300c4c1890704103100d000c240d4454907002604d804240b00340da00843d030010b40100006410154100c184041003001c92045128060050340d0a5803103010b000c00a00703410000c241d90b103414510014045402421105403d4144500c1540c10b9a1060031000201d602d880e01ca9124041c80521202400d07800030060098500c0300e0002c8240980b090040002c14807940f810080141d12511810950b0b51071b2081402d121401e10841580314050a45940e4800c1a80d092074580800342e99a01104000780080c494885804a281000d05030445c1010380032403000c5009081d0300c40a82d8035103050443c02000100b1070a0440f0794950320280c850541302c0b00010390035040c54a0328000c140403071160800d224040040d070900d140e5450a0a00a51001980155603910107001d5115041500a04900d50000c1d298401280c15400411018890b981c003900c0507901500b0850300d0f1000082c54580501202002608140d8100c0490b07900060445070940c2e00d03003481c61400b18250006810f0001281c1c109802 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644573210 1250 644571960 644571971
    0x150501120908120c03190c0e0d14010606110106080316171b0c010f17040b06030c0d0501020409060609290c160602070602210c01060510080601030b041e0e03040801 72
    0xc0000c124081c6101d628a0010440b0f1030842c003110006840740c0d1401f00c004507664196180e42410b00b01c070390144c840d000d91221000c49030f131110240d0840703d031380e48040c0001e08084018a4109002e0007200010b006040040d42007142509640c42c04490070b0380300030f0440c808a003000c3c2a410a681c291170400741e000a9100c40f00032844015a114980c004500f80000c041c00b04011549014840d004641c00311502064095607445e030b0f9007401c402000d0f0400394107104a2005210940c0c2d071001140c40c20b07101d140050b071190319042403030302902c40d00c1d00a007060105000d0188122120410300b40e1034180340c10f9818802d0b051071540c4000c0362203501c1c1030300e000d40242d0b0400020000d01c070350074808840c19907080b503070705c01d41d169422a1101d0200110070003c40d80580f240a0b00b01c0301d0000381101c505030717078000602e15a4920005144240d00c01c581000300d00b90108102680d81c05125110544c031081d14140301d103c500d15050441c070100b088100c80d05130754072002c4007580c0c0c400304141c81c090400600204003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644574460 1250 644573210 644573221
    0x8010b06181f030e06010f0b120402040e0304032006070f0602090d060e1c050f0a0e032e0b100c0f06090203030c0705040e0a0b061c051e0115050112090812 68
    0x6000d6131051100140300352400099842c0003902240c0454518140745418078070340c5030807843d0300320b07000e801a41d0180c0c1b0365000c1c0310098018801080150b2040710000d00100f100042d00b0050070003020b0a501c9010240004400305004411601d00d495004000590b10030ac03000000d1841c90360f44034017030481d500d094503403440c141001524018461100d1120740726655004000c072018030542d13404241da81418081400303484d0081c0d8000c81c941c84010241d8000c0d0000c4900020500d80f044100040c4080c1d200e0300c2d07641a543c921074110040381c1950100004681c01c4409080e20808000003490f4078050011441030140c1603001e0945650b008050380da480078810482643c2d40c800c0c0c00399611540ca8569062440c00300019040c0109501011051844d81e45008101801ca42e0140300981c1010701554500058006d220460104171a40c1d00b40d10345016400105085030003e24150b4011902001d00f40110b81c0c01564000c482d8010000c003081c00c483c1d0b0301c1c01c41c00e9409840a1142c1c001032480a115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644575710 1250 644574460 644574467
    0x3030509010210050411041109040c03020a14070f110102030c010903020d091d13051e010603120804030e0f0105090306040807260306090c090d05070f08010b06181f 72
    0x14600c4401d0b4200e854000c0940d0b03160040350070680b001886061448281152400e00c0c0e04008c001140b08403240d820004c83c20f000c2000d03200800c1c801d078006580024842551900601483c4020707806d542d82c9810010b9558800208617800e40d4058604104032400711006d83c420400c91b030701451880d000740b1010240745006961000500742c60004141c4580740480e12035600001034000cbd4410103030b09001c0351202c200d20000d048001c04152000d00441d00301a0041122110102c005030400f00000707486455414646201c8106a4a440400c14503805110210794030015454400e07200321038641c10040c002d001681c1784e10481c105a031705806110208001e0125940141a6581c0180803c042c40904480e40890b01e120301140c00c0f0f204031042c40400e5032400c0060f0065071000000902c68500844980010001c1b004040c04480c80d9020000c14001584140640c400030114007000388085100480020f40320701400200c0c0d40d011041035022802907885c80d010071100c440d00100011141003c0c00000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644576960 1250 644575710 644575717
    0xf0d051614031215100c0b09030f03010806010510080702060a0b0609130203180703020112180f050a03200718090b0903070303271e2012010b0913051204030305 70
    0x20a056a104d5030302c2c1003810080424410300d601c03a6100c100b6003409a556541100d030140610905220074811004d160341c40b80c0c000c2d070180030f039600141311755890709007001486580d0310000300c10406c003c1c040c44207180d0000744041d000100100e01181c503207140c1c4003003031850190358052540000d4a01980b548441d035540190b00540840010446c88a00c10300001d80d2400c5600c0000d0000351040c0e03840c480394100c0d50100c0c24085010f00d0464081c00741d5110441c500c503ca100c10345094120819140800d80c00a1070702c4000c505501c8024030400d1200c01c12900d4070f240d842018540010320310083e4103480c80d513101e21441d9a01c02814081410042c00c100c1e500d4000c01000c0700805d01d04403440c40d6003010492105881403070010714055004441e0f07a842c18a4440c50042402000c200090000099580b10701140c840c0b01c056852070301d912542c08000c4c9445894041020b103906d003016600c0d06448a80c211580150048a2501e00c0740c80c030b1038038529115050503009044a00131070040200340d4010000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644578210 1250 644576960 644576971
    0x60c0a06022205030c212104060206070e300703110a0b1312050a02030f0c040609060302210a0501140403110118060f06260f0d0516140312 61
    0x1000305840c0c840b002c0c580e64112082206900200e0500041641d0041c1480606c201011909584a03594038000051013940130400d8041080c00201d0107208403035040280c4d071340c061602d00d4a0706100408201086443e40d400b00106c5940f070080022007115044080422850883c8804440c18a40d807800c1c80345071828083c401e503124042c05000006c0000b00d450548210120141c01500d6441c9403992145d8011a01740d0112134601a80d5103000251343e003800784e0600011448040d001d031b05030500810003100c0c0390b504030700440c2c1c5c6004410710250b281d2580703000c00c1041c09000b030307620040b8400e9824070740220804020807540c00d0020030160458900c1b86640194880c0d11003d102c41942c690b4071b8242c3e5283d8411401c1801041c5403680403034050b41040360945107080000552503101e1202401c4c0d045515a40c002080032107001c4014844100062000c00400502810055178600d030014054403440300c4480c0040141d510f82c00a00000e00c1d20440d2465101d01169079039a000c0441155640c0100c2c0c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644579460 1250 644578210 644578267
    0x60f0a15020d08041e0c03060c0f03110c1207080f03090709050c030f04150e031b1b010801061d12010b01030b030d0e0d0c15020a0b0c0711060c0a0602 66
    0x901a106809400340f00d0055500030f40d000101c80d01403204014065440000703075090448004008042101440740e030341c8a060590303c0d25000b1034180c0019040d699100c11000b00709204000d0301d5903446010560000f07001c40c054a940c0d65145604101c0083d014047c89040b420710000f040c03020044000070f021044568900d004d1040360340304e069030300c01800300f207071400050701042001400088640c43e02c440c000c880b0781d000003100c0800c9a1007a14607045294442d0081c0080499000003c400300410f49003259004241c2d42203051400001f400000107225190034040203580007100c2e1803100039203c820304c8014115804080441c604540038102c10100540880d02e85200340c181030801041030102583c06031903800c04110082e0502000b15a20002a83e0078800d102d03010800c8501494445d241010a500501070300c0c0740c0c4d0800d20b02c2071030040d00060500004000c0000000d05052140c03420200c115400741c0c40310022401d8609105050000a00c0c00d440000c00d41c00c078503130b08074030084002081c56 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644580710 1250 644579460 644579473
    0x408101103010b04091e06080a05150c16080702030a0803041104050606160212060c03011a03010f03030f031407051c02070807020907091502010606030f150905060f0a1502 75
    0x40025140701c280940a5003d03802c01040c000301140d90050031000c0d40d400f00c41014010b4040d05041203a403170703030818592500140400800c0c81400c10100c0d15080e4802c6d4011070505042c50b0b4540603101d01c81c11750b0f540e410420140f506116030417013070307a120301d030058140c907415800c6140010b910741c01180d0482d036075488100303a801c09042c0b503c11136208010140809140112011541e1b0906603401001c80c1e011a030161034440d2aa400d0201c2c03400381c01040205601da5040204600c0b4606056141e10748100d418030041100440402e050801c90380c1504007540c007150200f404801420713032040c0e01c110050000080c0f000325603001c0000c01c4c4031031481c0142a1b064940c0e88100060b03102e544400307048140140100d070301503d00500a2500400103080c06000d0741d41c1c40d0b01c11018103102c5100100540d646040810115030076000300180013020b0041000f92425050091121b84628010328448580e100c0008519444030002481011001840c40c103a165480880402c030703040c429001c000602036030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644581960 1250 644580710 644580731
    0xe0d0b071e0c0f0201080c0f12040b2a030a06080303090a0302070f08070e0a0207020907050702040507030606080a0903021911030106060302030408031302010306171509030406090306021e040810 85
    0x290034000b001980b01e483d070807251020ba0011101010050246400c0030820010b0b920300001e9a00140625025441099100d2030181001000070f01c0c01088401040d5548501000440c08840201c5603000c1070941c0380d44a840c2c01042000070500c0f9000b8219510000050140c840c2001076030400b5036102e507085400c25070321009104121101d07845400c3c07040d444a101400104082e01210381e0003100214014141801e43c1c00040d4520700c1079401801003100020700d801035041c10301407260700860303034141440101e1610b60001c10810000342810000c9580d8540442058800e003c0e01024500194101c1044c0e84da13030a00a1082001c2001c01b40f0075071034400b000450600a00a41e40b1030368001d1000b03403c565400090401c40141603504904042e0b0f5100c02107a42802000100e051182c50801803850360010301800018081c064510250b640c01440204000740c0c1c420403420a580d4040e0002d62200f40a074244405a0101132260f01040d00c04900810355142c00121505c40242580060040740c010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644583210 1250 644581960 644581967
    0xc0c0909010c02030d0e030903030307091703030402010e040b0103090605070f030e0c010c0312270219050306061201090c03060c1403070e060a0c020406030c0501110313060e0d0b071e 80
    0x42d06000540c0041c810101510182d03800b14000a40040540e4a0490000c0000b030450b84101c03010303c042004600c0610240c031902c07200d001080c0301500118035604240d00085d04d401c0103911200d2145071074013000780c201e92083d0816003607030382c0c0301320244580d083c990f40207000007107010b0305140000c0c070701200d042186800041412006206850b04e25504605440c01c6402c001003c001e503071100d450310412400c0b00f20590b00044330301c0b801804a1000c0d8024410400d03807160701303404c62203107031800e90090050742c0d800318506400443c200d4000301f00307050904019001d0000500050081c0340125000010b0004603007048641c8103695642c5004500c014136034410038002901c0d0540000c840300015038290804200608201425040c030351400a260340c001426120740e504101d50b00513015a0802c06540c101c40c01c907034403a421401441c281085404000074140306071041c0c8041114007180c060072601c1d000703601d09145070455502c2c8100d2410079006003402000c440d406130707941040010a40880d12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644584460 1250 644583210 644583221
    0x6182003070509011505070c090c0e0105090a06030e0703140a03020105160f0f0314040516080312060f060702030d02010507090b12041b0b120901051b0f03070c080c0c090901 76
    0x800400707804181c0d09002c02c4d540310104c01483c403800c1c85402c200f044045040842174100904c0c042001040c2c512b80c0d0b04000b0101283d451100b41408428414151243da034451000b00341da1541c1390000d000a0304555032480c241440e030010b0031842c0c03d01200c42e806100030800107101802030b0005c0c8002e0b1070301c03403101c0c12448020300200c1c006020304c507405002603c540a0081010003900d17000c58181c400c1802c8010840003a030381100c5560041c600c14040c90f032404401d000401c042409503007010b103000f160303021001d4001c00c100d1290400c0b141090b0b2941d02c12040d14001ea8001e8101d80031643e1852000c0d00808040d101100801c44100c00003800c600780ca0100c64102051f002c002020b030311165189170070b100c040c9030011440340d002c103400308910104201510041e4003000c0340c583e0506100d42140d08460026001c3d51011068441c11003c09141c03030100d414150003141c590713581c0da81c2d07580100d4519601d80300041801324000b8000c5144440020700e002c140c802141d0b014015125141124200c80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644585710 1250 644584460 644584469
    0x601080618031e0a020607020105010b22032a091a040c090b0d06180e280b040b0105130b03100e0a050d02011b0509090606070618200307 60
    0x1030045000030700d1822140340c00307108101040100d9007003451510041c1c2c030402440c0880d010518020444a4445904100158000006000820403541000240034441c896901405110403c8e11056200c640d4441c0c2010b00950300003c0c40c09402d60759901d03070780c0b4940d010700111180c2c84d0103510104462003144101690001240b07005074010341580284405840c0304000c2405101a4450004400c07000c0c0008004520540000103034950924050408400000c0200511240760110204010000141c1c3c4405d00e42160107440b28500300c504031044a080c41400188004550380038041009480c40c1a0350580f071003100e0000300303544449040300c01c031a00c100c2d0140c0d01d5440010710802c002c42b45d074800a04083c0e100155503002d501070301e625140030380e03240411006039941e011f900920120003242c0510071040d80ba0180c9071401601c00518180d81c0a0400f910541c4001601020803e281d407041d865803480c80782d0b9440b020501e0030054407024984101020100c0d5258510002e880d01081c0b00081e40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644586960 1250 644585710 644585713
    0x4031101151a0c1c02010c110d08221101080106030207020a18200a022e0203330a05061c02091507062a0f03050405030f0a031a03060108 60
    0x340d2400300c840342d2a141803804000c40220402c030044a450040c8840c44421810105659440c015054001e00311805610f48030304206068902c0411800d0200301503443e0342052402e80310640b21801c000303111507007280c02004001c2040280b5010001d070110808802c01090302c422040340c0c0e0390003040d4103034440c0c200029406100720005000c8070031100d0038244c0030b075007550001884914102c1039090a019800c000c1c1004000420017410302c42d410880d560004d007405040c00e90042c2a00200c2c0200c10410300d040494a401100044039904007401d801d0842d040204005411010b407e0280800b028917000d1502402865001081a0501d0303001c03251210703014649104080f40ca848010001e41141880300c2e0700010b95200214090170850107440d1842c00ba85000518030380c0100c150b10803c2e44450030b450039943c0544640d00c5280c100e0b011810098aa0802050070342c0d9500c0c0481c107610800000088484020031101c1002d949540708980c070300c03004188070780d44010726020150340b10024450082203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644588210 1250 644586960 644587001
    0x106080604244511040c030e06040b060d0c06120b010503060105040506070807080708040f080105070c060510080102040b0d0b0a0506160c080102031306180b01050d020a09110304031101 81
    0x500b010081c452004080d21000c088080e01450140030f500c45441e40c00d0341c856405401d40c44040c602441140c00407903240c102081040d045071400ca45681006001a10442c400400a540390300d5001649294590010302c000b0110303101d12004c2d204441501444600d20319080080d00c0550084080380d0154005844040c205484d0404000003544043c3e000c964161081c442480054000406002654410200039450b5401d082100c90450150780c0310801984c140001e1140080d0402a0800b459812020100d025078650f01c1004904105612114056100150002d00d0035055805006000340c2d142080c0301e5074003400204514100c09000f5580d10610070002c902c01a14502c00e01b889203071140c040c24100991300c024035422a003040b00e120742c111407980800801c21a241c81001911041099601002c0100b900c80c20b400c400140545402030981d0030b030580540d500e45183c90002d0020510a1100700700460548142d5001910300303c01141d090781c50446001c1c0180903030b80c01c060041a80000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644589460 1250 644588210 644588261
    0x1c02090c1926010333320c030402040506010509150405120703050d0e130c0e090601260a09051902010f020601290903013b060a0b03010608060424 64
    0x160000800b04000314040d40101d030200081050107030b003100000c404206d1b0960114040c0d07040c2e5500001c2007401550b0341c14010800c400040d00e050f03d4209406490001d1107650386001a1041d00c070f4960b01c00d9004002103040301c48425004001c00c00d8581c180e5030440882503168403035544520500000700349400420b0400780d4a40301e000120010400100041102138424070f200d41103034206800080003460400518900e8200000c4680e000f0070207180500204500e0354041c202c118442510b50502803c10300840c40c5104282c006000041c4c2000940740140c2c007003900c0b886040741d0810101d0100d202000d091180c01d00220b040c0d4100c82c0c6c9032040343d00134140c5200c01c2c0c6040300341118070440120700b4030001800382c80c00d200c2c01201c50081c000d40c10510341ca0415928020102408480510001401803900b4000200340503400280142003c9000d01401000a0160646400c2000c0a101e02c070100406e1011030000c00c0101143c0146162008220801c0c900503a0b600500f0b681d00c1502c07045074660f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644590710 1250 644589460 644589503
    0x1803060f092413030c02120105010303091202031905010b0a08031804050f0a0509070e0106030b0a1a040303031a06030c120703020a170402032a0109051c02090c19260103 74
    0x1440c070740300c0c0c0340100c02410703558001204040c070b071f8041030764981d5988010300070150001b4035440030b40300d60b0202a00710b10182d030002e0390b192071400b900c2101e02c0d0020b00490030020250041c0f48189001001ca00001740c4414080d079580d00300082c403151603046083c0c0c82d0014200b51143d05d001e01410400c10b03103e560750f4525a8003070500030f000c001c44d42c41400760000b400d0150540a0303018180703941d07010440b2600300c0704003d00a0004d400507080ca900e1312180740c000000010896084907418200421b540100c8540c07105801c0d0400d41d000c2c0c205800204100101d03144800419002e01411017000d582e0300c070310801f03c00300d00032200c0170400f103825451108010b240b000e040c04e80c4144000e0407070301302c0b08951391818500c0d4180e004900300603102c564100c04070740e04055204090202990300000e02c240c514040c0d803000b00e1540c4064000d00d0301e440400c0040c40f0120450b4000d0b0058003003040886d08911008142031208440c907410411685404020310740480c10450403a900030300f410f092640c0049000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644591960 1250 644590710 644590741
    0x1b1507080c030408150f0f060120012009030601090203011a0306040b041a0f040e03040e07090306050f182a0103140408040f061103030703021803060f0924 68
    0x8074400e22040c00000344040042211300ca0010614442480a091407000d5030b005500261544403941156020440a41d0f0b000b0400400550800600c85065140b800e60314010300d810144084030620726251071000440c1100245425142a0105c0340c080c4c0c0c0c0e50b04000101d000a014400c034601000021000703241c548400307183c1044004000060007100c403400034cc121620070310307810034901d88004007860070300d4200c2210355000e0058606001315007621011540b24880e9000741200003000c0804070342c243c0d00c0b80c10389c0c3c0701843c3d115400700302c0d80c1001200b40110382011209003c0585001e207c403200d03100c000c180c1c040000341d40d07011240b800d44560300501107085011341203410144d59445205542c403202e540035010301e02401641c0e03912800c0c1042c6c070031744108540003074091050400e06040ac0c0700e40042180c2c0c0c0000645030058840b0150411b9105001c00294619414422081404030402c0d03014140f43c045d049210403655132024501c02011081e030051042c60960105500041000c01e0b002c012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644593210 1250 644591960 644591977
    0x180c01030902130504060e060c0a051902070f0306060f06030e101a04090c1e0303080c030901090804060f021b03070605031807030b0414061303030e1c021b150708 71
    0x1141ea56180300e0f0031000881e0b2048409440583c2c944080011080e0280040c0d0b41143c080440305280c03400350303000501715108203200c03029140056086084020710074421903001e000c0841c0c0c0c00b808290b0701c0c189200500214021090120000380b00010f8039030180c41002c290504010103022004800032491004010204c0150101515040c803840d10b40c0d2a48a445100c2d0700c21555003c8460619284080703c16030000c08150080e00e0030028004260010f00c00c59106e442e44458541c0c9035540c5503000d025201400001389902800308010801940104014520000950031509941c038201ea85400e40c0f000c5d164142d80540189009108a0b84524000e65001610004090710b0400b100130030361807c0d80030790066a204110405010400c190700300d4911311860460000c0580b07090910740c144000c64030144c02402d2698486c0c010715207440c2441040364102003014648084102e000020b5112503903c00d11015000c8030603002005491300300d0070001000010005103041452955510b480307988040d50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644594460 1250 644593210 644593219
    0xe0c0a081821070b010e1005120a0f0303060303022a040209030708030c03070c0b0307020601093c0c0315090c140403080706050109051302090601110609010c0206180c01030902 77
    0x140ea80180150154a02c02c220040c8032281e41d400f0030f08104ca41d141040e04200e40b01300001080c404c20300e48150892065800c00c0f00da4441160070445050301d03262424034000c141c0e00040d0541d4040c03540560242c030849010750299200c01220f244075085091489118403203052203107200c1600c1c0c1c209035000d070111010260403500c202c0c0c0c803122107502e5a0088490174949900004804041000c60b5458200408020b054581542003059005e500c801c01409821900f07940c54071051884140500e10010f140607555010b6140d09a00d44414506a0340d00501c20714182004241c0d0440c501c203100c0d0010000d0002c20b05802e640c00c01c803002024100345c084407403c204c1724158680c0301201100c020402140700341c2d040d030340d5041c1500d443c01c01d4030f905130b016000300342c50201004041d021440c101a4010b80c101c0d5021066510340300169030314154091315480510030305040000f404030552099040303140355022200c2c2c1e0764440c09041e240f0843c07a00f480b0b003190414441c492281d4065001071801d00e10041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644595710 1250 644594460 644594473
    0x1031209080102070b012c0c07021f03060e07050a021203061f020109050115080a02040b152209050907060c0c15020a0b070302041d10080f03040e0c0a0818 68
    0x1e01450981e04021002d440c0012480010840120751144c000c8072590400e00920700c4805a4201400c0a400200301e41c1244400180c03041c215a40e600104100303164244859a009001e048020000d001c1e50040344181100a00400c3c101c5015a040d0380003480a80e00038410007140c4500b241480e00054a41a004001c04010103604154009032105032070b800c2d800040e0605803030901d113095a030100074000600512603000c4c00a0720002c100c140e03c081d01910040740c81c609030b40100e042417105800e0031400d0b180124800500c00c44e04003041600c11410398490803c142c40c0c001480071620107440c1c2248681c0030f18401c100142c05a00b58503d0035000d1079405c03064566810340b040c51030008400c244010303008504410200f203202c2c00c2854001410b4941141170509210a4105103c0d0111100d00c01304c000c1c41c006280410b110700f00102600c100b800f07540510030081c40040c2e99030003902a00c2e10402c4420005110744144001f5500c0749281692503800380d0300e420010031048031490311260b0f0303a0301410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644596960 1250 644595710 644595719
    0x50a2106021b06090c010c1106031b04062106060f080a0b0a0b0a020d0918020f090a0609293c0d0f0603120f0c0b011221020601031209 59
    0x4041c1040c480c2040103000d0304c3c0f820301c40716428400445042030500030b4120105020940d0501c800281000c180c0b240355894440c07044001841c0c96646138003080900001c1d01150712540118050350240700c1c442c1c1e2010400b201c0043d0020348130640112130009811002d90381010744100c083e290002c00146001034203014180c0862030b0142103405c03041d01d103680094040c6013070f070f07040003004030320440c07890440211070901031600302d0710141e001e4509090b0740214080c401451401308444000c0d03402070030811050394460001c1c201c0c6102d4890b45007040000d200f1078290f028480400e20140205a031802e02e031480701c10605160300d01c0c1c45420811322048c2c4040d01c2490f56401455151011144461501c0c0d03500740308041c09a8a6450704c14a0070343c28480c0c100001100d040713105040300700c241072a040a1149450840c1c10011412000e440c2c81d810000006e504140d068014004502503420303621104102840e0101011a929114005074040d00040000c00d544103110110f4070b1480c9050090301c0e80e034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644598210 1250 644596960 644596987
    0x6090e1302010504121a090d0c1b0819050706051201061b060e0a02100c0c0b03040503120408040303020c0a1809061b0806040b0f06190504091103090106050a210602 72
    0xa084040740e030301102c0c0141884a0100f00c10340d1f544601e81c04003c010390752080324010b000fa01075503801418650340c0e0424881c1c10002d42207480c0544032201c00c0350502c01c1501124074550102c0701c000d0b0340074043d0060100305540700341c00700c0750b001b01c4001624089034079101048480e81400c03980981c40960382c0100b00e000980b1800b41c002c0600e2020000c0c80310f5102401045000418810f40005201040054200150704108500100c440c80700000c0d46070340d51410441c1c118481c954151104080784010881009084006030064034041c0d0f08841800100000784401c07000d403030007990041a4404e8214114056036007016903420b20440d808110171400d410044200f500c1480c1c00408103801c0800c02c000c90a2501c681c41e00e8010841c1c00c0150607214201103840b5100b024405521140351600f500b9a09000f2402c440c004d10800804010721088a4200308054100707070b030310303240650a2100014140ca001d0500c10305070b038400804405031801d9626040b0ba0820321b102e003240d60940901110151500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644599460 1250 644598210 644598239
    0x3180914071407170a080a0501080a200a060c0b0c090f0d020312041d090109020114220e07110a0510020a0c020d050d02371e051606090e1302010504 65
    0x1c2c02076a03551100301030b45d4085c1800c0c4008008440251514004010000340080c01c5106035410468000280041c9108426519001c039280c0c1e4221002e10304c000345007544681c030100654007404c4488040d440711200b940303540c0705080c1c2d4180d009100e00c20500e12890030003d1864072500c020201d601003040b070700c0340003c1c1d13410503481700301e030241380f46800a40462062051a030000400008000b040c4056002074480401200400c0c1030300c0010503c0745001403016040e01030050004042d1580301d80e00e85600050300c100b2900350001429402c40b420045030300003842c0b40850741c0300c00030741440c24800d03070528025000302450100700003144030741e03d0150329084120082c1c079002d00701810007100703101e101910f08140d9420740d20359142101041e00f01110218145030130126a40542d00c00190301d030520314849803803100042c0c5d1452182c50510100f100c00120300300a95100129154503507039610040d02c1240d50f510500c10040300020008038407144204403502c0f401c0c030504202e42425180c0b64241d00040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644600710 1250 644599460 644599493
    0x12010207110f030a061b110a080a05031806010305160e0403020706030c12020f041a180f040f0e060921030a11070c080d02101e051b0703180914071407 66
    0x781b008283c042d855441481210b40042403002030054403001d54400d0301510070b0301510010010003001080040403105101e0b0b481c5c3c80c00760200c40c19940c403402c2c0541c49801c40c0448003e0b501582c0c0300000c000001c03150345840350b901500549046441c140b01a40900000506a000c003c0042c2070801a40c60f24406040c000b402c00c4202078030ba5080054a11041b00510b0305c03240200c400740190380c1c000e103a1205089880106581c0540210309a0000c41d02618501c006400002d08041e01c50381600c40c0000c1d81c41c03141e05010101c4110090445640c1507201c0380d06245910103200700001034001086410503110481c41e000c80900d40315094959028150380e0741c0111649400041c0000041c56041154100501140e441044040c460b00020000341285031042c03c1c0d40c58072800000d20581c1000d807a00c103400c0403031114960711005458000c010a035043e5002c4120003c401e400300e4040030b1071141441c2000b42204000c41610f89182c02c0c1c5407265561440040040c04114880000300740900070009003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644601960 1250 644600710 644600741
    0x72d021905210c07170d1b1509020910060203070807140d02030d2711010306090509011d0f03090118030c03080901020c01030e1f0e030a0e12010207110f030a06 70
    0x1d101e40e001c5a41441309661101540c0740440c900700e000e01001082c80c0c8041101810207903080d44041616180000d0682009000b10840c02914102c030b0802d60001124280f086070709a075195100111043e440c2004e01900006910a2005000280c081001080713843e000d410000e1189800301c0c1c20915010f950901a030040c0c00200d41d00c1007039225401085080c1d40030000344182441401d9540e50004000000901410309141d54940641d010f42d01880c05402009070600c458036100c801c0034081c0c1900c41185201040b07941d01d50f03110b190007003641804200500003a51924402100440f01940c1e80b804504244030000f60000c000303641d040000004510499a0544807550b14001a04082c428103e2505040c1080c2e00d520210a0200341c1d46400f400c11100c02d12000300d803c0d0514000d00c80100c5042d820300c8005400340e007064012240e091007040841d00010080c85801c0c02d1400c1c3e02403148001d080300c20030342d04900c5a1401c6142c03518107200103401c03618250902d843da0000e4605144c0c2c1d00402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644603210 1250 644601960 644601967
    0x903071a0a112e020c0d0207140405060a09050403050409050a09060501151e020304050a0927080307210f0c02060604020f041503060509072d02190521 66
    0x405030072044511038400b4480141840c207401881e08441c09840d189018205590055a05406003090f4182e400d000a440212040700b5107208019540748543d014220320a5590615000b1134a418042d85203d101c0c00f03085042c0940c6000404405044003410440901c0401c0c0f1022076481c61a104403482881d1944002c144450340781803000403520180c010b504c0000d6940c600a9105400010104100f40c4541d8074911841c0c00350001ca00310b002d5a0031050f07100c07000c00d800280c40304050700084c1c0d8241600d0900c060050030b220470b0780c0200ca04e1420040100105000081010307010300008000c41c803012400c040140301900405089400c509041301000781c0d90081c9000455041120b6039100009031011441c03c0ca414143c0782080c0114419104805150400044003d1080e00100000c0c20003800d84119801d01c0318001d044c8032070306181160f441804802c00700d01c2d207200c001e895035000402c1e00600415000f94070366419240800034140c50340e208230b048820002114150f00944044988100fa88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644604316 1106 644603210 644603227
    0x807030e0307060219030507020d05070302010b060f1306050913050405120f0a020105150108010902090a0302190503011b02060f0709030506010905090c031609020903071a 75
    0x80a000202c0ca0604200140c0c019124810035008507070f0b4004000c480807000c07240125081d4005a000001110ba50350244008001c082c3c0280f00100b600312186001c20003560000f1030084403240c002613090030890701540000d0281c400b40c541580340c04010380000f9540608500100880c0b942c0c0c5011400b00710742004840c180303144103510315440f000c860703003d5001900100c16580265081c84005034200c041c8801610002c98161140e07050750f401d03e002038009400281900360010054040031015a44802e0b145007822101c8411015440c100014182550311201d00000a140c0b4149440840e0760040362155128020315204520b6644a240485100b80c00340e101401500401002042003100350700210700c103040c1c4070104c42100380c4007001d0507619040300400c4076004911107810300c02a0926001841007079001412072f05020348030301069040b5040b815451142c0040000d240e01c = true := by decide +kernel

theorem cover : BRFrame.Cov 644424460 644604316 := by
  have h0 := BRFrame.cov_init 644424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644424460 ≤ n) (h2 : n < 644604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
