-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1809
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:45:27.424603+00:00
-- url     : https://prove2.me/submissions/d375083a-537e-4d34-b24f-a1dc717d9e31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325179856 ≤ n < 325359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325181106 1250 325179856 325179901
    0x9090209030114040f0b01060f0806041d101a031c0e010c0b091f05090c0105030703061d0a06080a0305120414010212061002011a0d1b09061a030708 65
    0x240d52800300c03540c0003080d07821300880c0151000604101d8a0a0180c601ea42c1a0311003000c0041985e04118032507400366050703400190071540892903080b12001d819540c42020401c01e12801007150f014509c11039a4800c110030340100c02da080300180c034a000c054640c0c41c04644c2884420160081c1d80c00c082c850102d0015400050405000b0109d507a01ca084074004111206e80c0d0f10361040500e030300805490000c1d081580c60802040c0304919204064640714800703107500d00e0500ca0080003007000070380a40c02080184c9452184d00c02c007400580a2a0b00c00707001551803202c6140740040c0400c14810202d8800b102c0c1da0581c481c40e10b40604c00310741c0454800010300542d00c0141420f0440c003000020b00042c00c5c3c01100020043e160304000041015070445070078410b0545e850301201e070030900006036500840c21000c40740c0c072024021500704811080071521068101c00741f200130115088c0925441032040d078030350405044a0101000e01034400c0d11096a900c2c0125049800081c0c4840c3c0c0d07170b209070f4070340300300b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325182356 1250 325181106 325181111
    0x6180203120406200115030b1021030f020c0607060209040c030b060712030605100c02100905030d080c0912030c3304060f020a032307051917131a0106090902090301 72
    0x41000e582c1e62800007c0d0000c03201e003e001c03000c2c040000310300580080504920060006004c6000d0300000241c06c0282d4010107110000891240307150082c0001c032502c0d4006089203540308041c1c90003000950040034024400ca01d403608070010381307100740320300c640d8024041e18442c40d258940e20703652100c80349424003208058803104040740d42c1d00d503401c8081c160183c82d21050b008404910401203c0c0e40c9505002042201990341048140e070006681e4a2003201410002020f07103490944000c04d20400d403046810551803005401213960000060881e0b80b40d030003d4a000c54142114101c240d4074820039070400304040300124031351442c0001d0b00c9400034400c03980010705098046008090f0f8100c4100200232a50724010300c001c01b5030750f10070207824071308040d200c8049203000c00d400381440c0105000295610f010b80d5025500038011200150944c880703080703070307907003032401a1946800340d015290441301084480580c0e803489130184059416145503443c0d0f950103038140480c07203009408c1350100950564 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325183606 1250 325182356 325182371
    0x80f0f01020c0303131506090b040b04090201080a021608030907150801180203070e0a030803060a12081905072f060a0c0b0709030609110f06040e04020108060a03061802031204062001 80
    0x603562084100230701d60401c0c08144642100c0820007204d02d80540e5502441c200491000180e0b8040c0402da07011502c0100181c8442204921058000390030200178480c2c0400000c1c0201442d00148600459440c00f100340e0400d4521a400c13100481e0070b20403080440042241c254ac4259a9005554058254039282c2420070003140001c01000580d44144c803641c8001040c09047e0509000b920007174844100035000c0d00c1141d0751801c00e47d106094070798598015520031a408e140c81401100c440e581c0051502911b170414000120900c1d126240d2141c64240d0603d888425080c814151582050f00ea01c50805a42a58655181010004281904100070200c011000410a1145849590103401c52030041c8000c00e0500035400aaa081248240d00900080100f00f04480c00240d0080d4286443c05598454002007070000c5c05640009154a003401d00850001c40b0b52111004004e00880c01c03140c140c1c203559118011031250303000301d4002034404d1800f080d00380e940304905003141c07414400004030103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325184856 1250 325183606 325183643
    0x409080d0920040c05031515070b0609011202181f06110606010c0503031302040209060d0506031203100506031302181b0301060f0e010c02040501080f0f01020c030313 73
    0x481212108840c0146007907038081150012250305031040b0b800b0340c0e00700028411614050101d000040003400000f9900e401c0030a2911040c880c00b4983c51508400c5031640110b02d490785807203d04460300c40c0111004070001500e1640171100c0348400e03030090420b90240d201c040840c090450007d2040083e8035003504606998a108440d0500030085562900c4042082130516070a0860107099a4100495030303401c1000315601108403034000001641c0704540320000c1c80410064066100d80c16807188000c00c1080b203000454229500c81c28089080c2c80c40590b800664070114041561005281901c0c08401e0040d414540d00664100c900181d0000741e001b260340c0081d41920711040042d078003008050500c03c0d4134214010100c001001801d2960466040060041c40741940703100c0d02007000303460070710b08201d41d01840000c50116005801804a90303143c0034101c0d40c50b048803050399801c8c800c0500a000b86070040c801c1e140e54401e4030000d1841c6864205003903452203460b207000e5a80401c54204202030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325186106 1250 325184856 325184861
    0x403030608071203090806060a180b13050106020c18060d020f0a06050901080a0204060203160809040e25080c011112030f040213090222021b0307050127020409080d 72
    0x620f10756030010364455031807800070415291640b010895034404804e1000c0b5544101034401600c124180000f6000400055003001d4040184801d820016511850f07644400d1070308118180e4070306408882e40d0312040c0061018170070140490391810780ca0100841c41c245041d8508440d8180010900301540b824075000500d68202d65008501142000a00100551b0024840e550100661104504062611b24043e450f846200300d050b0594801040c140c04120a20060350062000a40f081143d0000b1002040c0d03602d640000c1100362422600440840c0c6254070740c64020b403131540c005041028140401900c201b410072000140318007030380c20041680250360010390301c0b0740c4900401d46260308050041c045401481c0b02401c800300e04180920300540ca585900030200042c2620142d200c01c4c6644803031000740201e0f800e0744501000b103100b8a8001c0320000c05084402d000318000c00045c0c0c401803800082c580c0d400000c201c0886401401000f51904da44048800c500460302c2c5450304820700201001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325187356 1250 325186106 325186109
    0x709031101230a03110a091401140d09110a0503070905070323070e0103052403010f06080309180601091403010b0901060f11060106020307020f12030313120c020612040303060807 78
    0x70328900100f14038140c03030b505004103410b0004241c1d00f00c0ca0324106503c0180210614020000e081000a4900b1440c0c3d108407440785600003998180c2e0303254400c602100000d44000c000a0b15840c0c250103401c0c10034038100119608591000740100385482c82e00802002900b8002c1500d0140b554640b00000003844980c0682c0048401c200009801d02d000341e001741844420390840c60406242804010240c0c00740b1500031014040f4540702c03a241105c1d100002e024100501c81d034440141403120000394480b001020b040c00c078008546041400017060303512100e03420308039900390010f0b072103407820050012020310b4203600a4000c2c0000c5a00100c2074040341e0000c0c1d007a4044400540d01c481c801c0d00480c0c0c004c1e0101c110111a070040c005135450f200000707603280910480a80300e441641c150f00300d5035480c0c40c80c044c040202c800a070380d22860701003800040641c1158080d0380200c1021840780300343d445501c0b40405507900510749402d107214414200d54102006008806041d0366907400303ea4417104008210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325188606 1250 325187356 325187417
    0x2030703061d010c030c05030103140f1605040f0e070b03040602040b0f03070305061206071103040e0711070f03020a060c02030c030f06061c050709020a1e090501090e0709031101 78
    0x15400408042d22421108000ca040007018549810600030381d034040d00b1681140e030080894903044c65013000903410700002c800000c42d6445010300390414003104c42900d80481c0e60464040209042d003120b032400b030700c201c800d40081c42c1d04800818030402010740050f60f000742c02048010704180c0c544411402a5200514604d400314000c8100007015031305020302035110f0000d4030510314074104031001c61303510703140500034100b80040000340740c414020130000d4034000d0030b500400c45000d003002040540b8038904401a41d00038040c0700720225120303205110b540110b945c0039080030b10040c0b034020200c0701c2c840301003c01c9078140919000c280f0190390030400c440b0314880c0c0d200a0041c43c10140200b010702c0c405021310600d0340603103038020404500e0100e950422038240c054096540c0c0000082203072001382d40008540144010a803105506500428100c284c807030a072100a03200303840e40d001c1c0031f66034001c5611000140c203031002070000800001060081c030f84181440007030044031101d41e1070070725a40c24041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325189856 1250 325188606 325188641
    0x316140a021501091e05061306090c080906010b032409040302010f0e0a020f0f01180f0503010f0614150c030406030e06060a030218090a080301060f14030601090e040203070306 77
    0x1030982d40300c56a0110b0040045070700400459018541c030f49000d1006000002400f41d50fa40014426101c1c0c402c0e000e91824515810801143c0b42d2400070700802c41200c030400000c11440000f15010800501c1a040e110601400b5046640e0300c000030301c0d40c044240c4801c0c40382c03214121401d4a91540002c2c24000c40c800c0c0c0001c92807030350100e0b002d01124000301800d40030340e10209440c000b41e00e510b0380800c40d2010540d090680e0205840041e00c03414412221103044204c1c004001460314942140802a108200c0003800703602407002040c4142c2d841ca000380a10741880040d00c8070f891401890000c4529900e45005003490708040f80703039045410552200001c41c1c0c541002c4454600c00b07021165000700200c030740f9400e10f070070341e0007140301862009442c42c0f03d0308000c1c021070207180c0100405841c181d4051440707503496071030308401031000c410408030b0b8001c25941050102c0900a03502904d10484c0b06a584101891401c3e881e0350348680041c00c180d2701801040350100108800d40600160390074010b00300d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325191106 1250 325189856 325189873
    0xb0306010201050a060609060e0a122f150901092103020f03030403140d0e0703030c06180b0601140c070305011b02070e04140c03060a051501050f0316140a02 69
    0x7900b50340008002d00506458000c00707121454100903070b001900c6161401c04800c000311004200d03044500d070400785000c018081c01c8020003060b0b116046410b2035003110141019038481c03000295041003a82c591740060740d0400102c0d4840e02c1000303080d40460515201444517034480031000345140a0400175800e816044590b002d02da0100103292030100b4040c0194610b2409403801404250103507040200b504c07001a0000d003130449904a0034250011000fa5040d203580c919000d80040f1540a00300d03169800c1480d41c0600a1955551055898205210104541c1da000c011604404992903030490328809001c0c95032094010001c0700082c1d03105500005800820203640d0f14403001ea54210011980301082c280515110035107070300d0700f25910603810320500c640e60282906020b01c81082d5a0140709060800c0f40880e080c0d003201e40221141341c030711100c0201c480d004440c5803040203044070051a040000c01d2803800310b001c201140b00302504d0440f000e00d1080303010b0f000650149e100c1c1001030b44182038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325192356 1250 325191106 325191109
    0x612070e030727050606130f241202130807030803072010021c1821020604140f030c01020a02100b010f0f180902131203020a1209050405010b0306 64
    0x9207070240043c070b01924800a44040342c1004010002e180d03c4201c4c2c1c40f60302217a40d0391290425544101420307582c118113280c86001e41003080c4404d1080c3c440c4510320001440c003241c240c3c00410180340c01076492954191003195441c020754042030000300020b070071203070000d003070700052080341b0207580301c0e2040b9a540d081c40d5030020030680d0404400c001d42d003aa580590100c200c000307290103640c2c02450b80940c9aa06000742d800302000c4004040300d200b400e00482c1c040213405841ca81c0c0f15188240702ca0780510b02c002000c180100c0c3c3c0108a10b0150f800000420040f03401e62214040e080100422a8100403270030844a0441d0040644455582e401260381c02d800c50301030041d40c40c0785a51a400300009030125000070510405189010244115110280c1c0e0f914802c03116580c3d030281140554206540d0380f00060001e41c862090903490700007100d03010030b0001c00109160071064040d4001c1c0900301e00c0d0780740d50040640804000c001d100070940006050745550142038024507000074644e440b86410030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325193606 1250 325192356 325192363
    0x90c080a0b03060f0f040c0e0711070803130e1f06110d0e0604030b04050115120308061c02100203160b0103060c11100b1c0b060a060504030b040f020612070e03 70
    0x75000c070b1282e0021801c20540034100541c03554030842c40010054681c03154140f46c80032505a8001a5080014604218076a0780140c146601800c2c00030840f0912592104955164003540035510342000d0001c400304520b05030106542c0d082101241d880f02844100c000c030142408280c0e2240700890310800241e049140c05101c000c500f00510306011440881000000d925407007075010084c9210400800300d814400d096220704908844d410360300e29043d0301c4141c1c0100702c0300c40400440000d160140022081c2c10b00c00e0310103d6a003d60000c404400d1115400c0181c0090800801021448140040200c0c5001c0d05402c966090158501909550642c240305042c1d90903004440180800c80300f855410f40700000f00a03d80141d0300310006490900c0c40000344190b540d09403540030041c1da090f104014440e12003100b80c003501d402c079482c001550761494141d656018034440a089604500d0010300860403128038040540c2c401000c1e9450200b9102c510313402c285050340e44500103081c0401038412410101b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325194856 1250 325193606 325193621
    0x50a050f010e07080a0504050322050a060201200714010c0e04060905060306161809021305010206010308120703060302091e06120613031403280b101404090c080a 71
    0xb02900107651616560180001c040580380c10525569180040d06000090040c0d581c0302d00039001c44007070794000c040c2001c04131403a80580da2094600140001e17807140148940d82c4003400c00b59040c850f121408140031005c0d000b40c1c00c01e030303070380c0302031007404204141d0030b1240c54540c03505902c44d91400c2e545001403108075079817600710004691411060140720b960018503158481e0b030042c0200e201c075003c15401c0f00c000c89801404000703200010300220386403170960080c144441c10007070407800c40c0f0354840049036189804e100280030004200841e5040f9040300d1401030780040389080c04510156a03501040c01050704031208114003943c2c003541c4a0420820f150190004001c070b842400690710104843e840345d4015106c000a9101c41c1c50100401d4003070b00800040603000f041850f280e24202000369007040f260549a804042210105190078030315104c0da44910740c024252582c0d010352040166940d03210b0003000012070b01e05000c00108010749008810260549540c0c03507505040c920700752000d480a9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325196106 1250 325194856 325194869
    0x7060305070915020c1e030307030806030f07123201020a09050303030c1602120d0c03081308221509060933030906020301260a150c12050a050f01 64
    0x3c2064180382590000b80400e40aa04030341489140956540544a601d000c00100750140408a080c00905402444403882aa0190196002c41140c103456a0320342009014040010075a004d03000007007600f8100c2d03074074001306820031800d1840d079152a000d42050207070b20094040c0e400240303000015901088200013804190019030031030900360b400101c0d0340107614034001c82186105204055540f04cbc002104006401420b4540d20654903000400480c42254281d012a0b68203001c105034040c4000d10b00e0b016074100e8040c9052400082a402808444000d000400c40c80c1c03c1012800440c0480320342030035611a01da0078252468920082c00105095100201d21951008081100000e018040c40442003020075148444a80350041d0001c01e44c84901a04080c4040b001113179000c0042c0c2c54490070340141421000007284105183d9441101c400c00410080c0508003c1014943e1504520f010344004e08108400d0b884e8102070100301c0ea011101800c01a0301c0344148202044c4801c07905014101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325197356 1250 325196106 325196129
    0x20c07030c150806060901050a140a081b04030b1527160504030c030803040f1e0201090801151502150a0605010306050d051b131b030b06070c0b0307020f070603050709 73
    0x7007071300000c0c9803401800081414420000b032601e0300148524001c04114031280c289075250940003c0081981c40c2c22660320601101b071148001c804001d0b1410754040701c0d4803456603c03140c0e440032001d0391940307900c001d0250400100d003820103404152100e0004126290700f4407400d0352916003841e014800384040104140101048248040b5500c2807543c02503c0d00506899665102c500d08906980100751020303007840b440351400320b040d41185500c0b40d03609000740e030352110194071054040d080b02c1110a6108211420b501e003004450b180070000c1d00d040340d80d40142d415044808070340d5420628219240703c003c5988075001e00c130541e0148204406840180c410001008031551006c0d524803a030042c0c1101210340780c1d00303140555205181d600089040b90018044a811901407110000681d803030308001c2410811089040e013006030035210700c0390f085035034000c04c00e00e00500c0c442e40b68809442d6000718007400325a64240700081000308020005a580041c492525136030081100c4281c3c0c1214170b4040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325198606 1250 325197356 325197361
    0x9061002070b031b0c031c060605120406020c1002030a06140a1e0b1603020607051c0b061306020d090501140d020a0309061b03050901020708030f0703020c07030c1508 73
    0xa6000440c40191001d00b14203554946840d0182d0001c0c5000c3c401028a01d5070004482d056498048003130040204005d5850015500307024071032003690750318041c0400161007406143d5810201c1d001140d0018025400181360140c140b04003410180841074080b0103075000002d00070700354414880c1d81d009240b4a2204003070b0303241080c006080c0a0407442804002c1a1140ea08049509210b43d950020a10140200c0e518000c000328003640e0004503009802602a000000303544e140950122130b0b454070b2801d030a4014502c0c0c807070140d008044440186420883c01d00c501c55907510020100b00c003500241c0c004103000304034030308000c01c2d0344080c1e044070341080130281860211900345029a02c010300c00071009a154910b03050201c0050a0414015150605011030008120002444035051007001d940c01d000c255990510142070344140440180240420000501150609031020390840c0c003600c0d0262412850340300359454260b036600190742c1007110802c2003203080200c03600d2240200c2141004001072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325199856 1250 325198606 325198639
    0x5030d0e0913051c0e06041701050609040c09020717030c03040b090a0308061507150203010503071a03010e1905040812060d0203120c0115080c0a081504080d06030807050c0906 77
    0x6104d50504120000d00313801c00e420190b401010b4400c1c425801a00147d111592425040c030343d50b80c817850382031255281902141e15401c08805680c45950480d5040c60700d245062100b41c02584020303815540b400c408000650020001401940500d4580b1900c90700c90519041c0840140c00c090880f41080c0d0010101c940040e803c2941284e02840440d06020400700d44036848040e4841c03903500600340c2c00c80b2140300461100300c0d0701440c1a5541642198407aa0319110480ea43e10003d280000381c2c40000e100410001e5101103c840d48908060303900d999243e00f40c040502910b030152001c03258004041a028180c1c94400f800035031150003120700c01440b88030364000c40e40b105400c1d02d002c441b00c0e03800501c9181500c400d400c0f20700c400d0700343e264143d4082e68406403d5203400d40b4418a0340b252000c001c000462040000341c0d41c40d600341c0c0700a080450384a47ea00d180300c2c3d1b880749030550003040d115500000450010f502030900507010300d011700b00802c4200108507098200506c82e51142d5030030540314030741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325201106 1250 325199856 325199863
    0x40506101b060b040207060501060810030206250203030c0a060f060e04020f040e162c070809012007020901050319150e07061106010617040210030605030d0e091305 72
    0x40024011030003802842402c141028000e4030100b50b03003050001074404200251644400d04803401941e80d80340740d842d9415604030012280c813020754444c00900c1a13640f0200c03080d007c000c0e40080c1055003a0b11102c203601107402c6401c03100401da440e410101c481001c0c01118000d21940082c0002e0410040381841d80e140074032a1b024002a002c0c10901012803443d44a903030120101c0c294100881d4444140d900710811034890b64041d01c0076044252001502101121641806030111030a070b610705661003090441c2e01c01c800500b03298440d0b40f201117583d0584410180d140c5844221000d1640d19201c6005208081c40180d1040e070081c0e0260840304422480d8180503800158012140c3e603002c4400c6500c000640024038001c42e075400f8682d07000607001d41000f0b030910b0041319034064801a030303a188001d80c0e2981c24003a51000501064001400614190301d075007554400c0ea00b000210907403118007092425048200d0740340440c050032400c4001d450f15006440d4061054500c0f045000d43c1682c0d40e584 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325202356 1250 325201106 325201127
    0x708010615081906090b0a080606010522030f030e041d0303010603020703170c0319050405120904090c0602010c1413031b08121809070f140405060c0c04050610 70
    0x204000c00000c190720f210600308201c0002072845080c0802600e400d6400001c001c0b00d01114810620050001114903010030b48901c102c205845050500110032080c1e500c20351b40c0214001c421405990120000d4866001d2a40d0540070303039141160004094140300440700e207a09212103402d09410711425610b000401c07039041d911185030140c1c6032181483c05035200300b600010302c590140315a04020300c84d40e11001440c4182602102141e82d500242c00c21021280d003981d02420710b0300600351035041024900010502d5001c045c0000543d120552140b800381540e927000320700183d4603010010700c020f0740308180c80310203542014540c0c41d250b562010003071016080e100081400c080c90600c07031280c01402c0c154400400d401c40651303401520070b0310345080d254801d20030142c00e540088206683e900f00a100d1314443c8002e519030955858451100b80c8034411034035805c0561480404c0082003540b03e047c050605d0041001c006c2200740010070070001078400052002d405070b694421100e0b60b81d076010640300b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325203606 1250 325202356 325202399
    0x3040606141c03120b131505010c050c040519050f070816020709050702010207080f030f0a060518060f120a02030d03051303030c120c1e020c010e01082505070507080106 74
    0x1c10050a0000d004c054002011225130046410001c074000c0c18082d01708000e0090041030b224603254840d401075900c800c5011028001c1c3d80000e4464074103040c240d20054101c86c031070401c1c1c1c2149448031082802d5134000c442101800280a0611250341d8004104c07a4015141c0c08000962490000300255075040910a10745031984800203d0351441c005e60480d07166031741140004d552818001d501c2d0075a51f009030b401e1a9054442030003c0d0004105120742003e940001b401144c10807011151100004800750503c1d42c040240c46c0b007203a080d030b20502c0751318440740300300090503d103c00c9004050070000851a50300034503051800b00107150742000c0c0e000d45c205902d800c0020307180809030000c446150f9003650090000d494a144c0c0e490203500012200303030b4030005103001e0b1205100340104989a4580c2200d072400324107110100c00e00d660181c010140d008041031001c01308032036102c00341c035203000017407000c0341c04070350001001c40901109100035005440710500901a11b031030180f000d502c4020000480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325204856 1250 325203606 325203617
    0x60e0303120c070c0b03070f1b020d06240e0a0905060c0f130b0d0c030b0307090b060d1109010801060201060e060105030405210c01060915030f08040b03040606141c03 73
    0x150810445800e031400315070001d102002454541d45c0c8403e02d030b803040c2d80e1030002c18030384002a05d140d4401d4000300030000790710011401341543c1d0350074443d001b049504203e03403203915101000b010159a004114103080c0c1c00586884503482c2110144005c00046c01d0040403506010141003c201c0010719103400056800e031460f680c0d98a400490814007440c4101c010a22981c40009802c01d01e0f24003504840c42e0b001c804001807032a4203c1034044030300c00500a44c01d074000c0c2c6020400c0c00c009a100da048020068030007031624801101c21021a9a4000c004803c074002146603c03a551744040740d64050065400200640341c00c104881c000220010410b5042150000000d400c01c5420300034074410740070401140c0110340706462850b40d82e800c0321020f500d4039032803da00003442035800c0c00341c070000c2c0ca603020998281b40c0c15038030b036050400640030060354481d0042200154100100340154460b41c0211800144e075030a010003182c0c8051241081d1b44a07000004441c0301d0041c0701c250b00b5070003980c1341c14035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325206106 1250 325204856 325204861
    0x8010510080c041a07140d0e0d05060a0c090e0f01061e0c02060a2c10170103080c0f070611011401061d03010608101b030903050d0b010507020d0813060e030312 70
    0x1200d24810000001d2140080c1040d070040101c1c001f1b440b144400351600c80d2400c5800d0201800101c40041c82c02070442e50120000c075081a0540d4440640b854042c034010b9405604da002c0041d0200e400d40d20f0021102070000100203046d40510000086140d0550170000001d200400600c401400640a0310804000075581c0c4981c1c050392041011128034590f5a042d410002804103200e201005414024092095124880c910900d00882c40c101c01c1050700540d82d080d6120b0114942080220401522411190210001d420400f490042880c0d940300c0940d8041c0003078242c00e40d1500030b07000500000680c0180301d1031760841300941d54200e4844019030702c3c44200c00001c0c090a515480107101c0c0c0552001c2d803181c0703c0c0a4201484002c1c0b00c002d50300005070080c0e0f04604560586c1c80203000070304240200b144a802582003003209100c145461820a0301b99000621002c85003030342100d180b040010540c10b09500d1072105001094281001c68490582c02e0220784c41c4d11906c0c1c3c0840100b09410300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325207356 1250 325206106 325206149
    0x2060c030c1c05060405090607090b070c0e1f060507030f1206170c041803140c100203010914060a030803060f041803200708070608070c0f0308010510080c04 69
    0x580751001c100c0214041c2220102d81c1403401480140d5a1a0145050070f0010307190030380000300d107405800e26540d190001850700b221030515401c03011040741d4000315500c001448420200341d86009219003100902d044001e08901e01c078800d1241c2c45841801400c1c40350307001083c0c00000150b1030b55480d003040c900140407458018010038040d0080308240b24010300d92002d8450000342604600700640381042400c40300c8205141542e18400000c1c0081d010201103c1c149110724080c084a044800841d81e4401d940c031000130130307071700240c100b04071540e035403803000302d4004901a40c160440c10503070b0460046801d40e01e078203500b031000600090095143c0c0340c3d610311a03252a8400c420801203400b46240300d40c580c3c40c0c01450741048c900c09603180388203400441000800803401408031000c45005011844c41d059080d9181000142444284400201890045030741010000d1005110b540c400405604004c01c214081c074900c0b030b0308002c1000580c00c1045110b00403040b20291004014140c445072003111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325208606 1250 325207356 325207381
    0x150b03071115060f0405010503060c070c03060e0a03140a0c020402090a1a03010f0803040e06040b040b0315040303050702030903152a1c050f060103090819090e07030c02060c03 77
    0x40445103284600300305000c604426604440c05100c0844030072000141c551300300016140203000300f13039040d013000c03021440084072140203101e000e2007141d1000b04141d03030351140c50458a28039000302c0a0b400500d2007104260340401c40c90400201440490f080c1000070400034002e050346240240100d0f80015182480e5580740c01d90b4000344400e0f24440a4440e64800420031504207100b4800c10003480f550120760302d4004010303142520001ca4601090350307a524204001b605040040340d800c1581c03407400e070070a51014400c101c191010103a2840b0340d41000e2800400b00c82c07004000d00d0840d0000c0c003090003e0b9501144011103036510140c3c0950685411f940c2014a9801c840a0721891482e100e02c222084000000741801401c003030b1001d000016980500c10544d501160300245001801d0700103100796001c0d60001e0115800340f00c0306801c010b01441018603400701c8280c1c805c007043c0804400c204101e0b00011032648412a0301d0180403d24642d0400b942c1eaa1000d007400c4c4202101000040c404160300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325209856 1250 325208606 325208627
    0x50a02010e06131211090f0430030c0917150a1b0c0c091a091915140a0605120c0d0624080609071119030e030d0201150b0307 55
    0x1030509001c20382d40d0300a20551102c10101c100c1e450311103a60149401c1c9031607990719221f800e54001401e81d07039450366254113180008125154290424041c441e640311087e844840303291001e610300250724030484001a1241c4165480801016150720840e80f940d04003080180381124030005400f015107030300c041039001c0d10103c4c10056010303c2251030b2111459001601003901c5016140c82c544080d00d600320700c010345840340b203034084017950782c0207141103410440e5601c0d078444001402c4a00541d0220b50f6402940c074150f101c1c24011461450034824111996502c030100501201c00c00445071518001900342e00480c00e074004620a032500044040002c2400c0b5402c3c14048802040744540344c1200f080306080304402803445130440d540990040c0e0060118601070040106030701416503400b41c0449400e1000c080c0710740c581c000c0598500c0030032a03401e48100d080c1d111b515a0403481c5413090502d442d000f521f01940301103a0400a045660f001c1240d15201510720300c0150300c0d0b5940e661401503425421700c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325211106 1250 325209856 325209877
    0x3020a02090916140901060e040902030703150b01051c0504240207030e030c0a051302040b04080f010506010503221403030406140c04051c030306051c031803050a02010e06 75
    0x264104405004082040364080c005038038441c800340d80301c4c012641e80003441c09040307800c9804000107105060041d842c01548443c0100b0101d5015001e5000c02e040c000380d640201c440010141001d00483c5141c000d10746901001e18202e820070f0810741034103041c2c5842c0405041e006a4a001041c10f0200c48802c00d50070341090305041d40d40c1c140800110000b0b42c007e420950000d62001e071801c3c80740c600858003d6603028000d040e042081d05080412a18101c0c1d0100354049a9003040700145422102002d40018032008c400307401e20000c42113003e4207550b4001c001904000e001c104122105101000c3c502d800000c0c0038500c03844081502d402d0680301140c21107400c2c00c0c84080304210401c9110341184c0d0100158003961021915102208200c5006034020079620161400918110450040d1580c4045000e450301241040c2d481021400840911000d1a081d6a020010005044c1c12a040c0000e05c0c0e041e02000124510f141c0301c50f600d601030464000d0400901c1e060310b21195541005079100e4001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325212356 1250 325211106 325211119
    0x70b090f0a1a13030206060907090f03050c0411091f050d02070b06010f020304050d0803060f040908030106080c0304020d06021b010c110606030111040e07032009040f110a030903020a02 81
    0xd08208801510100c1202c55040755000002d0070000f103d00e0300000594140c000b8000c0e500c5450401c4007110009203074070100031240710009011100500c034107000354028005032400a04000034401611010310b003544140d0002c011a0345a4ac0720101c10000072a407424000711801c0330400100c0d4144942144414214004501c92060000c01840c05000b180c090301c80c0211400e1000c0f050762240160b1213116840030559a6010202c0c00090080d40d0090740207009040400c4d02c000068211051074a0603145100044014003d40da08032140640003d0000402c0c0d0452600d175002404a4194080040a55802241c13400c07000d0002c0700010b0002100100900c02100066002844404440c507051901e10030074010420703034201031045a007101803244c002c074079290620741008114000500300008140d5140a0b1a550903a1b10360000e62030320158002543c1c1c0d208074070030482500d00201e940101c89140c04240001c101242007168803540e020b09000c10700c1c0b035042c01c0680c00c2c0780740c07840c005cbd41058 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325213606 1250 325212356 325212373
    0x6070f0c0302100504051002011116140a050109150b0303040b0f070f050c131103150a090c0930020103150503010518150702070e0402130e01060503120f070b090f 71
    0x140c1103c080d00c00d03150107950301c484039009030008a00b070f2100c40e404102c100908000d20365900039001036412aa501504cc2000a254444203042c0741219040003911565035480c0b501040005802c02d41d00d08905129040c03082003028000291684168817556011100c00185e80390710301c4801041d03642258002c8946103101c20641441605c80403040e02c0c552041481855403403c024651240c03190741032040e0390450a5035160310341498039a07600c204896101107000303000a2086118060f070b5451b0b111039507034a006507141203045501e2406d020f142c0382009070f40300365034401c00281807d0b801c00700d0380918000c40c12000300c7c644100c400c1e40c141c01c4150076500740002c02c885e03c18100c84e14541c600b044002c84001910040740300c0b00b8ac04c0300381c82103401a00f0243c02000300802c11442180c100340014545031042c0e04a8202c20104d80540e001d224490751602d42c00c001924051084c166005881d002451800482031080c840c2803182c9030b40100007003424804607030040410425401d4402189080300c2c3d4a5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325214856 1250 325213606 325213639
    0xd0909151715061c02130603050d020c0f060a020a11120d090e010506090d0f17030106080f01050613120c17031e0405180603160f0905100506070f0c0302 67
    0x72140c01026a98103507039072000c42c61030b051020740f00c1c50780020044544e0600c80240d080128901410100d04525601c401010010071010300804100426580040681040004c1448a2219402c181c54858002401902c0c40d985c1c0100e00018269840040300102862080000c0c00940b0583c3d84000a846011000105107801c044448180c68103140c5004031680d85070100500c511925540641280f400380c03d40000410540201102c1031003011138114030060207085000700c0d0026800078002031404003c1c0310b411100e4a0506000d04004d071416803500800c4850399801d40320728440e44040d0b1440300d1122051020070030100014240306945007a1109641000d6641e0350440b140e4149003a1100d41c40e0020700102908480841d00054412400c802000c0816012134900428031038050003010041c1c01c0a1800c035814401600002ca25584064103040e08032003217038801000403d80b12516a820711a66840c1001e5800103540130756002004205846d054036000030301c1d80021f400110040700c00c0c0e0385 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325216106 1250 325214856 325214863
    0x305120c011a030a0308091f0507030e0111031506070506010e061903020108160e1f020d02010203040b040b0c0408030f071505060d02040e12120708090d09091517 71
    0x8405100000380089015440703030203011103160350b41643c15484400080002400740107040e5106400b8400d45001c0d0700007404050182c00c1225442c18481e59442c10030412540503c211010581440003c1281c222918000101840064041c0c066050301155641e2295692000c5840c12607004e4142c80c850350392440f001c5541d42c0144c1c0c2c0c95201c0c8552210002c1031464014403401201e40507518a001c646a00c51054000c01e40d55034000200320518100010700e0710f441c503030611000864045c0039844415a0802800d000c1030681c01411a4010014031001c1040d410000390020780102c2108190344131a00f24100512459211100fa8003022540555070858030010744041c7c4e001d01244030301003007510001c004407282114030643c85001440d5202c00f40c10150300c103c4001c9442c00c21140b122040420702d1400d40c1000c1c48140340c00c40c46504100440307034441c2651350040d400700c00610389030304c0000001d081c50706280135103540644d80d65040004082c2402400000300600114000858101c41c445900d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325217356 1250 325216106 325216117
    0x1002130503061f0b0307050d0c0e040513320d020601062010090507050402120a0b0f030304090b0102011404050a0201090e0705160204060b04121505010302090a02090a030512 76
    0x201c1d015950004079881d445089a40c0c04116200c03e51000c0c070b007085a0146a40c10140068042101c248040c2c03032084c100344140791030f00d462a200e99071590a860108010760307600800d0414840e040100a40004449521801e980a008050341c40303115212030355948800605031140c5981d204142c4620b844a801144443c149ca40941c1c50300742800640540200445400c41d004115502c62280a9a481595400061000d201d241039442c2182d9136400581641c000c4d0100071920342842050204070030703140c411141103400c141c3d4a9000a201000080d8582c01540300e918500f41d1220084407507a0f00c02c2d4460401e10032807102c019007604203410881d940e18140c0c0000ca0100c1c0d066500825510701c402c02d90351058031203541c0c41c2d20301040d40404030545040c500d400c030b800c1501c841005c9080d0800401420141410000542c2c001c8141d0814040c81521261881400ca180100600168036070621242d4800044000542d89000140c007007000e03090035a0025201d40603800004121401c110004d10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325218606 1250 325217356 325217359
    0x2202030c07031115071803081b0c0a03020a12060e030703050702100921030c080c0c0307090e070303080c0915030901060501020c060909090712030906090b0a08150310021305 76
    0x34101002c0070303601c0f5130314803030310380c51400d052001c1c4005100e861181d45042d404110300c85c0030003041551785d5035007113103900848145014090710f0403020b09800c508221102400b141260f07105145407440e0041035003d009800307a0034800000d620b817101480480c5e0000a068440c020440c1e651301014140241150040b034412489000800780010059200c2d0a645080c0c031864402e00b14954903002810b000d0400c4200110b003031010b624503120100d2142c202801d540942c00c00a004208a00c00c10103040c4501a004070b4516882c2440000c0c0386140040d070322060ba50b042c1441c031030316150450703501c001f40100c0d6545940b0900340860160001d10240c05507016000e2500248600e03626000166140c038918141c441d0404400d01155000346040068540c00a804105a40780e2640741c1c0ca81c1d1041e4407c40d0000d6000c201465002c02c1415440081400100180c00c0100d040c807650041c010940880a003148414555002960044c0d9400f0700000f04030a0700f0310b01c00c540d03d03010303104550303142e14041c071906 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325219856 1250 325218606 325218617
    0xa0308091203040609142202031f0e09120f0301060e0f04021c0e030913050c07200a060305250e180a0c05040b0d05070207031a0a0509070506092202030c0703 69
    0x3040b8906210002e1f8620510042c0100403503210440000003e400040542c84880d4001c0d406052041080e00351902a00240c5103900d1207290202c03c092501c2c82c82c83e2020380301e08080011152002041003580e042d02c40c246001200c4030030010014a03124649050203030300034800036000042c45000c80a40d4010420382c00d041c041100701d49003041c1c503801a984196005902000303062403507900c82c0c0c8000d511800b0920135504005441d120030803046003522032003000b03d6440d44024900e107071076450741000b083d00c0c1c03405020914104011040c10f200391752008034050400198a0260341c02a01c555206500180940c000c03225080c3c0e10290340c0300c05031203980040b45000c550414161180b42180c0940700c6010015191110640180c0c0017040024260021400b0310900030001882c0300c102d46007100071003155241282488036008040703c0000e00709130341c2c070303484600d0420945d21100140d0310b42290441d55036131440c0c00310f14212801c4051003990403410f80b00204101d00a84a00040e0050301d000c0d90740c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325221106 1250 325219856 325219889
    0x120c03010c0905010e270709060e06160305070309090f0204031506060503071815030b031c08180102040909080c161406030601020307140106150e0a0308091203040609 73
    0xa03a0480b09900441e40002c59080da81c4c1024240b6883d00d80c010702c90405440c040d004071480ca030444a10a84802000585001040014030b074091180309820764100c0303000349400e2860303601030300110040400405025002ca40c003010b041c001d5003104010034840009200c0a551708100c80000c1d40180021030305070b890504600101209440ba14040d0b600315100c1320300c0c54480c01d10640c0e00040706207800001e4000d4400c00305c1c0c01114011000302d14140b944003c00c3c0341010108060400e180002c001000090a240c101e201c10344c480220313a0803002c107420756540c048118404901a02c03ca4002104036402e006a01080140000003015490074000a4480d000d8030301034001c408040d240324101c801d000303100d2110131a241200084d50088030500450b403400c203089d0764820549003060031a64150b50760b01010007a41541c00302400069004d40392020004913200e0005142ca401c6000c06042c210010a0306003003a140d104034031403003c0c42c03082103e071210b07038170706000f40300001138001c00481201c8101c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325222356 1250 325221106 325221131
    0x305010b0a0603060e07031805030a090f12020907030e0a0512030108160806070509040b1c06050a0b09130204180c0303200c102a11151215120c0301 65
    0xb945094030300e0803907220390f031b038607913900840140201d03a186200345802d40310441300094040001300b82d4807a079070b03e65400151034a1140320702c00d4400e0303001302c41c0680441d44010069550b1f00b24a5480303221070400044050326078070703950b00e040840d00004009102e030070710340c04105035010080c0d8101c400c500100c99603840c05000c40015203c040c130602910f41c1c070803000316907240d004401500b0440d0000e03000180700301c2598002503e090762880000341461641c86603400780041d030300a1542c8403000c54020b002075009940030440188004001c42c0706032074114140e908558460b04900401b40240c2d40c030000c10003650030035802c40345407444100c011a200f1014205942a00c00a1400c95101d006c007521640c074140e424090040030200c00c0f141000180c01c43c0c99188800d80d16401c0c4007659152043d012201c4614003080c1c0190080440c501c03d0000300c03c000000e04c5e1a5040700e00d6181040e40030ad9480d100c00c03480d806007818070314505a0200d10340054030912400000e4550030001c0840090251b80ea1011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325223606 1250 325222356 325222361
    0x30c03070f06140d18060b040b0a05240418150b030c070c08060a0c12022b180305090f0d02090a1e060e0403091403210c070305010b0a0603 61
    0x4564030012003560001c10070302e4040d4000d200b500e03800200d280e10300002c805148003218842a50f8070354410503486040281b001c14400d82c1c1c0940001e5404019038201480000c0720303414284645c501c52011107103444103c40000d4071035600401d1150b4180d89494403030002c810f64100f5a031800e01985d1402c00d44088460001b0b030100100c0708540b80d038520396180c07896604150780c049c440c02d68000c1c044c5000094004010003110b0f200e481d44e100000761201c040e0380d00502010304050380b00d038800d0050204a00400c4449210320701815075020102c804004268624050b211405800303d500c004000c441c01490382220040610070011601890311003081010040d4a10f031b8171102941200d00c00000807251496540556000540d0942d002e01c0e2070700c40d4a0400c242c44c9640c0114100300400b50503c0105a0004000c5015140d1a01103511400b01500442d40c0ea14040000349000300d2000203094410401030101c41d10005494181c41c000d680324200350380a8480000028011026104000340b603910a2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325224856 1250 325223606 325223609
    0x6061407021e01030b0d080309010e03090a170f0a031205010e0f07050c0106030c080d1418060a050403140106061d13110906070605070206100513150807080c030c0307 73
    0x280b40301d1980c0d506241600001e15100740190500da40c0b000b1865290f91000402010603101d20a166074910b06400103500b584d0040642e0181c40c1c1c020700c01340405a558160440960301d0303c0a22607081c40b9010700180c540064400b02107414020840704c4001d242d0b021504205440400c00c00344a2a6665503503510034100c219282d03404039296202048565206100400d03151800400102d0701035181d88035800b040c1881d6000c06120781c046000c410b0f0884d003120390030300f040c8181415030b400e082c400310300c219a85004016080c070458000401502c00d0380104141c81c059a041038403042003d0708454242d0007000207010380d001050382414511124031101d66211003c000c040c20104080a40c01031520140c2581155006000014001e030100e544500019084003801842c003c24103007840b40c4042c2c103204000d8010425042842070038840c4d074a54820b13001441c0e00d295030028600b400009003101c040310640140f01709000f008400241500d000410080c03510048003a1030303a0702c0390181011b984000b079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325226106 1250 325224856 325224859
    0xf3f1912180308191121010503070b04090e100e01021305030d12110702091f0506040e280606023f1e03040309060f02120f0c0703060f0606140702 64
    0xc3c4800544110302c0d00d1407144035880c80d4000829032144242c12034440e500400740c543c4103501c035101140c810359080d040d03ea00422040d4023600b001030900d5041e03e03c5108500034181526107803a189241450204014400d42c1140082006080d1070520458042d602180b02d00c4012140c4030004034580ca0045144681c000950301c418031400f0400d4080c1015001d4a5000c81d008001802180c0150701d48000030b901c285000030403105000841c2d44100c0340c40d540e07508202d000324000c0c0030520102a01c04541504000020034101c1803064034100f18480d00d0070108500710840c2050350018843d0b800107420003101500b401a11400b90703618282d0512454007075403071141000c11b280405074055490000708103612150701c0c400207078000c42e00d0007100b0703500c00c0e2821000900000c07010000f85a100062109142451000d4084055068000051070003484104490030070001510007005800301b096000440d032014040c080d402c118070b00100280050300c52980810030091170a03000c100a201200d043c180d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325227356 1250 325226106 325226117
    0x90a0c0504050f04020f0d02070c080f030f07110a03050102030901110c0d050c0a060e1f0c090608090a05010e160618031b0b03090f3f19121803 63
    0x2402d8100100c03c4541d0501d5030704581c3c02c000d43d81c410641d01d4024400d06401d2040540e888000d46003046451a4a40c411001c0d074210703039026090983c001c130031540300070429000c103a2140410b003021484a4811417410340e02c4001104000100305064000c2c0d442246001d00820150345681012a401d115030014001250000071403816458020780140107594005012210349990310b42d94601110f041b1907444841d64080c00041c1060011400c05980400a04001b40a101e0310b0b200c0152005849001d0101404070110009400b60020020540c985400800901801c14001203c1361504000c0001036480031640d800424914090706245406c0b8011a5a5141d102d00d9502c1c1c0d030340380040c00c00034958401c2249400280c4142030308080c40c064640302d005800d101601c000c05a1400c0c039540000c00360000f5010207920070700d1800381c0d02590529807001e000000080c19030b800240340f1449442414852100428445244e80282d980802002e038400401070f40c940f114090b41007024070341c0300070002032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325228606 1250 325227356 325227359
    0xb0a2004030615052d0a030f0209040303020c03070b040c0609230301020913050a14010f18110a0807080a0516030c090f120b0a020307020a021912030e090a0c0504 71
    0x42d0182c0c0702c4007002c01c10700303142400315407200d0010b089620700903001ca41e2290b050418030790b440d18048602c0201c82046401071542c0349140ea4540310a03e00340c4001c1c0c410608800000c003414025011117002d68245400d4070756a103414a0598011042500d050350708030104840802c40a00401e405c209075091b1003200024402461201d00c1c21022650000d40c041d5020300c808001c1d038039884000c0718080c1e04040003060342c3c034100c0c0100e011039a003030107004403c004003401001480c007800010710907640392000000d4003907030840024010703280044030f04140c50b80006c0c80c0042150b0101c07039a4001ca6145e40d407492aa00c07074852900540b40c0c2034900000c5042002112a085d500a80c4004907900f41410a003441c035560301800b00c11040143c1c028144400340605c02c00c200444041481c1d0321450f0b030002103065082c201d80080d650310720950000d0190440c844107015104000384244000c0404003131142401400c1e02c4c1c01800d0310101c0751258024828840802c0200241c1c1c02070b03501000c0165519820107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325229856 1250 325228606 325228613
    0x61903240b030f0606090a0e060c0307020d09060e0d0501021201030803010e0a0e0c0f030f1f06091509111c09031d030a0b0a060803031303020706051e07021c0b0a200403 74
    0xc40050f00021603248c0d43c03501c440d25298107001c21407142e0305040325207440e4580a50040c0c101a01c04014004201001c00107204250b0454004500620140c40c81e234400c0e0543d00d0502d0081c450002070007040009030000104015140300190f050312030100106d80e2544402c03140300180c4411445603078545c0c120810074102c50416041c40021000020211075060764520305450625004015581210f82c0d02c102c41a6448614000c01c0001d0046140030441201a82e142442c0540703d0302541d0034154071040400b1291620300107880c002c840c5c24050550702440303010140010000184100c02003030521011402d01001e0300700079a0500d8001d8007070300e441c8506548111240100038500440a5521034003c0f40840041020351301c0359400741214244c036942410082c0c40c140c1c26500c83d4080210810144400d103850343c8a507502d0b8068011101e0f21031041d80300190074078200b00003100d20711180c480034030240920192058000c1080d03180030803242d0741e1181307206841614a0b855082c420390410080002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325231106 1250 325229856 325229869
    0x15010905060604090e1b01050408031b03041a030f070306030b04060507200a050601090501030302071701090b1f082d010b0a0b032508061903240b030f0606 68
    0x101a00621582c81e154a130744099081307a07656054590145d22101d0a6103220450b00f00d498201311090038501e0500d894508282c1d035920800b0601e450000c803940c002241508100f0540c0c0160680d10040c900c001440910513016400403906100d00c0141c2402040340303140a4070565083c0c03a0003180c0f4080c940c2d07590b2522405000c020f440001000f00d000c5001c0c2c0304110225050805501e40310180002c1417042c01c0861520b20103801a032480c0380f4000040001a0b00001c2e540c003240c0c08402ca2000f031180850b50319004001102c0080d0202c8100750170801050103c14000c03141e010351311413401666407200d0903256a4001401400325020400c1380901c18000e004540000c03a1040c8000880c0718003040c0007040f40b0070307026880086140404002d001141e0351240807424101c1043d01d03881040240f0b01d034003c103282e201070583c0e4040c40c01e180e60242a8120111890051234016040d0030226606503400342d02080700c0403580000c18031701820400285004a01e100c100c440d02001028552191410040d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325232356 1250 325231106 325231111
    0x105061c03030b2d040b0301020906040e04030e03010903090e240f061303080403051b0a2d0e07030b03030403080a140d061401080f101a0c0111070201020f15010905 72
    0x50100e42003a030350748440180000a8903409140480241c04181c4d002030000b640c50403105541309900601c09041151a010150381c12134246450440302502d841c03c007690140b080341c1c0066015420242c0c85024980c0003030300d030303011205400b441c0c420f5035603106100c0d400070700d05070040e032060708a42c000011907103041003510790f6608005000c00d15020050b40381086640d050380c41219801c001103804c009024040c0000c41103000e00105500110020000140318200d4601500b00660204a200f0540035501e418052100c080b1040048095899511811804000b1034000c40040d04000d001d1380076040c080706031b86c100d07030340f00c2c4203103040200c1c1100039a0312140c000c0000c03181440500102d140c41d90710f40203210007406000000704400c82c40c40c000600b1401c0040511802940303886c240140c4081800095048403410742207403503800e1803c0402583c0c0d00c54018a60815070030010424941e41002c0c00512600e8030036021142e449071a045100d40f213103686100261815048401008103d489800040d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325233606 1250 325232356 325232359
    0x10c03020a061e02070b090705010503150d06020702190e0112030e040f020c071206110307020c010c06020405150c0607020607081801110a11070503060115030b0a03050d0c050105061c03030b 83
    0xf01c0515003103691000301d811a40c415522001d5641c18400701040600844010b00028603010b1320b146445074280d0380c104600e1143c14000e4410101a40600640781d0540d091282d0082074002c040d40d0091030300c0d0a02c0407d0280207018005100001100c60901200180c03407030380350311840f2505aa00301080010301c404500100e2007a020030414400c074106001c81070180420900c0c0009888142c00c05c2e02c101c5805680b0703d034030340300d04000340408190005042c4502c12000d02c1d002d00e5070183c0386071000183c010f42e40100e8001c03600c20144031842e1400d4000e0038500c0740d1031044500d190f0b02d58000b240e03503200641300c0c03001003410000441c0c230654000701480c941c18407540000c04d11940383e0a18211940c0104508000102070b444003404102042c05a000140021801800c055040c0980d00b40342038034000b0f00f40c040c1941e4802401b2103840700c000c40c1008541110a950ba600d031542c074050880000c0c01c1c8101c400d5464480003955030b240c41d080c2d0100b042882c0c040e4105950b0b00d550240d00500384441c58070b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325234856 1250 325233606 325233641
    0x3020a020d260c0a0e0418060209041104090209011209030e01080a091704290405012d21050f07050a0e0907020c0103060f0b07121101020a0e0a05010c03020a06 70
    0x1481c081190480d0785008030350000b41513a4402d040700008240ca101e05020a100c1d5080c9100c86100120308a0382241d4140c000200596808401c40050000c00d6150007018035070b6400f1400080b1301d01260b0141c10b14138000e172a50291114ae8201807411a40c91110081c007203036000350303c03000b0f0b9441142a503500121541002400e02c803580c4070100240000c00302e082c0c0315200040d0a0000c09a44000da22410782d01c4085103c1c2c00480c07603280c1c42c20380a40e0207502c0c100220341c15a00c202500080c1c048014111801c08258182142c0304000c2c12004034442d0000465488070100004007000d1040ca4454600703c1c599101c540ca446404a0703440e8400c401c1c2004100300028074010540c2c1c1c3c07580150040c00250000c0800c40030307000c005400e071080c50f44640e2980304905420049403441c04215003141f903019544c40d0b41d00300b91190980d1040803c42c4000055880401c0741a4442c4d0132000c401d0412204031220580780780d07210b004480c55800d66500500507040060402c00140882d000350070810b4440241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325236106 1250 325234856 325234907
    0x4030f11120106140a06020607021506030111030103060507031103100303050a050c01142403121308030a0801031a040f0308071e02010207060509010b0a12020f04020f0304020109050103020a020d 85
    0x721401c1d02e100350001c0311000c0b51042070221600e006404d6400810301030015108600d00314002a44502100c2c0c018240d0007041c3d40041c245a03003e61040051b0030760041010f88070f50312400e10030020f010403282140801d03e0300083c01241d01c5c0e160241c9205001a8400703621b010f0550782c0c11600c94011460aa051000601401220040a0081c008407100340400d204c054030f030041c4907094114980c0381d109144007a4200d5019a600c0202d00d000302c0402e45d071082940c0e5034410302c0885404002d43d0004e600c81c00007003010080e055100840504a074052035110300c003d80caa00c0b08d0344500c40103460082c22003d42c029003d0019000f4480250310500605000d1030b40d10703181c1d106108070355071154800b0050350700144601c10000d49104843c3c02c503051400800011441307102086110949014032506d044040c40341c1c03011036680201d984070349040070340b06548a55050049902075001968100d011448421010604d9446131007542e070f000304998020f04502e0025001a9105004500c00d03070100d6038172504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325237356 1250 325236106 325236139
    0xb0a0c17030901020d0b060301060c0809150408060a15060f2f100612050c09040512041203110d120e0703050114070f050408100c02030d110406030b010504030f11 71
    0x6144180c00b00c000243e40c80c00003c2c8a68202c07845114490700c5010b0600051120b29032200561080b0783c0e000a000c0c1d5660030b03040000d410a18017098040700160000303004940310801041c200c0c00f41d0201c2c0b501340078800e1700c0006010111524011075000a0300d080201c544030707104190400c0080343c20791004050781000c0e40096016204483e56400c554842054a0802d48880c031070034004001004403402e001c4650703500d041d1604110880e007072084404c00c0102d41846402d00c6845208c4480280145d603a50b40c0b45040c0c0c1c0710507a00300c1c0580109407900d600c550090000700c1c801d10800165920344248450001c0b00d180182910307103490002d0301c115500400080d00034820f28510b02080030081c04585010300c1c006001c881e1502c062002c00405100c10007044500107a42554440140c501192000005000703d283d4061ba04100d041981020100d140b0521710200810507a0101e540c00e00541c0145401902e0342d10641c400241075604e040402c0c00401c1d0700e240202100b4000418031400a8040350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325238606 1250 325237356 325237403
    0x9040b040b1018051e0105030c12070e100201050601090302150d05040c140a030302060601082206151707090203060114040b040e0a090302030304260a09080609070b0a0c 74
    0x400c10b60200d00070064002c0c90614031031902000301412500c6070740305580b80e000540e096060103245418440c000c0089002c484000c025162021a180d11404081c58a080d0092066200c0101da5004005100d00300804600c18002d440c071402c0180c540905540c03541c1e080c0498588403c2c10b0404480c03041c45110780300d050790302466010b60300402d0400889801c00c4a0515065510b002291190390191010030009070089042540602c0900303007202e2660307512503027801030300c014108100c0c00220300c814103040224551040c00517410302c20890760741545409403152141d109184001580d44011020020840590000d550094061400481c84a04245c244200360800d030001241c03203101042c02c0c1301c0b501042400c42d070b01c4150b06409102c8180c268030017079124407015001078001d030a02082e90010102590800031151000d088440e540c42d0403030001440a40d26000d00005402040c0204d200c4010004140b000c0c0c5121100091500ca100c110940e1300781081901104c49880701c07030b05e513440d040404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325239856 1250 325238606 325238629
    0x5010e010f050405010b0d05070608060f0d05031c0b0d061a0a0f030312020f030619210b010e010b040b0a11011805010c1716020f0106060e010801080a0809040b040b 72
    0x1c011442c0c0c01d20340342440c2500d840303600050080c0443d51801000c5080061600f04444d0f403400c16403002c0c0c840c280460000304510005680148000d09000b0400000000601c01c0702000c0801c00f80c0e40d004000c028060352529841c13280e1159403284c0d1140403685581c4102d6500c007151403149410502000070410140160340f01e54051010030a040003410f03004147c40082c0301c0c40c1d00007189041d0f508620150b460002810280c00f80f0381c050f07000400f20750550202009800241000c982d64009001140200d4240e0481112540d4094000060441c1c040e8440d80c1030312940d14043d810319041c50f020b0300060f0000d0b00f01c0010030041d404852580f035000c1c0b043c0324514030741050300c03d08450242042420340d80c0840d114410019801c0e01a000101c0800031690401c15107403010b51200c0d060b000c1241362980e0301d402c140942d40781c240006640754004200540884007030b2200c05c1c0c00e03031381c40d58002e46501864030702800d07520f010000e66140f4500390b80180800c0000400010341ca03102040800c160340c0c0d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325241106 1250 325239856 325239881
    0x9060905150901060e0711011e020c0f0c0306220b0403050a0905030d140c010f0509070302030111070f0605070516121b0309090b040e0f03040e06010905030d0c05010e01 74
    0x59001d00400c4080301261942c0240c0040081c800c07545071074115002c8a40003003e48081006503071004060b03450a41000d04d4400d401d03242190410001e0f054140250f11071116010a4030402113208a01c1c000030031503081c5000010041c020079a5601d485600c031010140780280920140002c0e040015050300f07100740624042e03035600b901c8441c1418060303c0035450360484c0380f0940c41414000d2801d9400322110120f28000c80c60503444640e66140107024240c81191504401c2c1803c1c10003000304000105041260b0084000348001a524081c2c41118411000084c00c214000c120501c041112600996086401440e05503d0203101322070408080303041e50350481d00000313813a0740c10b02001d901100400b94000c408441020103401503802412007c960b01c1841d12043d1101d00c4d6800660b1603030701031403034610710100303844000400303802d101d45035440390007055031001c003120104415510402e2401d007556805402003c68014401054030300c00d4000f00d086074a03640300e5802031f2440d0028001c0003644c0d0703030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325242356 1250 325241106 325241113
    0x403050904050615030402010f2a02090610080a05070504030f0f05010c080c0409050c090402040e070305070e060d0b040912030b1201110306060f040b04060c1505070e120109060905 79
    0x1080000b500c00182c040c920920641045201c10700d00c2100f1070740c0040c0d090030058140040c4507000e50f0040d51a59122030706907072820400307500c0b42c4001410003126100300c61451880e81c80f40100718a243ca801100000106460001590051242d03c041e80060050401c9401d069480e903c00310108408030045900f003110030350001c1000070900503070358440086d04100946190120040701d00380100d102e10850700d41c484011074150089403040380c00c803010241c000d641d1281c942511111005082d243c070301c00070740391000240300548141040000c800c4024005490203a40380c0c2e90b9400b42a89401490b441541d8810410014201d0000d4400910160b180420044500381c100110040c0c3c80500e040740b030341440c219500300c4e24030f074046035400101216801d4840f41012168019802140c111804103400042c01146898002c80c01c440224400c02c801001c280c42c484100c402d44a0a44890340810341c500010f0100c4d150400014202540b4032000041c00d42d403584914003501d0b004401941c0707d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325243606 1250 325242356 325242367
    0xf0c03080f12090601050108341e020c030d0324090b030d021203070c081b100b01020309090604020d0902030a0b0a0e03040609030b04150c03050702160807030602090402070506040305 80
    0x300300c03046642d03c001c15801500301903160400107400480300034105804498440600f01c410800e480c950030003485110784000c3e0200101c0c0c0c0c040d00c0104c10f82c3e044810b610498101070301452001030191b43c4070301c0241c098020130000041c2680540182d214514110480b9020062602c1d5580c0d40e5000030012107e000c211000a0310906080080f0000130350115005440c4401c1c0f590410f508a03038005246140c451030102c0c0c0703810200c0007401012103a52043c0d180c0310303041c10000b10008090300b10b4510302904102c2d42e0b80c01c0d001641d49105084030030b604081e480b000941c00740ba0030340c040c00142ca40d0640c0401d90400b5580001e0405480c0002240e50b01200c81c00d0103c2a1454030480503201d080b07a000350b00c0c01c0c0c180381010340b9070a1284030040201d40c0610001c0d041000f142d041400d00007880c6c505204148100c280580074190807280040141b0483c00c40c404014101e07007101c011568260060800107086813140c4000c0d5009401141d0442d4007081000005042084881c1c45203020b80e64164070f90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325244856 1250 325243606 325243627
    0x100c09090f201206060313020919150602061f05030d030905150112060b04020f16021807140f1e1b0a0b0c031009050c07020406090c0504030f0c03080f 66
    0x2460385503400c003401400d11440c03803100d44403c0c02c503800030b10031290310b500d03a80e541e5100840960703d100000c1d0080c1c04481403203135181209803485040d56074100f080c446c0103954641016171400c44d20803130340168440b40c0458103503103ca00749144446500c0c10704c03007101e907101d42c0420300c1c1000c4400c1c14030019980b8900e0100780402401043c2d483c901501c40340d0070300d524004070f0342035101503514003812103640e9122034511a80c0b1a412594035800d4040841d8580c019020000e034004070802040e8043c3c40e9a80c0f80070200210740c40094414169629903c410380f00c800c480d07045030381043c070b4280041d4400700600106191103001e82070705030b50038094165030341201c05035000c40d0945480c0107001640c0030500000006441400d81580300d101001940e0f125582c58060000088640c2c2c040c0d0740651034582800240d4000800400d200e0303009503400d00000790b444940904441c402040480028405c0c0018800242034140350130750b05004032a1322140a40b03d8407000743d01d90059071a84001174001580c04040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325246106 1250 325244856 325244891
    0x6070503131701110910030b03030f36010f0c0f060c02010b0f090a0c050705030d05100614030708060d0c080f010c02062215050c04051507050a0201050f0706060306090b0f09100c09090f 81
    0x40300c09985288080c40741528801c07150cc00520031960512000000070881940310f0060145604c0c0c105030220b20059081c24180005c00003c080c480c01542885100603d80c10007140e80c02800728040c00203081d40c0e4030318624900411003035660600300b000401419001c904200f01516990036181030010302410010b15030300c0000015402001440307560340c07031401003106020503030740d104a803030501c6c66107a5100400506a404442c40c000c002c44403500c004281c0b11000504110111400d000030400d002000e8001c1ea070365241102c00d07004d405002103140702c45400b48110510010711400c5807442d0031040c0d1007003d0a80b54111116036000c900881d007003005141880b01e050009005146081c90030705503840c1e40b41c40d0610100040c3c10f00500169005120a200301192a010b0700118100051a142c0c54040e010740f9003038a065540640400107e00c141c2d240048a070f00629035940140821803d05281034050703c00002950103000fa1440d00040c0041c1c1c42c010149050b407a2a0001500002d91102255 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325247356 1250 325246106 325246147
    0x90f070e10050d0b0406030203100c0f0903050304091d030d0e060606071110020304050a091a06040e0109091b080f120309070b0906070503131701110910030b03030f 72
    0x4501c80e920540080a900a02182c2500700d4840000c140c81111002080241282ea07000a400d4442d00850344c91056580c2c0c4604000425656000e4040c401e0250885521000e408080c0c40e580080000b00030b903050952000c01c030690314540249803a1103c0341c00380d0a6030040c40e14640216102c804c1d04041c5903017808940e03409030040b03540d1410b10901d42c51b000b544003d070f85003031030040d4218034010801e14000c1040e90010720005200040c5c030b0b9210030f2031401810b505200040130700040e010000035480c00c0c1054400f0340d0800c00d2018402e0b03203022000d9010385650101550340100c52041450440529441030300540f50706c100130400703880c40149103490300c1500d8010038100c1c50305009000b2811303804509903049602d42240b65031500c02c0840010681e208450008000d444001189503080402c5ca040c40c003104d2a8a000c4039401800c0c076034070f60030303960901c4441c1e90414040000c0090741c5441c0182d840302040500c4c0008034040c1400109280d50301801d0000700a11000c5018111503044028a01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325248606 1250 325247356 325247359
    0xa09061128050301030b060f06030c1305100f180801020403080c0607020f06060f1201020d0c0906020601051305041103010f020d0f060521030d020304030507020f0d020d02150405090f070e 82
    0x14441440481c00501030b01060000070002c600000100e161552000e514a80e00f210040c08036540c4d0a0807010b4282681c481441005100f00c5480000750914040048052020349600c1e000c0c0758442d11001215000d000079005807000422100206800f002480941b000d1807054030700c1d0303a8038081c070340c1d61034507202c4d0003042c4800b10750115500e080c505c0c0c008030b01144c001c4c5043e00c42c07400000c41c031400180508000c0402e03000c2ea61001c1200c02440382c6030703081102c4803400c50f2621045980c64400880c0c0b10402402000d8000416058019010714150b02c640e51040c01104400e00f400c181000181c2590f140400b0020201c0d0082030503030b1024200e200c5d1650400410a0410419142102041500001d481d4141d0004420081d040d06038805104031079030310724030038001c43d13032450649006001d42d0002c20083c1d008204004d004c2d02c480c2415101440500e40007449000984c4032070f030030005001c003440051421440c00740310010301a01d48240c0c0c03901451940900c0f07034191500010003403151043e40c0c0440d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325249856 1250 325248606 325248667
    0xd020a0e040b2d04022110031a0a090b070f090828050705100c05060708011212021603150b010e090c030411090a050901060501050c0709050a090611 65
    0xc82d602d0751a141007103c03801c40c0038a2003804448640408004040301d00c01d1981040c00003407110280c0b111403a030100055800b000444803603c900c150240c40a200340070003800c8032000c407400e103405140003101c1e6030303c100010400b00d1001c6040d60341c03a407d54403d1385d001c0041819240c00c8030202e50810104806850014028240001180f0000c0c3d19940e4080040308488104100441840400e00c1400050403026128003110450000018840c20a03140b0030b441c00e02440007c2900315115161090484e40f02c0c0411000f441c2c440e448142010001200050a51080008202c8961000c010f80c90066000310071a94001c0c0b42c92440c4810307500705040701810007500303103040e00041d603840c81059040044c6d5110652203a0300c41c030300303822030611b09103c0b198030450300c2c0308000d0f442c1c00755001240303c1c04540c0002e0108954076401540d0b1400360744283c2050750054001400841215030299900404004000c00e240403540c841c0400c0700d1584103e18000007001541c600c03409907842800c100d20102e220359 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325251106 1250 325249856 325249871
    0x41a0421121a030a02010503060a050d0b07080c070c0510020703060e1f140f0c0c010f020a020c0a0305121e030a090201090b03060105040e040203030909090705014805030d020a0e04 79
    0x20340380d010300b2138001e044c00404000b00795562160f40300c02c1d000c4c0902a181c0c885422640c10268051102103496400044940c00040c880c403040c407050311240f9500c013001c82e400c1c82c20101003004c41d0744c1103410b410441c40780d80000000300307203a40989500d00280e14003800e14091850180d00c400060302000b804c070582440e0300c203400d50490004095006200a500e40c01700d40741d41c140391a1a1046140c0d880156003005004034400003264001c2001e50815002c4503034918080e170910460b03003414071004c0c2c030702c0d08400300306100a88104000c00610b281e85000b801c80c560840d042c90055041680c2d0821010381c0e655018085580100c080c001030085210a10b08519100000070805d20030390003501030051941000c1000c6480030025100b0846000784103507840c0c901000b4103550b44d455480ba850004291203840c0c0c9468110744684068200e020300606002c41e140d281070f030b60800401445882010b0101451004100c060014108c0070610705009a90b9016001005048280c0341c1000d030b00c110300c2c0102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325252356 1250 325251106 325251109
    0xb090d14030703110409060303170612060411060c070e01080105100e0a0b060c0a061515050708090312030c0a0201060b090d1101091d04120503041a0421121a 69
    0xe80b540301040b4600850030803100d0b0706001e550301540e4400d0070b0044c1031002c00310415030480b01c80001d440c413480e10450706644a408000b5120780303081e4000102d07001200410042080710340305004124005e01400e02d4907901d08203d501d0910540e0000f120421848018484c0110a01400d50080c0403030700507403509070030b00342d0b60103c0d001c2c050020031040350b075100400794903182d082c00d03103042c2d01d140d4041c0d4913590042e050540107002000c111400c06802c404c0301040e098091801008c184140c1d941785810302805940c0c1d18519405002090381c140f1502080d1403017240014000c0d0b00c0340b048100c140d91038020b1020080c0c00d5900c1d44d00300b40d10f06c00b030a014044807915198910300c4065000040081070140c10750041e01c2d4042983c01c16428074400c2c06540081c25040e00901e40920300c1041a403c0f001c405290448560005071001840032030301d100282ca040f00310380292500030b80140ca0480c001d811420f03d00c20108148444000490440c65451322040c07000d01c03442c22141c020640401e06440c9a00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325253606 1250 325252356 325252397
    0x60b030c090c070302150f040c051516050c0303071406060108041721070c050c0d0b041212090b1f0e07051303020d240b060d0203060301090f0b090d 65
    0x400d5110b40240104075072082c58420885440551000c01020f1103a090807500208607140440302a211f00c4440d44000a06042440e58111280c0b0300346601030078000c401d030391004414a10581a030300c0d40b0400c0c0d001c0d5a155403d10040181c1031090580e140c0488148a00b0f90819038010b0405040c803040004000c04039400000e0400310b0b60740c10020586d1103a080780390035442c030320049649960141407820007501540040100c081c4c44c0c001c80c212984946d204c420400c0c26100000c0c010715111400e004540064000003140c0da144400d418014029400b9010301000c170b41f14524103440034140003060020020018881001c40210f000c0c100d4203550074002c80001039a005854602040300c0080c500c034070f000240ca2050050341e03004244000c0d429090400c46041034002c640b0211149030001c2c0304040015500c070300585480060300484c00c0145200032240290002071846406549071400b22000410107a10302c51550312071007458101d820210510342c0b81030120241e01d010b2101e01103e4443c48000300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325254856 1250 325253606 325253611
    0x7120908040e130b0103080d150b0708090d0b1f05040b0d02121510080106060219020405060d0f050106090e010b090f070903080a030b0f0f0d03030c0e120703060b030c09 74
    0x7070b482c10415031185418100100e000f0080a4065040f450000c010003500f00000c01c0300441c000030901c21610380c03103402c404051491040c5650240204000000500280003614407441e0060411210985541740c0320304020080300e10780c0140405264200e0060400240003000d0801503070100591024031010074407107015a07001a21602e4101c0f6450020f4004100e44419a480100c0b840c00a0034050a243c000388024015201d0550800d81c022139041d10024901e500b076042004038030310001c41d030b4080c0002428042c04643d00103029540600c0450850101108414460f0000140d40c0c0c9c980030741001118083c2c2810340f01a414050440081d90319210400d40201508460710050348550a056828111650005200240106241a642c2e0b01944607107126a41501d60080356141d400410100c001d15420352648040085903600101e80b2a40c480a11a040380c20b002d2a800c1002c00000c00202201c43c43c910b00f9880b006c8103104010f2240902c0703200141c1500286043ca251200082010500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325256106 1250 325254856 325254869
    0x3170405030313060b0a18230703020d18120206160c080f0403021203031005060304030518010e0301021b12030c0405010503070e09011502160305070909060e0609060712090804 77
    0x583c42100f0500269600c00b00e101c00e0300610403141c20f690713502000800c501198143e0152072500e035184800402d1401d00000c480b85503402d40c82955a00e4000b90001e400c804c016a40c1685d485039880e04d102108444902c409000300700c42c07648686001802481d164009050006082900085610b1340d03401c822503902c1d0036800028135440340c10301c0031081058016644040c0d40f01c001c160f00700c408004044010b5021750a140002c02c103054451081c80818407094500400080b030401c0307000381c1e40d0104840042c0c0c40d88149024202102114002405d84c0c00141180f0051480080c1d00c0507444820081424100040c80c1407a081d0b140410f0244210300461203410b062002c004005031501d80f02c1c2d260a0380282005100201e01d503105c024111100c0d07181c1014101600c540d4580c150a4000c84100200710303944500146030706814460404043d100a02c0101c2e00c0c55183e564486c4e0040d03042c0406c0f0320621512004203100d141000004184010101c6003200d141d140001e10404140d02c4030031101603848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325257356 1250 325256106 325256131
    0x1701031a0a060803040b0f0720090a02180402090d020901030303330302012114011a03100303030e0a0213020c011104140603070e03010e1011120f040201020a170403031704050303 78
    0x20000030301c0e98a21400310020046081e0002002640d82d10032700503082d40340d042da401141c130340e03c904001c8220720601c0e0035001c08907500c030b00034010b51078075400501030290003624607081c2068503800329840c10000e030402c03030110741c40c3c8070121006008440c00c40c01825114154641e450101d0b00001c42201c403501001e410451f400312100130750320b070303410003625501680741003007122100d14144403c44450a024680303012041c000d90b550120101c5041c1ca00640740c000f182000a45595002d40c0144600304502c5507500411f2003080c00351b03844040d02c102205100d000545c3d2020ba000c0c91508542400280300751007041031100307000340b958200d0043c1e0400401c2d5a0b480e030700d454411007582c40040200c42a54590700349554036540880c04600858030345891042800b8030a13280d0095060343c050344101401c1601c0241c0014813080348440c859030000d0060040da290700803140c40c1c1d0a41c6e0b2440c0002c8810710b54001804008041d40700c43c0003480d0940e010403845003808c256403115140d1101610395060141c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325258606 1250 325257356 325257367
    0x1b02090403140301030507031b030320120c07090c08040f03081306020d0207030905040216031209050f06040b01120809040e01060e090a02040e07120b071701031a0a060803040b 77
    0x140900c10002c00c120154840a44039030703581c0b07022991580c02d4041203c42c0d0b00252800141100610038141c01d40c1c0d4140c03204184020390300c50303a018076015001c00c2d200901c180c2414501d450310300c0008102013840d49014012a80c03e0504c01c0040e9904002003008010000c0100000300c0c0c00c0003a04090a94186000d5403e42c5400d01510151001c07444007400b4140300241e00310f0121505d50083c008244280c840041e030301e689130204030407401a40d250001d85000c00c0480000a40702c5e5100d150300c4101041c00140b52081740e241e0b1890266901c218803090782c0110140800c0c84a034001c580d0052242c00000d10702d039030450340c401c1598011400030743d005688440088100c02000e4004001900504600d040540762034001d250790b4480100c1c00b42e009600e404450a0319001c04a20501680d070080d17102028103030a90355900035004020700303400801400250200b82d000805064500850003552a14508183c4031144041820003500804200e480c2801c00c104185010082e14101c45031201042d8590 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325259856 1250 325258606 325258613
    0xb060c1e0f0d050309060f0705180d080415080a1107141e03090f01021204051005040b07060609050a0b0a0506160b090313080a032a0f0b040b071b020904 67
    0x1c1000305880710680542e4404041d4070354410040c51089200100b10703159500c5a1444010645042e2103400014204004d035017000c03402c10f80b00860295018120a04525060302c0d8803050350041e41145110705188040101e007103a1280ca0350781c012030300e46820004c1545010501c0f41d640304a4400900d449110318104202c41070a0000020244181403450b0b901d00d00441010303280d078440202c0c280f041080310000e908651001440070300301d409004c6440e152078205410400c00c40c80003411501004810000800d206000401a000706d40c4640004107245003028070303480c15584004e000c600c0c440d281400b940c0c0c030390b682c1c006010210742090390780964583c1e040d4011910540c88000c0505102c1511007440310101000004009094800040032a101d480d407103001c2e2200058000031700003071a4030640700d05007492003440305510b5005180004d041d40080d40c1d00c107204d03400350038240c03018014402084140900c1540480d401a41d83c61702d0303071320410000560140c004e003095020b402212508000b030100b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325261106 1250 325259856 325259863
    0x40e070905191e0e040627030f020c060f0702040b0402210613020319021c0c05070201141e090d0f050f10020406081302030705061b010b060c1e 63
    0x40c0601a0902068014440b40c00700740380c00b50300c80c280081c01d03084802500544402c100b501960b80c0701109000395112511450041c001842030843e0740100940c41d40300100101400804440c860307190110960200c61020381021120101c980c0100020088052803c4d4000c084600440c0d0490b00050508104800f26000f801400c03020742c0c2e0b41107140210034500007000310301d5108480c1222190031712400c4a6420040e030200351031564117007a0b0b08000301310300610b580180202c0c8188c910940b8130b240f2103d1012064409006454001c03a00c0010840d0a5582c8000d07030450440172800380c0b502c0d204050070204030b5800030a4140110003000f01d8809480c2d940e17140400b44158101d4101711031002a030404075103030f00002e11146030034400d92000c1c0d403102c0c0c014001d440c215202d83e240c0400940d40d000041400240c8207a049030726001c1e0303020100315907403020040d000d45610040350503125554613011130b003100c1d90921060320858050203500c0e981240012074000c4290450341881c12036a80c071185034039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325262356 1250 325261106 325261109
    0x8010b1603050c072102040b030d0e0d0312060308030612010b03030301060c1e0308061905030d081e09010203060a05010237150f18030f30090b010e010b040e0709 71
    0x545295181745030154004000816062170088604101e101425810150390785400200040411000c03a441c0846140c020660f00e0030074080e0602d454040030006242c000c40750160000c0314a0380c00403043c072205046c8511080c06450b1483c0c000c018044c044030000e5940d0005100d8401001070100602c0204640c0c03044103405000761310020034901125150142000c40e0854140340a0b8000302d444411440b810700b5014100d510141c041d2200c0c40110b24102c1c2e40c048010301c0e90035441102440e0850348035840b10454800d4180d60001a12070038540100807481c54964000750466001c0b50340801c0e03180601c8000d6400c000c9138240c04601c1550201004684c203081c0d2000b4108c0d40c00c10303040080855468104040c1192046c030108006113030340110a01120300c01c140603000445458a030f20f01e0601410b507141e4070314000c4100c0404806103114500e04c2030a018802050300b51904031010402c118410424094903000d02d0070315584d814203820f030296000701d01c074003001c0c3c6400d1000710b00c520340140d042a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325263606 1250 325262356 325262369
    0x7110106030605070315120f081c05040201110a08040b030a110301061215031a0703020d0608070315140703090204060e01090506030d050f27190608010b1603050c07 72
    0x881c1d8a00300103008000071620300f4042070406444aa5200603600c04100352010302034007021005c1ca50702c5850350380c1d890704421143c8040030030503100e001c00130484136410390604074000725180c0381610004145643c50b2664445a51042294200291645003a0340585929010040c1c40b980d403420500040c1204400c0d403400702500100104800382e002da0080540c01042a0a000c00403240b0320317480c0500040e10001c0c0502010440b200c0300034100d0070030940c0010031071a02604190300c0e01007600c100d4040360b2111071707294003c3c3c40400406c901c0c0a0b030f41c1c82c10000c040003003080804200020b80030b141d006021404269613111600215580d0f80e0001e0083c285c20a140007296856140e0700f4024030046d90b8480c428482c00e403801d29000e12940858186406c030300b900d207080c8188070f150901c80d0142210030141140b8505040502a290001d06500c411400e40c07148407014508030014083c1c61060300034100049080248005e040444c0b803035000388551602d4000e43c0d80e15103400f400e042c0b0040d0f40106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325264856 1250 325263606 325263611
    0x1715010e061614010b1c0803070309150617070510110106081915111b0709050c030f070206040f12030e0703030e0f060306090604020714011506080c031905071101 71
    0x160144800718203d10059070100000b045000a9081000510300411031106107010030a0601e4000484950255400c41001d00b800b152101030b990b251080003c0407600402803030b41d20b0303600700b103101a401180190085864054a403403400d010114410004100c0c2010900c04501030981400303900354068001030142200355003280107108501c0c0d0400800c00b0301515001107240486041c41081c2c401d10800c0d40440005618110300e03071b0303a02440c0c1124100c001c4801d00802800040c6e024940c05100d105401100c021a503030f01d4010009c0d41040005003442085601c44000c100000742c2039046070718200e4101c03441040b101c8025000320040c080b40300c50103183e40510400002055048001e003803070401e04030b070740b60311403106001070000c140000c40300d440c0e02c08084000700b042c90500d0380c01008568041d003241c5404407041480c01c0c4c2590035280301c007850000710240400c01c080c0c2c0301d00c07165000a0181030b82440d43c2028000d0105002481c55000509503841010600160140201d10309404100303009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325266106 1250 325264856 325264897
    0x4150302040b1206040309060f03153503072901031e051f0608010c020606150405060f030a0b0d03021b0a0f03080d0e0c0a150c020a151715010e06 64
    0x7e10400252140f003010900442114516900034061140c05016685805106610304802400c0d030040035031180380c40416055038502c0a01200c111300030440c40c0407005641c3c0700c07940c1c90089602c01229648001e20400404812a0a0004400c90381101d410081c0d1041d000103c0c6a4000b903e07038880c400500780d200d007035401141e854411400c41f20a049286080054507510101c15007640d04501d03400005802a07000240303640340c00307403031242c030890b01c55040c4d030400d174a6078042142d0390b1003005460005e044c0841046000603841c01100d08600d0f040e10558001c15107660065500c0207803028402d51808a110b0103441c2d91a02c41d07000e0001c0070307406441c02010740d8905295803a079110305c3c04462a01e01b045030400b0407000c00242401c06000242420340c07110301d8004640c0d8072030742d048203810402a99904080160350342d14144809010007100c440001d0b01c0014000c0c000700a845004048504a541080101ca0303400011408660003801c111504520310000241c40d846403d035040a44115142c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325267356 1250 325266106 325266113
    0xa030e01050f0706091424100f0e040611120a1e1803120b030624040c03021b15060609030a12090501091205062e03060e010b04150302040b120604 64
    0x40006070314022000b03002c00d01d1b03040003180e4503440a0128082c0a015215a000d0488280001c9641c00360101d04035100c04e540300c502401668495a010132000d50f10b06040c4000c3c483c141c45961040180c52040f1460855900880c40e10707100001d0a5001031662846c008a50402e5240d111000340320848041250716208c0f81790080d07035820100c0503000100c2c072440c41c0140c24110702c10300300c0c88c0c00028010806a5030320381d0141c0d0401546201102016510814140152254010f0310402d8040b80c03005a00c550301c0c82d8031a5007422003c9a816159406a8000c0d0218400f41490a402540c04c0d02c0c0c4650341c80c0444046803402200c0c10000b4050380072103c48401c8103511080d40c07410765030300342e8458a2465850007207014845002102801a400607000710303002141c00700c5064002c82800c0460300395080415112980c441c110f60003030f40c0e8507031190141c1841078420b00c9890b0032180304440421044203444c0b80441d01000c0c90100034041c1e5070703030445d0285a82d200400c600300c0c400c07103400310340c2185420701c2d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325268606 1250 325267356 325267361
    0x9061514060408061303120903020a03080c2701090308040f1a0307080c1810020105010801050105010201020a0905090601090308070c08010f0e0a0f021201020c06010f170a030e01050f0706 82
    0x2040304a810008808100c031441c12000700c41c112400040148255154038403d4082d00c40158070480500c1104c8920900003401400795218090103600506030007400703410003038078116009000300c0c0400020009100e0020380071100f46680400d28840450b250944001030307800b4a41500b0140841101050001d129504224035100755040900c25103030801100c0340c040514003003558020080b6a03400c0000700c0e400445005072040552800003d01c181c2c1c44c01c008a00494402d051540040c3d440b00d00601441d0000d000e914010602071008519010040e58000c0c10408c1c2c500070785100e8000d030740105041d6031140c1c60280c0a1034020b03a280350384c0c4c9054680f44000000300c6c0b29007002c0d942001d000702c141c0e654502c61044125802c1018200f04203081c0d5900e4250f24a0190890748442c40c00921a50354609201400050040740b0092105504241800400740c3e03013a8080700b25a07000f40b210800d00500420f51205482c0e2500303240355036201040040c0d416003c6c7c108800d0030003601103504414040030b42c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325269856 1250 325268606 325268609
    0x3120809120c0c03151603020904060e0c210115120f020a120b03010c0c020607061d0a0204140124020a08160b1e0c0c0a02030102031f0602030408060c0a0201090615 72
    0x45003115441038100d9203412103070100301c0e9001c07034031b082080044030b8040c001d030001d182c040d0004100181c13140c2c440c8084054510305880004c1e60070800304a6203048844900604104100d81062642540c035111803c007400d8001c0f5800b900300070350803030203240b0420301c0d0b08440e54014965600355200c109190006207520202081c0803217603401c01201c600a814188103844d102c0440da5149454518aa02400042c0d40011403c0310100d54641e04044100f001200100300181c5180c050001e405103401040182c44a0781c0e40c1c603401a051100401140d40d440021310303806601e40e8041e541d00f40030340c801603080041d50391010785500c200059004907451040b94280d00d161240003015581e4440050461030103020f108101d45a100d5840454845400303e03014203000040c200c1180c032072400304d601090030b80e0001d403203503c2c0c6400441c81c1c03c40204ea440c0844000780c602032004508240c50f2544060350354030042c011210b040d0000944000c040d200307400840d200ca4100c0000d00045206020740c02480e90745 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325271106 1250 325269856 325269859
    0xf0301230106090e01090e03160b06190e06090702072d0902211f030f020907020f0604031d190911070312050604090c0803090906010903120809120c0c 66
    0x858001107035241c09400c1c0442500c413200003004440e0b0810f0540ca00030b280c0c0501d04507980c4800e1012882c0840c4107228000603d10487d040d5100e42481d105000030040c001a1150410307013555402c4c4005d0480300e41d01a48444200c4402421751504081641031a100b43c002c07803c60000c6403060010001444d100c003807104100c110840e03041707a8071042c0004900480c04142c011640701d4480c00107840242c0c42803500514104c1c81e820711003012041c00c608018a681c0304660200009081e10b01f903142038012182c2c89151800902200c5115040007512058001d0006080c0020f090301010052180d030b4420483c60000381a403407119030f6005038140c0010a921070b902c4401e040c1013801e07441180300000c2e1210940d01d0349401c001c2840c440581005441c000f0001074001c2e60303601d95030011403815091840188581c4014694844145050107020340004004030305002510b0420400a5044004008000301d41e1900d455030b0389541800d5410030900f01540554a41d001c50181c0300c1783d80102c5c1d00304041c1d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325272356 1250 325271106 325271171
    0xf0204060810050f060a060804060c1e02100b040b180403030f0c030e0601050111100e030f041d0708061503060d020a06020c0f120d2d0503010e1f050d020f0301 70
    0x11030104000382c0381c86e030f8094000020102c4011400068464001c1d46d034120b070758108904a200300284540152000000e004016807041d4031403907110742d9512524101e0724056400703001c9004841c0114088900e0340b010160340821090003d014144030350f03c088103e000c000c1c0240100c462640e0010050900c04210300c0c030354003500380002140d41c0104251448510480082d14015608002540003041103d035000241c0c0000c01c655200c0c0420b07100144060030391440041151141c1040e2014031500c011b00c6031007481100814440595074203c1403020340800803400710f5036903854002107403264405040c0290410b107540c0010900540216120b00d820000b078800039200c640c0e035010040348e40b000451001072600086c040d101d03691720902403205c900b441c0400c2d1400200110032140a03040001d841c490018002100510815998110301d5070002070450100460800300c000b5441d01e0b01c5103208941c4250300c2c01000c0411500e400e5110540e12070700034020002c0c3c1d501e40301042c5550440b0202d0340079490 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325273606 1250 325272356 325272361
    0xe040519030f0c0203070b07050a050d0809150723030604140c0403032003271e04051504110d142a0403060216020a0f05030a0f0204060810050f 63
    0x5140390414060381c160b954002e0345000322030240d500d14040381c402da03054029550042182061400207004282c491002007021309964140641011070907070080e0200500a030a0054251000070003c81c400c100f40d01c441c0603611020340681d40504003c241040280c070210380a003001104002540c41880c0942d0144101c6a80c03441e01001c4074000c40700d400c1c04603c203000c00d00120340700e04c10b0740b510b1032540b5170000c44506900004a195402140c0c1c5003000d00c089600a40780c0703031030741d03683c00b081d002050307802d0900d955100c1000d070b8410040e01072031802240d80301c1c00980e8042c41110308040195014000704400801c08003c3d010310340c000d1003403101203410700b0140c1a0111070014124800c0e18507010f0810390407003029034906100381c40307140314050120a110200c0411100d100a00c0f070110080845800340d006032050181c11019503001d104809100c6804201325200031070701c5030383c140d4816030006601d10304d8070000d0000c0042d5089604648202d40502d10f01d007202b40c0c002d901444034001009810f5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325274856 1250 325273606 325273633
    0x20a05030106050a09050402060c060a1b1b03030b04180503030609060d023f0a020a080607091202060d0501030c14030607050d09060b090702101a030705060a0c0c0e0405 74
    0x3142e16100769508140c4500082040d404d0350f6000c80d0b041840100160f04d444415a4946d01e400801d9032584d111a81d120b03081c942408074280340906150075800e106001102850022428414005000c1d05042d00d41044603e1036440760f020340901c040c2001060703007070801d178200303299240c200b140e00f5401482d40c0000300302c2924288507007140d00c0340c0c0204851050302c00340c10700301038600c1c540e0000700c5a4030500c0207940400140f001100b1100420200500d07400020380104600e140540d440008036411035018401e506520040e544150b5a0703060303c00320300034600c2c03002c00c0c0ca52160b00d40000ca03861030000040304021202d190724003210442a603200800c107140b000c254540c00166191b0010030400c002410288100e904a0700c415805030100003111451000810165101100c1d520b00581012840804510703a500c00c4181c2d22201d81009030354000c042008c20b60314025030240300d00c6071901042c01001c05104661000702a5071214140701029a00c8441c0a0748840580b8200d0745030107a8107024480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325276106 1250 325274856 325274861
    0x111c020304080c04051315060b040306140a0b03060601140903060a1401080312010603050402011209121202040e131716030906050306030a08090a03020a26120d0507050d0513020a050301 81
    0x144d48400706d20325410300680c0d00e18120006415079045016150700b000944402c103503010304004d500440b400704d45200030740c0c1407054112004181c035103610724240000d5400e4038000307011a84003000b0300f041c118648112641c84601c0c0201056a54036210b90400c20849003695001408075600f00302c0c0d00e0405076250550a0b803680a11081d543d410661080100500d43c400d4000c2500a030060500c481660f8000c00c98505940c420381d4107407681806820364000c059480650030078010f03840181141000e013070150084130714a005d40088614080640f1400920080e0b131850100e0312055041c017070745c1d49031720111101c07003d80ea1003003500498180040001c045001d001103920401004018020f40c0515954481068012002c05c0e03810140c050030100060b240d06405401420080c0740c00c840d845500c08420400c940c0c40383e40301000d80c024003400c0303010f0340c100010348603440600d07000414982da81070300c200c406004110303250f43c02034100030911041c0c50756038910108050080c3ca0300580d1903194002c2c1404d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325277356 1250 325276106 325276111
    0x15220b040507020a081905040b0c0a020f0a14060d0e0303010f050f090c090103090302100c051b0d020303070503070216060e040c0221071e1b0e040201080601111c020304080c0405 78
    0x1701c04800c00c105280004044585101c4016904001d82032039120102c9415079081081450101d501200e100710a510b04902e441c01070300e10403030b14454043c0c102040485540140f190550084c0c81c0400c002508150580141d1000c00745001100d4981d80c0d2954840021000e91091501810190201000d02d09040c00464840c1c0340752919940303000a024011401016082020340850081c00c0104880a42c18007610301802040d907115074035441000d203111504005090f038400c6540c0402d0b001c041c40c3e6000b00a1369405001410426200d95900c5000da04104012121018a0b01401004294150440c44010700b031075058500f0002549a094182d03903508066204d40f0300308001c4405400c41c0030400005248946c4a50742c1d26441e02c0c0b0891001c0d1a2622109003160700302c00070b10000d074009012901c420024100c1041da00c80794145500040c12070840075084a0410262025540b031400042002c06c401d02c1022000c001c0c144a02e100c001c3d26500140104207282c09240c4001401d4030742405030f03a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325278606 1250 325277356 325277363
    0x325060501080312010302090618070f020c04020c0a0b040c270c0e1c0f1209052d0409060b0a08031306110c09180714040f0c0815220b040507020a 64
    0x3140d086d0b40800c1410080113007040ea0180e4011400c0038014125041d1600980250721010038222200d40041d04003002164160701851040c043e400b60544d001940c1c0c00312540040002e03585883c1d80c10001041d50b074940200c4440c83c4580f240002880d220141c400320b04900503010811b03549080000c032403015a40302001e6124a061049d000d0010343e40541c00ca0345441400392081c148034955400c6400040440090041040d020040200781014800390001c7e04010303030b13503c950164146075000c2d07040304500c40a01079596803d4020405c0516405140f0264000380a035000c0ba5850039029903c1e0300850002a102d03014540000f0454060503410007840e60329000b80201e1030b1150140011320740024540d070911885142c0595038403070180841000340c5a2241d202d02c1210860045c0816508800401012039150950800c00e481d8403c1c00107410128440704917421401700f400003401511681c00c110664000b040c400200003000b54804000c82070140d0382405160755401069032120110b41015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325279856 1250 325278606 325278637
    0x30105130e0715020109020307151e0206220b040c170109080d0e1e1606110a06110405061c05010603060503030703050309070b070f03110102040501050a030e03250605010803 76
    0x900101c0307480c10308920f070884a84000907a0205a80000f441d2180e00e07805046030200f00b1031030f400c5065002c201070410784140503e4200b00b2485000082da40d480007400f01c09842c4070008580214841c2c10a4070200640011a00446061509040e1110a011b1103440100800c942d1b0000c20327450b042c010b600d5040e4008692906204c000c800d040c01034090f9080c003076440c4c0501d01d4001c0d9500c03c0c49401c0b02e8001030000052009c0421001e0140c161401600524144041e11a181c502c0d541c0015440669940c41a400300303a140d5114003000d807502032600120b0344200d02040c44540215481050b40c4a07040524040c420b0f81da0f5250150216070040c05016090741080100c9070119001d213004603008132500c0210f40882e03075603074003942903034002000441c0d400580300181000e00d41d10040c010303000c41c0a0300003145003d1820300040d05900c07038642e000301810f44490200410500074019100c4c101c1c4080f483c1c41c1060202130100b4182c0d00400001c80b10783d8a09000801c4140b030010a5070740d40440040c04c13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 325281106 1250 325279856 325279859
    0xc020c13061d0a060b0a0c0b060303071101050903150c0a1b050307080f0408060403081f08030307030c0e1002010b0306010b0306060f0c0a140f0106050334030611030105130e07 77
    0x1ca111a0300e00074030300303d5940c1d29a5000035803001c0c060003d00c20b0130195512800c404d0050300e09040640701c00f802c0b081c400ea0050041c100420407a8802d12400d04007400e2960742c80d068000480d0400c03100741d148042c10092641005007200c4000c005001282c11031b41c881510618407042200c400008000c0946954010703c14280002d1424005082000c0115402818640c2d10140e039843c004003220210000b501c20814000541c0701200660008204420001d11082c00c00c401c2a42e01d0000800700300c10517868030360350007125004080b00c6034040d10107425480200d240b000040c0c060800180454080d102e00c900024610a0480580340140001820186030170085c4200c02c00580005400e80c82502801c0704150000c0c40c2600500041201ca0014204003064116002c0c01c546840c1d01603400780c1c1180110458010f0300b1680501504854003a05102048143c40e192304084d02c2d8000818480c0384c0031600c1d05401c1411301650403a141101c810f80c080042e0b80c0314905440c00c0d8000302e4802d07406913a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 325282356 1250 325281106 325281149
    0x51002150f06060403050601091a0d0b15120601120b0f010b040329070909050c04030215030a090203100905070f030809040f0b0607110a0b070c030b0601050d0c020c1306 74
    0x1501d500064001d018509240e12a00c403a814000300707038040f12504e030743c942e41204064043c03403400340910382c11105812002010744640007c024001c01c5100008c14403d2500c06541d03410854400c1e003401e40049500035a1181d84075450406401000d03100d5580300c42c0010000c03d040711155040e17450000c0300604051030340d0b55004003102003e0210071104200a180e0b002007048002d00352103000c05903034801440e450b08030320204461002e4555420304408100900241c3c4880c150080c4015044020560382d64a8070204c900800a9104c029494020f81e026100540d40b2a04915901c0d40100103440e400d45e56000c2503014403205100c001c0c80002c040c40080c07401c1c60300754031450f80c00000d03400125000582d200050442d50049a0481d1803504102c4850401d0800e21201c1c00a8420612010f161000944a40358441c01c1d80c48010401c82e140320002d035840c0d1042050382d031042c0f43c200e010b01414080100107504c0d42480d408090080903859190180c0c00340e5070080e0011150340c42c0d5400c04084902a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 325283606 1250 325282356 325282381
    0x501081902010c1e030909021312050f0106080604060c0206060f040903090b0301082a09060d0c0e0a02030708101815051f090b0301051c050109050109060605100215 72
    0xa00342d0500c43d02444040c04203004402c1085000480409070000321654134010f090824940c002280311481400641442c40308580c501054680180056422071102d1500c0340ca0601c0040c281c06241d4201400000c1d529400140e40c1c4c026442014180948030b00120200d0382d681c011200d00d9407100301d0b4400941c0302c0c200390b8440410580240f81c5003808a45610000700030740d2081e880112107038005842800c80480c18042e0582e40a505c07441100030312000c1c0001070115501a05091040c03085040b65000c0112003040e105c01004130b04c001d01c40528101e00d4080003034000f10744060104540000003640702103486503201c140c0c2c600f9000c0444442000c01550020400c070301104007050036001000c00c65a071410200345c44407040c120090302814103800002c0ca108019480401e249800380014000303a520303016090b0700903006492403011182941041c9000d04000d88010342294030348a644424005190042c0c01500d00a90320307551086071000702241d491900e2402c2c8000310350020b0120b1007580b02d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 325284856 1250 325283606 325283653
    0x1030f02060d151703160204240b0306151204030e0406181a0915010819050906011511070905070c020619031b17100801020d1a0301050108 61
    0x1400c0716081910005902080300c0c44800c2c1e00540c043c69640c2041006000300008625042c0d40c0055802e0041d2041083c0450b0900e99000b88203540f21168a20140a800da1140028014001d0140003580c0d50311154943e80c800e881e0b140c01000131403051000c200340e40c011140121003101c44c0c000710380d9440d10100c482900d078071a140e501580301d04000a0002401c0c1d443c0c0c0e000c2e42c0c0e11a002031340a50720403c1240380140020307440d00500d9440200016240d030400900200102801c0440c502d41c3e80b40342080045017007000c400081443d00c0d007481a801400150a0f0503035441c0c002c0044181d1500209403181514220f0f040c00b940d1202e041031000c00001c2c2c00039900848681484000c144c0350b94005245a00444801350301c0c11403a007502107420341d16020340e4031003009170060031004400703030b0400400310741d03020110000c280c0211011680013260440d04500614000e00210f440b08401c001c940e01070304411100100c070440c0d00c03400484038941807007102e0494040700c004040c4152000405a10380c0c455 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 325286106 1250 325284856 325284859
    0x5010905060f030402010e0f220609060b0403030c05011503050c040b0105030c1803010906020f0d060e160f2106050102060105120a02100201182d080406030e0705060712080f09030301030f02 83
    0x540040c481c0b03600c0389c0c02e142c0e1840d294881c80c1a13900c1c0f2648161001c4491962200203020300300002003040765000d07030859040c0d0707402d480d04484c00301e2142401ca01410994140304003007007081c03000200b40070011900750b41c0400210303000c0c0503c200321401107410380000e4400c0c1455210411820045154181c81c034075402002500100b5080240c0c1c462404076003040030340301c0c10f028000450b48003082c40ca200b80005400c0203002c1c000c060030440c9001103042024941c5800f803104000f00c40c1c5400c7d02449030401007803820740d5900c124906800401000d0007042c41403501500c43c220020400d413a04c100f09005030130106000341402092034081141440d51560043d0a41d561024001030a071344042144d6911030080c050104143c03103c14031044403500340303c80ec0c01c4518210347c40f02e00087e80d940443c0d08a500600c2c01081d43d580003a0102e050000942c00b144d071043c030000d8080304220303642d40507900501c11922510304982ea6218801040b40080358001d1458004000620003d501c2002d8200850700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 325287356 1250 325286106 325286119
    0x3010501051312060504140604050a0206032701060f0b0306061213061b080610020c01030c051b01141317071104050901050103110a0815250905010905060f030402010e 73
    0x140d602c0300602c4104640004e4501d95180c40400090040c00c040046c001520301008100300e1034103843d0b10752120031103100244500c5001001c100c94460140304a050782c000c01c0303a40390802010512107802080e070b500c145558000c0c251000a4a0202c072000d0301d10601d4043c008030b1074400c280600c0b50312408010510000c2044902c0058042411441808034080180001c2c42010583c50300203030201c800140014400c41900c201c0180d0740b907022895003801c41e8282000303d9010260441652103000d041e058101c01c84581d26049a100701c15003010406419181d0181d4440d10b5514004420b0340c008840500344212401d0356881900700303c40288a05801103400c103004007010340c00078080d42c005564584050f91a100140140309012003241d01111040780d49280e045c1c40c150b21203446250035aa40d03001e48003014006032554032a9195224000038100c504040b445030380d01e024001301e006015090029010720408030b0b260a010007201c111010003d5464195900c4d0780c011503500e5035050101e81c0005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 325288606 1250 325287356 325287359
    0x18010e070b09090405010e0f0f150c07021905040c0503060f0a1203080903130e09010c03021606020c1606020d0801080718021b010612060b040209060712180f05041a0105030105010513 80
    0x24428230881048000450103005409030b031049481c940203000c28981e00c070000c51011710104162440843c2c211940c190b0b8503c201d0303200d00c10324100124045d4031144d0000d05002000c4d40403a030040040d8807032403045074540d40111200080c865400d00500540d890559039010a101181c01840f64913407240c0d1840440b807504828402d60740000d44150b014941c00d6000d48280000e0302c80a001c0c2810001c042c1c5000c604010300c051010100f5024000080c000c1c80d8001100000b00505100c0b504940500840182c0ce0355952540290796081411581000ad0aa0000840c0101d0085003280c212802c030100480804de42c0c0384880000d512140150204030203202d52083c00b204203004070300013002419000c240d03101003400c240c0c3c00c0d100c4800401d44a684100501e800385d64540c2c0540e8030903600000e0b4200d0101080c04103403030f040c050704068040320034a2000011140000c4a40d8020790f0b00903034041c8640c40c01c8218003542441e0820f84103000c01c0003840180000d520038000740100c01c420b04c0700b506105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 325289856 1250 325288606 325288631
    0x90703050a06090302100905070b0c030702190503150c07060e03130315060501020f0d0c0314070c05150304030903080306030312010e07020c1c0308061818010e070b0909040501 77
    0x2001403482110300b5500c0c1d10540084c59014000f01100d03950000c400d00c54810f07165981ba840e448035010381c10204002080d10710342108104180c401c2c0d40d50250020201a14816220042240f21702c0b445100348100030580c030462050410b02d900648111502074100305d2980c0c1c0b843c0c0680030103000c240340c6210a2140c25801c10310002403100070350107841c400f500d10001c04280c0302968115049281554804802c0c50a29040040d24024079502c614200021610780e00d011603032034482120481c01500040381d0744c02884510352901c02121021142c8522043c07160100030440d010803070300640031400c54441080890b01c02402181c0c05940202a6072408400040045018400382c00204508000c201004201d40e010081c00c0a0030b101110008918900c400f00602d905880c61402000c03c448030740418003e03102c1c200000b040c1c1040c0012300d0014035225081c0360a842c03019441c84507660805c00c10001014001c5400000c4c0c0d4482903031640b9056440f802c1c003010700800703441110159698099503880 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 325291106 1250 325289856 325289863
    0x614072111070f0c0f060224090a1502030a0507032901031b0206040c09110a1803080c030913060b220e0907090f0b01050307030e0c06040609170109020105070b09070305 74
    0x101031040d0400102103051507100d00c0d2040e22074101806560284188c07189000e80d101e0010003105003803a220f01d00b9a01c08400710b050880c1100010300b21103003000180386c000016005076101d600a080100b10035915444d0403419074042001008030050029810719030034040032200d51070440f040c180401c070515040c03d404c1e1210191000030005805c070b401032008002040d1140c1004000100060000c0c205500ca8000c0e03911031510020b0500401da6032040000707480d207480c44015500481c480d03850b4424114850380729480f0700c4543d80300c0c0c2c0b4600b14101d5801864403c64050b14406400641095002810300c1c10b0640980c01d41c0080c03403011400045c0c009450000c1a21a172081c030007070a0b50b00c0c0703004121010b541444001081c0e85040072581c14607640c3c408140c83d88540d040c0b501045060800324014100104050019007000c000600072070407540003446501181c032101030450807844186901400c9420081000380000c100304000e102090550900540048480782031751002c540d01d5036400d14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 325292356 1250 325291106 325291133
    0x30310060c1a0a0b0f0d1a250801060e1005031b0d0603230d0f05030604090b010b0405010e0f061227010b18040c0303030e1504061407211107 62
    0xb03c6480710780140d86420701d09500aa03005094510700c0c0b1056442d079038007880111100307181160658100002d21112000f0504c00481300c0b010f20102c9054003d004014201ca40034001c141c04a80451164046030414010f5485c49000f2070f5956811600c40403445030340c1e908240340300044180c040c0800400c0b0800340c03244000542c07161100d04217502e140d9001d1401d03c0d0901071031403071607004108002202e60700044102890f4140e46841a40d940d224030008006140c0e524002d00182400000814466226001070003500c400740c1f10f00665000c0407040000580c03254030015041130702071000e0360000e510400341c00c0d041140c1034172400c5402030782c001c1e580c40c000940052061a81d1112201c2c521410070310100c0c21010011155403000e0314045e201c48081d201c10381700007002c165555175110941b9005110001c41807c0d1051408083e0038a4103151010305851020306850204480114400c58052170300c0d0720482110401c240844001148813500529160381600180c1d803081003c01c0005282030305445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 325293606 1250 325292356 325292371
    0x3060e010203010323061504090b0405011d011a121f150f0b070b0a1823010209090103061e050c070b0601020304081b0a0b160311030310060c1a 63
    0x142c50b50f00d10308084030000407004111403a041603603507040c100e54000c11400e5101200002c0c0155a0343d804012400914500c0350240c0807185c00390501c420071a041d008540c640c2101c6407500c840c2d500702034403d400c0711010200c140d5030806004190702c05061410070702d24070b4604803040e01e0100c2c50300460100343c818201200d02c5e24955400d600e00340c030301e4040c1d0f54502a020780500b0030103440c109040c04540d803040c40c0c00584441c0b41b510004100140c0ba4100400e001191001500d802d143c524000f4001c41c00300300d008654030140588800e200c94144261148a24000c4c1701c0c9d800c1b640703903440e9200207001000845182040c240318099815006004e41806032120701008d0742e55210354144000003000242c40c89045400400040080b40d200241030302e82c08400910b044403211003803000407440c43d138580c850202d0f04008905400100c0c00c511101c2000e90180d00c07400d2400e1142c4002c10b031688000c84100055401243c42440201c0c03180320300d010114410f84c411195144082d130043c513413001c05c86181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 325294856 1250 325293606 325293611
    0x3040902031806070c0b070302030a06080d17090303070f12060918030f02011e0b0a030213090201020d14040e090c0904080d06050108040206070209041e0602030604050105031c0e0a03060e01 83
    0x190840241080411361001c034038541440d99082c650b45070020410003900304401c160300031021907402c904951041b001441440b0880d104007020041c003603c1e900d40392040741418034a03000003c00f10080031045034840d032501c0d91081501d480c0f502c420b542104001403040810780d6240000b00e01b40001c0c1c46030241e103c0b940801941e04908030b19004054008046184045905015030381c001d40301c0e600c1a0301200ba0510340c01007442c92400021035444201303540003a6122040c1c80c001e41d41c068443e880340110600031b80c01c0c3d400c4803030061010703104036850150860002008002c00c210804020720401d4210a01c0320503141c0d4082c410000a2242d2429070301603404400000e0754642c0a2518411440102020f0078071030300c5031030070b034001840754000d52001078050940c600005e001c12405145046040c040c003c500d244040035414050000d4008440180c0183c1c078060000c6818500015800300514104072400440302884004460124000c0310032038000d9554600400011054001d8454600c480b1000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 325296106 1250 325294856 325294891
    0x2c0301141b071e03021e0f2d0a08040e09031305010c020103060815060102060a0c200312100311040612020d11061204051905030d11070605040803040c060e030d0305090304090203 78
    0xc40982c0081c020100c04580c0724400c0700d07c000501288221140c03109803da0b240414090124146c6032130446081c101c903000e0740403007208201914024200783d400782d4004c0b14050f1303503a40d001503072481660010201c0940000d800c014541c46000c10510161040c074010461690b02c00c12a8030b04400d10028101144030401004183d580c1008010303440a00c0a0b018800c0701203c00c8050108114036800f0184134035070a48580360010200100c2c2e48594504902c0c50041c50208480f032441d040364002110040b41c00a00003038549024094281643c001c0300924488140d95070030001000000e42c001ca032000d40c00100000103645810207820402c009040c69042481c0500d0280e007402c0b01c1524130403c0b0f005000340c8101088000065440034689186c0002e000c00d0075000f5407626000b4148020455400c0200300010014440003440c0150311035080354000c0c07601c603e0182d41c1c010101d0480c0e9003680c460041c104e00c03244030303800540e003102e038240070342c1e19158440c0f608a060340d10417a4020b1044000181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 325297356 1250 325296106 325296133
    0x120201030e010219110f0d050c070e04020f091510110114010e0417040803030a2f160602040314010903140307020d0806012c0301141b071e0302 63
    0xd0441020100c100840c40c00340f83c0800150b40100d04034440c1c08010800f8040e00c245c0104010940440e04680226581c80d01c1451004102d0380c051580c01400780151400040d0742440c40c0c00ca140603039402010b203040341c09008144400c0da00010103503007201800c911120625250341c100008000440c1c2e0301e1181502021a881d42550941a005001440311800401420003005034568000707910290244c00001d40345048061130050341c022500034040082808501e00c880d030b20524000550400c00074108a6042d01c510b0200b1604100c00300140d803c210081d202644410103101441c42040c005007440d80b2503e805103900c0c0140861000c50b9900d141d9901450307008656a03c80140340d01c4081d280d40740c2440c0084d00d4140080c550303c240704900010600b143e0140031101c800b00028034135a0111440c8036020a03112201e810060b00951074a078074804501c1d01400102c0c460030f4107000e00440c0741d0041c0e80d5850035902c000c40a840800c0c191500908a01103502c801e20098082c1d402010210381c2041e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 325298606 1250 325297356 325297361
    0xe01120f0e0c0118210317010803040f0e1b130801051f08031602091e040b04060608010216020603040807080f0408101a0103110d110c06010602010b031515040612020103 74
    0x205000a600d00d80310410150359200c9440005d0144480e884085080c68a0240c1d100c0580b1080c0308601c1101400110f8201800400f0300110b58904000d000d0362541d0b001134139811001901c0c01610b51080140350403241032400010a205d111000805c1041b6940304103960841c0e00c10780b80c60180e0340b04a40b2249041041c000c8840c00b90550a002c3d40c50424580d0003507050001c2801d00a024890003400115541440516544450140c0724620410b181074604850072110032201114441d20340316010900020503c2980c000703030000d0036480c01a01c926002c00c1015000204100c9950408120000016034170f40c016000001e0794096140d181c0381440751140c14008901d18840c1840d2400594180c911100c00d0061031140c800c4c02c1c001105001540d00385018031908003000851801c0040008a203050000100140c245803410303101c5c640d888035001c0f8203031681010200d501d9401003140c0c112001c001260030b60400798515400c2c02c1d014101022070181c80c4039502802890314824841d1081d542c060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 325299856 1250 325298606 325298627
    0x10212280503060109060e0a0504050103030309021e030d0804150c0903050f010203040f021011010c110c190b0f0702040c0c02010f1403070507060b0d060e1c0e01120f0e0c01 76
    0x70306200d410343c07501a00080c0340c81100d11030b11041001603084041141c855010750805030a0240051001d0368403414050081e040d02c04007240a55244130548d6159840080555200c00c0003d000d03183e00d4494174021a040e660181042e0742c0e8140d1c480310380118102d00c4c03082c20301c0500c00c0d40760312001525506005e81000b01c3d044008100c0d0340100b08000014543d4104070340c41c1c5034111469542904045401c680482112100014542c0392118003505141c004440c8110f650300a400c07a44004256018080481c0526118510883c1a200f05206810310700018002040d959800a070404590f0707000542030f1040c080481022a00712059401596801181d0b17007200c2c00742c8d060102c01c03941c05e90069031007840700400e0f04003003001c049001c508001564010b50b00441c3c0003031645d10320b00002c0c02e02c3d03c000d10303101d05005040d204481c034500301081e480281550714030954840c4010500c0700700c015217001d007101c0011090729648488000201ca0288180666800303c2d80013040c0007112400013400407502c3c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 325301106 1250 325299856 325299937
    0x6070201061401031e050103151d030d0b0d0510021209030304020a0603150e0405070623030a0b13050a0b030615130f0e03030103030206042001020a0f02010212 70
    0x1401014028041010780b41e016060302842c0c0055608500c00c2d00032204e418004d0a9100603040500000070300480c0e285554410000000c00c002803400d0302e196040382e0945c0c1120044940003800141007581103039000d42021000a007400942d0140c0d6520309051902801c0c01134900e5902058042d205000102c8059104104d10001d40c1786007001c1d000200f80ca0801e206080416480b080082025006000f02c200140000d050350703242400d040c5019a224121030080320000345d088800314046644038a8080c80820f80c050a09241d0340710b104155001c2d00441e404140c02c40c051a800440340d0361144541882403100d0740c000038001300c03420105030500002811301c170000d0043e04024106940e0300380000303110761610880091505c007004040005070441101d00d00301c81c000400000141500801d00c01d1045e0700c140e002c0150880341e0140c8169000c03104520030700607440202860001100d40c0c14400079907005004443d41f0258443e6070201c039500107603003013500d1000300c008020341d42a400050540b4a44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 325302356 1250 325301106 325301111
    0x801060e01050306090a060b0706021b01140f0c19030b04050c0a090608100314060106030612120f180603090b0a090b06090a020d050403050711090103030e01120f06030c0806070201 79
    0x90840009000e4040500131a200342540b001180b041e003a1907120704020240c8110640e11132501d420414029002902c6102030594540c0c00c0b008180018401ea1409070001110741a00f51582c400c071034040003005002c0480000b04209103881d0385c1079208100500c032841e039800302e09111800c05001c2030320b41c0a48101c4400006004103056660815803180584120b1714104280341d0b5a0880c0200a01c010b0740040c01d04404180d0003c81c001000c2141c6060303a0349520244440c56a0703d98018500c0f0f001d84000c1c103140c3c146141800c0c0d182c0b281c003189000c3c0b070544c0340c40c111000c0001203400799070071a544907001099445030303d0740800c0345410446a2040050b2350405c0307100190703101c1500a0301c0003000d5078880d4044d48006000d0400c11743c1510008440c030032040040b03140034640135105a05c0380f5000d48403040c41091183e542e01d004500b1134142c80c3d0555600512120150044d01e65840c880021034019071641402c80c010482881410001c501942050b001d541ca03145001e030034104050103001c03c690 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 325303606 1250 325302356 325302377
    0x5060112051504120f1803060903080c04060203040306020c0115080106061b0b011217030115140a0e0f010909090819050c0721200f0409020d020909010b0d080703080106 74
    0x8900d04030981302ca043c0d07414003916890000008075916040d0200750f20001d45910b6020003448419406214418481e444145168842006900300d0b40568070980006900c00c02c010300008034503402405005006800118060620030003030102001c558110101c269541c06d0104881548010000e640f0741c00500103208030281d5031904a541da0050040a10501c4a80410401c000f64030320440656201400344940f2035859003541a0000400c492020000e000c01280c40b00100580088139111030303164691020959044051043d85081c100045061190828000038002c00901902c5845442041426500c4038044041810b11954103031420030803409000044d0b4a040002d880030507a007110700c2110346000382c1e42c0c0b480480d10240500a00901101280c1c16442c9e001103001c0f040044221074402d04000c80070140003c5825004000c3c1d4492105c25020001d810300c11030141d0410801c42c004142c801803d13000c15020070b01030504603038242d80041c42005060780010094003520207441c0034440361 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 325304856 1250 325303606 325303613
    0xd0e1c030e1905030307080c120c030711010e0607080d060b04080714040f0e06090c0108090706032003090a0303050615030619030c081614030d140705060112051504 72
    0x1003000d0074199000d010b4001160411900c40c0d078480008000040c1200d54403195032502007156000000144168413602c5417540c00e0b0184542520704410a09000310704201d520f8071a5440500f2604485041c801011036840b0541c6804006043e8a4007a44d074181e076800a0b141014121096a4020441c1e03440a105c24810003178045901c0007101e00300440d8042907a4210001340090901e001c000450301c1c0780c04003825500c040429246d21480380300c4107441c1200360150054030310041c21203844040f5000210280203040c0030f6403225101c1490311164205c092000380010905070700646080c1c42c2035002c40b807079404041e130500411b680b0140c142c0352010f00503400114880c290101400c0e00b03218010800c12034140d0103002c0d100c40c0003144c10000004003a59501c0076039488176002503110410f0500c2031808a114403401c8418441450054014040017130091002c4170080140ca03a9510804400c0010402103001001498060105d00800d810001c04a242a628011142781c0d10310040c1400400c00011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 325306106 1250 325304856 325304867
    0x41806060e010809030906040f03030e0f0a2108070c0e0702070b0304060902060705010f050618090604170d06090213081518120c01140708100302060d020c0d0e1c03 72
    0x301c0500f801d02d41d00f00e032580054141140100b40c11943c0002010030005540c4140c001b80000b181d01030740392004002090b07400d115802c0150020070743c00000c0e058081111803c1600c440103030030a105681c00140f21550303200100c5a20001c0c041d03404503041c0c8070078041031100314200e80d00086030340014a540c40c9020340442041c000140041e080743d40d14087c4009640f159821141e240341e014000304900d07205a0703000d42c010007003560110b00622418076803542c1407890240890007041007100030700f540c3e5120b44d41d0b818450419500f13842c003854148202c040401090003241d02074011000c0c007685a40c80c0c40560150b5203a030307078865407042e07002c80148071403140801c01c2c0b40d8008050350841c2000d0502000c10500e80302203142003c0c0c800400180f6141c130070106602505082c0807150700c10246469074581240c24100c1038441c2003003805110302c00c00c01031801000600d0510300104015040100400394030b030400d02e150305d40c2000314406004104d01e80c80c0004c00c400009403030041c40e40344000103441c014030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 325307356 1250 325306106 325306127
    0x117071404020405060c1005060103020705030d0b0f060d0905060f070f03050c04050303070b0103110a0e13031218021206010b0d09021c0f15060b07230f010204180606 73
    0x40380e10120410650703480d580c0445003c0c000c0500400d0b030300d5550824583d5a17400c501041c005052a080108011b076100b4021600e19642020055040c00291441c0b08010b203c441100c0381e1141c017030145000151100d60203011100d020401c0044c043c0c0c0c190a100d0b0501c4002440164104442c0e0304100906400c15040c05401e0054500040c441e911000300000c075115a4100660503c80496254100140d1a0719141039a2042c42141c3d262020750050041c5914035000d0760078400d101800290700a43e6003440900760a010345002c400074511301300c07540102e84941c00c400c210110b114540109500f041180d0a040ca90130100400301076140032134110050081c050007030043c03526008c00d82e0075952000081194000c8560015146042c03a19004d0204019100203d94400f0582d100d811031413a1032040800301c40c0151016454609a070303850144012010000c1c040c0031200404e44010854100184c1c048100f60070b000581d102e040500c1d1174007400b00200300460791414400140b08440d070050f401c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 325308606 1250 325307356 325307369
    0x70c0c09050601210e1006060806100309020d0b240f1302040306050c0301060f0203070209011809050106060315050f030c011125140303070f12090923011707 69
    0x2940303071038400040321090080020400745011545140c1301c251600c1d40300401c1c0000c2c610442c0c1181c0240b44442055038011710541000c00e441c01d00040d0582030a060581303c160303842c40c0004109e012540020022140082d0a440c0d5042d082c1c1009040c03181c03034140359034400e080200810094410b40000d1410258404258000d5a00140351001f6a80e0f5405a41c003031540a134041c40f251905e0303224841e160300700b482203800050322448101ca5450000c01140c80035500505000b2203a8240102c200041d680050030208440d0390706071403000708600b8440c1c80003500c034a80d07000c510440343c03111030704506c0441e400c500d118524441d04810b1035980003510b10307030010080c03c024840360b011202d8182400a08401642d12400c0c410189908844511001041c0d0f150555a086050000e605050f038030b000d0980002d050807001100f4801140c1858042c91580f15203262501c0050b445910f541e083d05c180000c424000030340380800746503030b0765242500307405000c00082c0401c400000316003065075070301d1510504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 325309856 1250 325308606 325308611
    0x105040f020c060a270b070f0908031e0702090a0906060f050303030a05060118150216061b020a050a0e010e0c0c150a06030b1e0f070917150103050303070305070c0c09 73
    0x30410300f024640300d045d1034200710407940a4401800c0040c01c0841c02c07204403000943c0302c01c0799488503001c0e40d00c481c00d4602d98001141400312840c800102d001c210050b103402020184054030040c0c4e41d0307106140c852100c0e0300c8040341c4c0c00814501a4107540845d004010010f18004e8140b10340d45002060320342c06000b820f8041a1600d41d20010307100c20f203040c0c0c415001c512160704d0102e000c642900c0300b100100d086134210b80400350141052012901c59004034400035011b040c01ca81d801c000417000105040c002403000c510682d4480c0041c08407103203a40944250315903000100254480c44000c9640403055007001c610f8500301102180d10740308001c0303400c5404855070002c02c1140070f00c1c1e4020703406035510050321903241c05c044500f1804c210001d90340443c401202ca0020f00c40300918100180075041d1612408409814500c0d54010800c4021302c0ca00179102da400182600358840003003034001e43c0200301131992070802d030400405584000380b80d1801c0c04016105440054500007200c411140ca81000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 325311106 1250 325309856 325309871
    0x20106170a0219050a080703140120030601030e0f0f010b03150f0c040305010914010c020d0906030c0512270601050f0409020d0203010c0306060e150301060f1b08030105040f020c060a 80
    0x44015018551300810340211102d400491102d41c001a41c01c1030b00d0148021a2030034000c25045826550303c1c403542500b410129a01d030640450300c002564020805050208109584000052910f6460f03418884286e0210104944001c020310500d810382c801940942313602002400806010702029200420800161000620251585042d05c001d198008002d100d088400e00b046180724480d8a9016441d51a080050010600018800000c7c1d1801d450f01c070705da207107031a5003500103208245080e030600c10100104181c581040202d01c1c031450014010070000c0716290741e50450104800c130413440381d03404480140078a40c3d5042038640300170b034211008540d05c02c06101095100403a00c00003500f546c00e09404d215941d4060b0004810340f5401c0e5245502c03003d6200030410780703040f0000c0c0d1504942c0100010b10071188107440d0318825605a0408020340f00c405030a000000d41c0c0400180d4032070340040010b021925180c001e20171030b1542940c1c19810503210200081c0c461501030030350701070030b540e071084d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 325312356 1250 325311106 325311139
    0x140106151707081909060506010909021201051908010e07030606080f06060d03030608011505120a15021b070b030f16021903180801020706110a0503010603090302031207050a020106170a02 82
    0x40001c500c040301300e8280228545854002e01904041d6221404181000f8011980c0025882a175904604091986c120703a4a0b250a028014048404d440700800d03500002243e401001d004001c2e08150b128010800c5501e1820700314201c9200d50428400d942080c008401d101d10300159035074000008a504600840d05440c003030703006003d43c0d880901d4650800b00110712035942c02d040103040300d906850162465004d203a1140c0c9514140c8001800c1e49552203403415503403015400791104d854005040d4520038240001a0300e040300f00ea02600c544007001041101060f20841851b401030004d95071104018000705000e03403155003003031650021140c0302d9005070038148500035400010071848206100301c0e0301c40b1603a034040e601c603900c2134404c00c0c2088064182c007621081101d0308048c03240e807258110390a11900320050103c0d064184c003140300900200c4071400e201a0403901a80381a1035290740d07101c562034040d003940c1142d80300b00c0022403104003000d10740f0001b01e83d00e42d01645c11a8106000f005640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 325313606 1250 325312356 325312381
    0x1051b030a0219020c040609060b1209030409050103050f010e160b0d0f0e03070203011109010c020907050c0d0e01020c03062a0705010c262202010c14010615170708 72
    0x404002030f1684140d5507016801044015100400707540501600c1e4807006200180c6160f845110b409282c1001185140a2040c41c03680d000030b00c0800350380c50544c1d00c1e100d01050310780a8005503100d4202401400492000f4450030001594034005010b045100c100b00c824000043d200d001d00489000481e0380074981d141d07005400303046040d54100800000842c98582d82c0d006040d04038081c1d071901814461b411251419560401c1c016076400000c9070040c4d0074002da10b04094508018042d045c0031160300d030b00c2c4c00d0140b400380079011760300c1000254009000901d4545c281c08020b0007070b0082d9040c42140046a0103961003003000403152005422800c090920300d2141c480b02400b5546090a01d00380f450b404101c480594010051028100500c000c0d80b11403108c05845140280c00e1200d010700c0099042406900503600505019401100a03194002040c1b91400400c000341d54600041c46102ca0284036103603054414988695001030620002c029010084e2013903041c0403c810002e02546241d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 325314856 1250 325313606 325313617
    0x5030f10081b01020a20011101060803040603020c03040801050c13061b0803060f1801030b1f030f06020405090a0902010306060507020a230307030302060a180f021302090a060c1401051b030a02 84
    0x1050814031140445000c0541d2001d86e900c640c00506500a64201185c05000784400d560140700517614291030103030158025403110352280203602007484000340e000402c0c810180b1a901981c0b119664034642800300a0010050300154144441450319181d03132a1b41144070341a00c2c0d0300100181d90380c3c1300c0d040001c0020000c502c0007540882c0c1680b07406550317882c0c0e402c11030480348940780650454032824908144030000c4a408080305c03000040c200041a82989941201e0f40100c00041c589601e81c4085500c0a008440c04d4888688801030b0f00c0440d41d05116601c01004249401814280198001414010079100c3c08001c0003905121000d00c1245031542840c00c0300040464a855a583c40e01a44801c021942004035518007603d005115001800d034002165100100441580c8541d00704403903130400010b10717107025900780310f03d100b59214014100081c0600b92140840d000311468080c0318040c118411002030b0f41000c0a0007000701c07076a00384906040214040c1500c95549245c803100038041c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 325316106 1250 325314856 325314863
    0x60c02010806031c17090604050a0f0c050402071a0c03011d10090912020c030c010f1b0204020f0d050109021603140f0d1406040903080604020f040306020a05030f10081b01020a 77
    0x4411340b0000954002500b003100c801c02011540f41e90b1382c0c0307072282500c410080301c010300990403070f2500c030300080c003840c1400800d0780c41001c000122946680c045001c2323800c5103c0c1104c42c0003040c2c641030a11007400208aa001280c0841c2c18695810309481c0d58054402c99002400e8411707450101d506800f1843ca0300707018291b00c020401164483d42400c0c5103414201048401600807030b02a14828207020494000026040c0c441900b280c1e024001100c4800310b0481e1241c0030140001c510b030050742c840c002002c4e403072203911015072030f5000042100308885060b8006100c907441040f4a884da64400b41c0d0104417a0740504112107a02c0a81001031018071402400c00382e400d10016034004500f013180c1c441484441e4000c824805035075104140000c40c6c601140c00782c082411840010118a01038009002040405828900b0180d0f01d50350031050743c0081003140089000402000107001c1000785403580000180c100503800d030f1607c00c4003910740c0b01c410080d4903002040260040603900810410407071581c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 325317356 1250 325316106 325316143
    0x1e120f07120314010b0a0e090703180309080d0518011b0b100303080a0213032004050109201612171314010b01020c0f030f1b19060c0201080603 63
    0x101c000014024041c007180c1e08a034035a50000452402450401e59280c20420340341c014501d640388082100320003009141000305520f690350041c1400c4110400e880c124403903114290110709200001d0300303160101c0405000c1080a208400f02d843c070039107045200b40d41c20b0821030111070800308074990741d02d041d42003c0c01c010903240500140081c18400c0030116070103580c0e841c0180d241c1803058000d07403050b04804965100341490900200d0075488810b0388034102100440c644004400100d019200240d00050a05075107201001d840b00402c000f20720f0800b030541d0707041c1c685000081c0806c007140010b0b801034101445108800d100780e000381d05a85000001d8006544e152424004544100c10000e50071204d000d0340b94214104d4210502806000305c105070081c06a0485110a110740c0070683c5510961620620030707183d0a010060000f1000824482c030340c075003205d800030207106943c0809101041105090340c4c041007082e52010040c40030f01d82c24646903d880e1183d40009140c94203a403440140c851 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 325318606 1250 325317356 325317383
    0x130f021216031404030c0209090106180203040b0708090304060e030a02040f0b010f0327021c0b010e011203120507140d020706050105030f0c090403020106081203091e120f07 76
    0x1c622030030050341d1015540c148410300a0140749034260b41c0c15034004020600000740c1000501c0d240b046550300041074000043c07035544e100740391007044080310004401e00f9400810310061090152131140d01c141e5a060610460500d4188940d8a2145206007410040040c1c001000d42d90280b15007511203400610900c600000d4103956802404e1800d10710b0702141c00d500c0d500b031000d4003d0145101c40058156261861540b900d9140001405035804036404141e20782d004103100556060045418040c1c4400d0103698140b040b0300b1520300060708901c08010040c092000082da2104c504461242211004100d5032203018080d5000590800d07004000c450104009403101465805001c0c0c1c540928410f02c107a03640d4030281034039100748980440d05a0480740b041d0225041045040e03422500c03074400011a02d0740c1d440700c1800d00040c440400c1c0018000800d010506404014020084400d809080c154070300381201e02d5038403e50301482028174403012981c1c4203240f900d1003d54510f0380d0440752151407907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 325319856 1250 325318606 325318621
    0x50321031317040e0906060f1003020901030b0402040b0a0212071e1e03050a14090603011a0d0509030301091b4109030f0a080a031505030f06060a05010e130f0212 71
    0x2004c2100d400c8603500c03c1741c0010b051840c0c5081041c420341d4014040004003114000c0031130196100e070800905250300ca012580454449100510003409e401501c2521040c2c03590000382001d80c0e011030101c6010023888200f02243d4464003a003411100120102100304207450100700341440a0610301184000c00c48080500d60004003c00e48803080b566408407540d003210a6410900504403d6904420f05000510581c00e00c0c0c021a0300f5819201a81c600b803074007605100c0e06648040703070044456040800100320307102660240075405d5a00a260704c0a81030000001040d5050102d42100000c224414000305040320394042c401d1590800c1250045481c0004d91011650086840078001d1044010b00c0600310f1010480d0410300358401e04413894020000c80440c00740079240300141d91030034140000509660200325040c220291200640000d00d440300c10840c000202b6440103040c4186001790320b04603991806100780403440344000245100c60070018a000780034540100120001343c1040c071600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 325321106 1250 325319856 325319879
    0x14042304111c062106020a0302072003010506060f071119030303060e0717070305040305190e040f020307090509040507050907080412170106030e01111305032103131704 74
    0x340d240b994003489015030b281c100e1003a40c64004000a5440381040c000d800094264004001603020b92801505210540c0c071441400d24601075068580c400002c0c8600042c1000c1c01130552040c1c04441c01ca08060392030215540521405800922560000403607843c00e035203c001307800f4004211040354070441d40b05d24000d4001c20302030040b0b6050b181084d00050215101300800070b485514402c804109445a110030b8010b45400352044081c0041404420352103140c0302e4440140d4019035a504615030f9040003404119228404030b01a20380c0104104510250040319400c1291070a981949032a40c0d0750800504208050704010341c881d0865044c041d811341d000010500941c000e495541c0c1c80234004500703075001e00d140303005680403050f0702004000d0503020b80d103c030807400e845034000f0900a86a2020320340b140e11030072000030b41c1c4103504414000350904024507419200182512008500c1c9006032102c0c600000b0010400101070b841c0110410040c0b07507440b4141c01d4580da9942e1550f844000d03a660 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 325322356 1250 325321106 325321147
    0xa08041202150f091519030606080603280314070804150804020a060813141c1b06050c040e0703091101170c0c03090d0c061404230411 59
    0x2003484000002c40104102c002241c0b42c1101c129961407400f82e1200600c1580c00c3c0416104030011700074003945007142c0032007104010402c896a0001040f45c10000058425840500420302940c400b60306420410038400e00c2c3c20b0f611900f81c2c0c0109040455180c1241d568103c1c0001002001001c10794200b040301c11000b5000f80e07150013400e48000010344030704450101d011a0041d41c0000101010008030b802000d5440d00b00070701300024902c045407078841e80440c142441c41c4040f0b50380803071a86580d012001407403041052140c6000403400c20824114a00103204180142c612583c500224011030441005c86008100305000b1160b80d141c05c0780c0180c0101030000064030700322158a84000d0540c803803103554585820101c0c00841d55100c803500d03003c131900036411110051000300f01e044680d990b0103412400c1240704854031946982004802002000d0403444844d600c903003480140051180c0c9000c1e01e207042d0451424284c0000c1440000b0090031100c0c1c400d4a1035100080c1000c41d0441c40d041040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 325323606 1250 325322356 325322359
    0x50111040e072604170c07030c0510090b0d20030106030f0c02031c060801090b091605060d0216081216020f1203090a050d080a0627020c0a08041202 65
    0x251942c1c0d800000d0b140c40d0740c4000840b000c80d5444034004074119590003010b400a00500034110000c0032900705c005c460b801003001e0856075010184c1041084543e40c403201c003401080d05c1140790301c1075141015060740382c24000d404540c1e00200c1e040100003c242c2c40b4640c8440011200c00441c40c60589400c0168000c0c0540400030f4200040e42070b407000280030755900d410044d07006501c0c00d104136007000c40300e040c0901700700703401503c0d12800104080d0900440100c00e00510079140d0030b003031240040789419000741e40044103150700d0404000d15910385040d94482d0192050140c1c0c0c400441d8981c00b4520080ca1000b000c0f00008142802c000e042c40b0081c503c0381c0c000322580c04400715008010307030f9250300d1811142000d6000700088503203040d144001d55000842141150100196680c8043c10310100c03805200010300640100810042c040c0030304e00051030000941400d1450059402048582c4140c0060140d034000078282c600740020071144460680040c03d164540b92140c1c000d41810308208400c1c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 325324856 1250 325323606 325323629
    0x12051803191101061203080a0617070603180f0212120307030501361a03010c05091309030e060307110a080c010b0312070b041e06050105042703120905011104 69
    0x29107044414030030310003030301e881412000d54002642d1b4126090b80e0000c0090440580700e40c00041c48501c000a070710740e2200c0d040090304984e0704080e4018102d0b80c00100c42d103090b41001200c0d2020495403035503514270540507103440d5056041d40407a82c1ca0150340302c00c0850001d0b000030030808142d5040c0d20107810394890500710001e0324029600121210f034800070241c0342c9100040540c2c0e134210180d1190800412140b00020000030301d000090840360080f0140700030440003b0141c68514102c86481540c0300302280811041c00c25440013010000f54203a10f03400f40300000b006c184502d01424060034000b034000e00701c8200c56000d03c0c091090b42c21221303803118250b00b426000c501c18640030607074180c0c00d03641091043c200f504075101e10040d0030016109980c5102010150320320030b040034040c07034000c6000c3c0901083d40d5140c00700341710480d4a80c112170301d0780c0c0744624072280131a00d5120760003c0c001d030149031040b030300c00c08072020300010802110010215072030030040110521080d4081c004890114840 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 325326106 1250 325324856 325324877
    0xe0c160309032102100b15030a0209010801080f060601050a0314130303060b0f071506210b0a05010308030a0f060b0a17093004050d050c03060105040c1205180319 71
    0x800f41d4032414000f420015030403040c080011035030b465100380503014000344150040800381c0f182e0111544150303003e18809400040345443c95030006541c41c0106640c50043c40340152003a035054507958083c0070b19042180004108403814441c2d0414201c2031201a407810003030800b8182e03d11502e400e1481203002c00e00b0800c00050302c030859000e13941c881404e40c03944c0c2e24203038065840e81c90b8100360401110401d80d55040114258184a48404103c001220303500d29000315420070380b40c6450000c140b210800e041400600004100c80705407a00300310708480108035420071804500240046400950640b2404200e50a080368400003101403485034424030070087c2c54255140307444d40c0302080e400d00c85103c040c1060900d00d9082000344681d4081c0141c20741450785880009134403c01d01ca000b95a0380c0d01c035501c08046403400340055030041c0b608403403c01c03031036807155000740c092010210055039280c0e4840c00a5040103050240d110320074139034420f890f41e440428200c01156101e03071840000241e0700880 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 325327356 1250 325326106 325326143
    0xa0905061516020127270524040507050a08040f05030a030f050a06061707030e01020f09090702161205010b03060c031e01051e1f020321040b010e0c16030903 69
    0x11403000d244a11142050001d00b810203041140c00c40d003442003001100304146c0004a070181c031849001d55601c17170483c1c03250503080705600c40038920550158031540c913050070b000304241c000d0100c0f8000f03650b40c2001d210990340d0b8280b45402002d8244d01400a000000c1c8000c22154150b0141240c811148001c10035519141ea4041c12194a40681004910604001c403c859210301c0e1155011100745004074192540c140400d0a980101d40301c07554501e00030800c056941382c02c01c00c140e48105244000c003245099000c003900c94030140d00c5095408041c04603c01c3c14044203400a04580d0400f90071604039081165592516901c220741c0140e090a48404211215032101c20340d50403200000e1003900310810fa050803c1645c82c4080c14254460352000c18204681041400c0307201c0b00140e50041c640b034030a42d03940d40b039940c0321610860464480c20410000000c2090f030300e1390f040d40d801e62020505e65544a801c84024413410340d800b0310103840000040201603000c0d01c2002034902c142e541007800a404c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 325328606 1250 325327356 325327397
    0x3120f180606060409150816060306060806010e010e15071a06120c010f03090f050a05060603010204030c0b0306040207170d0609020711040c0513090608010c0504050a09050615160201 80
    0x750100e03400f0704208400c101d5010990000d20401c80c8522214030500c1e81c41103018a884521021603c0d000d14012040090542500ca46801000c407410f04056a1801c400001d041181ca441c150b41800740304103d803045902e0314481c0c1ca5200c21149460382c0c0d42c0341642050900010040300d482e072070601500009555003420301e4042140720140009101c190604001035412a003040304120405540f00b005101054400e001c1c4411180150b0181042502500703010742018002044140240e00401003040000d2804003000c080b80d41e00e411094880c0c4401002078040d02c2042c2c0c0c0548045050349030843c0107240740b002401079840404080014a035644400c1083c0c1c0a410405001c0c0f400020080d031450a040d00210f4002c0d41d2484c5c02c524000c18480e5168203400741d80c1120f1022907840380184002d4409100701e40540407581010ba08007450100092440ca20500840d00100c0d00e03040822200d46074003841d07820010202e84102c1d00c442c0c2d4001000c5560b80e240d40144c0c001030524944165034201c59 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 325329856 1250 325328606 325328611
    0x1020d020d080a1103070804020f0301060b0702060c0309041506030c0206010501050706020d06090510030c0e0c04031509150e01051320060c03070309060807090e0109050903120f1806 80
    0x80c0c001e881d02012214040d0b8031450001c2c5801c9401d502c1d0310300a0600301003c0c000310310506607a141e901c85814a4014002c041041c00d02d540c4c0a0380c5031105c240302064071041078580003607046030301e1a9241680b2320110f0039402040141c0341c2207030820780d6080c500344030f102090003a00c0680c0c0c0e040220b5a540b2400b240d4985080c0304d08c5010500400000011462980003403804100042c030200700349960b9405901240c5044907440040b4034030704824401c208000110f80d0040010498070f44440c14010900c0d8554829448018858620102a419003104036004003200a40004402404400c0140d00d0805400c00000c240115403034080010000038460030845d949541021103075404107400183c02034801e403040d01003648040c0a0111051035002040100005031090341c03540c5000d450303c00e0203802108050032000030b00881d88014041d00f40400c07040f80c1151644a00480d1584410881c1401c510409000b001d202036207008000c2100ca5217458035010b424030405409121002582090300c40405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 325331106 1250 325329856 325329883
    0x30f03110403020127030b01050a06022a0d050304030f0c060c0c05060306130f0912260408070f111504030c0b03040c0b0309250501020a0b0403030e10090c050102 71
    0x380310500c0035500c0b071200340d16048245c481300008044820304805103008958000c9440d02c00c400010301003801d149400030020070303042c0007d14081da18080406501000b000c2c0003aa42203a01c100a2015544c80002e40180d03600503044c1d950300d03612401c025000c84d40e0300109840300d12603ca00042d0152042054500320798000d141e00c0c1c2c455041608003c00c036030000e071017194400d1700030101030340c0010039104410343c00c40421000612041203281103445461000610f105002c0c4800c0c01502401024052a00c1e00380400b800c03000d03550319407800c244607001d00c00c4080c01444140b00d424003007040c840750800c3d8103942180e5418542d0780c141c840d10900d02c900c0c0030050810000e02c004001c0303220703248045d6800c20710540e80051140c1e141c44184516030011106000300b98401020030304055072600c0030030000c41120203151003403410600040d546582041300180081c0c0c0c1c150020702818841c0c1d000b215000310707030340a8482913100c9806140192842c0d410644034114a40c0c03000440b03600000712000f0b0703002d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 325332356 1250 325331106 325331141
    0xc03040b070f022e0305100503100e190209010b210412020616020a0b101d1518010b070201020c03010f1e050f1609090f0603030e0307060203030a0207080c0a030c030f03 74
    0x1940404070046c18000d486900400c480c004041030958007400b04240082d6248000a84580b40c4510186407a2003038840c512051000840000035031150311100e41074400b06001c40d030f071f1411012140c8211035103034100080402552070a01c410441c807005142301c0c0760441c0c2c1c02c4513508d48401c90311751103842002203208050f912821041d0009043d079070f07d05a1060707142c003c1030001e541e5180d900500380c089030181011901144100080701c101404130403040b8409607034540d001f1041403005c1c0c00d1880180141c50400101280540441e8800c21981c000c28602070028405240000c0303107200901020990000010034403019070180c1d4030b1501c205842400310202d0b03c401c0d0b495540020756000d40c841854004c00a86000200f0b146145008503454840b82810009445140d410300420300348407040d0041c07280c4c000d5402013007859030020540342c0002c48010b0060b95803480d46080e582c6403040d143d002d212402109048014160402402d4044034020344881c0c2241000c4c0788200c0440b0b20003c0041d50001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 325333606 1250 325332356 325332439
    0x3090409020a050310020310060c0317040609200f03010e151e0103081c180314042402010b18040314071b03060606020a0503030c0c03040b070f02 64
    0x94990440c4030003500107807a034100b080d03e5601003420445016407001c041900002400340a2a05010f000010605450b2a40c9503803102c0d5030041051240980186404807880089805c3c04047e501c00250580e0190011344c0c02c0c1d14607502002d4601c0c406140c24482c1105034080b00d01410180503100c81d800c641400b800c000c404424804100c00c40c040d00c140c50700c4111440300580030380c58070750b002c0c0170f0340c06544102d490306c03150b981c0c1231075032922044c150001c00c2c20080440c246001030400d20400650504020550402c901584244c5020701e501143d00207000c104c80c1c02111700d030200c4060005915500074040c0c54092420b101c8640d100340895081c0400c50400140070030300c030b00d900a0440b10700503001890f2900c1921014104003210320030550300b00c09110700308100003032032291000070403040c00648210b001540316541c50740801031110f2017001000a91150448041c411100036000b454101034072109241002035a03603058480480c0500302c5030441c0005442513561017414502b05128220f000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 325334856 1250 325333606 325333609
    0x60718050d1112030405042a030b03010f090f020f01090f03030f1b060e0d02010501080c01140405040e150c12070c03020109051c2316110a060c02040b040b030309 71
    0x10003891070544911110202002c11a602c0f0042c007002824000e0081d5192401c0c80e003003100b150200f1606a106040c01c40507ca264503200701461018669070a00059003540c0101080c003501044841c030404512b44000304040207580400e0060890081c0c8203003060140d204015501211a8098441c004480c0c90701000040d1050040424001852801464030ba940d0340303e1003010280743c0c00031222252291070f6000c5ca03c004124804103031a4500c001d000307075454446119200c810003440241003200c0003481d40300e05048a401c0394014440030f402000006003441ca03183c6c85410521030854044035000100b081900d0003015a444040001c0d4050200c0d128410281c03860309010314210190b540340d440a402103001444011640608203884075408500c04000405030203001d044200c41d08000c10881d81e08181c424141d5050703402000c0b942007840524200007020050a08810394400c480c40400310741c00b1b03401602e880080b0b01c01d9a040c032001c1404401c11003640c0c031803242d168145cbe04c2889960582d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 325336106 1250 325334856 325334869
    0x906040308030c07061505040c140d0c021c09050111030a020d0c0609020406030c17031603080414010e01091a09060402041d03030115090e07050d0507090503031b06071805 75
    0x403907001100f0519142e0180e94280686e1840240000440e582c42010800303400c0c140a100c00c000300618241c0040410003c020600c0d014448400c6d040598034004902d00a000700900030000b020310b46031030584c0c0c140840080141515000701030005020f180031420604001040c1c86503030300950007038032002d144441708882800c48000d0a039840c1d070303c1e50000405030b2038511407280514020003c6005a5050003c004e0f0824011251424598400c2020492407a03920f044001081d80c540790a500c0c0b0380f141d041600e03d030079410780014629440c1c400000e1400c2c805600c41000b4600c1044c0c801070011807840029002e034421101c146049d00030b480040c005141c00e0344a00366130103074501e200041c44000c40d00c841c07440d0801d820045000507080c01644500e0382202e0248010868842064100e107001c100c02031a0380030f0701007110255616030300400c0584d40518150000740002400322078841e440580b01840e008107103044d40b00036004d41408143e88a02c200b0461800c0c40c1c07515030311034900e45000c052104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 325337356 1250 325336106 325336111
    0x8060c0901030b060c0a0c05010c080316110303010f1a07211103040305060103061107030f030207080405120607091403030403020f0f041401090e0102090d110f060a020d0206010b090604030803 84
    0x101a5a034452100d00d613107078000b500800e81c2c0000200040210307032400c48400d1900d81c0200381800300310114a400140380700d040700e40c40400180341e034a103212480010303541c0310403c1c0000d1000707001c04400410300b00341080845c004c94550b81c4090b15400b4204040e00180d104403503003d070956903c07840202806400b2183d1a021940c04c2ca000300035400e8002100e81103401036081140c07680c100d80c0c010028454980580e0000d500100d210901d004055900039220108031020740050503000b103040028040d11a00381c90003014007509aa21540103c00303000d488000440c0c10344040392512801246501102c00621190700c0e01400031450036095408000c06108402a03c1d40c2c0710030745511a5510707448078000d0785903c030035140742442d45504140c0ca04040e204c03100070b01e400c035a10521048099a07500c13249a0750454000e0b031105851a82000400c422400c90794010350050340c00240c04042c0303540010400962010390b800c0d00c13581d07603c82c13050000318402e1089a59010a0910081c0f0100306900300854 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 325338606 1250 325337356 325337359
    0x9120309060c020d2a05030706081f050a060f0f0309050c06090d1e1e0c030308090f0604110f090112060e0f0a0303090b06040b0904080d020c1204080f0708060c09 71
    0x810720704441e903604600d8881c038441c40384417046070200b045241c05052110303c007400046000d07089584c20400e00400d1418020000000d81c15280e60010f07020038409600d00c0949001307048150301c603480368400f4250031702000b65800003a91809141080510070711401a0840d03002000d04007009861080003103a400100516034402d04042c40d40e0001034a1055184e1406060940c0d041e004841e030a008407510a08040100d41120b901b2103c0d0005d061028124144c99040c200703208103407a150f010500e40080c29022149600c5480305100600a078150074040d0040201c904c102d08079189414401c1012080c0700e004085140c020f91003000030519017000754040703680e20803202c0ca005001035032451304003228825400300b40d4452205090103243d910b0030741c2c40182910203000d141c40c080007103154040d000300080e220910204610b00890020f8049504045031081240c135100e40707081c410001c40d40a48149a040e10602c102c0980f440b20115121080b1070114015108541e503200c045038031540180341d000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 325339856 1250 325338606 325338619
    0x120c090f090703022205031e06010e071403070e0f0a05060316051603080403120506030a02190b0d0b210307060507090b031602010e070807030f02032b09120309060c02 73
    0x50320080003064500c03020f0400001d007105c0107103004203050609a52089142e540703400b9641c1114042c0c8001005411546954503090195a9050b41119212100c2c040326008000020030303c80f0083e4440020559440115540c013040900c01040000300d5081d4400c984c1c10040a000064000c4510303107110080c120282025460042d2018504002c5044004214041514842404181030b40503042d640000f542c20000c122a04181d400a075807101803e1000384901e881559401203815100540c030000c002c0c1080311501c4500001c03100c00540070030340c0c0f0301e805140070303604600f0082a0000e4400306041854080c0d8038240c02da4541502074400140a01c003032002e0845c00090b9402c2081c011072103501d030f000d80d11001000c070b40402802d441c1e1884114602d80e01c8442c00b40510b00c1c010038010100ca0f40420a060549002d101180c1005580d45108900308149681000400542402d400000a1666030b02c1052521081d002e92600c49844003d000a003d2681c2070206ea4000c0600c0003000c1d00040c00d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 325341106 1250 325339856 325339867
    0x70315140106020304080d1d060c100c030b031501030803060625210e06030c0a120614010f091208031314100c0809061b0c030f120c090f09070302 64
    0x40c0c036408002030b4480e0005a200040c03c0102c031206105a000780c508034a0310b40003250b0b01d400740c481950754107182c20340300d01400030790107105401c2082070769034000009006005208070b40b10060020150035004500034041d0b0542004452030603400141620780c407207001420350319500c0c140140754000515010241c202100c20110040344c1c0881a9442ca20416600c058000d030300118040c444042c0d8804014803410007010080741e991003003583d03030000ba4600401c0e240c000d00e00048511001d002480c03070002e403600d8804103482100264100c0d51030806c1c0c07194142c2803012002102c032085c1c80e228001e0203000b0200c0d102c001590701c10045401148400032401d1090513900d4607072071070042604000103a802515083c0c50021280540d542444146c01c050803286011100d042e21050300401d048a82c3c4515100d00307034071500b40c6040d10404185042180d44506141410040c2035200325000030182035a81d00150b014801d48003110341c075110113000d4120301c01d004010300540b40c4005d000581450303000d024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 325342356 1250 325341106 325341131
    0xe010b0903120301090c0e030307031403060301060f140a0b03010e0103030e0f0418260906070f0b0406060602100b10030c120e07050a080604050d14070807050f070512070315 76
    0x610b02030000c1c400c0000324845606c0e8044c0160b442d45038403034002d0700113000720008690446050100d0310920302901d5500e62360100040d0060602c0e03000400880001040400c9008042d00401d5003042c06891000409444184020150009204069002103d80c0043c4006449594007e1061001924001021484800040548040c190301132030300d00091686005000610341060340002c644612628244021180481c50b88604001c080c0074610025a4404001c1d004030400c90b1640c00580115050400349884000b40c1000d10035000140714981c10100030f4035503842003010310b0000030002400c03c6403040c0c1c150b018000808864091007840768098840758514010fa041265450b03002d007035000d007048200244480103410800d9550300c07280c00c00c8002840081c010001c00c0b010b00304210007000302103441030a4450001c0092442501003009010440002038502120403030105840c3c803d030f21102840041d8404c20724200c51944a490704002040b000b0340c03c1100224a000f012510404914 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 325343606 1250 325342356 325342393
    0x30606090c020102160809010915030203041506080316020d0501050c0d05060910050d060f020301080307031202031320030307230607050f0f130e04020102070f0f05100203192003040e010b0903 84
    0xd000c2b50100307030004100020030403801400702d0300c0d00d00746104201c40c904020310f00c0c0c2e40c0d0042c1b0340850940c280481d140d00965980f090300c03420556000000340058600910580c465401141101841c0c43c01c0c200403038294501038140501c00d584a415138030000c1d24040411140d0609103400342c03911030752014100028045400154040c0c0f011354025643d60f296450010016100200070750b001520500c24490303064140408040815042181440300401452000305103150114030150b25100000c1e03803100700681d04e0742c3c130a40003041c3c001c8801c806c5c402c0f480c20b40e00c88900b260380c10001b610800c207540d41803541401401101d40c818094608205003030300c00a82030242d503080321880c0a105d2041101319070b410070900c00642170001d00e01103050300d031603a0f03904040c10901406100e0100044180003a034820000c1e01d880000c0c6521800817411803900107803070b100f02d41d000b680520390922818010382000200b1101152540050240c8580c41c0c41c1e07040c2000d41200c0c0e0900d5050250081d5282183c0808 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 325344856 1250 325343606 325343639
    0x50601030507051009050a0308090a0b030406050f07020c090f0a0b030f0303090c010f022a19230a1a040f0e06030c04140402090403050f04030606090c0201021608090109 74
    0x410040c55810b040c0f01c100907581100c200d04c0e1042107034030300c3d0602198030b034000610200d0354003e1071103455801c16000184002e4064101d4410080d01000f048240011500882e000b03001011040c929900c0d00d140490720b54010095890300300c51010042558240303c0c1280c0382d4855801d00c00000c465894100080c00c0c0076886031401100c0e407022003402600c0c0e03000c2c400c404040c03009003000c0c003000d0702211029448003101e0341c034101d81c180203034480b130445050a0090950703040002c1804454840c45021401806c81c0303030048030307492422445480000000403040300c91002004080c4240c062421130388580000a00d140c5040c050400d100001c2e90030002650f0401902854035201900e2500509141c80d00d4840204280f042d4140341c50351046a0500314041c1d00140c0580e0480c034982e840c0c0c02d050707400340320304000071030741300000200001405801e40c088419124401d60a010000034100308a01b40c1c060100703200080313200300000a000070b580c0001040e104a060500301ca4507941c681108400c100704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 325346106 1250 325344856 325344863
    0x18190c021b01020a03170c0d09081b01060614130302060f0a030b0102240619060f08100e0609090a0f03080108160f1a1306030603020901120213050a0905060103 70
    0x20900c0350801d000c000c5100604034030078802420b1288203610b0040207200b00803550b031040c1031500081171900e130070304049034084505003205016a4000c0d10b468603a0394000e81c202c040e10200071801d251000c01c180544022606a90b41c1c0780c080c00b112000e40750466001e809000c02008010200200503100c05010b0090b00101103011a215460210301605494a1604042c11500040944817580c006a48210040c010f8003c1480190b5124000314000f01e503503007800c0c3c02c2d4214240f40000c0090340b200580c2003021603507a866660fa251040e155100d40c01034000c440c00802484001003680c2440d59015602000300402c691011410b61641c0380d414101030015000107441d1801884849010003500c0d0100c6034103041114050310740414606070800a001308568241c03108e01d102d01d01c9020f042a6444c0031008420341103510748e25100640189003510089008800001c00040c0e40514241003c0c1400d40151510784200b005500020083c00d0040c40c0c108a6660f0f40f0285012803000c121180c0039510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 325347356 1250 325346106 325346113
    0xa0c05120a090c1203020d030218031203190b060403020409081606020702100c050c1903050106080c01030b06040602033016030b06070c0302060304030309080f0307090506070218190c02 81
    0x6035810b00d4100c11030680c00c500110b84c20039150b0070000743c1c0024426088000c5107070060702c40321050356a5078075220380c6d071046a06104444010300081490030080d80100c214880041400e188c55171600d0a07500801400c03580500e0070f001c20030140c02c190308803c56030b42c461242c440c030349541d44a6260501c0b0707036220190b40480d4045002d00c00c41c1440300107240381410721700b00780000c544596580b5030785041003c907040c000d4116070005182d132000c1c108013401a680c0324000b032210075212200142c0e514840f200040c00030b401c0c000f840c507040c1405002c94042d04c1c1e4960203907260841c44080c0f1401d1130143c0b0000352201c1107680202c540d5004443c0c445000700080307400710104000c0100010152101c100200c0e00c40c1c0f0003080a0000207070191180000c5a0b0305035000c5449542e103040039401008071240240048800050300822218040c005600c128019180c076151140c032101800720a000700341c80290041d1920410700d1400c1c1700420351680c4900c9400d81100302d103150b2800e240588071030407207150241e031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 325348606 1250 325347356 325347371
    0x302010905060708040b16030e03070302011a090705030a18170909070908070302210105090a12020601030b0109050612071e05060304051509030c060c03070f0306050105030a0c05120a 80
    0x202480b1403600030310145404985420291140700041e04050141e40400480300300e003a903054029006000745245035000c1c0c07902c070b580c9410040e01800e03908201b5074003403081400c030001601d882820180030b1400c550300d480c155038824003010010504118030303e0703883c0000c02040740054020200183c0c0b0011740c16440380c48030000c80501450140184c410014031405040c2880f5046d8001900b8003181d0b0116400350001c0c00085010640c40d0010510f10925420078003040900c00340000d40c00784c490720842d280141556a218200c1e2030715403c3c000102281c0941004100c9099140c000d19041080107013001100304c0c3c0c01440c0d40c648480c03a4820311115041811006011034025013000091109555640c55480c2030350750161a5010301081c484e071105071002003030710050100140c5054800c40b004440150030034044006682d00300300e910000180c42d4545110441d17200e40680e000700e40f0103854403421500d454095201801514680100f040001d01c500c4600b528111030309801a40161000100d64 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 325349856 1250 325348606 325348613
    0x31b0615091d07080309060a1b05160b030603060a0e030c010f0b010e04180b04030c06020a020705100215010e0702150f012103021f020f070b06100f0503011a040b040303020109 77
    0x1042e01c00c00d0003550030014013001000c0c1c000c011101e801004455075580c5202c40b020a41d61030141b1040c0e200700e900d90090303803010084006841074060b400304000b1a49295590451665884202c490f40d403da080b82d000314100c801660042602640c4c410250390402101329480f50840b10044036000c50140c0b51000f4095651f001944c58801000584060200300d19400402d0107890889074000c100100240c006028544960244024142d000701c041d903441c6101036000b540c1e80006e026840c850084013003030000d0117000080d141e84c1c6051104421010740c0c6840c00c0e1090264005007008158020a12060500003c1404c803030b218048860205a165041c06210030640c4680714490a222615613007480209400142c0c0140c1e44940c581c1203021030300e07110303c010003900420800148001c03005c640b8400f002b03541181540318000c10303201d104404d640003008448044030480b00c480441c40400043c0100440c401c00c00030400d800d0301495107401e40d0742c03000d107696900c03942c02500140d40d10320642041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 325351106 1250 325349856 325349891
    0xe011821141207030501360608070e01030201090f030b0a0b030c0303130f090606021515040c030b040506030c0a140a080d02030c0d0216061b051605041107031b061509 73
    0x1500c080401c2550001884000002d5100b082c1f2a964180100900a051402d1207400c410054004070082c0d40c81d05a4800381159444020f0000b2804252a03400200d8041c001144550880340c001b513540e2101d441e48003e00008101b0004940d804d07001c3ca40c47c00d061070b101000146051001c4820209040d450191940e600301e120350000c2d049c0f2406c0820801140703a000407403150080e110a10441191940300390b078526009540c1c41c2603001030400708054405505988051010b0906950521056a401d030070951075608840040e580801c031401d0034410352170800c4024480b50b402400b8000c07010748500ca00b615108042d43c0010041c0c0c8000b640b021411014000d05000050500003042d1007000c0e80c500e07011507800c03030007001d0402001c1810009903109aa40d60121903810809555800c603030260040c7ca0b6120b14040e4074001c42c140090f180d00200d50a00f25181250940d8615500038482200340e60050201700d81511032980f18504200c40c640d800c0c0341c40005000d1001c0c0000c003050541000100b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 325352356 1250 325351106 325351109
    0x230a12140c0102070501210c111009030f0509011404170d0e1c020607201c0b0105060705120f0310050301330906090e011821141207030501 61
    0x2440e0070059003040d05036000100329050710800d00744040241c66414410821101c0901c124030514140704030030302e030640c001840b072180382d03114402e80d1814a4200000300030f4811103040140003a03072441c03410a0b1244541c028111003801450000c0040d9071599890420342c000b80c12009422410300d007100b0850004109001201c491828001012000c10000034002c294481843d0602ca504200c440304541c1c0e0002181d41ca1903104000018503900003c05607203a026820340140103111280c02920300700c0d440c00440b48240d89c0220081056070a0100b4005241c010020498043c840c040a03001c02120000c080c2c600c58000700000d64503480c1000c0c041c041103240703074861030117a45003440744000301e1101e142c240c018400d2840f0b0424248404059162400328941c04110b5a43c40c0417808a502c0304150040c40320030102c00001c1c0044500c21908403030010305901c0040415904184110310b85642287c14009020f4904000000f0072100701c12408540c400e40c030365450548140308021040e07403d4441c450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 325353606 1250 325352356 325352393
    0xa03050d020123040303090201050c030d0e070f2102030c1002010c1412040b07050c0111070212010c0518030a0210030f0e010c0f080402190605030a0b010203070c230a12 74
    0xa0049201101c2a4a03c40300035102034201901d4040c00c4065900078400c690640c01c0f0041100d070b880101c00c001c20020700c040041110180281c54000910541d00c0d000041540e8002440e0b020041d60504098840421034404917054000c03c0d80303591103aa9008071401c0c0001051300045104003002d04001c040b00116021048541e105020b014400c11904206540c010791103904400c454648030400d490038066102050545d40c01d000b4501c41190200c00500401da10940b244500703001c06900450a99108030385160020300c0a00036200c41c007158810380b0191040280075103404541d42d40120745051511400100841d03210401c00740d20004600c200b01550180000820942d40340d00c800905100c81c0145030400c2090400218043d580d44800c07a050b081c502c00e0ba92042256503902c0178280d82c00480301e0800c2c15141210b1024194004801c131901c2c26840300440445505020076010818001950f00824110022006580703417141c2c0302402c0a01000300305090020041c0c985800c280d410394040d070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 325354856 1250 325353606 325353641
    0x1203280903080901032408070e060402190c06091a1e0408040902090406181512051515090907210c0509062407020103050903090a090203150a03050d0201 67
    0x70008140c40b04191408000240307070104030394901d02a0f41c8140e80d6000160b0b08524851080024822400244441101c0c0b01000302071032542c5a00400089001f0041d801907040015106401894030403560140c1d06481448001520b45242e103450a0401c0c45422864000301c02d00180260400c0303402c405140c8501c1007c40c1072042c50280e650017040d014520844111030b0b0045881510741d91180c110b24081d00120142c0010755171881a21009068a11141c03804107188400100f184035491004000740c7d40c11500401040315121103440114000070000741940718440c2c5901115900c0d11f004600485a2000820805041966055690204140b211091100b24400a0000f4090188001154800c489002d032a0383c80902291590b01c0082ca2400000354404602d00b24103a02c00180140e24000c0c1c0e0100301c19900c007450260b4900c00c4a0010354001114042003100c80e1407034000b5a400707190301182540500b2460046103a46c8880e400c111500d4100489a0000c0c40d4241b2a0409524184848 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 325356106 1250 325354856 325354859
    0x60103210e090c1b06011a0a0203040e0c0d0914060106020d0c021003020c060a0e010c05160f02030c030708010518061b0a090b030109090201020708160905040212032809 74
    0xe0501c0030203100300c5010701e60342d81c00511140264010b40d050078039824640c40401440c4258107071101024040d0302c01400c3c21b010030003a40070680701540c0340802d40303400440ca00341c14007610001004005201181d04002040030311501c001a01841d605039101d28004c0c19001c200190712428200c05811100c1194031031a0668407a41e409100d5000320340e0143c481c0300081503841800c03006442080362441440c441d40b021301030b40c00441d60100510f524038100030041410800d00031905446070041809800d00e0340400e50380031501418900303149034401012218004a182c01083c10820154007243c1565990b000b086840102081522410740001c400303400c8614103407500b04c1e080a0007203c1025100c1020541c251014003030740311100544402e4003002c0e03c0f581d5440444003d4480f01c5003ca005001e20030002911050005000c020014541461285a810705c52804000d210040043e68050317561203802c0043c01061000342200c001b880031904400741189202d0070542c1c8202c03070450801050050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 325357356 1250 325356106 325356173
    0xf09050c092238060712090f06360302090a09021206010503030f030a180c031223090301020d050901060305060f0c0a0509210303101e060c020d05060405060103 70
    0x180e02600c526182c40c3d0201c031030100d00200304035005100e0f00811b2444000c2c001d2650603044010701c000c40c0c02c0b40103089403264564034200c994082500d051030010159422456000b09140341392004aca07417510f00002166626000070354494400c0c2c0d585500395554621650070350502e45800240010980300410b1194501008280e5130710940220401c038500100c04581d440103130307800104141181202e030850000d09801d00301d9482546d448200c0c0c00b01c3c50901181c00140c02110344c00c0d0144000320030542102d00c078150404156200304800d6626544c2000350800d4000c00d0300c01c00b13029900d14000080d0b00f44c15440c04510703100000d002003842c0c1500074100304d4608946001c491650505142c802c2d2220f030254007003280212003800c800e01441210080c0c1c052031070000081c0d44140d444481848a640c0c1d40c1c039200c4441020481d20b28502c2e10151414480c181c011140c81483c280302601d414800300440c6c48840c01c0483c251030443e15500503400420501219800741d020501c11081d00f40201408600d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 325358606 1250 325357356 325357421
    0x30e030906091908010e030a0f020d080601031808040b1b0a0503031f03020d0f12090b090f0d08040b040311060c192604051005040f09050c0922 63
    0x140d8840d00c007050300e10320f00440d0709400c01c0040280400900c0044040c103581c0e9202c0d08105c8004000039818490010064800101281400001c0c1c5961099850700c000440241c00d03004500680304071650001c80008018100070001801d29003400c0b40c036102032001281d900c0110401e2880d05522044031040480e0011084039006070107050001c81d40601e0f03815800320001d10ba4006540b18140b140c441081c031020800c1c0300c00252003044916607040308001c003035401e110319000c0d0304442e1809000400e51414803d000d034030200c40c01041c0c110282c8030340d0340e5082281e000303800c00c40c041e081c003060030020803240f076840060040e0121141e40c1401c080c503e1555030340454035040b0440c04205241041401802484003107030f02d100c0c118013001c0300300c0c0b80d2170002c080d4054490f0902608541c0e00b01d00c040383c0708606460035140400601c030b603998035180c0d040e400340101a00103204000100900f810581d604003083d03d0345200010110400607d126550341110054501c0402d0081460021a164040503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325359712 1106 325358606 325358617
    0x501020d0c110a03050711041112060d020d120c150c0e030613032d030605040f1103070f050702030106060206061309110d0201030b040501090c030e030906 68
    0x110421200d02c68100c001180c40d41218000c800068032070001000414020743d44112100184800501258041110301c2c1d003000001490181492003800b01c281d00100880d0081c800d140303c1c1c3c002c038885801c0c81600400c0007030201d003180c410174060b86981520541018400c3c0e403202220250070300030601615000003240300c00303160407001d240014000b48070314074601c400044e110560381d00761040030710b40c204070303d481c3d0120079400310100e00c074141c403012078082d541d003c1b64035840d110921040314003c3d00c00b00300f5141880702c1035800c40b507401c0c110794000342c941c034200030760802e11842181c06018190f0300079455401c210300040c41030f81c002a800e01641c411a6404040c841e40803011080b40c00e00d04005089410000c60090540313010403081c42014018140400c2c0500e240002404407034003604044071140e6a2a40e00c1311455041c4100314480c1c4a010042d0300e442da07880001021401003 = true := by decide +kernel

theorem cover : BRFrame.Cov 325179856 325359712 := by
  have h0 := BRFrame.cov_init 325179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325179856 ≤ n) (h2 : n < 325359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
