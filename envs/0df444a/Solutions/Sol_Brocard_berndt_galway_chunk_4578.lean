-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4578
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:11.656655+00:00
-- url     : https://prove2.me/submissions/3b0ce28d-e503-47b8-ad55-01812b08976c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823201438 ≤ n < 823381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823202688 1250 823201438 823201469
    0x412030b0d031404080703080c1c020712060b061615150e1b07050c0f060a020d03110f1611040e03070311010f06140109050405152404061206 62
    0x540d188007800681c980c1600d000100705024558515881c8102d07003140751180b041040c00810001c00c00d005140d030103450000c1d2000d13145400d10002803022440f03100b0000da04203120030f03c00041c5d6600c01b601c03090300840c00816401034140c0402c1c000c3c3c0c0603c1c1102d003401c0f00041c408051012014140c02e6500c500b9004101c2a122038003107501c1100d56003e44101300d04081c011071104030902104000700074400e100300d51303a81e4091904640e1948a0000507008030302c054102c2180c0c1ca8103030280c9030026070310b40141000e80d01e880401c400915850040b40c2c04407009002c441d51055106c009000409928070f607402c07001d4401c1c1031225410740a000740c00d00ca2402c0c03490041c2880b074088280d54071940e1505001642c40e83c441070b100c4c00740001e40c0c0d164240c24900b000004000126447c03002c5c00080c02e80301d5210301d0b511041404141c0c2e008031407030204040c00000e041c4203070030810715940e030040300081c0c0c002e0b0a1010060b07070103a65120b64480b00010b260318250846ca0001032151030000c01440e00c0903802c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823203938 1250 823202688 823202711
    0x15100f031401050a0b070515010605030411030a081b07180c0e0d030c030530040b0f071b020609090709080609030c0619020d06030803070e0a1a030606070c0806041203 73
    0x1050131806251402c06012441d00d003041820130055030740c0e00d1500d02881c010b68503000002c003a9001160281c40907055140d0380e10b001e013004035000c0801900904d20381d1402140c0c1c05400d04403021039240c4e00151090b4440014040d80d40085500b40303072000c02c4c0c00b045c020440b000080000d080b6040d854880c081d0382144c0c02c0060342001c0a01d454940c14240a40c8503102025100c000402c0d2890340c00903c085000402860f1140003161813107144034007440c11554459201031490240c2c12a0300d4000b20780305070342c07141407020004103103036985100400880c13038519890701044a5640c203940e0100880e444510a000d5024244000d5621101020003181049804003030917564a60207040d01c4500340c0702843c0c8408000e038640407965070702600071003806034650b00d2403c0301c03040d07000b00e4420000a03400300040071035141c0010510121020015404035240300701c3d4030240191702c09080b00742c0c000020007400d000180f115140000400b400c5010f00624a42401c00e44641c8030740e810260109458850004031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823205188 1250 823203938 823203949
    0x4140c0a031104150f03050a09030801090b0a0302030a0f06180c0915030f050f0106050f03030304122f0c090f1302131a0f030606150315100f03140105 66
    0x440c4449450007041e07194920010251030321840e0094981098107410f50700c0a0764000380c802580560307640d4104807564842036644c0460f8020240107001a41c03420040122200350740103011947d800070710b8510b10658940c0001d00d0100100f000b102c20300701d40403801041c00b1503481070900840782110091244c0415540d40c04480c81c2c240201824691748904602000500c0d4400e103020750750141030403603c1b02c50380c20820f64400b000d000000c002d41c00e001d004107075030400039131050115202500071402c540741d695134802580507004180040001500740c9201d024030002c807010105900b6055942443c0c48818003d041c0007500041c03500449400081c000714102d003034500c2e90300524544807406040345030720000304200b1034007100003203c60030008807403500b920303040d0006040034007140c041580c01c000c5414140c079175004550306580036000d420003684080d10341000710b0b8000070040341400d00300410400521000c4261009100145180d80c03000b50039509445041c081607180c3e01c0c1600d0381e40c034003400101c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823206438 1250 823205188 823205197
    0xc080d02061611010b0a0305011a220902062b20120405070f0b1209070302060306190e0c0d0c02060103051207031e0f020d050a05030408071e1104140c 66
    0x41108407111590f90190a600c8180001c0b0f00610041301c4c641da900300301d806001c44042c4070820900e490180c0220749484400d110411141c1d01d481940e0402000d40301c3d00900308031805980012040002801d24568460a045113010920003205048014003044040320414203031180c0702d1301941c140c03c07800500001a1025081d20720502c2d411507480b40780403803c00c0096840f60721445c11450001c9800c040b614050b00110500e484c030110540d40b0f41d4207540d0340f43c1607480041e4001c5000c001140403400d00342c0b51024080e82100403100c0340c560319400c2c4580d81504036140554405c0204400030f404084c1d0042120f21519480144520750464480945441e0500d82506401341e0008603a41050b00488202005200702c0c1c0701b000c0100d030191409811140e9540d05d0100600030a040d07808058050001d88180c0d603016034403282903a50380d940706016548122425201c24007420101d04091010085000c01309102c0c0ca4440702a61008041c00162140e488030408240da10004014070340301d00c50300b5038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823207688 1250 823206438 823206481
    0xb0301031a040326070e092401051b1f1b0f030f141608011410121a090c04050303031b0403020a0b07200105091003180c080d0206 57
    0x1c035442e0320b441c5801e80d605508201200380604003e8030060b003014138400000d00c00c1215448110407900250104000b10004681c1a60b08882e48000e2540700c04444a0380c1c1450700041c10854684501d404481c641051043d43c22030460f03009900010081682100503e01e214503c1014000751484e1780644140150820031101001040080d92032103e21a4010302001e000e100340801202440d80b620350600ea1040707480307903040e00620944070582031144001504031149400480d050036440340070841402e0225100b4020080d440c01e0414410480e13100da00b0540b0001c0b010345540d02d200b10148184c0750002000740c00200401c0c44200140e03240442201c3d071159400c40f19102c01d24004c500400c85001d02d80000c2d402c0b04d0582004500304001400600310b076402141d500c60920041e5104450107003405608a0000e030040c0103030b0031740782131160b0a1610b1a006090100d42d560b00c1840c0030b40f100741c020341d056511070380040082003100800d1000707441001c11440039000c549441c2442d10326001c0c81c080c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823208938 1250 823207688 823207733
    0x30506030309040b1c231c0f20030d060503010b0105041809051f0f06030f021c0501020c0d0306080304081e1f05070e01080f010605130e0c070c0b030103 67
    0xd0301c480b6070791901c042c409005c0010000e07920780c4050900f400c02c1c54101600c100f0410151581c03252030100001d0901041d00c25581e81074950340441d204540850703100c05100240642d0340070f01e0501101944401541f003103070340d00a43e00d03804004240801d0b21001e0340841c0c02641340005145590342d03c0b0b011601601d080c21325032103024200c0d040350402400ea0200280080c022014444c0301d8040902a100310850059000d210301004009850126207061100034204400c14054030018240410845107502c0b140c03840d00307040400c036120282640d1210304207040982020480c1c1940139014801c141c040d04221008608050400703629907a00c07004d0114440d030a04800c82d000805541c10001041c1c0814164907800140a11021140c06044191490804100d12585103130319544180c0b26503100380d022072000300c080e9280403025680d9600040242030305e80b00142c2c01145404084c9841030140c0c4040d80883d03980d00c0c9909000048501c50b4009800a510070001080410303508841003410120b007540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823210188 1250 823208938 823208951
    0xf0d090b070c0b01151e05130e0108030313050a0f03030605030706031103060105070507091b082202120115080604050115080303060f0d0203101505010c150c09030503161203050603030904 82
    0x5041d44d240b0143e15201d03841d118406d0b42028445d6009015081942c0c05210260740c00c0d8940e0606040003500f4010070007580d1043c4002032800c2d0380c002c01601000c1c05a03054855a400a03110f00358801c03540142a0042501c8003010081ea080c01c2050000a007924507080020024016801c80c0903c03000d01200e0400c074011558105010f000d120510003050303640d104001d1010b0350352400d02d00246901503140450032000000ba800c00306c2d228005520b5549a0b54802800c119600300b005001c00b04264410790f6607101800c42240f0581c0c050540544251002420340b4034140c40c025007520415041e032440c1300742004040005002c00001c0e00e811550455000d81c000d00f20401040d6070303e0891001030b41c50312a4071004418000968059100d07001e1a000c0600c00c0d9803078500640c0c0311950341d10000c202c140b48500d0719003041c613039900c0f010302c256451500006190362074680717138910340241c2420320070702c281d03816403904115030100014042c24203802c1c14001450640006034482c00761803030090180d43c80b642c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823211438 1250 823210188 823210229
    0x902010215070905030601060f0e19050301090302010204032102150408070b0115031a10080402040209030d020f010b01020106060906030903210603050c04020304020f060c01020f0d090b070c0b01 85
    0x12881c0c84040c0346044100d094030340030900401005481c07040303501038041c8900214219101d0030340b1401d2022035480311407049d1003440910111004078041c03010269049000410503075003c1c058017500b05d01075800561902c2c210b0070000700100404400303051406c902601580c1d901e401040c201c600b400400e4020900740d481c0d06122030544135a06005143e90302d81c80c0040f5002c0503140001c415404942c4d02007010b80b0a039440c80b600009504801c95004160401625035075109820480c0d100344040c0015042488c1040840d00d841103445851000d81c02160340743c00300000c244141c00d0101d409100030701c8900d01d0504044d00607800360141e0000c241e100e4001c80709050286080480340880c00b540080c11110242e1010010120381c08212624001d07110828014078082c02a60700954000f001504c0b02040001040001d6108010480565409024031180c40f05890040e08056a40000c0840c010180389000c0c3d008140041030403092001201c02c1c10040b4a0704500941076450750f541c040c1d815440403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823212688 1250 823211438 823211443
    0x30314130b0a020c180702160e0604020c0f030d052a070212031e0a09141c02010c120504050a05011b0b0a2007050c010807050a080411060315150c030d09020102 70
    0x1050301e0f070b030008443e41040e1176140c010446a40b041c01280d083c1d820030304000744d40d2202503803d441611803642142e00852280d14140d402840c0d0099440100c0704401c03124904079086170170101c8410400c540d0744013049940d440002c080405022001c1041c1c0e4800440c01010340c25021380d85000c0d010715803d141c440e0500800300100c0d281d0308018011b02038800c40c43c503100c45156101c1c101d500006032900400117032100643c80c03254159000104003840c4c00d00301042c143e40c00084560140d04000c10707190008080b0391203011841d24240b9640d50195031314103081c140004c2100e10b60007a810441d41050000641c400b84200d492101e600000b03111280d04d4101a040c0985290208031806e8942c542c044881040c420300281103a512800607a00074401076001500c1c8540300711010b1001c19000c20640715014492801c082d8403900c82d1402c105c0e88402040031400780c1d0421541d6580380c03c103080841d842840e11815005040041c0a5924500305945101b2910ba0140d20300e4880c4468548141400b168001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823213938 1250 823212688 823212703
    0xa291903180b330a030b0c130608062103030403120f060b030a0b010f14031f1d2d100b0705100b0603240d0c090204030314130b0a02 58
    0xc1c507696001d040002c1c4403400c21204580000340e14200c0c442d9150106030380180c0303070344544004200c0c1c50340300c5c03451310707100b40e0b000004008001c404400c001d001c2c6141d50015495001d40081e80d0f6083c8240b42520a0000341081d402a0360594003c11801c0f2000d484008100e81d0300581c10300c3c0031820201ea090a84015113030182c0e84800d85400d1280200d99207042d900950311403051508107100b00e00c4641d0054402c0e0301c604005c2400a0246480e01250407620401140c112902c45228620300f41c3c5c0009800900f8815001542501821128406241050301d446600a004141d619041c44807030540b8101060134180b2041400c0f0380180060401c03007511001100800140c25481d648070348520f88a619802c0070440c0360951860144590303100e08055042d248286108a51090102418801320181e0100c644c403880d172012a10348590300160b10318040704002d00601d14050b0b2254214540549644244c048015040c00d0900c4440e402e035032783c01c812104843d2649441c03130b590308826074100e092045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823215188 1250 823213938 823213943
    0x2a0108250908240a0b0105030601080c07021e0306070201110415030e15040b01120f03050c0f0d03020a1116030602090d060204080d0f02390a29190318 66
    0x50f507001801007050240400303148400c168403003035159109800031048070010500c5500280041c80060b010303501500355150004030305480c00741043e60950000d004200b81120707601c00302880c40030004c042c5c1000c10200390001c110b4002030101804411030325801e4001c1e440b49042c01b070102c0c0248641c50380240c0c41031001100c0281a10000e01c0220f15541c0f5a030001da50440b0607401010001a0200900c030000c20511340c440b910044140c0c094500310b419400003010402c503070040c0180c40f51340c66010440c2210915450b200540c40301c420320030152441c04001081d032415080107010707000180c4046240810750f54411001a207510070390000c0786800c11441c0c40205003902c00207001c90b01400c001451120350f510f580c0c9600e459880c40e81c0481e21491001035180c2c04600f0161001c03103001c2000100e030104c201c5042024000100c6000081c114000d82c1c0c0700c5035036200d00e0540102041c0070f1070b00d0481c2c1a0300111605280c40103040340b03c40031014002d04401050f541c1c2c007109148803440d20013000310f682c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823216438 1250 823215188 823215193
    0x90616030905013204110105030a0212150a09090b1801020f04030c0f090614151c050a060501022d030d0906020909061c0807142a0108250908 62
    0x50002030b001e01c250407461901074184101c0e00811025001c0710160348116441ba0800c8468182d20340191100d81020300000201134092008811800c2c44245542c03141c036181841400f081c0652040c880c040200346c0142c5511402c015006020400c0703c0102ca4104a401800091000703015a65038024041d0302c0e101d000d00720303000600100340202d00b80080161610314034085a0340741c0c2c60080c0790854415105008032042b515641c3d074110f1910000000c038044a1100440c68562440000000c1844018801804a58440903c07403001e0441c801c00001e41030a00050060b4294500918425414592000c14401c09850280b00801d01401038032081c6940fa4030030701502c0d03142d00c1d20402a4000302d070020b008040b920001030a602d4506904054004407101000b0104450740322504543c0c090682610350442512652003815800c01024842d280b4843c00b103284802c029034800f090603440118941008920740a00c680c40c10100c0c00702ca24208001e02210844030f00806c10381c3e03202c0c5154812036860 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823217688 1250 823216438 823216451
    0x501110705030d09080607080f1504140a060305010b0a1a0d060e0408040e070f140a2708120a050a0309050c04050403020303101a0304020f13050c0703030f020309061603090501 77
    0x40c1e0700301c07541c503098038200025031b85940e540c0362089561070011500d0070440740c50800424412407000454544014000d00040f541074201d0f0311030b40e200b0200307139807041265640360810028004217100e5200e00d0902128161905071805403542040d00400100c08469031001a819140050640c0300c00c0080c000340d1b2070000c05280030b06066445400600c2500750368a003800c002a000b92081c0d2000c4928079282c4c0703808001402e40b200e02c44041d0050030800081c0100000c850315040240300035210125000200d2903622401d050300d040c00c0c407162110118030f080050240c81c017081e4111040c3c42c4450301a11b07001800c0b00003400c25034580024070b0030041d080351401c0180024958040000d40c03150441c080740e40c80f0b1507603c54900c0b40303070184641e9000f1055814404540103150262a4404901c0000c10352104071201003500c0341101c100f076030510054000040c1c400c0c00c00d84c01d40905101740308030841c214114a003029031036032211001808684190110099450401e000b6800021200d41100007000706 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823218938 1250 823217688 823217713
    0x30d0305010f0519090f320739060612030e1e040f06030203120c030d02031b041502070501050c0604030c060e0d0c0b310c12030201090c0503070b04050111070503 71
    0x611240207801664241f000d4003002d2220221401c00c2e0300d00341020ba018503945c40ca44203d44030501801200d0903003a1044041680c10202c400410002d20040d40503441042607240007001c56005034000182140c010b46c1c90000f1940103a8406a20301c0140c5400306940031003140a415940211040ca62007441c0c11415900f00b011380d4062400d481c400e4044410501c40d10203a4152801501c03c1c6000c0c0358420410345105084640142d0b400110984002802801c1201c02601d950041d8004654002e040360341d00110319410000d00f0010007083c01c0c050b10302005c0d2080c2940305c1400a0020b000d00160701101703400c0040551115040352886000d480e2111031202004000e8090800e040c0c91459000010440182da480400d0700c901110400c0d8406200c6c00908002c80111070810030fa50b54200e041d000a280c51900700340001851003980001440040b82c40c014030a0742058000900a911400d820701c406580f801c1220199402428001c007451040400c851808065400c01c50301030290a418174032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823220188 1250 823218938 823218941
    0x6030c06080402240d09020a150f030f051005040218040219020106090b1c05030408100507030e0c03120f09100c050d020102120f191a030d0305010f0519090f 69
    0x80f4400c64641c8450034510a0014482089081400e02c540307081200684402e05a4400d04c11144040c08900c00c9a54031440d000c0081e0403500d2032000f2071411113449040507810701c605144005c0303961040082e8100021078601c0b45889000c0c0a000c1d41c0e002504c407030030100c00d541c102d89140c002003044d55140b83c41402080c04540b00b6003500d000d036090160100c0c6205450068188040d00035062000035001c00b4a446039110103000c081d111400200f0012074068000c0c01424504409910041050f08281030700404603108080e100343c0c02e4200c038011098a58000c90349d031010781049a0b52a0715041d41d040325140c41d1081c0510b45074071070000c49041c001107821407000301c0840d0142054070040800108180c0c281d12450840714600004100041c55a50f02c01005580010701910101480514580c0d01021190000c1040007031f0140c402e6154100e103020000d10384003036080e1606202d207501d000c89083e946c0029004080c4150201441941860030300070501004110076903040c040441d140d642c480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823221438 1250 823220188 823220191
    0x5090d21051c0204030b31030c020f030313030312021303120221390109140a0305120c130306021c0c0f18051206091605060a05070606030c0608 63
    0x1a441a4400000201048940f081d44c081780c1e000601240580c0d1000c0f10f00591064084081100078000484181460030110800e003507103100e80c0301c440f00100a401001480300099000c40d11075481001100c8150094031514022250b05042c10580742d000c01902c00040c0c000d603039158159581c00c2c0e03000418041281c0010b8550fa0460702030b244210110310b515007400d12074060030740d0501010003003081500100d80350402400c040c003030b0080086500e186104135040d001155050a40e449408400500014030340d10340440341e1031001491320f0400c40c1d901030300078016446a00803961914000415030240f26007121300b484030140000aa10341c491400d10000d42002030f614968a4880015002e001c01030f109066016545880316104220322500c2110a00d00005080c032114050f03640018642d128180c01c4a1040840c01c00b91603545000e019992400300c418109441c1480d03c12820845900d0303960840346000c4141ca4210790f51900c3d810034001400207540b0003006044071440c0001c05940c00258103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823222688 1250 823221438 823221457
    0x3020c010c0201030b10031b020a08070803061c052b090e0405120a0f030e0318100c0b0c070209151809030c030a0c02010e120d11160b03042105090d2105 67
    0x2301d95400245801326a80c0558900007014400c0c01c000e104080b40316400a507a01c082d00810031000301c401e003d040e0501490f60a03040f101d0380d011345e0001042400e00500c0c00340d1858000c40c80d50100d03002690090400301f941c8280040190601c2c0480d083c050140700c00a00f20320072000301c0d90759000e504c40042164509508000c002481d0210b1200a40c2c1d01104444000911310380c040c00203409001046507102000ba45c010620540514110024981d402e84078422007007481855110003190040c002c4040e0003c11250381c100b00320348202442c1d640c1c1c003000c591003034600b10b80101c2965496515451032181548103100ca02c8049009100140d0080000414034400c4c1d0700c3c40c010940c5e58080c03141c148054001120143c000ca965055203501c82e9003508039208800c003c46154648000c031044601c50f49403c042c1041d00c000082105108a0b8507031041c0700703203000c4c0d07403008041d00400b0002c00f94000ea034107252149004c01c4840042c0026107048401d620171204406034050818080a8044c0d800180103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823223938 1250 823222688 823222721
    0x20702040608030c06011d0405060f07113c0a06090f0c081e0d0e010f05130806061f0e040209041d070302130c0207090c0c0503030c130b040303020c010c0201030b1003 73
    0x1c3e2041c40787d80158060041354060f0041426803074600304250800c5005048004000382003132102e1144404010b04482030041500c030820101600751014a900100d910358403400a001003440c0136080002854601c0e00d802650002c1c00f1030a900e4000c07410319103024040c00305d040507140440c3c01d24010841c40c02d500e0010780c2d054064540280b203940c45400302200700010810002202d90b503940038081450314001249400c07442c01c0c140091600c15550710781c201d801c05600000030403009040013042c8810262105424140f40070410900900c48403e116141c2d010b00d4000c02c80040544841e0052181c0c10024454800c07404004880c0343c0e030361400c03844181d02c5002e0316886070080d402203100b00220484039502504c0082c5c10724101c58041c050111010702080443c0401d40c0214100b80040c6002e0050084000ea440103075012811481c0c0702508280c13010002044100002900019078160359030003800e10080d80556400103030006c20b101c00a054100030100c07566034800c3d40c1940030305500d5200405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823225188 1250 823223938 823223969
    0x306030105010510050706110408010c020c120a0b01121e0b07030507090503120708040906060206070f090b180a03080a05070524010e19060b07290a020702040608030c0601 75
    0x1000381d0b034130240ba46403001c0340c5c0030080d0002090958009170046400700120b10314062761244054210b40e486a1070340c0040c3c100c0480c0e01141c1c90104a00c415440480d40144628406912500c041d0384040c811542c80b6441440030350308010b8800c070011240a218043c0302000300d20f81c202585e40050444440001901d01800120320754024000c40d815070b50080c0c02000998005140d204041d4460102958400018000000c00e00715a02a0b8800b602466020b0b08441c00d01d084054806400c0306c511700c2c10301c0481c0500344103181c0003406484036801e82c581c1c207107000e50400c2d0105a610780030340c1029200703403400180e448200740c1000003800814440c0003101c50820308403e0200000038400c01841c2d1019240004001000030115110342003052010b12500062924120004441651744000c10940b0045200f4040c044030303002502080c0d40c82150f000c034111100c3c1034412a01070040403906072550100f65401903403606c0d8000300142142d8000c0b1395540c440e078800e007a92014248a05400c40b8440354 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823226438 1250 823225188 823225199
    0xa200a06110a020a061106100b090409050f011a01080a0207121b0b040302011a04051006050304030219050c0108180604080d11030f0a0507020706050f181f02070b0c0a020d0602070f0602030603010501 87
    0x88d05e1400c551100d90f445040c0b9007068100b001821201006071800d00c00c84100b04e0090b9000e01c40c201608241e040e9103040829040000f5149480052003092101d02c1400f252002c035064000c00210300c60585880510368101405a00f04c2200c08035000d04101030754010030003050340540c40702803802c15082101e41c612051004000c19514100c40d042c04000c4150403c00c01180210095501302d88030f401034402c3c28000c4181c2825850b02e4142c1580d050348101aa01c50780d5801c40701460300040d000c01c0c2c9901a40344494a50b980b074202410041c10100e0002d9601600c010541c401c0303e009100416082d50703414092000510550151041e001e00d0b480e120115084900000b407050888007940c0301c1a08200360050190340b150010265001c0b5003100c15556101c590b18010001c1c0034610101c50004002d03005000289003000c0c1d40c0190a640700e0401c5883d43d514000902220215030480d101e0124249515001020380130f8080300906078403d05060384e0800080b03401840c441c803019402040b1580c0d0300c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823227688 1250 823226438 823226461
    0x218090c09010507121103030a020a080a050f040212010f020a030203100e090601120f060615031b0e0607080c070f060305070c170315120a200a06110a020a061106 71
    0x1e501404030340c081101c4000907050020302c0d5420421424035403240c1550040c418150b6004940d07a01000e9400034031075001c1c94008550903084451903034104100d29059101c50039005000c2c6c0040e01c2107502000c010702c480b0702500900b4604040c03100c01c2d52243c1444401401a400a84079030010027100d08011600c100c0e5404041d100362000d800401041e441c000d00480000c086041c02d54441701a6080c12010a40e03a0040c1401000806d0031180440920180103040715100c03401c0c0d6a0741c03d0b001c00e881c2c00c5c6a0380210b0007400c010044030081d5079421035107424111841403400b086111b024614002500c0c3c0c80302420038040b01d102d900c1c240100c2e501c1c0d030740c210b07020140894010a5118a145a0201d102c2c00030065507201c0411a031b03580240a104000500700d4080240725101d40e4040d40c07484080001000001e100e07420002c103c00310740c00d0004005010142c0c03500800d4100b1106601c4003c95040c1003200d614507a80242c4032003400c544074003004001d0301e9582d109111503c80c50307000c1008804c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823228938 1250 823227688 823227697
    0x40f1a090f1e070c020402030f041b06120b010903020a030302070314030c0a030e0d39030206030a270305040e011e09020307180e0907080a030906030b060d0218090c 72
    0x200b0502c0c0d8006075000c00d0055110001034640820080500100ca006841d0f510082d4010348043c0c5810191f85014541442d152408004121251610010400c541c4c0c2c1c002c3d03c0703030781c180140a5000c1a58803c000049850101552010354010011003000040c150040b4451043c1d078003a20340e20b004203041d1100517949200f0040e4080c4607a0000b624100400e101e4012100e02e10401004c50500b0356641e11200d0004a581301540140308600305a001840345840c2c10408200c03050220a511034503640016506000c0101301d0342ca8261034a620401c601d5140d666000b001140054440040c085030030002c010b03402030701454186002140010407410420308400120f1010324030000d19090411006902940024140b50309105001095480303000054001901500c0f6501001c1040d26000789010f241096542c0244041c0d04100b41050220703600c2070904065070407505011942c0c1c3c43c1c090101c2c103180b00c1c07401c034040414804103002112285405250200041c10bc0b02103405807140d8000207820b126 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823230188 1250 823228938 823228951
    0x60b06030114010f2106090e010c0c0f0512030a0504020901050904021f120f02070c0501091802070201020304051c060501080d020a0314090402131e0320040f1a090f 72
    0x2081d01d00d802c12580300e0034090018000c03514252407400240d01c820311402d011107400705902511843d01340504004e0b8440e40c00c05d0203c10f802840f9800f40325601414020f40480094416514200010b090002c1000400050000070784042e82e40d18107100654004e000689040b80308a030104000505890201034440c02240c0003402c4154402c00f4001c0b118031080000c1d00d40e0248140000d000318010501d11070031550002c41c5102581c0d600d040e1409040b03007241c540125060112102d8180b0019554000452060100c03110050380c1d041a400140e1450181d588103590004a80c040380d28003180403003c440ca4548158410700550741c86079034150312000c0e44854080164400399103040424881c080c3c034180740c07211810141c500310b00382020800381ea101302d04004e204420301004001c2d425061038419a01d1040c0586282134034207517610380f150394182007101d8015100c0b038104803407555143d50201c8161585d104003048543e040305140040c2955031035072a40310380f440300d00003510707010740a0400d842000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823231438 1250 823230188 823230209
    0x10e0105090a0f0e120903070e090303011211100e0907090509070c03210e0d0201110f0a051225020c09060411040b0c0c1c02032e0603080403060b060301 67
    0x69804040500a12501c4554280c06131104200141141c0c1031005a0141d04000300c0c181e6503a8110381417502e0308105034840300b0f10100010402840110100660b03040d50b42003a011030402c1e200c0d003030243d2448914a241c0380d02000c1038a4003510590404403030004a041558076513103542d2014419203400c0a60320034985c1002e1210002001d20340b103040031300001e91003030601141e404440c4000e60202046189400d0307503a40d5030541810307898001c003c00140c4800910080c4002160300800b00114021207800304400d05c0082000c001060045040c5c80265a21004040c054035040d40394104a004070407134150050f0000710b1f0070708090320105040c010500040c00e540040d0300c9241c144030084c5010888808100d205000110f1103c1143d0000c4c004186410000e20707100d9110307001c129403048403c14509030580440301c3c080c01610042884030100749414000b00e00901e1005c0e940c0e100040c0c4100d0b283c405031a0070800b00410103120046d0081d603029010400008015806020840c80280940d07030300c1c071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823232688 1250 823231438 823231441
    0x90b0306091f1e0209190f0909060e030a02010903120908090d0303020f07051c051c151505120a0504020d0f080f0403060903080c04060f0302091207120b010e010509 72
    0x1071460442c0003800302c40da19001034904490000f81d105608460f6541460035000249150646480c1e140d91400714480058000b1080c0303825205070780c17009584104d020050b00d07040f110060210740d0f4043d803503c2c00d201b010b981c2e40d41d02d00d42000b40240001035044004c901c03016256840d0082d140304038220258407550761454000e00c2ca00304100080303c070354100c0405400300080108051090044d0407a503110750001c00c3c0c0e5a0b402070150492441004000040041c01e01401030200231008801d441b000d0740000000b4a00d8150000902c0125503030004100b10301200c3e0380d040708660100050488090008240b00c03e41c6807905d5820580f602900c1c040c1d44010a20307c804041000040c190903068411825641342a03607840707030030400350007035881641d40f1507668218030240740d00f00200b258803452002880b45003038200840506181d03950b0703031400304055012130601440d4550780c082d881c140880300100c03240303107a5402618400c4400807000310782901a07040001800d041403a04141a50f00c01008040c0c503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823233938 1250 823232688 823232713
    0x140f0901050c120708073f090503070b0d0501080606030a0b2d0403020c01080f01060e010903060e1f060506040612090b0109060501031a1c1713090b030609 68
    0x1c54010012420060294440c071112040c4110010048184900701803500c8001c1070800100c141004100d604030700510400001c0c01130040700d402d44400b04442ca0356440c00071006800c6074501c050b43c11554061040250201d8003484440140c00c0003120380e0414003440e80c07200071807511103038150b036420b8150f84103c8000000500c440800c5501814108140070321889810304140c000807416880c4148000c0c00d406d010038181d05024019030060700f820101420705100d4002c1c0d5500e8414443d4008200850046600a81c881c141160041d5000070040c01495142c4100e50749807211440000841003010304042a964540c0c0509012150010646820700340ba1945c00d44002c01d489160382c40041c0d0b00c80400001603d180e948501800304007000040d002e04005c0050110341c070184904130400d1445190008a94a80d548201042c80025540c0c000407411700d09000c810b600c56400c40715004022559a8419040707400b00ea08a07a08501c042c0030f2a0450401c3c19280c1e10240c42c509510f80020004564 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823235188 1250 823233938 823233947
    0x101d03070803071e051308060f0109020a1101050405030301210b0121050f010e07090b09060d02010e1206060a0e011404090809040603030c020a0506040f09050903070204050405060403140f0901 84
    0x2408100e81c1001e1160356600d031548200c41c13450340004c002040740410800d04549030f440c49a0042c00f01000100400e042401c00000030074014810752144540000b59101241c0c8280c4003003c4034400304c1c00900403400c10749083c40d01d0f0380007400342e80c89403021451030341d840720501121758004940110822402d039080282e4510071403000701502ca048545140c00d0000901c0401003d103510148000001e00308031880c140c1d034241119a0b10000c25541003610320741d4581c0d240400726030440d4080350620102141480180c5000003912170a41d0302000c9400c45000d502000701d0600e00c0344d00c0c2103e00e04000b94031291080050f00003805001e5400c01103c00007242400c142c1d0003449110300410000b41000001c0b800642501c1c0b4681080f00011940c0c0307008421400e203185d4407409408101c03940d0f420300d410001c02950400851207103548458840c404264010018003c682d2001c1d0042c0c030a21140c80d0504113640d60380070558049001a280b03065104103a02408161031100440500080ca0070403003400440d0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823236438 1250 823235188 823235191
    0xc14061b0c1203070302030f0c0c03120402040f050907030606050303030403080109092a140d02010f0c080903100b1906020d0e121501031a070e060f0912101d03070803 73
    0x3145486141ea401c02c00380161800385200d105141e41c0540c4d6490103202002101201801d031000c07060303081c840b9030442c4801206648803803030f00d81030500142e0346a00000c2d015106c03050b40001400c0c038000074049809030110b800010b0340e00170321003841420780d5031051581e00e1204441c00f5000944030001400b42c0c04003908440c6e240350003180b4458880e140501c2400c10039045903440900c030758811404120100d9110010000440100c072030180540d4150006400e13000112020820094103074043e500f00000384080d21800200a01114082040a040a40100400200e00381700c0d00030300c50101000c00e08030080c41c4c02c0c0c40c1d031980940314141c040181a40c004002401c03203603000b81070b00ea06920f2400708018094a850042440e0442c6501d1428161094004909d4041070420002c080180d1b03140c0110340c51400240540c2c210342c1c0c5901c041c1981c2e00b14003031880b001c0d501581200c21495810f00001e0b080d0b000d025a00810481c03501460000300080c003a50340e08181a030400e002d0440031910640195 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823237688 1250 823236438 823236457
    0x90e1311090a5610020c010306050307050d06050601090314060601030501240f051b01050f01050a060e010807050702120109140304050d020907030b030604030203070b1e041101090807060c14061b 85
    0x103503084083c010009250741c0c106656100103034800c84000c01e40d0b6906024280007040e040d00502001818040800c0b8400d80080c409825a40c8540201b0701d030b40d2042c060140150380000c0d200803100c1000d80801c2c0c0710401a5000e60000b8100400420042d44812400440740780b03d0000d10480094058140c80c6080080c015a0030700805100040fa03402d0b1074881c80102c04000e000000b082d20f046142d03c1860356041e0826809151030280621071590001c494007210402401c0a089030340e45c0200031a094800d0080081d00100c5075605070a9050054004448841c0b04803882c807001588401c2d49540d82c002c0d481140d5014584040304c0c005428800150b0f600600c06250104e404d40d00040828603100065904800580c40040c0c00340034490006001a040b1020f041558040c0c918001c107201248400f80c006843c00b00070301d4030114584e00500c286c00c018180c40e429514640d50318900580401160350302a5000000d0400d000e03030282c2c001c82c2c3c3c0b030b00c030340301d600780c0c5401140e40c1c030007510b40540054048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823238938 1250 823237688 823237841
    0x41b12030c05010b06040f0509070e03060718120506060a06030b010912060e030307021f090c2c01060f031b09030b1509190c090e1311090a 61
    0x304e0342941c4400004001406012268145051410080c44a17041c1c0c0207180a040190b40a00e00800350340108410b40c200d00645490f5600860400002c2010200780c1d001e50075010745681c11404118010400398421031080b00c2c61440d1a9a508007074064a06821200c0e0020303103002c4d024000c1700d0010414818a074061100051803a091030011031070740e442618000003507030001040504e61040b003408400c1c5030488a00911070041103590740394030150700b406030110404074410f01500900408004402c02d1803403040c0d5002d15652400007410282c12003181c44d0000e82842c01409048005440101ea0303070010750303100e24815246850301544010064084105094101e143c000c4c19900d0150b05400345001d02610341c0c071004c41d40c141000301d0302100040c6050090743d000070401c42c180b00ea58079910141c80c801103206e40c1110702d000748c1100c1644440c643d0140d4440113200b1203020341c1d80088824054844a40000b50011581d2851540c4003100240d81c500360100e113500019906250b0602241c09560 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823240188 1250 823238938 823238951
    0x1f0b0a02032724120402010201090609060e0c0301230916030303020912060601090902210c0a091a070807081c09050606150d0c090f030605041b12030c0501 68
    0xc080d022441025400140d00e454401101c00920f0107890301d40d00300b034006000e918002c02003603200c801c6004405002010401c200c00140c1964001c5d044145185e0380400100007400d007a241038001410000d00d205098410310300004a141014401d480307081b400611703483c4207000314401c010780814005118460314081c4040c0b0901c0009529860005035120740c030096100d00440c0f090005c5a50746000440c100e41c051303024052a640c00c0419801a82c80c0c0c400d0141c3d031007540001381840100243c2d4101040d499001c100100401d101c2c02902d40c0c65200d94a030300030307155aa291861010094a810f080004c010402c1d01e00141007100186401da00c120f40640c00d1800303000c4520341d8040004405400c00340c6034103e22040081c18000c4507480b61086450045051580848070b0190003808402d81c1ca0705d585182c0d6220003401418010014218100c0401304035403a407800c4000b40100f603904a587d0394800044003141d40a030080c1400760744044103126242c9889442c100c400550840741542c11b5540c445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823241438 1250 823240188 823240207
    0xd020a1203081506070b070f050415051903020301081234030e0415050112020f2a06010510080a1b03090c0b030609010302060d060e1009051f0b0a0203 66
    0x105540105001c1d445204107868038011000900c01c104034400e00c20007081241c08009010004901d8205110707241c2080c0b2184042c006852030320550700075108889804500070f030b00383e178808010000030b0001c1c80d0070f0001c9003003200290280c0c0002c1c0114251500700800c1c411889902401410344034254520201b40f900c1c0a102ca440c0903181d10341000070460481c0307030640c2403540001461030401c4059408000d0260082c0f898000d4100318001c180c10080d00c0c0703241100501e00c50701514a6612031403401e075030313038128030102e080704908a06034207000d0741501a5028560364003140b81030484001a2420120f0008001304490206c40100030f03144040c2c0e54410380c580c40f4407400d0b003064a68225200091003003264100206104c08650081d1900d1004008202c620340365149002c1c1102c1c1d0544509451701c59812004c0060b0076581c028001b00742d000401c1203406202c042e000320858a0800c0108000e480d1150710070300c2e10b184505081d4000c00c5c1810204006001f0b00004c0420751854411340f0304045420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823242688 1250 823241438 823241459
    0xa060603031106060a0e06010302070c090f020a1e0503016c06090203210405090c0a08180c09091e06040507050906010921121d0d020a 59
    0x90304298000b88291007410308240342048201c1d0003850886108440ca4034006048840c1d420060500d0b04054000c581ca000704180b00b40c140d0b000e4180f60b10180000341e04030507000700079007008010100042000041c8400048540c1080c07841180d160fa603985903038241807007518007600300341c0805203188003050341d84d4203900b9884001d201ca01042180c03411032036051207a105c1c80140c076135501c1c000010064000602d0070060701e0311488164001d00210342e08015000090a002c110042c0c0343c1c00300941201224215144401403041d25800c80e911880e50b2034048a126040c0616070182e80030400712004103000c03074820708034450341d858241c00700c40114036008041000260140c46a4a46610007401641240242141a400003425000805582c5801d450b055510842413184c42d01441d60301002c91426407150b180c076409007078a000044003024200000e000c90030740f9100f054804410401c24022018400c408210700c1999802c0d82d1801514080f040112101074000d0482e80007135440c03000200c1d6001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823243938 1250 823242688 823242701
    0x3040909020a150306061101020a172503290904060914100b040b030613030311090d122a060f09050f030a0813080304120e1327120c050a06 61
    0x19500418171a1038800068014004022118091b90060000d8086c0780e0344601015081171540f50304242032745940c601d20a101507802591074003807485c00301c5000000c1c0c0581100c61090b1014000e001c44c11520b80c20758800030601001d5940c0f0010003400b01c1d000c24040c0c0c2003080802c0c0901d1800000105113105989040c0c000d0000006054440e4040c0925103042e01c19001059401d03405084c5a1510403180030450002204c003c0906683c3d92101000309800000e89003100c034080c00400000d060b5091855001e229085034400054134940e8440038802014a00300f00030000c4250481c40c0c40d029074a49014190403401182c0050b511f80c4d210011400801080000c01501405941d40c1d401c8540001d0070300300010541584500c00044d600002207581c42140d40c0103400c40c2c8801c10008940e6012200c09880741001a8800f00315403064410340300c41d51082c0580c90044584480d071036404051944202c8140030082e08400310841131005560082e121400c0c414482d4094400120080e5038140480c1d07078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823245188 1250 823243938 823243979
    0x20a0c0b0105090106020304210b01030c031b0e060d05120424110309040b030a02150406030b041104120c3f0209041e050111030a0b1203040909020a 65
    0x4088604420310221815890141005070b036241290b41c101500659a88101c1c803501d01030700740c662200b10b110f51515044901305540210004440d5941342000c14000c80707103001c140d4504021206010f48094042c0c200d0301200d125508004095903880d003000186c822004050302c0c039004017903000455801d610b0061006d08407402480d8034905002d4600130301c449d0100001024400715100c81000c09a00106a0b00810300403140880e900c0c09c0c0a010a041071141d100094000018045982440e000c81e4007074000c3c0e40c3c40741c1c0c1c00c21140410317030108002d032500c20312055041c1c43d00f0401400109030f00903044100c2400b8055119109070303035194580031035103200f0341540401c1000c80107030382914140a18019210f1200310b007405225242d00050703030b0304001400081c0244565040d40c0c040ca14901e1701c861815070041c0080040c1c40d114420702c0740720341c030803600c1502c00c9242c610054481c0c9089004d002905030500c00941c102403c10070450300500f0035000980e440041d40000180c0941450f4504c10303a443c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823246438 1250 823245188 823245197
    0xf020118170d090509070c0803190f0f1503030e040f021912050703091a09281109040506160203040f06050c010b010306050d110609120616050406051209010f020a 71
    0x90b000010000126904000e105480d52014800d000d40c0c0846080340301500000520741d03c0d1903100524503108181841c1d40081400c041c0b004032000c3c203961008445491000040c000810020300d91004608c49000007008202c0041100c02c040c2025440a1209001c0c10f10040c542000003995018400703901700700b00300094028240700c03154411806100d40142c1141000d02c040703640e503030704d1082e020070031602800d552030440c0014120040401502c0c48801d40507130144562407012441a02c403100900d0142d4006070750403c140e140f810b000007811b1084e6084400303040c0d2070711100450589804009a03000c1144024031001c104101d48554010040909407a85550342602c047c0350303400d40308400200c41c145440c1003420002c903200e0706a0262100c2d40a003030394420003403050014142d800751011058200f030400c4d58650705004002035090040000741015200290900d00032a400d20460091000244040c8900342d4070102c214252030304015400008100140003d210388202d03000340c0d00140004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823247688 1250 823246438 823246453
    0x5030403061d0d0203040e0408070f06150f171906060b040e07030f05160c0f0813260a060b0f04051501090f0e061c0c09050403030b0d0f02011817 64
    0x1402c0c10809100164818000b4604181c50002e01c7d4840840042000c1c0c952000091000200800305500e1600240c0c407040810219101c1400b161141c0c03c0e41c02070240800c0e1031a00407800116214007415482107640c02843d01e40d90310255200341c00c2c02c6040440311071b0384910780400d1502410014001400e030b0702030900b4140c034207035100409441204409014203407402d0140300d03e4039100c030100003410390315003403019800215107003503521401240000b90101300003180700d502242c011500340342140d280f030b010800c10b40d034988041c0c0151111441110400d03880292210000344180d00a60f001e00e1008143d18102c51102c00400e045d90411603000d0850160300c106441c266030003485c020081d148807001c480a1a0802070580f18880380603200310b120316854580103505403501c402c0c6076080c99200c0413400e00321380d64580100190000742c80031004a42001022a22400c01c21050182c00780c1144086040c1c0740f0940043d0350035094010500c07000c0201c002c01281d075180c490100004e0103250300c000c1085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823248938 1250 823247688 823247741
    0x1230c011104050303040303301416020c10020f030d0c0206102d03050102030f101502030f031302060a08040203060a110703030c2007050a0b2a21120906060102070306090503040306 79
    0x34ad400003402c810140c9141c980c079000701a80060182800d80c1c069445482c0c0144400c000d83c81c9c01420055070364207100c0002d040016040a030800c0c56000345030740032a00310362500c515040711f00199019203001120100309400210711043c0caa05184045040b030100f129440761101420780e8011180600818038080602c00e565071108a4200100f002e0002c0c00c0f00d80c00450740c001d45a1185a42c109244c03207012010031507a100c807094400748603038001d080c250f072120340c0140030300886011101a4031901031840040ea03100d01034001c88900f03209401c070252515403940da054000744404074192082000001494481028101c6642c181e40d12610007040b20f6490801001481d142c80e41107034506410520201200f94626110000c0082092901030145c0c0c0e103045555241407822110000d80301c81c003850800c0c1800c86940106070001400e1311701d0409544401c91a9070314841036401c68016440452304001040f455800a10303424400c0040d64a85592500c40000340c0e5440c01460724240030690b01c2114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823250188 1250 823248938 823248971
    0x91a070e03280201080a1b0f031104060507031b020901090902090a0b030c0d0f020907080105040f0603050c01030b13050906071b1208040201230c01110405030304030330 74
    0x20400c103502c26070a00c0818282c0b410610744007248000c0c18086501c002c143c03001c24540005510380384a0315020032409007040c00a01020341031a02c0804246000c00c05100b0249050859054a0064076158505089076504454080d040030f0003456166104070401d00594807501e020340244a50840850b068603a03004110b103040026040301481850b03e1404000c5450200b801d240050084400e038140c40184d090414050001d00c500950241801081001481d00038075a18140c07070040d02c0400071400e21400a50845c0e509020240090b40b01e010035080c55882500a440094006000c12a41d500071122481c00d442c0140c4074541c164010702c0400440a40c0503030324100500d1000e1610300c002419444050034601d611030784008024241c400601964011480410384810a50155078101d00300142d6010341c0d0042d0740c645125508141c102c2d803402c1804c900761400d1380e030010b0141d8540b61942e0f40c01d84403200001d4002341013111191610f0100c0f84400440b010781500f6050114040700401400003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823251438 1250 823250188 823250203
    0x21c0e0907021e03041421030d09030f0e13180203190303110f0301090906022502010e030a0506010909031806050d0f020324041b02210913091a070e03 66
    0x208941c000e0200300103201080b610340898000c191f45042c000300304030303422102641010714404502d10000480207215110781e4003d01d01540030381d035189452100390710105d9080c131a14168980c407151060030f142200c4003a5015401c1040c20004e0820303001650780c0801d0401c40c03aa5124644039140414000030305425000f80b0b51154103040c1c0241c542000400300c0d10305c0340810f000d0000c051b07660b10030701400c2042aa0490751243c9903840c80c40d400c00302ea1150410506040b00040340001ea03000812300c05810006040c3d42d11a0780400030700826803d040300740008100407c01a420021017114654880804c100f034003002d40500c0d9030300c81d50cc840200303100058a000d2404596614810410000e540c4156a443c1507484515561a80300640402c0010040c094207807402d061610300542d40c0300c0f61500012440f107100c500a400070144207a501c0141000c1c040e2001c400d80000c1e515082220980f06984400340640c4602c0d0481411a0a903032028840c000894228020400d141c0e100780b81c525003040b411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823252688 1250 823251438 823251493
    0x50405010b19030605040302070b0d0209031203130308100324051003030903020f012d020c0301020a0e0d03090801020a0e0436050a060f091b06021c0e090702 69
    0x604011030140c82024054482e4031001d01103a54620200b41014403e011170f40050103051600c0b6141e29a46080400960004552a11910450140100a507484000e6900c41d4a49035800510340c45107031010f4920400040c0091040303030b00300501100040f100980078140040030b40c2050006900c1c50011411640050051040d850b5207507404c00010358040f03007000c2940d906640c00792041800c071300103a50040900c4022107003040c0340154400007001c840440c07507007903070b0590840c1e0300c21000c00c0a16080740705141c41c080c00a800c09954015900b0b0000c0300c00e01003446843e280b0000c541d101d0300642243c00c280982c80004000b01d000400c02d1070316000b0000100005171b12950059200c00307400c262003a180510710841a0484201d46c244038040c0905028103822820500035020005107400040c0780c0341c141101d04440318502c52840d03280c000c1c03002c4160741590b002004035501c2c0094034042001065102d10401c51000402081034544009450150800b40c0040c040e92a07040581020303041c040c00304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823253938 1250 823252688 823252699
    0xc0303090c12060103120f0e0a03050c0a050a14040513080a0903510f062c01140d02040e07031203020901020304051009082406010c0b0f0a150801050405010b 69
    0x18008501c1c2146c031a021141281800100440108816501c80c8100b15055501101c3d81d280002488808a41112502c208440c2000495280d07001c00c0100302c031b207020f2211052a07420000c00b2908060b40842d8100e220b510b142041190984e680c83c11541c48060010002509684100308100d20f61441d0041003484000d10150585048252080b10380406035188940c1c80c1c6d6002e01c003017090001808400750f0785010f000c1c8987c03844400d2003000b400952150751040c1c01c4c81750041d50910080c0c03150040880c460199680d003646402c04900a030040c81701e81c254815004456003005030740e0f910401d078460380800c010f0b001342c529604040d180080001c01c46414103004000c41443e60380d001c4212130503075404071484422842486011240c0700241d03080100203104001d000d02c407010402c030388280102c00d40680021140d1740c410045850900180f8020b00060048012400054009810551103803460200107032400494140c02c50900c0c6a0340590b0090350b4440901c000d002d0280141c003603075082031f9035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823255188 1250 823253938 823253941
    0x906050913081e0910081605070305070318170c040c0203040f05190f06020307050106140105030f0916120b0a0c0503062205010b0c10090201051804020c0303090c1206 73
    0x16070603114403c0d8400d441e0080c0c141c65402000e4071554003510307884000640000e4910305001c001801c45c01003942d00d25050091030441d104a603214108a694569140c5d4802d03080c4001607800303641148a00446c0c01c080c481340380010804d02000029111561201002807004182540900c01165a218010002c40d00100301c180022441e12502808981069801140d40f07032800f4100020410282c014442c6840410700000340240d001016048041c0190001c105050b562a0908580340314130702141d000ca0000c0c0000b90031200744a28240e8821180404d40e95054000808159421401d81000315452152192001032120b6264240d40c80007001d00300b0004010500e034003410034000101043d210345044126040b41d405074020940801607003181c21702c81541c40e800c91211541249042e61040d1003034a59603102d520240c01514107140d01a10717014035025554400003e140011707412640c000b23408010444902d101040107500c55200d1102412803502c070b940170070a961010365501d418981c000750 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823256438 1250 823255188 823255193
    0xd120f03271a1b180405100e071106010501030203180a080d0e0309030601030b2203020303070f08131b050a030b1506070b0754060c0204150f0906050913 67
    0x3000b0f1000d071001001000d0700c4204020a0051000120b54a6500207090000388103c0b0600342c9030580690b403011340d426440f61f071340d503900700d491080204e511186640240e00401040d40640d00540d00400041c06402800040000c0e40d0301e040b41805c5c040b22402c1b0001545e1a175010305100e019840d4a03417001441c60103410038000b950311038040c040900001100d0010960030304080d210380d1a00f14061100e105807940390300b4040d403207070402c948440215110403040768003035100d50074580c030440c40b100c94508140304035100e21155905000c005900303c9080200030a02d40d0782c16400030000c5206054100741c2e071908641040c1044503081c901c0e4041e540500c0000300003480429644e610400c1031414684c141d43c10080c02298804040302140d8080b91442c040030603139020045441e8140ba25440c40d501d0070100720805446c2011841004001020446441c0051030075410038140001072030ba1503100a0340b58603032803001010b40c0d0300c03d41d01035540d40002c018500340740d00c2032a40700c4030b4408a2020340c1c600c0e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823257688 1250 823256438 823256461
    0x41e080303043c0821090105040308061215091204080105041a01030f03050315060a0c0b252607020a05011802090c07020d08030a0e0c0d120f03271a 65
    0x8010080c1000300104411400301410342c0e502c84005d800580030303200c5040c03c0d05c0d010f008084c16542a400140840000303503c0d400d010f41045901c1c0070040080281c40d82e41565031150100280080c00213018490a0000070007d036005000540961000012582000d2400248112a2114a4081c0ba03421170042000c64610034140c0002501410140d5a0707955900c40d44090064003407495900500118204000961084000070524400c0450213110740b280980c0c00c0e3750700388109900e104049901c2e05081c5082c0b2806000705401c40711200b6204108044e080104205801c65140006038000207040041c0300c4240255041d4400c00c003810b07900e8181c20303004150303201c10003080e030007004070000750900454403130000c600c2203c0d1300269032a4480c240b025801c005011100011407640c80340081018003450680d50180c3c04076440b40c1546441440740c0b40c15902c414800c41c5020915959146045d21007202840090b00c001c0f91900010710300301180b411080c0c182c3c4080300003071110b940ca020000108002c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823258938 1250 823257688 823257803
    0x20f060c0a051809041101200309010f2a170405090103031d03010c051e09060a0c050703120906110c1008130c09050a0c0203030408041e08030304 64
    0x745400c9540d43e0780014160440d50b421801240c00c55034001c00c000512410544862080201340d80f410b03041e00b0b4404c40c0a14880c0007040804842e042001502115801503c1c0513003552668107240304240d000480d800249000350381603100082c80d03400c5500c1001200070303851040380d15207140300d4100340c01d280115545c41c2050100405202d0138043c0140d000010000c079491104004000340316000d10b1000007012038008402d00020141d03003130716106841c6488425203e0401d0040d0050f800d02a01d60b504032005020800f00381c403507005075440031000c21103180f51904603440030713240c060380e0602c0c007100244070302030345408101302e50009100014250340c1c014000481140c507107444000ba07100e2084291070002d0401005251603141c0d6800642c1c108035822071840f44544c00400c00c900308091000313076224401158010000c91007044107110b820724000d10103408801d050b0398851003e443d0b240240c5580d1007950141d508510144a40401050000a608a810350740c0e1004084c500340074100d0704c0c401c02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823260188 1250 823258938 823258957
    0x140a06020a08030a0e030a0905030d020c0303030c09122e05040b06130b270a270c03060914060c091e06090418060c0518010302160b01060e01020f060c 66
    0x38000045400c8a410b50407000c07005d003607401038035030300c0c80d4100c0058804e60300c070b12a96000e40121144007040d54000701d03030241c68900103400b9500c0c6645503590f01c2e18035844018041d522106599034940120010440c69030450141441359a5801c400307104000c1c3ca0b001c2c0c1a000c03c44c0d50800041000094480021036049070041d100300a0742e4960110394400b42c01045041d42e0000c1044458114100d24034040c1c1d00f0041540c4d20a00075511090010807d80701800150181c4c0d40034a410041c8207425201168203050007002c0e070104082d143c1e940d0105680690300190740360240c08030b03c54030301003081c008107400134850640c0074a44074404022070400d01030070303a14a1001c0031120000401c0e442d03000c200c03408190001d00070084180c00000b6507181c00e0407514103070f44003403526000460583c01002198820010340071001015604500110041e502c4101c81e654818805010440016400301449000c1c12458a89109144404000a150040a000c0200164030040600482e020540f040315101e08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823261438 1250 823260188 823260203
    0x1b02060901110c04052a0f3421081605090f031e1507050d09060f06090204080111190f0504080a03081617010e060f04020d0204140a06020a 61
    0xb82050030440c200118031203d650824140700c03c0200081c002607241034200103080d507200b480e0816942411030350159101c5140003031020408d42036040250b2410300313a41c0d4803200030b00220050020344110300e0b00040c001154801003182940304a04443c412508044031285030002c4c0c0c62402664410000703114000402c103101000900300b640752507440030815420009011686090031740100240d005101181d001554080c50a02003108005085900d000d503551340d496904160510250500030a10703407000302c8501759141a9403080702010b024620081900c02e00040c1c48510b008480c03425a82000800b100d59407041114a0900c0f41c49840c1081840e82032900480900440d4000daa4900c41c58004d103903648105110441010303400091240f1130300d414440c2e0040fa0710441002c2d9080c040100c0c20b070708061031400c0144030080f03084034904e6200388010700c20380300c40420b00e0108007240c2c8800c120103102900050309110700d1050b02c03110b07906004c0c1501c3e08828a4600003009480304544070000b000741 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823262688 1250 823261438 823261457
    0x902190f0e150d1b0201140f061e04090f0c0506040320030109050303090706030c050412110103330e0f040807060b090a0c08010602070803120612030a0903031b02060901 74
    0x6400b42d0203940341d003401190100510080d080c01403601e903480c036220b0b00c01903080000f804848000528a40e0040030052410761523078582c10308018280d02e0b41d8241104000380d0f4010350700c9a83da20b00400074540c1c002e5003091418030f0a800c10762603c022a801488c01490100000c00000d0550800d00c2c2106c0f26100d00c0754a03c002d0800000e0141038030800c040c00318803000c030030710480d500045640f10031103000e514100400f95080c0d4095a076802281f044a601c00250740082c004103000c40f0003016148014500021800308444c058001503030018440e0a0481c00000340814a40c45801c2d0361000d0840403240141c5407070300c405071b003a9000004100610202000c101181000a20741080c1e28200740105038000604d0001d1800005207140d000440000d10000000581131b40003165160607201c00c40003852611a2b1002505500500908250380003038501d619103960b4081400a080783c2c15859589400c050301d541401004113102c0120b2044110310b0300b8000c401a075074581110840315007801e103130500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823263938 1250 823262688 823262719
    0x60807030204020c3306030c0f090601020106030b010617090613030c11040f0504050c040b06030109091b080c0108181f0f0c02060712051b0306060408070902190f0e 72
    0x1401a03da183c08200001c11600310f01c1090a08204421000b100350803c4082e1b03110400c0560b94040b03100b0513508201c09407505145401c044440541c840018000410b20303a64070b0307640d0301000d10f090740b2000000b00c1030300c69020103a03440a40f50703030001340354401030046040040c40c04620000300c0c5401024000d04010540c00c00145544c44042000c0c0100702b00724500c1c5000d104801b4200c200d401311145d005e81803022856142ca0303c18603185030005800c0b0b5046071b00b003101140090140354002e80f00129020f070381c1e034407400e05a014030300981842800351130b480301000d002401c2d514010f080c50b07082b203007801c001429900000400e92032000c108407180001e0790481c482480149070865a01ba40c080c10441c60b440d0107500010f4060040366940d8a071041100260448002c83c3c0c1c080d184014807060b420314001121010320081c680096006010b03a140c41d5603516030529180c00c0b0360100010710b4002c561072210113044a0440c4e8074580310304041141002404004140c40c40d09400c0a10410203241407030032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823265188 1250 823263938 823263943
    0xd0e120f21040f06060e040f110102010207021306050f010504080a060f11160302060c041a030901110304050609070b040b1909080321060d03051801050d0912020d03060807030204020c 80
    0x10001d85150034201c2410142029000c5008400041d100310382003040020f81a21100001803003650011000daa008451f035440008010a00e07404504564083c4a1440580c0c0d0345859000300782c59414002031950302c1d140911400f00461950039061100070702c400c000442021400c0050154001c80000f460192804104024044441c1a12008102203003404c000d94210030381101d118025000c80c1c0c3c580d59a000580d81c58420740c06180d100896440b520740003201c061001e16000742d420b400108602419220742d02646e0030032a0207443c9507028105000310f80500f40403240c06402c10b8440686170a0030701c102c80d0780c0340c41043c42e20700c100c0048540e1390204070b102d80c501e41c1c003078015603003a0703035851654500c007060020303011500d48003550303c8401203825440c040071440301403581034131b0755030407c204411481c0380c5540c0143c800741405400c0100c8440f11801c1c0c82a0300700540f0441142031070980f4824024680b0200c48480010300d890038100b0f00418000195032011aa811180035942d02550b444250 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823266438 1250 823265188 823265227
    0x302031e061807200318060705330106031b260a0c08150109060c03090b040e0f0a0e1c11010e060108150606031305030913020d0e120f 59
    0x510160000e0003c266880207134141c0746a144414018111100c68206071680b148120407031120f040c102505c0f180b41030100140c40100d0045041e1541191030110f414080310860102500440001d145071911001000180780541124a400c11120101942c10303004031480361f043c0c005100300c2e40c00c0b8081d0415143d03210030700c6c106645110103050038511a090060705120600401180207c000560703c50b414dd2203003400a8016034030036401038541601610031030f58415041d81000301500c004a00c0346900700c000c200500b00001a440c8a1800c40e88003000e90f02c0240ca646001406d24040c4810807900140e0600f00c0c041c4400e8854500d400c10600f039402ca805030440003515420400d000e128a02e0205100703048500c1c0406542956030703041003a941200080303900c96030240301413020944a04110b03542c6008184100200c1e4a0040407400107107a0300c91140c10080000c1e000603070580401401e000307a049640030000101200720702918a64004d004091505004d1800401c2ca2000b4500700d8120a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823267688 1250 823266438 823266469
    0x20303150d1509031e0c021e0a0902040b030103020a1e0522090b060907020f0304060503040606120b010302040f0c0516022d031c1b0302010f060b03090106060302031e06 74
    0x800080b141490060721400c4808044007030204582451005140940300d141b040ba5401030a4100441d4010148907440340500201500547c40c50f0000ca411440d520060014050300d0542c15165851441040750240d03461700302c03041d45440c180c50088010030f10204402070764021140451000ba80303003245220500e181c202e07061a603040080d4a01800440400340b0b00461065540f682299a015401e9076240d00750b40c8010181d620802c002c20071035200307001445e04a441040c0c042100d50f40c0d541c04c01040c900b000801d44003191120700400440c5060f10030412400315075042480004074004000d4203500402e003040c0188140e8620b000215500c0400c0d603071401c02908062102003020f5a80329500112400c0603074004e01c290384e9082100101010b19058a812542e070f00400c40c52041c80703040c00b80f103224000b1010342d900c444e200d039442200e40c003642d030250812035902d585900d0281072003400d488150f4811000d1500c10018030110b040f00e0840d801103140003030807820b030907140d60010400c0b00c01a008074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823268938 1250 823267688 823267691
    0xf0510111612110301021309240306050a05060f0a030807020d05030304030801140604151206150f02160303080105091e0f040303050f2211030a0c0602060106020303150d15 75
    0x100c0d000324054402c0342114058407000c0c840b03002ca402407508038070031420f003804400d10ba26001c100f400540d0b08580c0c51403e00d104a00d8213140c1045044c45040d269400450304141c440042101c080140e00caa20350060040f58241e50003072921005c201a41c1040c000504010000280d21041d509d41d1601124625800030032682c3d41e1400e4180140344c01000c0c0907000980b0300f4080340c0314107494002c040d41d06440a000e80003454901c0e040003903c41024a044918a803030b280c02000510303000c95004080b05610545075140e6118188c00000c1c00d01c072402e00807542805d111042030000c03030750003070501d815108159512002c43d2140c0c050b00c070205d00c58207070050944010000300400309400c01d560b14041c0344030b45c0b400d00c483d44400c1004400003004542040c22220707a14000e5024014039454103031718601403552400603c00344408a8101514400d0a450501d0b403a20104002941041050b00401140c40a103045041c40c880d141140e03103141306610303c0b03003c100c2940780c00d2001d540144030996562140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823270188 1250 823268938 823268983
    0x11a090a030c17061305193e0306011401080705040e0403020a060e0c0d0213090c0b07030f142d0a08010905070f050702191206020c01060f051011 64
    0x30307200702007903941540c1d080314000c59012812012440c2c05904115601c40c1c041d140900d4207058014581010000544081081e1001c2041280e02007050310400c02e514001c0c0c080b2011088c0ca0340d1005921140c5507400b0b58030100c010462042d04c4813003000a04002d02c3d1035685920b500000316040d0085400654500340f022051000b05500014144c07241e034840d03507007400222148002c080d107400c41120720b25007120008904100518284109403440c0941d800006182e12007501d4450049036103411040070050000703541000e25400c142ca00803e5040351400481138107503110303040460301900c104101c0400000405140f1618282d450004d6071100074040c0e0b0701c0308003004005206110a21030003074103078074080201d03c0c9c0300d2040c40700c100c18a03295100c603441d011080c1d09000b621075121649001c003200c41100816484c0380c2020081015015030f50242e200d2045480160840309203910402040c00145010480b0351109244d004050700b039424840001400801081c0c2082881026601d5154a808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823271438 1250 823270188 823270199
    0x30a050c0709020403050c0409080c010c02060103110607032109080f19140405090a020d1107110a0e0a020a0917032805220509070e1008011a090a030c 66
    0x40252540e8034400c4100c0d900310307644014010491107240000741140e000308802c03e50343c0c105a0000a4040d204170540c500e000c2d5681034083c00c55481c40520401078020000400502c503039400c1507141c0480440f030b01032401019650242035114400703902c40d180c00040401b682156003c0c1d201c4010385410280b815901d4404050319a0f140e840201060130340c2c042860401a014417820801080240d0428554071700360a2008206202100034504410b5940801c903100161405004076800036014410140c0c030b4052510f803021720300340c6034040c881c09020324040030007903e00a110f81c81e4120380f00e00380050b1b60b41c15601e003c40700c00d003154000c0240507040d0301d0315008005002008080392240d045100c00f40c24090750001d019283d45816100004406000d45010b55120420140c50403003007144090361035990344082070324140d04890f5400801c904c1c4039031180074284101c09180706403662a140302039605211150121050074903401441a0006c91b10500e281c54801054000d5508420f4440f0090b40d281e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823272688 1250 823271438 823271447
    0x30b09190309031406090705120f2508030a020601060f020109142a100e13140109050604020a120c140c01060603062403230a06051f0804110a08030a 65
    0x10322040380d1034144440c10440c20a00400d046001b1000038019150061400d1700708109040302d90303c00ca810b4042c418021040e946c040120031480284510040c00d110b0300110482d02c440070302da003d90301e5a0020014000b4890340480c3d40e070705480380740c10103040396050050f040303004105101c0d0080184000d440b021408003c0051103840c480c04141c400d02c0c051420b00e0388005040d03808a645030700038008811400707909000d0080d10329201c00160840140c2e03000c00ca01e11040c0c0f1410024081200c4401b070050241c2e542da80a115880b1000340c41c10740c600b1644140060204103134403500818259600700011005201e400640c11014803113500c0c580b41c020121200e80241460700c0f50320007007407412000141c00c60b03028140c11010301034540b0004c2c3c00310850806601030203d01c020080500080001014000042c229050107082000400500385080c0410302584030008101041401c0484200106503548071005650086c2d100c1c0c0700c0324211038140003007103541080f90003041d41400f010410805040d0b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823273938 1250 823272688 823272707
    0x30607030516090501080f1308030f10060306180b150418180515090c040c1d01051e09030c0d1a06010507080a0e030c0a09090303050f090304030b091903 67
    0x2020140c0120b29003014041d291211144a2140400c103c02d0014211244250034154000ca84a00195410000f41d0742c14a040e40100d0300503103c8011070050200c0c8940299001010785000d0400308109828441c01803d4880401070240e40c164130f07880d8500c0280c0355109501c81c240c013180d003001d45960f252001e40540100d6120202041883c0c18510049003084000c907003030058100c400303481106885919031003080402880d403c0e4034400c2a903076858640722417082800194003681c8141d1400c90803a659035000740240301140c1000804e0055a4003603001140445403056840b00c0310350359000510119007420402c007102c0b5031000c080382104040c441d40380342401081c2e0440c030a4950558403130f80152583c0c094601c024000c950f040c454000703018090160b9402c060b90080403aa4200d513120002414000613410080b050360725901c4203020144c00d40a8142c2040200c1c03800e124501d881c81078169030b80220710015104a505e640403402c208000e1007840c5407a1412907848544059504020382000700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823275188 1250 823273938 823273951
    0xf01121a150f0d03050915070512030a0e010c090b0a02190c05030f030c1009022e030606090b0a05030c0d0603060c090608100608090c040501140306130f0b070c020306070305 76
    0x115450a00e03264546000460703000f60b41911440c1c00c1a0911041c480480c0e50f8005015504108001c180042001080b100514144001c420343c0c2c4c80c58110b41c9201503c0d588400381c201a0b05200300c922007150032940f01e60a665602c80301d251101500c0c4d404a01e4420070b0f4010004940c01803910009020381112950142c8005404450030b042c0004c4c40c103035807407007200c010000c2e80e0003c224250807800150050082240018200303034040081c49000c2c1c0c80f030b55242d104941703548002c280d10151036070140981d00041a190400f418031500e4070f50500c269100358061304040000010010f2001909002078400700400003000700700700b40c4c81c0d01d0b218000300303142101013002c510110400940d244c0f14198031032040c0300c50119105030614003582070b548250007919040349406420b880c1025038070346119040c002c0100412048803000d58200703150800c503014065141000e0442c09034800300c0c5800d40c8445c10705074080da440c8155a2024401c0350641c1034210001c0d81130144009000c010303075154000a0003041c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823276438 1250 823275188 823275199
    0x2070c0e01031a1303030911130c0305010611060f0403030e060112030311031e0c0f120a0b0603060a0b1c0207030f2a0f020609092d0f01121a15 63
    0xd0300030700fa022514000c480900040c6400051100003d00c20f070000710000f482400c1075011981003500003481584103004440015944850043c1d000e0b605019460060a0300d0030004810340e495040c0341e0301ea02c2d0080000c3c0c400460000441d082500c2a8801d005050664081c0c510740e5858091303554402080c100d0540c0000e08200780c11000384c0c1444100d0340203941040083ca028906003031403105080e0300800041803102c080c8890b0450010140041a204040035074a1085181412034102112903040a0b18082d07841801001290b0302d03828688025a0041803c040d111120550912030361495009824500360000c503100d010150400309085140ca0283c54010407181d454910015100b4500d030080c144150104072100418100600c018070750703000dc1c003040e18201c03689000c1140090b050342e409030380d4403070400712140c1c541c2d819140450024403294054443d041005100d026898180100048003107585020000c200a2186070101c03550300581006080c6003d43d00d00070319501c600029806035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823277688 1250 823276438 823276463
    0x1a0403240c052703100c030e0f0f03090d0507030c090c1112040b09010e1504331b0f030225030f0611040902270f010c1502070c0e0103 59
    0x18011000c2c3d444808201448000b103a079200d80f1100c0c5202091a065014061881d0380400d00305180220400540592004246000348544952500300140161b280603003207800c0080c1d000e0004011194a01011100c14200044a042103401c0100940c4014032054103400b0000f03a2a0264120241420050722035401034400c03061020340b1a40c0e035400300c10340344104010911210490030301421400b00103141c00a550042040400d0108400501c000d50a46020604021018554800700014040c00c00428941080c40800e030007840c00380e1100c8014000c041640d48a10328041000c20b85981d04040c610000542c0e50401075240e041116405080300a42c40d40d400018400e1083c0800f2a136102c070301c1a8801030203403036100060a50003000c52803003000b00300000b14007220f17001400f081d2001c44140c0c480d03094528030340040940b00ca0341c0d041c00350701c40c2c112100c041c0c1c1e04078120101c01500320045001424000c0b01e18030092041c054000d15402040e46e010408104d07074010607059a205000c2101507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823278938 1250 823277688 823277711
    0x9011407020a02090c0d021e0d0506100905090c090301391425050715030902030c01030b041b0207080732010315030605190e071a040324 60
    0x16102c060340c000e0340020714280455600e42085000b002c200340501001400d0100443c003101c104141d4009680e11002c01144c0041a002d2034400c0680041048401c81042d664109014000f45d43c42d202d410700c07070b105200020301e0341180d660856540030b400074020403500f884009030305074070500d00e8069491282da00281c84000740d1110404a0841c100b034480c401a0a03a4280d88141503104070f1058500341141145c40c41c0500c0c4a0883c0450540720f1310103840c00d0360420345030044c3c002d12605c0c0d1404041c1420070302070243c3c40c08160340c0c015000038a00401c040540c5004200500201107007280700c51100f44e6148107484d0b000c038030360b4203848008081c3c07580340341e03110752401c000c08001e002001c0c41034254046203283c205542001c24446010f04000c18100074030300801102034000e0740180c41d0340303444804100b01845030310045a4604502042080040341850790269200d40c503007d02e559035042031140003620400d03d81a680259404000d0500708070300c040780d111494045c9284071900c90b041041201d071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823280188 1250 823278938 823278943
    0x10603020a12021308070b0c0c0f06090f0406032001080105033c070b092103030115050c0a030c0201140a1d01030e0d050405010e030c030309040519050901140702 71
    0xc003199aa920b807141d008155a5a030002d42c07148004518440311403900043c0440184459001044c17910103254840907106809418940002140c4e44580049408030803d030340c510080d80e07446d0005503990310320045180302040c01401207810103801078500c04200d10f622000b44c4030b19030b241c40d001c0e40e868a8036646d420074581d03200c50000e24034200c2d2074a0312520000340c09400e03142d903c6003d1046e54400740420300c000c203824803001c4d0f0400031052600284034440c3e424004035561260200840e050f02c80d0400ca1801c03074072030006014244e0504806e02411420030b02c21025199407170008001d480480302e44d03150107400544c807210105e0110b00c003070342d41c02c070081540d8090301c6240215032210507808200d5007008034241d403240e0815041c0355a8805441c1c84400c2000130180014454458980d5070f400c0a001410344007608402da4803d40c45a10340108030b03200401910410881a100400d00c2d45480c03002c0b0310b411400450302420781e8540310800c4000e0740c0542095541800f81004050181c60f0070000301d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 823281438 1250 823280188 823280197
    0x60f0812090910090c02030301050f010513060e04020d02280507080a050d0e0609010b030f0708150a0b06160611211005100507050d020718020904060909060207060501060302 76
    0x610018804082142810440340368084061041c0115044d15602d2040403503d84000d1100140c0c40030005000d81e0504190144140109080150a00c0140d84540c0c00000c1903020b14030402c810301c5170071445034442c0c0c1c05440e40000c801600f50340b608a150010161450b80c9100d5122800c101040700e070307181c0e010720700b19003190b50000001880c000420001359025400001042c4405581d00d0110f80d030900c042c0309030b038020a503240010501c000300404041c50100120b9001450760008401003201020009415000c000e5000722810560760f8003180e0401408602e44c030303640100d07000034494401c83e10400400e00e03562141004000c3c2105000c036414003401915505116140002d004220b48107400c0884c9070712460141c1007449054458010519401c100d011540104002140035010045c05025001c80302c200c602c000c100701403800891007035085055a5500b90180c2c00900c0e500c940d03c9942050001c0d180c00314041c0090021882c1000080d44400400d9038807501d498000f04200340b103402100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 823282688 1250 823281438 823281463
    0x3043002010207090b03070e19060605090117130b040339081c0213140303030f04030804050a0b0106050a0f0905030705060d1503030c1b05090115030e0f01060f08 71
    0x103083c40c40c103042c80c8900a00d4101c988584c188201840040c0b030340010000030380300c0e0a070a851030b440c481040340070000382c800b681c0000081c08000e1211504a9030b000445003000b1808401c06116512554180c8004d0301c4500c1d4081c1c40c08001b042003006140d00304a03043c800104441c030452000141909190300c111800901d0703140c52914040b04400700b1424005040f01c04c2240c181d00e056000050502012031744000442e80b404803a00c1c00410211940d00c01071140c5090540146103546001005c1e00611000208001c050040140118061107820410311102507800804103a007540c41c3c80c0040c10b80e80022070b4400000d102201c1480034540305603000011140090010406c07141058100301c04da4000140c8020075031360799400040300e80784000d4000c5c02103000c1c0c0c580b0042c6405606043c4003906c401c0384140c1c043c55a010040202e40c88050300b190450b904c410110907007030103001c8102c0207406201c030954254484c41c4c01c040f011100c10751103041290701c00d44c65913001782d560f1f0500c1e984034051600d42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 823283938 1250 823282688 823282693
    0x50c0304050f0a02060d0b0f0325170721151d0f100507050906210f0103050604030507063306140d020d06050a0f08060112020904061d030430020102 65
    0x4101174030046c5d07004203a200c80010300308400c941d50130b07020070325001c0c0020b4140046090310500a524003c011024000380c9050390941003000381d441421036a42740d142c41224085e14075803000c0b10740c6600d02d5000c00c8006030b22542c00c0d0b081034041a000c5015001c044548403a40b00d0385406ca1403140310020721691440740c00d4000e41202e4064822400003040300420a106100040100e1545680c4250060912180808442203540d451300d4a05046410040c260540c0300d001c0001800071850009085501079414605a070b43c5250620701030002c4c10049050828986c044a00310708207040e81c003241380c0e00185105012141c50350701c0b03104131881103820b10410035150b8200440000e1228030340007051420f0311014003054442e5a0400b08124200941c050124808070141c1880000c030300b4003011b4010312413140045810395803a0000307010040058030045c40e02e9030720300c41d01c83d800084002c244c0601b0884410303252100d50b1780d600889850b0512a400d658400a0b060540c40742e03c60900400c8055010b900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 823285188 1250 823283938 823283947
    0x1509211c02070b0411134d0f0d0603050a020f190b0c0a1403041508010609051c02040e011e060608040f14120a1205191509050c0304050f0a0206 63
    0x9176506241c040180840c1c220104000311400c1d40414050044013011a10b410421221035040d80c030410b040c0284031031442c0e440e928000303039110100001802d00c0d041d01000d180e55654845011021032148110104041c0d0814500006208001c202401402c0c0250b82c800c0c42500f83b0810401c20540c0b00901c60000444a81c06005020201001d8001ca042c001e0483c2c02841040c2c8450041c64003d6034401070312ba02c00207003808050a11065059241b40c1070600b40965410030001070b0400108d8003a140c01003135180c0c64000f51400c1c004e00c40c0c003070303e80207001000510748800913180604281d40c18141358031030300130340c02826500900c160801c0320b403140d44401c3c89d52120b85d83c040307510701003250a0301d801282d0b001d081320034101800011901c10100400175522050500050124401100041101e6103800100402524144112000b2409801001450307802c403159030102c100b40c0d0f030007444600746000100110700791400001c6004d00d0240d01211102d0707250384622030345c440407104000e401c03100a22 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 823286438 1250 823285188 823285193
    0x30b060d0f0e0a0c030302070e0106050d020f1b0d090f03050c090718120201110607080a020f0f04030c0e09060c191119231509211c02070b04 62
    0x280001c4145041c8100807401c001d284044500d0550343d2001a00e000c20941020010150104072040044c40801405800c0e0341c900314002e41680035100c0c04400c45500060f00c080c81c3c0b42c401d000c1314240f214101001c1c90101c07290800c43d598009007a40100422900c09000c02c04c1c0d0401b000c003000b101c1e4013038024a4200702d60b40c18483c0c0000054201c005005c540003000303032040920b50b011406880c00d03804032101d204481c000106041d0180300c0344204c1d60000410700074000c1e806011664091007104015a0b90340f44494030b2001480303848142c0707034040004038000c010011180e940c0b03012200b043d01605141e446041e00152078510546030180360b424200840440110805510480300009081445c101c050300c442e1141042049a9034001156100701c1700800c0003a40060441e842c8480e9082e1003100094580150741d80c1d200c0503488a0b58041c0b88000b0700308400c2004581703108140303584c0704080c5041c4011540001d400c540c001c40c007000c60614051550210354400e452004c1e800c0702108500f615581c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 823287688 1250 823286438 823286441
    0x1603030b0307301a16120c08070c2402070213020a0906030e010209060a020109260a0c060608120409110310090b030a050118020306250810120f1101030b060d 69
    0xb0304044030101c4400c4016a604640041c2044c0f103041e40803980001c00005c080001d10f2551103402640c1c00341c2c42c18480703020082e07003d520194044642c0c180090f52001c0d6040842c902d2102109580c04124078204d501e255401a0700601603451098031651003a072612007045090740501c40c21140001c00b880030400c07000d0304c0703034005200002c0d10400041c504040c0304007041d540d070301141d21b8401503912411100c0800c00030058503800400c605801049100c8002c20780035051064103400000c001206c0d10407800d10007260b100d14001c003040380c11180c0582180f174100d003094100f40314419100380b400c1c98030014003807100c0440340301d80310000072a00f019082160490040c06c101120603014450307401c0c0c0c180000d80034800e01d90004d11550300210003070b0143c4100b5141c114000c1c18003c800c1c408148144103928161401920381c9003d04001a15a0768949000c5c0151032a80c003d880d61300c9000d1108042c80016072440c091303240281000c1150850440041d41500e4040c603005801000401218100e000c07103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 823288938 1250 823287688 823287779
    0x2102030a08100312080601120b011e02010f05010f0303020f0d0c061e1d2802060304031704030906090b0309250b0c060a0b0d050a02151603030b0307 65
    0x30550b0b606119104d44400e88032403035810b032100104001c1c0c82402060342c2c20200c20840e01c7c00049050007060180c4000801d40f101034448070245200500703569100718000c0d0000c80700c2000b040c00c10040c0390b03502c03040500804050303c0140c01601504040c00c51540c8046280003c4030a01d8640111310051650b8641c020141c0da00714030710483c0c1440701d43c540034116009130914461107921114910189800160401110701c006425810228144a204403030141d1540303007068040794001e440e80c0e02c2c2e081c240c4500c8030b4011891650700110741040700705600201400d0554400b03955890210781c44000078251840290b481031204d611001c91400600032500c00361138008007030a500b058403a91040000030340d0300042501c9406801800800c240725400d4443d070b4460b0f1038121a082501041030326100c0d00e8442c6490301074080c0158038030490382d50584000303c404040d44600c02c0500822141401401000c124205910034062110006001603400b140d001c0e820001e410f051004404201c07210141402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 823290188 1250 823288938 823288951
    0x31104020c0d0e01201e0c0901030303020a030b0405040305070b09030c1b18060d0809040b102705060a0810170d030b0103142404050703092102030a08 66
    0x302040340c0a00c5281c1803208190b8440d40792100d641d0091100700141028104c055108034403d0401d07182c50312400c0010310340c42e2612103440b462080e1034810403124209518021036a801116110000081691681c001c00b1041e0740c44da070800510001204010130384034280c4000c0c0c00100240f0075100450703148070225801504800c112447c010401c4491820039042c1d00340601e1511440001d124103003130080c04000c084001118001d52741c900383c4000b80a40c28405005480c05102280b80700d002c2c0c460b5445984455802004210842020030000b0201d6209001030f5488405041c4801000345810b0b0200041e21402828142081000002220505802041070364060503018000440c00300350404002c0e0009040050601c07080450000740a541c4510403e5040602d8071914420345020900020b8114810302d520710b65065092508050055203139071140c0d80a803508081c08045071f0543d02c1000300c144502c51501500c0d6940704183d215401c0c807004400903800800040c076555124180c1c40f9803120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 823291438 1250 823290188 823290191
    0x11030a0507060519060b0409110c060112142b17060d030e1302031006020a050c060a0e120102042d0501030e0a0506040501021e1c0b0402040e040f02090f0907031104 72
    0x1a140b9a400d0161096640801162180043c0c1440015a40d0141340e281c0140b0803411440d01d1f880c00342b01642c80c0414842c45220b160b180300c140041110407503050841e103210404403002c1910025145400e215180d00e12003080903850300501416014010210312061080c400c041c4a079200700078010b200500000481c200031418049c0034082d03070780c160300b80c6101d080e181c00141c4900d000001c203951f20149030040360556100c600704000003580042c0744800e02c101507031155120450704200b95401212806417507484281c40300000340544055001e0021a02c1c0403003662134910720b25845090010000068280f90140c411050105501940082e0901c103e500300311002401d030340c2c460600b00003059408984c640d40009814482e148011000d007424042038004a103403002c19298112402084252100c2d80b03074841c0c0d01c100c0c44e55210f41c1a1001000ca403020a1020f1500e0300d0056421a00910124462411140458000201108100d1082119200914006003140c407115480000c00c2e00c000c0d40709 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 823292688 1250 823291438 823291471
    0x17090a080306060702120a14070e040303020d060e150a0603180209220b040201170606191803030903050706050f120a021c0c022506050310080a030f11030a05070605 72
    0x1600c60100001035603030340001030710101e202450003a9a48d4043d02c050262544405010b014200901200540250745401c0042c0d8907076072401c034480588466400900e440b8109420040e000c02ca0400e402a940c104884881d61581caa59054040b1560095851800c0d6800e014110050400b0b0410035000074080e0800c141d4100071084184040352a030380e084905900343c0084c0030465030008201203070b85500c5011101c65207000d80110311b65000f0b1a80c86108070003440f050310180c40c003542d0311416010f517a4104280864407400c002d00921003c1c40102d41d40d20901e000000d4a0340b18500781c0321401e281441c0030740340803503142e040c01c00604090003002d00558200040003040490702e4003d0158480030002103035207007061002030704281c000c0600c215400c1c441054501d446c058085104141c0d049800c00c90b45985a1200000715508a40c0140502d80300d0802070360145900008a079030483d84a54468000c10004c0c1030485c0c483c0101c4c2e2a00e40401d206000f441e000806907080340fa8007000290600300354 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 823293938 1250 823292688 823292693
    0x30d14101403030c2406040b1003020a030905240105041b11011401090509060f06030c01140f0a0216061706011b050105010303120e01051e090f0313050117090a0803060607 75
    0x144100703000c50302c070307902448216032005031070f2140c1c0d583d8042002c5808000c0114008085600c00043d0306840c02055400116072070181e000741e00242994fd00a422503066562071b4048074100c0c650b40c2943d6105609090001840307107064020f107042c04c04003c150301021030220f9400d903650422410195025501c880160280d02588220700d4020099a0340204050030300e40c192604003680907103a110f404120380c04020982d01e001030b1401d4401d6082ca0200540410800540054003a144840310036a2001a50303031706050307000880d070142c00322560040d08165aa079078180d80000b150b4406528060305240003905640c040c0c4540003100942ea1b14148038840265105801c44000342c0044021524602c24a003510300749100d0f00c2070b011041c00081065040c610005800302c2003903661400e46944c9400001c41942e0f051005000d44103c07541240d441c1e034040001201101c0f0750b409010f0026540c00080d074a0003400c00300c82c41c0180680c6016003440d9079180c03a802060742c130040a01ea00000c00b004003200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 823295188 1250 823293938 823293943
    0xc031006050a031b0e04050d11030a2102070206030405030705070b190302030a0605060705060f0c0c060c0c030903100c0e0409110f0a1703030f1b0a18090e030d14101403030c 76
    0x400d920600141c5840234600101030164085c200003d20540e00c01c0c806001c40d50380105041c001101075450b115400e180b401c646001903c12181d0094001c0c0d400300a0004022001000c2c00b01e4034814402d0340c201d2512489061014040c0030200310b10680c08174425610785000e5401580c201c0e484400100c0c0c49a191000300d0001da0140c041110031f07a02083c100714825107070140894001c0c0c4070101c1d82d0700d021910018641e640b1409400c5508003400016024060b00d0101b04071240c915019090700c0326200301c2810240106040b99140000c40d03aa2400d2050500c1c284c8101d55070150311000910307c81560000f80a11140ba01c00507a8002484244c0031a9210aca40001d511840307410004695900e00103030389289405005d00401d4090881756510405a40880140c0348800b400c0d2408841c0b051001140710450300241e0712412090303180030b400a4040e00040024000d440703c140040c41242c00445c544106480105c034684490f80c0390003414407020039000c2003103102d0309009044078100381008040700d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 823296438 1250 823295188 823295191
    0x62e030c2112122c010c110c04020310091803080a051e0402130204260d090308280503220c060e06070b0a0e120a0203030411031e0c031006050a031b0e 66
    0x130040700200090001c540c2405407010340c03030007407600c1140000300101b065540c42008100350310580d0003100040281210f140038400401c030340c100c14404055100d842d2a10965204402d8000495820000703650900134022b6500500c45000031221108030725159880740500504202c1c1c1c024a198402c4281d840c0500140028040c0c0c002c2c3c2c10a54543c009082a00254620240c00c085d00b000c20895a4160000b1849040300e400030b84159032040c880c070401402044050300b4010100100d0310780c40702e2551060155101e403500c1d003464040c51400c54102d44045052100042051200d98400e0180c03510802d43c50000c2e4002624190800b03003030390313540307100350340b045642d61a229659600a000b41310b0170051030240055844410745070080d510700080d102e12008201414040f034100500d0001d480c10004142c4a0020180c03215400000d240b409844a404c000002c1c0320317110394010710b10100f9052042c001103680003000081d1207171440c0d8480c5c40d5440d0300c50309522154000300c00040c40100742c08029 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 823297688 1250 823296438 823296491
    0x302120a05010f080a020904061805190209061804141501090e070501170c070305040824060406080c040b032a031c02062e030c211212 59
    0x2050720741c14011840c3c8050714035800380c41d0503489a0000c002584441c041070f500306801c034201040b13400c50303000c00040f4500d0520000b0020305c94248290507514403c048401130394400c513000e0b043e5465140410038404550210883c04103d0800400c2c0051080d034149814010100161111922028030f14031800109030321001001e5182d00304006600004d101120103041e003401c001c03803000c8082021001c2d02d04001d02c0702d000c1d003400042c03000625005200781c400420382c3c00c044410780c0c4845150204040001e44480d800ca20300040810003a06e000c0c0181c10030303100404001d0034950150700402020300380246030b55805008102003034007108094500f20040b11803000421103c54000d02c24185882c80d84201c0c070303207268285038440e6030b9540d01240c0350383c00504000e903505080c400c1c1d4110101114175001e14220103054160000208035000210008a5028030f400030300d03a0000b000c06c0c2d0505618520018010100c200021140d2030051070182d403413082150001408040d00c03111031450410f9010308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 823298938 1250 823297688 823297691
    0x11040b0903060c0a02033a0c0806040e0309150d0c02060916060806010804151802010212070506070c050a0606091406180106030e010b03061006140a05040905070302120a 74
    0x10803040c2800c200c507540182070000d00320302d440c202d40d000030b4503400b401d20b1384561020181601c3c40e00141c600c100e441600045050759000328a00e400c028010032140543c2008100c0e2000041c0007854144a24500c0030703550070295150802c1f03202007202c4416030b40e116031080e0320248904008440e01d4821001c180c0150f400605244c10604941362034542d42c06c2074888200c2d41d00038140305155000700141d41000080c00c0480c8191620700e02500640032254442c03c0e083d24112208170000380e00940090310a000781c0070340d20480b00001c01c0c000d807441600c102a2144e40a500455a03240c0f095071524022402a01584c0141285070748440507aa0198400c40300582c580c60140750446008488a4005000703da5074680a241461020000c100c144513480606550b8407080744248006e410080400314000c06840720ba160650340c100e02480a07014040000c1c24004103c00e85c2c0c00300701e04482075954541c99050400b441c0441e080003510004088404064003072240d500b006104908881c010f2018220 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 823300188 1250 823298938 823298947
    0xf0603051009020604120201020a1b0f05031615020a0c230303130e0c092107081f0c050f0714061302011b0615061701060503040201020c100311040b 65
    0x14030916054500020302030440c90181031100598902e02150100da21140b4111018209400180c0c1002c0c490319000e8000c0361900a04259030742901f4101041d81c9030719410a001540743c109042c2e49a0807032504140103041c0302e00600a501c1d04010030710010304d480c411600c0a1aa540c0d4a6050311100d40c0610b100c102c0b000c240324030704900481e01440d0b2040c294021410700d804911026407288041c03141c1c05c4041002030115002041e03105c21100307050303000380c001c40c0072402080d4a01000d039250f000304500380c090201e01180b861004568090355049a2007076445100310110700b5002065801d68403024040100001a41600c005c806400000d0040300340030741520030810a1420320030010145c0d000f486940c00d1540050382c1010300201944059080c0e02c1a48060386000e01c02171034817420f01e07074035642c00e00c0c00001c0090f03001c24131726400070390740a8082d0240d90b101e070244d4140c0400e807402800b40e00140300c00c46040c20485203103a03481240d0300e80460302c00440144500b281c0e020740c022240c50440002c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 823301438 1250 823300188 823300193
    0x3190f14060114040e3007080309010c0801150e010c330605010c06230f04050114150402210703060f0f0302060708031b0a030501060f0e03100b01020f010f0603 70
    0x3e1401c8510390b4291424400c0e401440d41d000e8903141c0300c080902d014010920501c02590780b82c0443e00303a60030400c1c002039481545040041c21600225160403540d0709100402c04003074842c030a4035040328401e001320941030075814016100701c000000103a0412140940d0080464056201c0010a180070113801f02d0040d65001d08540a039465401c48160909101c0c041000386d0303001c1340d100c1c4040e0302300b040014010009038240b03114016401703400c40f4ac0d1542405000214404409184c0641e219174001c00054856001d41e1003041012546014030f88484400e00803e41801d40003001489044080c00001c885080d00c000040a002c0c4c400c100040d035141400c4c8410020744c40301402801e2865203c0c0c864501d0366002514502c21070b40e006007100d03000700c04204003020803507000e544090717055240764036030b0014000240181000d00c68600003c0c0c0a040708018240a21500380075100045c010b050405046018040603254171040c0a046110b800c11104c014442031041d50848036105901041451950 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 823302688 1250 823301438 823301459
    0x90605062a24070311221503050717040c0608060f1216090b0303181c061a010c022d03160311060307170c0913050601080903070203190f140601 63
    0x90003181450324009070010441a180c2c2503e4981b005c1c0c013a2001d0309201803006400c0c00143e5400301800040d43c0d450400e0481e01500402d100c3c0329190369400c3d68120344002c052819405681c00307854040069014446203200d04400d681c03094002d031070850031031144008102c2d001070070628110b9a800003c1d0344409032010a000030010141c6034030500c4502e84441c00241ca138410083e905108403244d90281210707841c1c5024030040c0e2404031018020741002400c0000143c4601181e0b19102840007582c00150349c09040080c2c00dd5801510744072031801c0502200c800a010031b16600a000500d003510b0206540800000494403d5039240501071407440c546034100c4c0010607402c610480003030007001a07540d4030038071508030503441c160000455140e0a0790741101e84202030001c0e800c80e108003c103106442098000e540a0762081e40d0744070540c6d81d0f00030720781e880b4099400000e6058010810f10800503603c81040c0302c10f1401010340582404503a6519a01c22040d145c0c0c400c1190010401000800d106 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 823303938 1250 823302688 823302691
    0x60105030f07060801120201110706020f010b0904150b04020d02040b0706050108061303030507090e0109020903060615040302060c0709050f09060601021c1817010e07090605062a24 79
    0x101d000a04415042600184c08600705004803c81608001a90819a881800300f088200202d209440001c1d40b0380e20025194403442600e214290b0801e820b07640607017006a034a5101e00d03000841c40b413000704894201005480c02411640c0e02c1a024801e104081603180b00500061211051482c3d8030446031a140060710b205a000344401e811403420002030400002d8036824503585450b00189603030f200341080d15030250b280c20070403030750940800205044c2c44a43c002d00c000d600840840b4003d90758041005040248078401c260010024042040141069405000d5004e0300c18282c0b032109480f85c481c0070483c0c07400c940110410f40410207001010b401400100d411007428805408403005a400181540c803040440f48100080a400744104000c0d4101c3c2d00041e016800b1251110f2000444146c00f1f0004562250b2040c00703054400504011140701c3e60040350800740000c0e0419400242d022088080d00001104040b075420040c00e9081c0207101080459140b40000d12180c0941717541180e20110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823305188 1250 823303938 823303963
    0xf040e07050a090527100533060d0e0705060d06170109020f01050306030118062c0a0f0f080304061506110703021c0b0c090130050a02040b0c06010503 66
    0x20f011300f03002940c50f803080020030b030306162800c54071030705502d1a5a81c5004a4210303a564810b11b4101848041903c100307803d802480d071025000c2c1c290251000203000e603504000c0d80c582c04641040396920400498100106000141040c3e6011701d594001060b890761085690003070300c1d660755005000719884424848000000e01000b0020b1800e180e02080010400008060503c5008800519a40d609401c94141e0700c007000d00410f51006685801d001a105600c602a4206510071400441c01c80c0c40300c10b030150712841c40083c040418941c9481c0001c0c40182c0381074a101482c02d040364042403104005502a91107038030006030040010b010130b02800f005030000010042006000030202100041000c1030700c1d012a001c0d40020808408001805c2800714010720548030f100400501d2880c00000e0480c00500fa250380c030030708a08407141185012130304a0300750421a828612220300c0c002e41e200303030b82c03020300d80d0801072516480b042102c1e1380390003150101d062a484000140083e0400f80248200c600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 823306438 1250 823305188 823305191
    0x80708030a0f0216030b0c0403061404020f040b060d02030a060e09031207030603021828020d0507020304050d060f020702060d050405070e0c1b0307080a0f020d021203150f040e07050a09 81
    0x14403c00c000b040b020f203201c0071b03000481ca134001c5402c490062081341c0c01980d10910400c0141c1004611448a20044400b6840350260800030301c0d50707040c940655040e202c0000c0c80036180205582c4414001d400282030040c03c180d640f4030104201001c6000140105500d070001c0da04c40c074441030f40228100008083c00105414a0010070068469035030185160701c060341c1201c00d942d0358188503d03c0c0fd810824071154101d44072050340c001002a8000c0603400c440394000e002581e229842030f40c0e2480355100300d81e04118094521008152944d011900c81c001c00305001d4540f612640029840b90000c3c070121003510350356002d02c410018100042401080c10084031401032070200d01e086142c3c0549a100d000c5c1214280c00504041000c6c01101d84031380d4004042d51b201d80c2d80d200c0090081d45100804009482400d0355124a00d000042c1407041d200d26007040c0d403560344c0e4121000340480c03808454540103002071400d0001543e4600076111527001201c02040058503001c1040070150940d4092030340c25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 823307688 1250 823306438 823306453
    0x1e020d1511090d030507051515031207020d2003101d0105040c060e150408031c110a0c020d0b091c05040e0c07020a09061203110c0901150306080708030a0f02 69
    0x58443c14641c400746501810700c1038990b5000d0506904058010508120b00700308141000101541d605002413039179801d400319040a101070780d80c075191744103082010358030241c02c0c0540800146400050000e0960302070220b00d1041018020914041c00301a40302e403a540c03251001c00c9100f500c28481c00700011404024422400c05403030b00440c03004103020301c1c010440081c0c10814942c035903002140b90080ca032064140d449176180031040d265003107590a1107000c0312084422071202e40d140202c144541840c4030080c903007036502106580301518550100d0300b190b40103442001160390f04451510804a58019065110303158583e22060900400850b040c45410f001c180003d07203104008603801307080d00e080756540d040c9a0002801404240d031150781d0043c1044404900c2481e410a203114036442611002d010070a100300c0c281d00c84414100f801d0b00407403010300400c10f11140035217210081503c0d0500095035603d5501243c00c045e0260416180c950000520003000341c0c0c000017907100383c6020310142c03071103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 823308938 1250 823307688 823307707
    0xa020615090402010c06110909010f0e090d0e060927040303150b0d05070e1e041d0a03080403030e01090507261507022b2304031e020d1511 61
    0xc260f140100034010b107036900c00c0401815601f8040b40c3c8c40c400010641061582d480000ba100f5500074000d45143c102ca840c0410500b08000850040001d41034441c0c0d4030010b4498140195074018180c00c6074005104842c90070101d4020200d1003041c40d00151006151416050180070760b100c41401444c1000319400c00c014200c1e5050a80780d584d280c5210201e44d039100c0c00403c6524070003503403c15921881400b850005044810381150200e8000d0360144941020303000c281020350750400411950340c006c0d81681000a2141c000d890740640b00341400155055020141421a0100c2500311001d42c80264188030070b4041890341e6003521405030000d00f0540c580c07142d481c2c887c04056a01d0310b20700100800300b190340d40280201c4045030800300c0d07180c006250040300b0403100c0001004500100e1506221044903468200e400306100d0b030504401c1c0d150502e103603a00b075603030665a5402100000540d03d00c2005076107007104a02411b0144900da20915844e05420044803c06c40c016201c0b41c9040014109 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 823310188 1250 823308938 823308947
    0x406050f07051801080a06030c0b07030908010605100f0320040302090f07090618031205030f09070807210b01061709190209070302131715011a070c0801020a02061509040201 76
    0x50036102031900d103e240e242e88034040007408040d000100407249c03150340070800c0f01070b00c0040c00d42c040c0241c0d1812080350741d13024414220740303450081d40d4106103000503040500d405011000d2650f07209107000540054a0700ca1000d04604140c418600b0a200007410400d511700885180d40009502c805c1d507902e8101854007420381d01c20303071140c3d0007030208940c00b01040b082880c0100c0000e40c1c11246e505480340400030010229801100c0c1900c00758445000300e5500600003500c0c4003070f501c046000b0079006080002500081300c80e203c02c0c1c3e40c00154a00144000f81c83c0c0e50300c8600070201600c1d02500b58a55403040002c0360001024022541e000c00403c411101c0c20502400001d40c0540d140d81c400d0322101c0045000e44140254500d0540c4002e8000500d4098008002d140e9031001c0e080d02d80460316841c1114020b00c082c864080e9820a0082d05500c00e0812802080054421303103400300ba1a41c0c0c0e804940c00d9820480d07103000560000b10412001c0145078a0021300070300102c4031030309540b81c96400a003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 823311438 1250 823310188 823310227
    0xe211b0d140f0d03050103170a02100f0e03340b06040203040305220609090204030308160207080708010603150e0d080903040f0e06040e010b0a140a05090406050f0705 73
    0x78004071207941e201a19420501c80e006004080d0710580c0c040c201410400340251000b84001c551481044d20714000c00c0082c482510b007503e04603806030a412031b1106810010b0580010303003e4600769a43c2e0881000b070010401010341424110503c000030700403488025841c000410740d0b001c8286002604000603070340c01d42d8581d015100320b0300140c2704d4455080858843c05203200c0200001660002440d41901083c0c0c1541151090740d0f81610140d00d50300d03c0000d070b000d503100c0180840c0308440400c2240e52550010502e010706d84c070440d02a65940c000c00fa10300074181c0d06c0401c1c4c1d80d544400c240188900e10725142c05075400ca0005024409008078940d40e600f00c45851f00c01000050004150381c04420b1040303400606031103819503521912415419810901603c5841c0b082d4501259041d031010b040c00f0b9a213200100411082155240440b058542c3c1004045558450b000b003001244a6030b442054a0180b03004040000d00c41c039018484402c204009401441132000c1403010a0300ba400200099 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 823312688 1250 823311438 823311443
    0x603170a05210f01080d050d18050106030b0a11091f1106160806040c0e09071103030f0a0e0a020a170304050604091b111203070e211b0d 60
    0x16603424840d44100d601d030044660ba10722420340360b641c825010300100d03151805828004004045641d0710380600344e860100e105200f0101e90280610824000b00d580100c242641c0c02c0c05850a01e0b1856545070308545039a0011201215202d0a00c4001d040c503100e40400220f02101c80d034540b0000000040f00040300310481c8101811031800c4904541c410130503041c0004803181103e0560074000b0418200e0916540d03c00c4c00542d50400081c1c2d20310301070241d024220001d4482e1010702402100340a1480b60040001050040181d041c0c00d001c0400c0004600c40d03120418021742c98140040110306580e20001c0711481503018038258000340c0e450540b52001c4a10926640c14010115100e80d803c50040d544400d03844000411300040c04007181e0080e0030140c135a10320a03414125241401d5500c4100c00c0c0440384542d2000c0403280d0502440402113400002500300320008001100000c0c0a2040c090302c40d00a020b08210218441081081080e0380382e02d42154030001c0d2810b14001c00c103e00c0980101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 823313938 1250 823312688 823312733
    0x181b03120906053106020705101706060f130e011805270a020603130615030b0601080a0216030f030f020f0906130b0703050702030601090920011b060e010f0603 70
    0xc2c100000c0030440c3c40b481e040303c0c005070703003140d581c0b454065247c6005125250042e4006c2d0302c1d5040c214801e070680c00e1010800d41c0c1c0b040341e0b034a4000c00c0c04850b03000740e5204111590208203c1000807405d070502002003840541240c00c641c101030f0b19a00d070403101c0c19420000b90606040c00725040d03c001c110059154000280c240620900010300c2c5040c5501d04041c0d00400d00005200726004008a41110710380120814442d906241380152440903c511010340246ea528000c1401c03503206264043e0040303c9908054107240388110590181902003004a0220352016030108090740c05020740050318a00c108114205042c41c0300f101030610492114506c50b050001e0001e0200b104100201d01500180d051191200854a4098020380c40503c040e4464410000000b44034103080c007454040c0b0354000040d03480f40ca00b034804580301000b076105d0305041c414020083c07008048120140d82c480d90013100013255501920649500310355980400400c1c850500707500f8400b180d5071800307440c0045030301d501c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 823315188 1250 823313938 823313977
    0x3080403260301120c051f270e06030705180408030601030f0c17220201081f0b0403060b0a0324091403070b100506030f1503101a01021609181b0312090605 68
    0x4450040040c841083c4250703c40c0100c01190138409c5691091084c5c0d800e40489a02549030800c200e22500034810f5000b41c2c5154400050004803510080c44c1c100c0d8040c10041003408520507030f241074031100b0002c4000140e00748000c0c402d0340f85c9420841e8101094407160038611510845000042d50440006814004480c02280003103101070150030fa910040c0341c11400081d1203c0c003420a985c018481580c0040c18060030750b603189040d8076548201c0741d00a2030006501d9820440c0c0e40c12540058040319441d541d00c4100000c07072152101d0340d031003105420145552700c1d0540b801e802025000350048280303024610040c01152546000c582d00085e561140c0c0003295520030103840b0310f0403c031a1440e01070180c2240e2039549001500b000d610220b00a070388040ca045d10f00c004981d21050b021144480c00c01000d02045103240075803045d0582c407425a5030441002c01a2104501c1ca070300400802031a8402e03007001c1062156201100c4021100d80c80c0001c0d071140390800c0241a8091104803100c0b902c1c0300c0741d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 823316438 1250 823315188 823315217
    0x5060a050f040c11060a060501020706050310050405040302100e16090b06070201050903030d060e07030c0305060f10030204051504090b0a0e071b0b0f010303081003080403260301120c051f 82
    0x1002203004d2041001101d64514140842c84086c114600c101c41c0548503118001c1941401082907078800c403070070191182d115103070000300006048090701c10707402c3d401074804440c2032450314003c54100c041488003c010000790380225001217005544401d04071407501c507043c001580c88000701c5458540901c0d105458030038000010f800d608c98000c101440919140000854a245210562080045031010040304515030400e0b0140c81c0b049400c1e691102e0030001c028090310703007072101000301ba2092600509240c2c0b00c5000c00c100c0c04003203000a040030030110b41005442c403280907509070403105546030140d00340740400c0e1a18544000d4400f005001d0b003a95020300e10031344540380d01e00c00340c2c120804a90380e040920400900d40400c2c0020380005880d01c002440c3c01c400d5030701c140200c81c2e0151686d0301e01455500c43e000c240d15104011080400669001a100b0703030741303001a5000c2e11a0040603555460a40f80c40f490030602a8005405284281c03403120041500654003c007505160811910a070785a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 823317688 1250 823316438 823316447
    0x30203092b0302070501020105060405040b07140d180c0f030b04060209041b0e031c09050d080d0e1b0415030206030912030910050c0301030b07050c0f0304030b0a05060a050f040c 78
    0x808410361200010080784141540040c03102c044800c281c0080001b41c50b0001072006075803003200c004d45a1700142020032100d43c41800d0010030210004240c1d41030810003018079043e80c128a0211108208040d0940c0031b00c44180c0940006110014080802d1461a40c0d0703d200640014000352000394045041001d945a0f0b412500b40b010100c02c20407445035502c000074021803d05545c0d980648600e841d04175000008403020005400a503d81401a07032502d0100003910714031900032a00ba1000340210b09c81340c082c600030f620345030454401030303c4c1c20040148407418005c0024902c600c10350400600301031017245084d850046c0e07501a121a50340b641c820210350329101c90303090403490044000040112816000c01c2d04810b40c0149001403045840e00120504140000c0c000504503180c0f50b000701e46c0c1035000308000c00a00d10450195410006181c4407281150410b600a85d20009040d00b0042e4502e814415268400130466403000c440c1d0030b06000c20039400e080b01896009076030b68200412150302a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 823318938 1250 823317688 823317739
    0xe0d0c06140906030c0d0e0c0109140d0506040f03110c060a050a020102070f210e060910020715090609051906081b0408100b030a030512040f050d0314060103020703020309 75
    0x303403880b84d40303007041c51100c50b03164005207036154040c1c644503814446100204083e01502e60595404c640c4509082d40880e81c0710720a962541d00c26060840c01d00011018800703180300d14002d41c039288138040d0038100504041c1550030350f94010b801103107840143d6a150015150988001c0c40c0503900e03100b059100b80d00900c40c20f103000d010409610030b82030420206001e400c2201411540b030344000e02e4403140954241e602c2e8003e032039128500b404080028201803c42c05089040b6204464883c5e80da85610303201c8034a180f04071000140500410711495400582e403800504c0103840e001c1d0062103070002c007800005180104c100300100ea4021540d450081603160301048002e51200b0764031591101c82654881d2070781088800d080c1070490712001803801184200400b40c05817070381d9142805000c0ca1480d5401c00800031950140700c4820280458410040d801500c0c5072514001628014030408105040c0d000340710134101801041880006640803040d502401003e458001617010400c0c10060f00300355 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 823320188 1250 823318938 823318957
    0x11b0f05031008061303031a0a0b13030803042d0816080d02040b0904050a02072409080d0c08010b040f061b080a0c0b240f130c0f0e0d0c0614 62
    0x4e030009010b40c1c10080158040030178440d440400c000c541070001c00507420030244181d64403030038086041080701c500a0050004a1481c000202003d4880c0d890703d885410644060741c040190040340f152051542240e01240042c9603e00101c07107a85640b100214810313003418060f0760752041242400c0101d854182c40320f4520001c0155100d54442440d02d00c2c0d50050080544107a04040104290364076070b00c2100c0080f41c101c6082c03a460034800c81460328045001030b101c100345030307203580c4280407510b83c0024043c902c1c40340002003031003c503950b0002c06985042e040350818180c10001002038030301c5413203941c088400c2c07810b10403410700c240c01e680f00c805034903004060f20705500029403028150b44002000d038424455032021400e1340f40d0211070280c80203805c082d003202108403100d080c840e10301b00800c3d1800e90f4005101c012540350019035882030740c4203840c59170081100b10280d914010742201001d42040030659aa80e620511038441d40d484044521490003400b0b12400d409110b915842c04413203100d85d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 823321438 1250 823320188 823320193
    0xc0907110a0c080c09010911030c18040c0305040b09060c090f030c0a0f0e090a0f03031e09210311031303120c02060109060b1c020f04090f0509011b0f05031008 70
    0xb542d0341d0100f500c07a52030310000d5219806517800491170603541d100300c480d6502100304032800c584d1080d424245903400f14002c001120b001c4080064150349501a42c4074000f41590b010626081a24085450780d5000d07185414980210b0100500ca0007541c090750405070301240c0d010503082c8617801103400d00707142c0c44140d0b40004400c44081038084100388104210362100d02044160350303c0a41c06a1952180c1b003008043e8800c0148100109100f0b4100d101c41155501c14990760312041c020b600c0482c0d0b0300090031584941d040e00d1071441500365400c40e00d00000c15090500521a904100d014144402400e054103c000131040c0410305105050703a9400c1030b40c0ea50200081410004041d6403070900740b1400d05a2410070b0008910101103500740da42100500c80b45060501d88100307090007a4000b1040591541c00501002030000501c1c01002c8610500e084000740c0703070911413505c6003903401c0d0085000740c42c0705143e00d144c1c0b4294881c0e41400c40000500d001c1c2c1e02c1b51a0b1409080403001e56a120040d1031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 823322688 1250 823321438 823321463
    0x3050606091e030c1504260d0f02240c0a17090a022e03051911090a060513060806011e0206180f070909061103070207090b030c0907110a 60
    0x2c0d641e8120000c001c0c4110f0880e541005050f0402000415000701048803000c1071004100e0103401c3c1c821026407201c00c801c610080c51122010510b007920385035913500001c146c0c4c0c0a0003a0940c040c4140a10031110a161020391203891060030030000d809082200365550015404c401588151105421480240307604000c908240c1009a510300c2810300a9106903688811042c3d00030249003483e0445c621000345024121030a801503000346001881d14035551448204802c88011a01ca004440d1003009420b9850711066000c1c40644442074020340280441007207038030300d1140e4130180f50048074591b14100000e4ac0d40d1600481d500c0704058103209903c01240001c1201e5074010840612811298101c1d804030006030034126a1002000321018494009400520840a0755003080c4080b0b400f540c408200301c000c4040c0c400ca01e510443d05100141c10580327081c03000c50554007407400d0f0034804900606070200c0210000d01d001c5800b0f80320f481440a803040c07a02c50ba040a0202c1090a5080044035920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 823323938 1250 823322688 823322719
    0x30f06020706051e0f010e0c07031e0f0e0d05121c02030c030702010b0103091e050c0306040308190908031611100f0c0203190e0118060c12050901020d0305060609 71
    0x3554404800c031030201380e41c60000d1000f8002840b21070484845400d004030f1a1200b407102d41315a804540e0950412081002c0882960900ba80440c0314240658070741070f14582200008240c0350886540301c3c421102c45150030b02040c000902d0f4001c4001251140395030b000036407070511825012880f22000a8008400c00ca0010b40c60300240d44141015002800814640d0004504590203444000c00100c24400039003070042c00d107549a1001c500c58400c5501c05448100005e00c2c2500440301280010680d47c20010251000342030000f00c00018942072210000f540ea442c20f041c00010800c00135404a140c002c8612031180e400c09540751810002d44500c403001032804806410140d050310005800d01702001072140c0b00108844520b01800030a048444101000300d031403140d921401410030002441250316a944184890300605030f0ba1180c40c0c501c0c0e0985031603100c000e00704881000380f0030188070068550f41c0114860040e0074441c41c00042c26135a060010301d03140100b20515400c8103094809055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 823325188 1250 823323938 823323961
    0x20f0424150e06030f01030b0c0d1404122d1215060e06161e080a030903020607090b0913020d0c030914010605030a0b060307120b1f060504030f0602070605 68
    0x20814050782d02c4030641c401960600c107036488155088811a4401e00042020443c1c00703105581005810195502d08122598604251030803a00303507625902c01c450a000401c00c80040c00101081142812080e500e03c03481c0750040458040c402840d0100c00380d0089140c1445000d600384440c00d00101040503400c071204400ca21444c1d805140d02040100340c4090307243c41c2101c01d80e480304d8190320405242c1c0d06c8680c0d41c0001c10081a210b9808400304050748000640d054001c0c042c02d031160741d4001042070035402c00900c0c010028103880306210754011300744080e400d05c03030880746c2000094035822141c0600c071150000a201d0710402080092800000782031056164005082c000d004110040270018000c81060880d01140f040a43c90380c02158240005110507035840d520035801000d4400d09581c0782068030351a030008000311101c01c0c00300104007041880900c419040c2004104028800f07090082c0030300180f01c1da001c040c14402c5a16245c070100055038040350f8660780e12030828065410600310500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 823326438 1250 823325188 823325219
    0xb0609130225213605030c0a09090501090611070c0b12010302091b1b07080705030d0807180905010e071806180305120c0706021603020103052a030a18020f0424 70
    0x8081c100b100b01d0001e45c42c07170005820b20250f80020701402143d4603022000c001898010b204407001c0d52103640c0f80010540038440d01140c0340810030410f54428052400c0510ba80300c541265410310030078492300241d030b07551070b4000b410b49a0507030303499080d5120110030003080d107082c15500c500c5600020b2101c00d4100312030b850b894068420003c03030355541d4a40c4a16a29000b10f8041c1d10742541c0018019540241b181d117005412840500700382c00129080b0700040d0191800303401120807591918010454480c41407415640b180491400540e0001c154262000c13200e254801c00c400c1158801c41e03103480300c8240140f0710046500004440100140b01100b0155801503d0219000e0150340740005085001041c01d806075950012401d605900f581e00550042c41d000d002e050074204e00c40051034030240c460999400b8000d845044540368030b01080e49909442c0340c4410301c2d408028100d00140140c80d1030600741a01c000480d0003040a08407a0316034401040340a81c1d0841940b603030200041d850f5425041c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 823327688 1250 823326438 823326527
    0x2030d1116080607081009020703030506282303030c06040b090607020304180b040203040609140a030801090f14010b040f0b0301180b060913022521 65
    0x48842152200758542416600d1140d194103400590000d40110320070142d42d17501c40417100f28100050740f500f00c2a805c90b0050350080300070940d40c3c41801400d1820303991031452070071686c5030801c0a500d00600d556a842e59441040c41061401c86030000610b00007541c86614a405421240c60b18032508103143d40d82c2c42602c054801ca45a80089200c071100403920724420300e1039400561070a8940390040d03822040c021141c110a030f2340c0d481744241c80d41c3c0350b0000714005c0c3c0c060040801e0344002802d08048c050b8016594400983c44034001c0e4000076040400541120f1148000190414001403d02c02030802c1500e800c501400560000c5640c0c1070050141080c0c400e00103104c2c00b142e45404403501144401c0c01000c40d161704d5100300d541c0c44400c80e00310485810024280a0624202e40041010405205040b90000d6004503041540701c3e60504038072030000300d180c50151002c240e511448041d50b00352200305600401a60742015079401501c0f03501218944504420b10f807000e00711000e030003007111502c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 823328938 1250 823327688 823327693
    0xd0b120303040f030e030a020603070f0e03280f1b2c06060702131b111504150615050c010b150f130b0708120108070f0e04030c02030d11 60
    0x1110048840082a680b04036407101d21408039054075202076540f83e45041c0385a60612420604000684504015600038840c07910b407080c007800444070282071010721a0001d4044e90042c0a8030611055441065503051844000c0400c0c041c41d0b403c01c0300320688151006018154140c8603111202c104200d00c20441c0c0032003051051300580800c000b05540c0e15160384075042101c0001040e01443e0000050912501c020a18103aa400001c12102a180d5032030268a1200300c5080c512801504405600c40c5100204041c0c042c0c2403160580350a00c0314054009410390400761800e410710315140d40014003802c000c503202c01c10410100b000401550100f18060080d500345100d070001c900300071840442c0c611505000b181132a50540801c125a0401c0d8000302030301031060400104680d00d900104a0075014862a03a13460021500d80482c0b2441070f84a590f0a034845603040040389c1c0c502101005a5030189546543c80e01c0d641022a2280c42d0103078041c1d070502a02617440115a0443c4030140b4a2885405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 823330188 1250 823328938 823328959
    0x408150a0501030b0c2a0706021002040f1a0d050a050a0e01090b160207120804090533040227040614030c0d050115030308190e1b01020705060d0b 64
    0x3031840c00d68400380300080256241030701080c0c1004100c070180c4007010110809042c00240008440070b110b100440382c45007a00000401e018055040c4a881d4079450108015458903103015070211404c01c5078404c2c0310410351084110360040c5580000c541e820030310000103000a05016000b03000a01040d222549818a0004c0012064006009040c3c0b05038200340c00d5000d07550f520420940b0304003421020011405070030004030343c41207140e5030322001c103000d42d24090b110f506000c21101124009000036901e06070f03d80429580c05000d69031031a1404035000400c902c003400ea4049406401201001d814100c03070140485e800002c07008814800d50300c00c40d0103108403546c070301c0c0316181c2000c0d420401d03400d600041d855926606000448008407031103200000f612000c0c000d07a101c001034154008400054880c42480040180410f40e200350703c02c804c3c4100106910505050380d100c00450512804000d0b1024110715a070080c0040f500801024141560300d9141c614040014440400c0e000d00c94202081e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 823331438 1250 823330188 823330201
    0x703030e06100602100c050d0e0c040b0a0f030305090312040e060109090b0109121b080a0605090c0d02041a04060b0c1902011704050f190b061522030206040815 70
    0x8042c0001c490040e0054074807006040300a4020f800055250010311404000c1500d8050442c03142c2d007220080038010f41100340400381000252042003810f1442445012410b02110448070a000c044a9050a10360303a07511110000c2800d107131407404011040c0001003000203c2080401c0850720440b0241e803031201d1031740c580e02d030001180c180c007255a0000d50561018062401103140c146403d50107918080007503158116000607000ca20303004081660011107191003040454000c05400070401000341c02464540c4000c9181c1540b689806449945c80341f50543e0032018004507100300320300107030007030020320785400b001e00340c640c020500c1107114031176580c07803080360081c03d0342c40c1400541c140d5900340c46030720741d00c008060030902400580e25801030703e0450b03030034800070001d49000c01924462940610700c00d081c0220b6000c002400c00380039030411030400138240b0035003048818007140c500640c00b800c003200034041c282c0111900003c1d04008000340220b2070318000240200d28002c3d0113081c0c0c007507a4416 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 823332688 1250 823331438 823331461
    0x31905131505040507092a0923100c031b05030405031510090902120a1505070f023c0604050c0105041215290102010f0209030a060b060f0703030e06 65
    0xc0303c019207540c0200c10240901c0940303812080801d00030201100140300d500341c0c1d6602d10120724000344003040e840c90082040d03002c1524500710740f40f14201984441ba4105001c104031201d515071b24400c004141d02d03a6420140200b50326180c0c4400329403a802581010714095030740b6031050050912038441d42d803c0402d0241482c0350341c2d00c24001c01c40740022891130f0003030000c013901040008030782c404101c1101c1040e8590070010b0f1005e0034060591909442000c0120000b260005402103040211000c4102c24075600002c018000620b448070b10308142c16280f0801d42031145604612003121184840301c00604d0000a82e640203030b0041c1c05030f48101c59014015074080c800c910541300540b250010403030201d10142c0d6403c00101940c400480d00094000c0c011404040700040c1d4020458002c400b4505940d091080b40e04001c1030490852510041c800040c1d61400780100081c0955210006400e250322500291501c440e500950162103801e2490b015003d081d15443c040e046100310b0000484c3c10540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 823333938 1250 823332688 823332691
    0x30f1c180b0c0a21200a030b09070e0d060e030a021b0307420309030807020613060b0402090402071401150608041103010b120c03070b0c0d05031905131505 68
    0x15601c403031115031410081d084c12003074203040b8801c40c0b40d5107240295070a5000441c01404400c1c0303201c030507521440c0200140c1100d000d89462805060b40608200c0c030640c0100d41709110f01c1301165181043e030803614005002c0c0c0340c1424141a82d010120305c0700c1c111500081c0780c181807209a545a0842c48806050645d1000507105820050030301c0f46224040500b81c03100c0040d000e41090710f03a20341e1019a000240c00c010b010004600099461807007030141540070b0310040d0802d409101808043c10030340d0324a115000d560700c000e842c0a03a42d01d640300455840364100c5000c454003402c2036454241604001c2025041003004000c00d50806a004d20060103c4501d8001d5a40c1c64a5400d026111615014450701c40c01c81110f03050740da01e1180d5001c950300c8001103940503400900800303421548006043c100754040c0d2040308581400c1c0128006044003007902c0c550642a07213030054a1765940121404040a4022490805898a01805001184142058090307405011a140c460403d01c44a0040703410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 823335188 1250 823333938 823333957
    0x5040303030b04090302121b0a080429031f03060c170112020d0b0a0e0a060e070909110904050a1a04030314240a090e011d0a0302030f1c180b0c 63
    0x7100c0c260201009030240007038540802d01c00008c051406030641c42e1140c60481603400d058041020024204416500c003007405402d41d021880c4174003002c01100d54000501147c9006800c01c903e000002d01c0b9500c0c017001541c00900500c4404c03801e00000d07041c0c04204a100303e40823000400801c0402c1202c0310340324040d5000e821030302004802d880c1c0043d1b0b0380e406820071076029207903040114030f514200548c51581d070290000050307040f20714101914060742a80000385850410495402140219201320031544055441c45d5044d80c4501d4603130b06009482d40002c00459002c840003098080c04290248600d2191720f0400903e014410070b01068041110f448070140424815043c01e44851700c1a07101c1c07840040c14030440151240520030a032080b00c030b10002507070741d5403080c4500c83c004040c001c8003045000b006050130b40d80b56100251244a000812a01da00f800152a4001044c0380707040705190300e40d0841080280c0101546166440b00034409850125450002c5031040030700311308442d140c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 823336438 1250 823335188 823335193
    0xf07110f0705010315030807060c0e010207271b02150c040302130b01110307111804081b031c0506030105010e0112030e0315011d0721092105040303030b04090302 71
    0x80c60500114060700c45c1c0d1701140205d41121100200050010019001040c850742c4042800c0303601c2c45006012804020405045502083c0b0400000700c6680e005001030280840d00f4111116201006005d489140034401d040c404040c40070342910340c042081c5020380d442c0d6000102e00c2d129500003040070f00603408069440104540b42400300031a07075101d4900b03e48181806a40005503030711040c15604080000e4034042c1c1540300790328091a20071401c910903003810040000c207081580b00c40300c103801883e824018140000303401820400080050f41c544402403c001d2006211071503000c0003400742601c10034025800e1600100d80031748900c1005050b280303085034020076403449031012640b0240320150035406008003201d003440d01c204204e01e80e0182c442e0f01c5440021001e00201c101d45014010403030010441c422211360a86410012100c0051004440c0400c002006040c07034160020606811074411030344000b01c1845640050280048034003a840810646650f901031006a42c0920401001178 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 823337688 1250 823336438 823336453
    0xf08010501080c1303020a060c0209060303040803070f0c05060f0403150504120c02010c06060e0106091a2a011a030106050102011a1c08070f06110c0a1412030f07110f 73
    0x1080644007510304d00c0c20102001c035450ba03494001c11304425058100f60001001c0d180c2c01015820880d14050300031005800840c40e0a2902e04110f40724001c0060090400c01c0c003603c403c09220071800e03084090000104071aa5403801c1c1c000421441e801032104075146282d6000c43c602411062080c240326603000151460003a41c8550700700c89000307661008038144100020b03003030085445031003104082c10b205860300c0255410300c0701c041d01d07803480c9134401c0400031000f0310110501d803c00c0c41031702c03030542d4042c81411211050035030b00306c00d0070110b40720300d48203610b04000b80c0c00424107680342c1b90301d12105900800c4251f17221070049098810f030ba01c5008405250200c40c104504010008100072079001c082a1070710703880c0381d446440703503803010f14161800500307203501c80305011951003120302c0400d8052043e032030402d840b00d9464540e032100b500906003114200000c2c50418060103032118414000103001d9a03413402d5995a20100300a42c1e01c06c00041110702c001c081e55000148111918810304000c0401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 823338938 1250 823337688 823337701
    0x40b030a0f080f0d0906020c06100612020d090807050d09080a0c0e0603030712050d1512030c03180e2502072106060603090b090102030c0d110c060906070f0801050108 73
    0xca40c40750100c00c030918070030001d120742500c1310700c00c00d10114030801d0056565032038610180d18240006e840300034940c00e441000c000c00c64109030b039283c03440710045016803500400344a41e001000d802c00094181c80c000074a4008000d008100180c9000035902d42000c440d0b1140d424658412035464001c01c903010110060000b06c189101660307012074003d0440c1d1070700c54075564858140301e68101450102d400400c1d0740c60280701c0c3c2d000380d44443e00c0b4540d0550245140c400356105050340650b014041c4202d2071401014544119400ea10441000c0140c40d0100c3c1e8411100c46d94810444100962401d0350f040d104081303080d00000c0341c0080c0c1c664010207080d03041900003000e10125196400040d1034990220002503c54000c1e880102240e0310001400c0c0c907913080c05070008500030300140d0641d02c10010030412500c08010384000b038000103000218004180c1c040c10032440f515103105058403c1001f00120f41400283d524454080c5550780324400b00e004000381d1314002c0030300809000c2401c180000e9003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 823340188 1250 823338938 823338953
    0x6020d0302090a05060a090305010b01081902090103140c041a0c031e130905090c0d0308221b05030f010b0901140118090b0a0518010b1b07060e040b030a0f 68
    0xa41d800b00a05a500141c1d49400091403a404070000401140d03504004005100c030038816445d0901003801d0600360f514140f000400c411980d5801c03d22425800300d10108941d110740d009041d2070904241c3c20074913040890402055420620460a03186003040c1948445014a02a0b90071211480015400c05c81d464400c50309000c082c40d501d0904100602c841610749100741260710092034030000001c1c460034814031711030901403001041405444052112000254481000d40c0d010400880e100b102800340c4080000894a009001c0e00083c0c01200041102440131f40300c2048504c110115100c2102e103210603420782d4009030505030b11100c0c980040080740c1d082d55400384000d50514203103210141a840306032031700000b0307080050400e5840302200140c0c145604800c01401088900c2c60050501d00c2041c0c601c00030500540070510008605429110b188130241c000c130700081016621040c0c0c807280010001c0780f2018110744a00d0808002c0240b0303050104000c469260046081000c2c41c2c0103489503c1c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 823341438 1250 823340188 823340197
    0x80702010c1a150906090a1814162108070201120f05041401020c03091003110a08040b1003020117070e1503090706080124030609020a0c12050406020d0302 68
    0xa040c8100120745030006010a002d9a0040010410110300c5042c10021240024000c000c024025410f581c00e00c00a40d0f5900b030001d80c8507195050210345030004040c1180d9102c030580000386029800c10b1403407002030004c291403441c961090740005800f6602d84058071b2103140040314404204a03100f240c0c4c003141d80c0000a007035480c0181440402c401c0c0b110741050880d00483d018900b0b035680c40c01030100300030502c1c2001c1410541180250300b4004489000350320307841250f00c15032207000c817468807200841c0280c114440d88c10072040e29035103901e0040e20140c6110f030210703412540f840951001400040110545e5002d50784c06940b21030b14510900395011308910050044000c0c08601141c08034542e40e454a58034200c0803200e059501d9017040da4446181080e2038000200384a4610300501082040c011907628070500001d204240b4030484405400030002d039001403100d540001a442d86a0390000c9554203d039101d0100441049440070044440d40101c0c0200401a0001c0004443c881e10a4000d031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 823342688 1250 823341438 823341443
    0x20102070c120f1509050606010216060e0a0e04031d0a0303050406031d0d030218040506010f050d14070c1a090712050c120d090608010501020601060804050f0604030e040c0c020604030807 82
    0x20100c802031074030740c800200d1840070403041542d02d6401c100c003081000e100050300003230b0a00003801070714401101d00410030800c0c0129010045440c90080803513a6000795034004013142c02c3c40e5581070815040003401c50124030581e56004131407d03490702050609461002c102e03901030707403014101401c09000302c001d840a25503a081913903011111804201d42440b0041801d000c5850069036119080d41040c400022424030b0361042e440d050800500e41d030485d0b544658056a03280140e41c500c80070b145000241100f01e01600c00d110b1036030400504541000302c01224074014820014000041d512100400d00b044032400050b40101d0380c07c10600c403030808040c004ea40310b0429219403502d03400c04a92f2010111200444603440301042c0d003107041c0c022082074013401640c40c00400300e6042c640041c0d610b0b10107105210801114600042c20300100f84034200c0c200c02d1103803e444050a003824010524a4201100392086240c101e800240030700904c20080301c030341d0252603030381020304c1e54551044540092405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 823343938 1250 823342688 823342703
    0x14030c0f030a1b02030a030b040203101a1c0506090a0e070902030903040b030a020403060b09010602030a08041109040b0103020a171207020301020c0303010315110f0d0504060b1201050412020102070c12 88
    0xc016900341c00a0414074010f02c03942c015615401d81d0396004064546900e090f9015a10400c10b01c40c0d08106800150251104001c41481b501d80300401c5800d9407041d0041a0300c50500c80210b035066000f07942003180200c008072071102d8542c8032009000b00712003d40c1030000042c0d0041c08108440d644540203103a210070302a0503241032035660548280540d0044801c440030550010b001e10070001e003131141e50042d180031fa17800d010039810880040d40d248a650004c109118906000508100c8000266a001070001e0040b1b0307814101442c08055900d004c0c08100e01c01d03200e01e2400308545a2001c0f0701c05401100c0c5004200c00160085081c8807030303109150685c0c040d5000c11251202c2001000290b00940c400c2c0c0d108050074821111410444049464240915030b0401281d80c42d403048006603409030040000000e12501d403480c25600074a030398096181c101100e8942800100c3c3d040d070000b03104a010f892004482d4a1080080b400c0303104072030005000d01001c00d02030107404142502c080140b4419410b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 823345188 1250 823343938 823343951
    0x9070e0306042d110a0602010e0a150f0204030b09011406031e0307050106080618010204050906210f031b06090303040f03050408030d06090c0e061b0a061b14030c0f030a 74
    0x9952034414160302040d908181303509120060340c202405400014142031008020000000c03c030651120100d07000503006020711100d480302000386510240681d544200b003150f4981d80c0f4a010300b205581210003031100c3d4a001b400190042a0307000a62180c0f4006006d0400c0e05813664405525031112243c02d0b01c184020702c44200000c5007446401c1c041c100c10300040a451510520b03402a03c0c0e26250785000d81e90041c04208402c0d120141c2e0035410a0040381c81031b044010b68044001c03548944804c1c1603407031080d0941c14900c80404801000580c40d8a0104504112040c0c40940d40342e00c00d0311401d055a000300002070100703142c0d45900007540c0c4680707803443c941941c60048034695000050f9a8150b0b5503100300801c0380b0b2b00188071b84024805c039828815403602d420000203160f402200e0300a4a10320b840103c896265105218111545502070810801c0c403078441804007245109403002c002090103140071140c3d40548000780c078032134030882c41c081e803130002c3c1c40d10100502d400281c01c40132400e80720b05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 823346438 1250 823345188 823345253
    0xb03010b0c0c03010f09020a0801150b07022202040617010308040b030621030d05090c01090302010e0d05160e06010809030306010302160b24010903020d080f0f0d0b09070e030604 78
    0x17600701c10001445000c207441d4480d0040084240550388a40002d80c5448641c6800c044550302c60012201c2200c101c91300c881c034030b001103083d10201841d80c1c003056842c480c1072105990207a0142c41601c502d03944040e88282c410312009041c5ca000c0c0405403080030107010400c4446104001554880700c040c00b403022111080d00d205540b2100c04020300155040170508510594180c855103910604c1d0700020040c0000040002e000c41c80c413808041c1c100490b42c1c0d0301441940700c0700c810b800025030040456115103a40d401c280130850382400b0703e050008625000c40c41e650300c1482d00600405040d00954503640360100190004d41c0009100001060078101140119846100f190312444405588850988030340110455840c036203501d043c10301003540801e0015880b5000d4403024036074030290751a038451000c0d01c1890f0902900410600412001030700c0d0300c42d094140c200b03113044042510040015200c500080d80c460b05c51035a03040d00f40c2d02c1030000401003507584c012440c69690080036aa5004000c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 823347688 1250 823346438 823346441
    0x50613081905030106032304030804020438030606090c030603070e041203050f070f0513050901120b0a231e09071d01050d03110f16060305100b03010b0c0c0301 70
    0x1a07010022490200040058540501031010b044200d20032585000241046c0c80b144c850b806403003d410080040b00042c02c54072113030b01c000c0142d49039201c558114032800c401c081c0d124110617001d000c0c90f40c0c284074a40443c10300081e40b5000e064003c1c80320403290b03204440c0102070f40005000b180c2c903100310040040ca01c4480405c3d60b003e640106000c0c040010407030405401d0381c01c0030340388091050307402d1308111201e90f1105c2c41c04400740151030407580d24105005c0b090301e10442a0003c5034400868400020440d61168044000500c1504901e1055403207400341c0b41140da444243c0098207242c502500001d05944c104150302c522108609522100c40c9080040400703801c560010142d0301824007806841c14903450104202c0c42c0c0e0361000d5603581844041002e503104410001c0510058441ca1100041c092010314002c0103074a049482c000a040322049494845200d40000b01e4540000700321030516035654901590480151030307155900c0c01407030310f0196101408500307080c0140034030043d082d5003e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 823348938 1250 823347688 823347727
    0x6060112090b010f0e1b0406050c0c04050114090f060a050f120d08100f08030909130b07090f0501111b030111030406140c1206040b0a030b0907061b05061308 69
    0x404d962950320703401d00c1c100b107002c071070302503c0e101c1e4601008560b01902104901114192111840c0c010780721685002c1e09483c04c00c81005050f401800c02c4004960500d050000d488001c0085072000c0d082d4039001544070020302d040d24100c1d00001071201c06d020f2410611000e18000001a2081d110000442120341c100342c5101c0140002825840610408180801c518000b40a1403a214024140703070860030343d5a403040c011024000c42400d0000b5801e00302c88900311000d680c11621011403850100b1008040d241d05008030b109600e26004045841d522406440f80003d4000f00180300401000000c8001480c2180c40c1651641d00c4202001440e0707010f0000d1801a88151004510703200300c02caa041c08440001c0840c10080028041c5914403039440d40d4843e0006801d60700050011484804108a00150340010300007a00310801d120200000042c0c2400300d4002c0d030380d45030880071643e04e51080340d0707040358026107564081e901140f03080b4200c2c4280d00d01c0c3c6109a50003841c0000d85030411030344541 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 823350188 1250 823348938 823348949
    0xd080103031b15050f01052d0904050a050f1c08090a17191d010c030801030615032004050c0903121c060b03100e1e060d060f0608070902040806060112090b01 69
    0x1000c00041000e42415014219451482008056805000f8030402c007000103000c0230340d22170320b802d1740403d090110510020f81c0b00354000c0107490b520f1803400d903910303030784d400c103040702181c500c10200940c01e0079204484c003600540c046405030086204a40f030b61406041084000042040c0c2000183c40f41010030026182021700354884070b1907642d080c07984803210002a40d001381881180a03070840000c0e40f0510190560383c3c0004000b034603040b00034524408941c0c1e42c100810001c2c42820705541d02006281242c40c00d641118140702f81d90340e035002d0490794050003082c19015807141030960701e082204406043d0b500b0400c0c0410b007240b40511782e0034040d580240d00c140060321000082c01440458841d021000d07083d1034102e0031040c200404141028100c24282c4514246082c000c5150b542d903007c1460400d54000a0038480e042d40c40c50184002c0a041c420380340184160040055416410b0003980c04031540c110181990355280c4005427000c1009003104600c0a83d00c2c07441c00000b40398088801d01815 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 823351438 1250 823350188 823350211
    0x30c02120105010f0323030a0f051603030e060a060305030f21010902131707030f030309020d0501050106121a12030f070c060f03090c090f02091305090d080103031b1505 74
    0x7442c5007080c00040e0041c81084d0506980002d500c1c001030400000ca4623104205d1030311020308a1841d208482902682c4a01060100078006074801d140d4076030080c48a8603d11002c3e182035444031100c9800b01d8816100003003030f0f90000e20150802800032000b400150034107012001c80020006e55200315071200b42c105031407a0b035011910f85006800c0c014034001a1900c074035042d10a98004404030350f120014031006100d411041901030801d44a9002402031590142450890100c80d00e003c5028000c2409030200141c3c11b143e01581ea09210b00981c5003890062108100910890303080c00f80c040c1420f44520011300c400c1140c0300080c0302002c010003405005188201a503410702100414000b1050040d030209030030407809002080f405000703641214040140000c1d20414504400040d0050405071640160600a214a100d82d40e400480c8603400c0181078920080c0c20850640702d41c8800e000140c0041c025540448002581e20003100c0c016000343c0c000d01100c61403030031000a460f02160100d5546 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 823352688 1250 823351438 823351469
    0xa110304060e0d09031a07090e0405010c180605030c07030e1201020712050319151203050d0605150d0504060f0c110c01080c090d08090312130806060d030c0212010501 73
    0x30b00b01445040ba602c0d100e0b1400004551640d240c0c001d1029110ba1002c1852400101095050f801441224010300140000342c40610701410000e00814800c05218042070741001d41c801d1105102c41d041c015036000d40c40e00c03411030302d0341052a40950080e203001c60610003005504003140c0d45821b81342c00740c0481c1c24000750f5605018905000e0000008603a24140b140c00c0c0300340314454205039a0221000e2025a002503030320102000141850155071014001c1a80980c2c820706055001000305620000100148600c0d80c0e58801d000300008071040720b02c000c42090121103521031031900000c4e0014024900412882080d00602e8210780c010310a0501003400840e2410684000380000d907022030b02400e040da0f2078a440007549125215060110344110300705440201080300c40e0040e13409040c40681140c8001c40d1040c200320b440e07030000b8a075001c4908146800100d480002800a209000190440d4901c1084c0e56040c0c85501503024100e80c03140341240c00400440007486801d0080105072004038a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 823353938 1250 823352688 823352711
    0x203010b030a0c0f0b122212020d1d0609010809010209060f030415110316090306060602061807060c020f060d0c03020921060f090f01051312180e0a11030406 69
    0x30111241c1c041e00048809000c0703120341c0b121b01e43e0902e0303114000e50056039982101c865010403d0301114070050500ca1840104003402d80c0c000b40744040f20249444428200250b100c0c0643c1d05601c0d2002c0c1980702c0e1701008881c9080d44605030058014081c900003500b8020340320002031454010b50321a000c00f981c003004000900906c1c41c0c0c0b00013800c1203200d0412040011102207446031000600204220b40f011198400e032510441400c1c00640d0004410082552980c0009449980a44500703012a80f100c41c5502c803018086800c4040302c00544414080344007030750a001c40195103000013540a0014801054005a14051101500f0140e6401a5947c22210030495820b0040aa41d120350f00000103d0301442d0001400c15081a03440c08104000d80d40c40d00d03404e00d00240040d061005500b02000d00078040e14504100181c144102284103140800b00c0045404105000380040f040710072500c00c000e00c3d550502c01c1c5801812489021550103e0030b181d0101c113500a403004c840c15039880404202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 823355188 1250 823353938 823353959
    0x1080a02040b0f010c02040c140d020c010c051315030605120619090512030c0f041e05180708060f0307030f0204050f061005032a0304140f10090203010b030a0c 70
    0x910b840116100500c21101100080c03848043c3c110086c092555142d0f005c0406005000c10840300c540142d40681c0c81984003848000f07904a401a0412036007047c400f006401e0190b0f06403003034000416903040c542440c045200c0c0540c0e4010301b0410503d0390b03440003c107150715142c1c441e09070043c00d08000e2040e0304003e82441802400907042180c1a1314298004001078800f1409020115001a190380c594440028000c03151007640c0c03015903002d0f40054001498403840955201c0344140c002048001541d5805000c482c00030002d5001c100800000003810541c001c42000d5008000941241c06c21103030b00c0c002c00c6c13400846401c05e9800060002c1c4d020114039050040716031050441040602c1c0e401c155021429268507014180306110b004030000c3c901001c90400c40030359000c158004c0d401034410742d0b0015007541c4152000d0302d000015064061220a00252500303003c0000302c000c28001c084030314800d0040c80307010000c03039265480c0d0310b01007401d640c1089003484090242c000c0c0b000c0307145455401030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 823356438 1250 823355188 823355201
    0xf08011a03060105060a2717071e0504091410020c06160903080a0314010e040516050102061504090507080105161e081302031522081909090501080a0204 67
    0x2442a07002c0d00041c0542e441e62020f4940c4c0d01c0381e6040c440d900d108149015000c0c00013041b04e80801030000d4000180c7c400806050312142d40000c01690030443d00d030040d0360002c0b42e01108034030310740384200c508100a08081e48482d03001402061035010726010500f845080c008112310807000c068010501c01c0d001132082c04021b42250285929100b031a8135800050182403c0344800381155030301040a00c500ca0080c0c210079818828000e201d4109d40e15124800c50f41c1c0401d4038203951911030341c04044950010200c00380242c83c0140c00030160340d91012052280340c064a0941500940ca6000c1c03540060b50400406010b4241c1300c0c000b03e803502e0300583e9045101e045000e003004120b054030048000c46400d40350f941c22851b451408029980d5000c403406072641c40004002d400d4032030700e1441240c4a5008003098010004041d40740300072103c40c1088001c2103152080917107000b6041102d0160103041c40140d02151006043c01c100781541c40710504100c0d0320990280d0341c04d8124a9801d0210b14241c0b1464 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 823357688 1250 823356438 823356491
    0x5090d2a0914040215280521090a02060906090913300c0618050604020f03121605190308010e0a050c090103110d02070606141002030a03050a060f0801 66
    0x1d035041d00e49500021510041748070103083d000705c00508603a165111003030306031021a40c0303100000c00480001000b012684801022141e000648070300c43c5c04410f40d4940c10303000311031070001490350001d55000c00c030380d99200c1400203610400400c02c08416884514a41c0d00c00e2840c4568004058001e05080b400a032400660719252484020303040c488502c50300c28425404011b140c5041d40c3c688610385140103221100c0c034a42180c0e1402c11850402500144051050f072003502e12100c20441803040c1941c991641587c840c60113424800d61400002d000e22501038503000d141254684040ca400341b04600a4103d41034001880c007a0060240040300728000f90400a40e40080140d46060603103c1c4080c05500b096504040d11000601c4404080d0310641314204104001190303034101d40c1c50a080108801d2240c0c4c15000c1903024541d10f20300d4116150051555190003071403814101c15421402010000c0008508941d13645000c01c0c2060340c4140316020b4170310034000041422a60006003404d0320b119024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 823358938 1250 823357688 823357721
    0x5101d04090b0411030a1a0411091906090c02070902090a090203010f1707030201091701062312030f070b0a0f09030e030c030606012304050d03020c10050a05090d2a09 73
    0x110380006144280084001c01c54100b14660743d21546820701d1800742c1c0c400041c5c2e120501c18140500c080404a00460be0150a00d08128035555913441e00c0580740c0c0c041c04000941c0024108028030115a0002e240c010350091269116a4440c40104101d030003c0e004079104809581c418031542007441c41d140401001c2000138401c880c0f86600003001e13454140035000c01040080100c8607075801c00d4105601408481040342006811529082e05000c80740e42101e124040b00d104065130740c44084211101e15008001d568a011101e4540840500c40900120b40140daa41d1040700404564440c0b42c00b9180b1903510f2582c103a40300380c1054645210802c4a9100f90000400c1c0402a07800c502156400440c20710718070342c2c00d4585080601c960007141e101c01d4001c034203960344e9402c040e40415508040c200c00c440907012070f030280780100d48600500c09903e01040b820450000940381c2030500c41819403240d04842071542c5110100000340f05074111038030304007210603030a10110207603000700340646017140d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823360188 1250 823358938 823358953
    0x6061814090106030b0d0b0f06030d11101808040605040e06100e10030905011b021213030320030a08040501050a0e060a0b0a03080304080a021605101d04090b041103 72
    0x20500c81c41032140c1d20a040ea2141e0300c40e180d03180c0c09036440c0c03500c2e0001a41076141c98500c6195000c0f83c1e0859100e0b20034000c0000c8040c083d4014803051140d07150020003401d051800e000c8120044c03082420442c154011a03a20000161010b4000c2001c0c04143e0341c0c6a03103603850311151110701c17040941200e126500b00031103d8801644220080311181003200c8140d01d44162401c103500820b41207201034070b00c2d403c0041d890810b01ea8465903941440e1780da42141c0c3c09011200d07166901c1c1c0610714040c42080400c4000f080481d10422900d190582c464114883c04c1012140c200e1550f44001d10400c00300701d22008100c1442828819158070103c034200500843c0c682d0074200d501c130f8800a1410100640d02c01142d04c040c1c0314014180095a882000745a881c100350810021540006d61804010722404000c2d1107800c0b00c240c8400f04541002c0e04403c01d450003030b0ba068540f10500c0c1d1880703101109040003203602c0d54441c000d00b40c138240183c01c001c90605260030158580c02103400721030b01030b51200d41c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823361438 1250 823360188 823360229
    0x501170604021324080d020705100c03050409020a0c02151305150c0601082a010c060f0e0d21050c030402090c040e070816021f0b04020904060618 64
    0x3440551041e4100c509080002c1480300c3d02c8010060060304044000ca412020b19020702c42d032aa480a4410328401c40300314080f1001d0490b6101a2401010340010308e801c9005030a80c064011200c040b840380c205a41025203451140040707070050440503002440307400e8000d05508010301101420300014200a01e494600c0d281c41501c0841441814080c41034501e00d4550582030034203075001d4012160948109503520321a84d95900104041d64128003204421803408564500100d58511410707110503400c2501e58440c08010805040070b40002da44440340709501c80c00500c924248403140d5210003100000090100e5210f118805c4500725640c0b521050086011200e02584d034000e6048550160507a5186c1840d03041d80035503841148000014420301000540242d866445200e14420b41507140d208000c00706e83d1640044040b0403c1c880070b0101302d001400c0c0d600121405240648050b1424002002040880f141030384020005070106203011900542a81604000c00b12041c15403039648030507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823362688 1250 823361438 823361443
    0x504030806010c05030d05090606011803121115091006060201060b04050402070516060504181b0e0d0203032d0c1504152d020a090e070c02091504050117 67
    0x5041503050000a0030340350f0400600b00b007119402d400c01242400300e8100717420201e07540c6105649003404034a241d001c60031000c2c0100040750440c1e07080b1954100e040303840d10b010750340110845180300d454003c09201c0501c0c0a0226009401006840000c04401240806001c2240c60640121085904000c42000002680000d40d03094540480700148e42d6000d40c64903914150940c00454451104180d000070480d421201030000c40e06960900b1b2441802810000102c6061840e140c220701c1c40c2c030b00304940c00c600c1111240000400503000c0c01d030312a21a0000380c5146c0024259140106038a03100c81d801c0c0c030f1010040800749101094142c100255203001640ba0010034000e900d031859000002802c5c00201d1102809040303030740c082003100c4c198120400315000030f241825400e66480c04600c1414006920850704d91603010750312001d90710f08102c100052444003510180801096a0000d40580c0e01c01e9030303444c040c0b141c26201210320440794060006450050380144220141c04003248405c0750701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823363938 1250 823362688 823362691
    0x71d04150e1f1e1512060902090105030f0a020d02040305011a0307060903060e19080c01050609060109140604030611040611030301030b27121305060906040302130b3105040308 77
    0x34030a11805444048000100715242e5103c00100300348158200109038025045845001000178240000b0b178a0b4046d5000f6442400040c40c0050410000241e4481c0e0026403107810000d01e80b0054030746221002c40c00140d0304160400c0c2e40d247d544540c0008800040742507103111440980181400e9494036501030b00b0040184006802c5545407103120b0380f809000c0c42580b4500c1444400340f40103c8007170401800300c1d0004241c1261940c41c045c045880ca103040c401d007920a21050b56003040c1c25050120308002199030348285900b0405c14000880000c0346400f4190003401103031f00c1280c40f10700d803010007081002c0300600c2d14206d070400c00050020904c3c41c54a00c1d4080c10500e01e00e40d2091103c049848100000b04840081d4001e4041c200710000c450002004407004203091207602d50f46031410007559204042c9048d610100c100030800040c2810303c0300f208a4000303c900022a0b1591101003114289a007600400f164018810100040036003074000800c1e03950203100b00018649941d015180000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823365188 1250 823363938 823363949
    0x1505090133022406030d02011b050c0102070501020d091b060c0209180d02101103061e0d080f03040c0e060f0111120409020901110d0503071d04150e1f 66
    0x920a10910710140204199100c0c90840110010340ba02d4400e002114044142c4400d44280070710600021010b10500401561302c43e45007422101c02c01800c415203c661296003001499502170140c100841ca0030710290140c9040380d07a012880c0d000c2ca140080c4801064803c104a601d440c0358207002040d4040c49000e8281d9050320040d02c0b640303908150480394100e49043c2d5130380b40310728451500001e501080e030300203001130b00c481800001d1541c00c3c1c104103400b003114500e030002d035040c0c0c440e802c42030132046140b8030300d0019020417100e603031036100d104541d4054a500a01075100000b404108220010420300800c00742800b00b0145c02d00100081125007180344260420111081101d0000002d00c20142407042051003565165a501350802c040d400c0b09203d513020034003503040310307030603039004030b40c0f06440d803034a580d07642c615a0b60500c10f80e82e1480c400c3d2220200c01c02d924100e5a0b07034a0301c0c442e40804a52809110444034549070402141c0c0c90018048074015100c601669038031600d0801c000309442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823366438 1250 823365188 823365269
    0x207121e0606050907020f24190204051509010909020304030c11030705190e0609010303020703061a040c08040c05060408280506040c030311060103080901050a0c020415050901 77
    0x5060706000c0040c1020340c00181d40502074030b041c0a030a50b00017070110083c40c4040300740e4410b1004c10403441e070212402d074039141000a010700091042c081484c034001c4800002240182815224804100017608410a08107034281c0010710800c0d0f9030704500240010202100150303d0341c0b8190382d004250000144006051040f044090151a82d0500c040c0020b40009005140c5002641d0000c841801403880f90006002c0c08002146083c14107000e0103058030742540040c81c080c0d01d10b41d04d12008100c91131906001d111800381340009035485020b0108080718a0740c0c1c0360514101030910703408006103680920720440c0100003c00600e45d020402145812100a00845032414090f26400c0c0d0456175000400d9401503000b00020012601520410f80b4040c0e41c03661038103d00e1801069803094280005041c0701c2092016184541c40ba000401406074103103040250280c040d800704040c0c0d8100040703107981e80c6086a06114030708016020500401c8019a10346215200c0b078440320512010400040030312 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823367688 1250 823366438 823366493
    0x40b0702010e10090e0c0306090c1e070305040311030f0d18091b021b0102031812012a0311030a090c0807030302030904050c0c060705030a1104120201020712 69
    0x582c0104a4021480c41c0079200c40f010341c1d00050000c103090000d00840c2103010901c0007003081e181550007580d100c2c94010b040c01042d5212840b42000c540c0162a10b00c115903180c0800c1004000040c0140904522a448458a4a013545403021502d46180c02040c002d0340201810800ca17000001c0204001c0000d09006050744441c00e20013a8041c080d0300000c0c200c41c1480000d44442c1c21a140c0d2000380341c069402d440802c4071032412020300700554202c40340140d00900c0700480c0b1040310803002e5502c10000349150b003010b00d101c003c20b0030340d10740180d5122120000805190b089040d6030342c260000309145400c01065003501150641da0002500c813244903690303642c40e40d00f04407404c2101c00c003503e40141103405481d52403400946d030340d01014240f405282800c1c0495003032810441aa4542d40085014020540e50890201e600750130080650720703800d4445044903500320700301c0001e01c05032420304010f8200b14198000a40381c64081d07446041429200d030680720105004140c21481584000c0028051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823368938 1250 823367688 823367693
    0x50a030212041407080303010614090a0503060702010f180b010312020102160c031704050f01030e01180c08150f221e030311130302010e0613060f0320040b07 69
    0x1e0194107480410800076030103000074401c880080a980c1c5008408950704c2d1074541e11010b03124003083c400c031000309114414580e0341d1007404010301130480018000d400102c0d601e60010745010003d9500301c0150350b59030351068045155000d441c1c0482c1501c02034a03010045940e44e94100041480b01420f854040801801101d1003074044580d155143c0707540e40e000e030189080980009541c0d11049900510001c050107181c40418203840450380010910020141150300540c0a00388110b148402035603186107070420040b001c20f004804500a80b00d445845007400340d010710b0030110b0408940c20815640421041c01c0c0704201c0c0075482601c640c1403488203100e40340340e10b2551a04400c0107020078000f1015000700318100081e00310950290350309000e180602400b056003072161f62046801400306807000d00155008085600b81000040c103c81e04c0c3c90216840e0782215040303600310f0f00000b07030520702080c003069240c0035060b60003070207403554441c090010022a4051045120b000005000441d101c0d06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823370188 1250 823368938 823368941
    0xc031f1d09010b06030717010e010f1e17030901020c03011a0d050f0105010605090f0a30020901120b0c030f130204020712020115120209130203070306140a23010501050a03 75
    0x204078061320450700c82c140024068140007540342d030000484124800018514030040600b8100d403c59400e40c2c0409080c0205083d142d070340104e82c250b400d00d0f291400039100f41e214502e4900500c0e4a805580c85111003000281021000c600607403003a818002c01e0500012707203501c006c040c05000c894028650100380b80940c105150b07100d200c1c07615464840001440c641003c010311440000b21000d0703510803460310401c02541541c6c010480d51030740445c2d0218840b20501030b42e10003140301080c501540200c6900080e140703c1b00340c101c800101c80c0c40300b0312030030403c003000107076000301e43c500040c3c3c29807904101d8840404e90003010886071040ba24140c000b9525668100c4103000d0b00000099800e52110601034041c0950f1409030380303601c18200c0d0010740351400d00c04141c0c0d4254010418812900c86044071003208008000031303a0300d805444400400121688203005100103172201118091800d030914004480e240c081200b941d002034603504030115152544681500d03c2400c00f243c071030301010000c80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823371438 1250 823370188 823370201
    0xd0b0f06030f0a0f020f0102060708012d082103012304020f030901050f0112051002030c0f030115180627081204030c0f050627090c031f1d0901 63
    0x2c500c2c090105200d043c42480d40c12250994000e484448595824100480e81c44038201c0c0e036940010b10800050149811419480a8092140200c0b0700380c0030440450011100050388400c00030390054621107280003205e04006603000e030741000d10782190303d081741c048013920701d0284120300a600000c00360000d1741d6550590381c45040c2d02c1406a1a07203450040c0500034142a980e0701001100d0b600001003008844032016403442d8800060718048200740016000b9400107810422101000e000418202006d8400381d8000d000502460814000c0c500c0003400308200c154000d00c41c01c5549070180301030380d0002c0301604080f000c4207038060080e01c4480d80401010158010b000e0340e01440703003803807034002c00000500240c80c0119000ba180c250b9504582009041c00e204440e0424018030103908682c880c18881d000c20b4940485545101e85c14200042d03031990704860b0400c00880c08010b000c4680003031240c1c204942081611001194240405600c800d581c0020050b41c038820400040d940c0702d020f4000c1c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823372688 1250 823371438 823371463
    0x7030c1a0403060f0506012c0f0f030a0516050612010320060c0106031a0906130501060902030c030a0b0109030206043008280c0b07020102131806050d0b0f0603 70
    0x20032948801200e144d010342010703100d0074001380c41070009107210050001c601d407601c0c0a00c1440505090608280850f084070185100d501c560340c0584c5002544080c081c400b04a8818001781400c3d1038041c1e18400e9001c001d4000c1c5024070418000318407880e4078900d086064940102491011885d0800c1460f200e0014a4460750410400703c0c4140e000e81e0150001000d0364440c040c680034020400480b00001c110455400c8080d41c02800400c91000303400001e010f08a02800000c100f41340c6500c14441a030b4410b131078501c4210310010400c4980b201d248140c005280091800010003481c503000244280a24066040007031700c0300c2c1401c001c488220a280c5000c0b101415110096500d5090500013500802030811210b00508428ae0b410342d0100102a07407000d0a0311040007440382a00d600169060092a900c20f641d400c104802c0d407115000d00140040c1a40c540965400c080600c1e840306a03840b5500c07541c0100000750a4400142005070b159501c86800780d5204200d682d503c000030318104945081c2c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823373938 1250 823372688 823372691
    0x20105030103031d0a0f050120030304020f130627021206040c032406090b03010810050c040305150118060501120902041e091a0112020d02190815070207030c1a040306 73
    0x1d0f1b50301e6170807200c004560b026282d911101d04002e031041c402074804003000d00d198104100140042c544421403401d4440050120240b001010035184200c6080d5000a020700800c0091480c1aa101d03404e45060145a000c0550078102c00450020707990b20043d182d07512440d120880340100a11075400801c1d0001c084203030501c101c3e02c45408156140b650b0248000023404c000001c04e40c042e860044038101c0f503000c0d005100e950882000180280720103081e9001e124810080007011803400c0005a10084181100259135450080310186d40501581002d02150070100200f140740e0300000342c40c0300f0150905004c03174021880d100080c0280126521204450003452101014042c0c80c0d0045000d01d100d8101c0700980b01040c5c451164500f0b0905c501d60001440d5804100103080010b120540944003a1680b01d40d041b0103403006c02c00b00110703008840309600005040003044182c1100070b4010b456400a41441707403c0d0b448804440c4040c0c0100d41d60200700e000b80240030003c41c42118000d6070800030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823375188 1250 823373938 823373959
    0xc052b030e04020d020409050108031903020f040510110c010f090e0c04030c0f080111190e0a03020405010803070312060302030d080c04090c0e0306060a06120c050c0a03030902100c020105030103031d 87
    0x34813002174000b4059502c19918100c004070ba41035001080390824003401d022114029504501100030b58442e1048050b10141031000103455114121600e0840c0704e5a2507080c0c0d0400b000000621300b00000762440e042011002c2d2154076150000b0440050b03034a4520307080500e03a1103c088e41c80300d2195610040000040f2540003504008455400c4151400c01e002408034a44135140f16204d03004032220360860742441620100720501038a464040542c003d4820400e5550301d40008049801c07d9002501300e82000400740b0425a000181d130502c0109280100502411078005c00d41c2c44502e00501002e001001005c20300401c06001642d00510307000714180700c10035000710010024640e014038180a44100d8003c58102e141001c4bc05040e07602640e00c0240d604103000c15400640740401c0b1007410b00000700a01e4111030f00c20b0004081d0700c1d0098a0100341425103105014440325241140340421a42e00c44000050b80d02c0070407030703044a8040c0340001e4940c000c00d248410740c640c01a0038540c010035a07503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823376438 1250 823375188 823375207
    0x30b0a090509060f070f08151002071701020c0c0918010e07150305091002091206150f06070f021323010807060c05190303060e130c052b030e0402 64
    0x8001521410401d4142ea101d5159130158620960060b80c900c000300352520380310503442d88510440d0341d103e008614401200c405140c04140051075040101c4011f8000080c140441040b0050742102010000b00031481c4c0189074000303503140d018038021144500c40400c040384a602d60900c0f0040c40300c1480008000e0f01410820f07083d5103081c0d611580e03071818000d22560000303030f010b03219040c8945c5004010380030100d101000180258041008070341d0154180c00503010401c1c00b0041c251003460605641d00610b80200c0c20001c1030f080b4070100500c21101000000c00141d0890700c0c13804065410b42c2c0040ca008002e0a114029014600d01e000c4803007981c80c04601c68903503040007141200c040c0f4003600c031718a40304e1804888080814201509581c4801104d00f40e07001e6100c00032402038064030300011555128803c201e01810280c4140c6502c0503000d091105020644042500410b004c9544050b90290404003015156900148082c41e03040400c44106041c052203269030318110081c0119610080320 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823377688 1250 823376438 823376441
    0x804060801090f090209070c14100605040e0109081209010f0f0209090604060515030c090607050a05010f02040e01050d150c2d020a120302040306331410030b0a09 71
    0x244100c0b480c8908100c0c440842c680c25110f18411241c0107010411244c2e00d805041d02d49004000080380c1440c041d940190301c0802c10310045003445912100410b9031444c10080006444501044030000c0c1d16102c3c4010008280c070742120020031040b82d81c05480c3c1d89001c1c1c00d82c011321004254503003840c1001c1f610707400c800c2140d00506040d10121880c285c40e8485006000484005009080e040310303c401580003100c0d03008001c1c40e800812142482d00d0100c90501040154020542c122515800b0890101c1003080078001d0b515075088100c401c5050500d0404045424101882900c0c001c030b035108012024055400341420f41040402c000f880380c0c0078100b038001c004001c00d192401c0a0200000311111804028050f06480440c641c020b10301c6100315210f24210301c04102608050581c20031001000640500400d8120000d028694078000c01d00c4d601c03240f181281069900412440c0b040c14031840c041d88035103101c0b01c0b00a88119002140400060300100174640c2020740c4010880782c000b41c210750a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823378938 1250 823377688 823377691
    0x30f011d0702191104090b040c15050315061303080301180938010909030305090a030c0b1f080d020c120303041e0807140d0905090609060d08040608 65
    0x80094541103081601080080015500d0303500581260455402c0b1091403ea0500034502854410014842e54400030381207428490044a0001c1d940007000306028030b2000d0070004061110380e450440d860382500810302d1000400c04200e401c061561514580c03102d105452521038902c0315102182d441341001c016030b8009200c2d0501001040070120804180ea00481a0365584504807a4028050110001100000909204480da820010004000d0204104034000d041800c80001c2c011440e04008058501c0140418140e5000004490020b07038824504501d072604801c400445460707003090161880c9240d030b51403019440c0550040b854480c040307004114200319400312198800c00b642841503030500e000c20013109070011303c0050b010500030362074031092403284aa402000000380c0c2d00d0595035007041f54103450440052402402c040f004104c00d0102001600b0100402032420000a083d450000c244030301440319800400c51640b20744622240c0594001800380d1207030f484400080064a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823380188 1250 823378938 823378949
    0x414063601021c1a0105030a0e010902131a0f030c191509090e0705090a020d1b0203120906090709020c0a080403140c040b0d030e010c0618050601080f1e0c0303030f01 73
    0x284c04d1140408040482d1508440001a124203065941d288850002000700034800c840319529801d03100b0050b0f9840c1d69500e8090f02140c000110120a2030f2203c3c4180080149680682004076030314081c0d50300011300c5040c1400440f4004400500007400c003103000004d5006010342480380300c141c0301841e04a40840251130411404000c2d004a1041d10b6603111400e1058640003c000b002054482c0002d0300200703240b699031240441c450220021008148180040b001c4c0141c0012800c0c00024400e141c44030741180c206002854a4100050810303141c405510843e03078800c1d80080c031811008014490741042c1c80d0810380e0326454580d09d04140e07144a060a15410342c0d4000c4482c8049186014803034609904d1014012040000070b50703805490480c8140341d114180300c1011000d0300040c019004201a00390141121004c54140d403601500e020410b030400041504075020444144131b0010342c0702d400d815641d1400e000818440c00380e60804600847c0c00d5018000002004012000b07011001c1c1242e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823381294 1106 823380188 823380191
    0x18061c03210519060303020c0d0f080a02030a170c070f05100f1505060309030711010507141c1e05130807030b0414063601021c 56
    0x110001c24001141d81c40e03908002591500461040c80e04074001c1052050704e0456078060b403115404407203540265050780003171007444080300c59a00c0380c2c0c0d000503c2d145d0700c008141c002074882e4002c0d002e540c046040444903501041c0d04100241c41490a24007060401505075200303100e03410400b00c10ba403544590180007420307143d03600c9504042d000d540d2000485040326450f9403210806580414480e45c81031003040b00c084404022280c108c3c0d840400a807000c1240c00058845024065004e46801d074000000d03070704000001450711840e114401555110300f0804030440d50b240c035108002c94030115282c0e540042d0b0380140003030a14012000700284500c1c2d11040300c28501207040d48180c0f02802da00c03041c030041c818688400d1002102c5039010b40f00034a06141e0710111070700141444103c401c2c400c524070071070366080052040c1a0914000035582c0b41810700d044c0f031101440b1140f909400f03 = true := by decide +kernel

theorem cover : BRFrame.Cov 823201438 823381294 := by
  have h0 := BRFrame.cov_init 823201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823201438 ≤ n) (h2 : n < 823381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
