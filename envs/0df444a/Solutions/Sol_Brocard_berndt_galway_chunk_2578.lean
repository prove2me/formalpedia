-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2578
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:07:55.747036+00:00
-- url     : https://prove2.me/submissions/c5735a0f-0162-47c0-90bb-132b9f6500b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 463489208 ≤ n < 463669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 463490458 1250 463489208 463489219
    0x9030f020f0a151b030801051c02090c190e1c060603021206070f03020a020d0e0103020d24051c0f0804090e030d0513020901060809070b030a020d060e010b070809 71
    0x280d241c1d84030030144201074100c00820741d02483c110741008084a41310320720740d241c1c2044c0e070b1440000603030003290f55415540c0840310b024140800104607aa240a5207802a51040d8160b00f0301594a034010014940c1c0300d031000040c02c00b94000003081e120202014801a0404442510b03e10241033055003080c04034417a00c800704900b03a884d00001c5003814010280070075900b01d01c0901a00c15000b000c42d06411700c06080039403c118080301c01940b0342c00e071b21150074103203c2c1010465070160320a41c1115020f520002c001c000b21840c03044902c0b000100a140701c03171030090010b804102440d00700c803034940b140725900c1441c41a07035580d540d00909804d058001c130b491210500000c5984081405201d5401138810015900c07280c50120f440203840010300071104624003a110f40001da03c03032100c401e0550715242480c6601e0b44642580a260090660000001d07110200500c5411001600280800c0407500418020b03503865111101041c9400c2c410f00451820402141d00002d02090140c066818010003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 463491708 1250 463490458 463490479
    0x6090f07020a02030a080307090f08030405011407120207030b070201063507060c020103050f06010c0f1511030f071e0c050705040c03050402041b0e1e030304030506040b060d0309030f02 81
    0x4c00d01d03140055000301c41d0b5513004030401801c90b92000845008040c0c413008440712503e000803aa44a00c15030042c00d0411291030440c5010312050004c4401c02940641720031050403000788000d440d4002c80c001202c00c0320505011854a17407050284100fa11030350b1400000c9006142500b80d42c01a910b03180040c40309001800c10300040c002d00c0f08400810144c1c40f00c0c1c8050423184001800c071140106040040d480c624284a4580d81c80828001c0d080e070303c0990344991250b40c3c146000100144034443c7c20307160a2040c00790f07440d44aa805036018140e07020aa0f807980c0c072500700c00e0f20b130100d022200f191181c00600542103d113100742011910a4011002ea904036525040442c1c02e9a0941c650794012a440d40300340310450520f44102d01007024448205a2a041c0d4044e0043c01103c4070131600d481000300300180f40401c802c2c0340d181803560b680241200e644039641e00c0c001d906c520b01100c0c103a910380c1ca490002a0903041007400702001d6a459684e1003129811951250788143c000001aa00b0800e00f4a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 463492958 1250 463491708 463491713
    0xf1f0603200a0908011107080307210609021b060f06150c060c250c09020d140f0717040803070807030f060f1802040e060d080f03070512090606090f07020a 68
    0x20a205403541e501c2e803005504013000c082c20341e10700c0310070701c4038080b01085500d01054044040ea90400e42e00d14001500e81406881446038022130420300c401540741040008902a855000344016200c1c02100d0840c41d03114507a00e519448116a01e0480c00d90003c0007031121f1802c0034001c100034103d440314605040c49100d500c1c0c91309c40c2c1100c500d1808540001c610302c1303244111a03013100407003a212408107a5a807603900c182c20000544104d081044d0003203a02d011003405500701203403407021600d6118041c034280000320250001a41c1840202e42c4440b00740c4d42c40c581c1680b00601c500d420500803859600c510004807222031000304908101a07441c914070390244c45900031000144041c1001c0d41c000c50501a81c15401c502d60010700c0705072841040304102024061030900c0e40804201d8009000034540c1c00c140029104100b07150f14001000410011001d400402030081c2004030300a1100da59124154143d40d010b09640719075000c00f08400040c82c00c3d40f40b414941d4041c56500c1651000b141c5a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 463494208 1250 463492958 463493021
    0xf0b0711010c030603030e03010c0909050a09060e07050405060a06300507170903040602070b07020f181501030e0a02210a060e0c03061308091809060f1f0603 69
    0x405020003c1d0b15440c0801c245940542c20b030400380000c5008001e840003406015090042d03a01c1144c60050b00d45002540140459000c080b8203608882e06010146440c4c2030300780c031440c65019041c8182d02d4070020032088c3c00c2001d064002d6880703036101d080b01c050f80e241c4504000c94400000080c03401c0084400c0d00d0941d120301170f1a0084074192036080c01507404c000132a110960041044000d80c0c0f003800304000c010350000358042215900060281d90306ca050002c11110007499a2094010100052446140d245150950304ca030a00d59641c01c02060500c0044082c0c4d00284901c141940c010002d603005484c00100590412001e14200c1c2d200254000180b800c00080b14001c0d2201070340e400c5003000c1140c0c188a4010700520480181401b85000c02c03101444d6014070102900d40940450201120303110040d1140d8400c070021136034100d0303251820419960b118101c8008880c01001e50200b03000110080001c046601c1c881c0f1014101c0e42403850840007010030300d0144030940d00f4007806a10301c141c0c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 463495458 1250 463494208 463494221
    0x5030d0f0615020a17090a0e09070801021234050c0a02040e030703090e0c03071d06030103060902030c0103092003101407081003020d031419090f120f0b071101 70
    0xb99005082280010709180055280c0d40c801300d04000d400300090011a51280b0f0400d060340c942c0c149500740d54407850a90f44c540034403904807060030340c0b00040111100c0701d01800b2521600709491319000b8050100d03510850080b444080901c84000020b040c032203180502c000d4000603074a8400c9810041007900010255090041d894680d50000038100043c55401003031038000e050050314182d05403c101075030316a184030007001d032404c0000c80020740e00c03003a002c640040480d11008042c0e45d1a03507100d08110000b021b466074220f100c0e200c0c420150030103501a010390120b00340c200c080924202d1030003044011081e06010f003140d040c0600c40390030030607040b00d01c1680061500e100e0b8441c42840c06030400707001c02e54064803c01802e607942c041040107a81d42c0c5606124243c1c940b1b890012452021f01480ea14001d0100000c6800b900701122254a54001c40e10802c031420140c0b904156503030f6103140b40e0755450303110003d4040c601100195000c24a88026290031000c0d515100d2521040f0007040c6084a99 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 463496708 1250 463495458 463495499
    0x90a0906060311041a0603130c1a0909090d080114030106030203060a0e070803040308030619030209090a030905010f09170a080f0c06070806031507020c0a030812100305030d0f06 78
    0x1c40c3c09014000c3d003072505c034807400c181080c520690a00030704030000340c06000041885130702d030803180101000c0189900d0784a0040c8444030b01081030201e82c64490509402c581d00c031601400c82000002c2e07082100180304250008a601c50303045590a01701d910401c44103140c002500342d0748541c40040103031030401c40c06100300c0001d9030000c0c3c1c1c4404040b0380c42c00d05510790b0120040390b200303000034004034595908407130300070300c08035291840c9003045404004225020b500103540550a041002140c400c085003490780644680d40d481e08054551006582e0328101c0e001090010750040d40500c0002001d03048202d41d070b0401012585504551344d04c1c604140c0c44500101e24207203010803000001d070f40c100040782e001501d80c182940700385400301c0407070794658000407180e000d030103000c0201e120307140203001d8000812000b5240b00c071640d4990418004a03400844545000d92030303800058000c205012481d001c1d030340e002000c0d5260044140342040a88080e0200b0740c0d0403031345c401d00011104010043d6044892 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 463497958 1250 463496708 463496723
    0x11161221050103061a03060a020c012a0206160c0f060209060705030d05061e0402030711160303020c060309031209071d07120b060904020a030f02070b0105100f0509090a09060603 78
    0x181141350800070f0762600c0c81107140340c840d02e1205803002d0307801080399540443c25010050303e50000c0080c00d0702410b800001400700da142d490104075102c81c3d0603041c041507841ca4084070000c1d21140018a80c40c25418580c800280107862001d001a003c183e0070402507020300c0015060100c080e0005100754800a022195544005032541e000c9510380036040d44150f0407101034030180e01d0300605801d505200b1034403a100750390000c00100d0031401429900422081072045506480d0903503100c8858003064042030f030141c8250700440645280080450b881012080d01441c10025803440c1e04400d00006000f4400c0d070f0207040400300b0882185103c0341d00c10340b21580c42c50250b050003040601551940c2e0300d0340340c142d0f040076145d05a0703845002c21a40110800d8900607990001d9503800c41c01000030f0f1245140701d034000101e15017070000c1c640100e4165441100e8101e201e00b007890094540d65211030101303022510502045009180200365513500112420b0086410495541c3e10401c90b03182c0d80040f03c206 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 463499208 1250 463497958 463497961
    0x150f0102030c2409010e0d0e010c06050c04090f090503190c0f0312050601020f0703110307170714010f170408040305030a08070e01170112080f030703020307031116122105 75
    0x4109038800107030004144d8000300220440c070329075151035444000d07011050089079001301c03085074410420485000c0c2c20100400041c240124814107950140c420010010b060141e035508550080c030a0400465005005501e400c20b000c0c00b2005005125002c142805007594901001c54036000440f01594440c0d41c821040011001c0c10408a9401030000c0b4110352088608150525001505c01d040c1e80c0c0260702c0340030011482e40024500b43c0075420bd03101013202155800d886000000745101078840140c028821f04501d24011201c1c03201100c030f1480010f00e660a01c4444600e100d80242e0401e004040e034503e440d032281c88552441d4040400300c40000c03120010400ca035588a10307594040002480c12400075007101113000b1604106000b110700e0504103c010000f041803490495880448070021b954592420310b5014000390411140b182c0407a040c282006001480501180c41e0100c02141d19046401c040d19980c803841901048001440310002d1805e0b00e1146a19107041c0440c40440041540d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 463500458 1250 463499208 463499263
    0x2030403080a0e0c0108150a0902091509060403060e0106090504031806020309060403151b0c0b011d04060c1107080d14040f1715070507020f09150f0102030c 69
    0x80e5000700009202c900d00642c0c02e07090903012416034480e003030910f000b600c507071100803090503100302c806c2c0300e5942314100c520b0001d00b504194004d0202442c0c00c8030388400054090b0b00c0c5d40c2c1140b144407592540220200b00900c0002c08613440b00041e40c008800000d150354442c415541120010344041e00454503260758214000014000305d0054034040c40a0b50924040720080303000350080d800b0003440b05880c000303032099030441540704a0034074540d107502c1007001d1760707250000d4100314240c64140c54007090400042290800800d2001c401034481c03420400c03070707070340d5481c2d1500415083c0500d0302006524189a0f89060080019001a0441c07802400000c01d00d60005010038072040a013043c00c0c001808100400c00111094000311220110b066000c40400c02e201400c010085e081c0700c4441404105020b021944a8060400b00d0720940e41e04c41100c03401c0c0d0402805820450b58556050440100503010341410030f084241c3d000103004807810038a507503580500b4a111103123a1102c611428000c1e460 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 463501708 1250 463500458 463500467
    0x190804090c080a0c0309051b030c06040b0a0207060807090e0702161517060607030818030a02030306040b1c03030c0e0d060207052404030c080d15030201020714060306090a020c0f0102030403 83
    0x44c02c2440c03c080144d2101c56880b59111643d0200043c18060701702040b015a032400c0c02410001c4400a0090ba6603d40315018180c0c150480021040144108000403406c0d40c05001a00e000d041070303440e03e800c000c0c6848103c0d500741b0801802d0f102180141120703501c0041505d4059009800c0000c02c1000c0303020b400000400b260048001d808034440c0340014004640c5809040b90202c030341514214400d41e603840ca901c00740c91922501410607200c0040c402210700e90200285004940444050280024030340030001045580a0b20f520a500608a4140041d0080e03000b4402c801290518010340b4040000080c4032401b68a4242c850940000d5501c1c2045410f01803412414007441d5401d034018001000203600c0c3c0001800202409801300444083c0310240742912104e06c0325450034001c6180d02d40c4980e4521407079200132800b51165500c0401d6400c660300140036404005010a0308540d2040200116008090715504406500f0001d00c65801c03002d01c106c0880440784400983d59040c03e150080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 463502958 1250 463501708 463501721
    0x5070305060a0911060304020a030f061b111c090b0d091104060f09090f021f020c0618040b0607170a1e050406030e1c09050102120a02190804090c080a 66
    0x64400349004003100001380c1e801c111900c000360564000d40c5071369407440421170030221074001801080c010414442002002e4000f004000320404280302c042e503403c58180d8040701c0c00c0070961595003200e4280707a02c1c80704010300340c0010b04440c5040400a50f4807140949940e01c406424815152550702c01c50134449491070100b800c0905031800c100b128030b0b003000c8501840e2076007c0c1090058566408030103010a40303c0001c01150001c103107648044500c6d800031120000091a5030141c000e0b404460038600c1c0403015240703610a141241e2208000348010080100780711360800b07a00c036000303101400203c0d07107640c002c5000d07503c6114601c0c0c4d118031500000d0080490108548903584010418002c91540304043e50222011410040740b5211045511070901100548491081c4000072000305030640c010748100c00c07648213800b625812803c41b22081d40702d11900d00ca040140c0d220480000b92291024084140d0324003440f81c1c0c3e410683c0342c045ca007095035a0007a1504c0041c203903400f0301c0342ca40064812103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 463504208 1250 463502958 463502971
    0xa050105131109090a06020d0b100f0503011a0c01093f0311090d06050106030f0e12031008060109020319051e130606091d0f1207031b0507030506 64
    0x940450203540c2e10101d041c401d400c60079000340e40c0c03040454003c0004110754000c4560000b000d42d10b602a51040400410100c01e51521800c2419541100c17240100e88440a154a070381c2c41030b1a681c01c004524451a031690b914801805080100d410440801e1107409a0342d80b0800141a40c2c0d4404030703400703002c0000c05100362b05850121680e001050b03038040821407400c03c8ad05000c9000d4401074400d1803203016440d09560446d003c1c132841d40400c1035640c000d0f416688a51410003100080300e19172802c49140c510030301195070100035604c0c8a510040c002e11b610406188420081c82d8940070302900340301c1c00f84e0000400355000300174002c8030844171480b01e1b80e100344490700300040d2030851140f440211a818044050003444004201c010003020101035a540c0c00040600605907500c00f0b140061544409081d078001540900090703030038001c00c00710076001c1c1d090000d00d504050051705480f15807101c10308a040c41010030141a01c0c6034000e1211251038081c402800c54140741d410183d04290005004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 463505458 1250 463504208 463504231
    0x1302031f05070f02060714070203011401030b010b0f0d050c2101080715080a0c030b030a03080a06050303090105030103031d120307120f050a0311070b0f011502011a0108060a03020a080a050105 84
    0x1000f1a4001001580042c05241c407001000142a04240358440d512010b500f6500b801c040390701800460341c0700d5049a21801095841d41e1740c9600c00d803618007840f03101c8100c2e00020000b440c40c600c0d068100e00c0d001501ca4100da498400c603012240030051000c410b03c02c10340282c00040050701c00610040c0300601d030700d508004072401d4002c001000701d500141078907030169440903401481c81c400d42c006200500042c0840303200c200517003000340501034100c0f18901c080307007043e0011a081c140030090718031a1206846841c00c50742540c0e000d8603100d21444108031280f0542c609940c95a4840b11030498120290002d1030740d41844c2c4c00c2040d103c2d00f080a0384014401046015056164010110350a14002c0d2a001807400c50088122a440c03041c1c40000d440207050b02c0910128000781804103049032040d24085001c02d020400603400c2e25030306c40c04480540e42a001148095029101c29644401c00400c8040c40c251254000f0760b6840c43c82c0c01040c083ea06c01a400001c00c5070134070615800011a121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 463506708 1250 463505458 463505477
    0x60304290402130c140310170c032806021207030b010207060f0f140a0201020a020f06130f050f0d080603070504050405300c0d351302031f0507 63
    0x10400d0030b010081c120040f9a90f0344c18500c4040c0c03080e040d078034079401481406070352400c2c5840100348203038441c064060b01c00340d0b046154502c95000101c210b0028405006480106170720880846920005180001c14038101320400000030071600c02894500345c8104504582d00b440240142120180001a815503000c98428440c268124080c0402c99401b450002c0750031103103900480c0c0c031a0086816004012001c1040d503901c07138041d00508140704465080740d144101111082c0e65611050750041700940d1007003030040c0424640345180ca0303682e00500440fa81119140c1071240381103c903400c410001075101040c49064981407000200800007202c0c140018203054480700d48514100c4510101d1044001c0580449a040b100c0f52105c074501d4542141c030f442943c1d99440d00d6140c2a258000001d0240d54008420800889000c144520704801d040c4488048040c203919140c018107804030b0300084101c080010f80d401c12008081501d2800b4441ca50501800001c054910203070408091183c00c49 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 463507958 1250 463506708 463506713
    0xa08011506080c07170903010207081605060c070c060813050f1510050a091a03070f0306140f27030406030b090106030e031603090302101805040204060c1506050603042904 75
    0x142e41301111005c0011699036001e0f40340043c0c024840c903000200011404900b920071b1110403000b804201c5c1c022001d48107170780c0da4070041030000d100b0390000416a800d118800c0c09050321615145500c50381076084817260020300e071211480c240c0c0300c01d01c01d0081c1c3d200c042800f110f5003649205640100c40d10306400e6a1a040c4400035031000780e50b004640c0e40c903984020380c490001b1501440402c13600050282d408094a800f1214100d900502042c1c610074140015a0741c4c58085400f170740d1055000b40400761141d1242d801c0c2c0007403400304c080c01d4091000707901180741c1021001d20042c00108040d031400952010110144100340b04140d1002092501d0100410110440030007240c482d000b10021486034500030b8034042e0b4460000da04069081450321040c451419084041401200105606111101d54800401c41030f4891030003403400184100d82d1400028008001c2610203a07400d00003c10b80799210030105045400c200c40c1561611a102701c44100e003440300003180007803450000300701d881e460181c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 463509208 1250 463507958 463507973
    0x2406040b0f1812070e090c010905010f12020f0705010b0405280204150c0b090c300a05030a0908010c08060907020c0d050f010b0603040c03030e0a08011506080c07 71
    0x7104264a81c00005070040ca41003a04180c4000000c010020010602c4074410541e13941150b0041814000c088000301c1c02120300020300400c5502c05039244002c1ca03083c500115864008648940180301402131079403a60913450010b4500c44026265080d1501c0003030801e0b500303480301540424041c52408080c040c16232500380c1203100b828010802e4810340a41240070200920469000031500340502041c40c80b441e901105060016001d4a9000300e2522540040d41e00d4130403210740380f82e0040018440046682e2001500c880d45920031141c02c0e0014250106c4500348041003904942d01e0300006001d031070480d040905c100142480c0c0c8000c000400071010040e080040c00340c0783d24450100180010030661080050954480c005070901c03504400e6481c01e503985243c5e0200703262255081070030364442d5041800980c1c1c8a0390300015094003007855a00c003030700c2070b0f5120b11807550007404e104030109402c0000d0003207807001107039800c01030802450000001d1444e0000341c4030061142082207040c003c260341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 463510458 1250 463509208 463509217
    0x9050723041a040f0f170c0907080702160f0305011514040b0f040218090601030b06090d0c03140a03020106050d0203030d05060102030919050405010603050402090f040314032406040b 80
    0x58241c00001c0350720028030364440d4003da038480b104094a40201041101c0810341d2030044400d112000004030124503490b90310380418580b543d410040c4080001c02c01841618100d4202100d40151035440254410903020325400c0d41000e560350384000b00c100300b0001c00348681100201100c040d808070f0b0741403070120300800c00c01d802e140c0c2c031964881d90031001b556100c0c01c1c62402024018821545ca01e41d42008015000360390700307080d20502d003400010348154000c0c060000f0300ba1005045515001903c0104495000c5140044e00d230b480314002c0100c009940581e0450306070424000030000444103180c000c1c2514001d800c442d0042186400389401a2400402e48441940051011520740d989200403481d601815062681c00014030b40b125041301e000042640645a060300c080c011603072180703c10b40548200b07aa000350858440b6000500c08000200000e40103417192a10300741c514403022401107107800c00c0c2d40c48200f04803118080d01680704403581000a40704140d03005403e10780f81011888070f40c0907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 463511708 1250 463510458 463510469
    0x30206070804081c0b0f010504050127030c06080a0c020c09040b1e010f0303081b0f181302030a14012706030807050303160801030c170f070905072304 66
    0x480070003003010000c6080c280c0b03500e50406003040e0f0001003003001e408003502e00208524007480d03220035480002e501c200100c4003503840623143c074000d403040b02c51400a00a48400e800b000a12042004000a154000e20800418413035a52913494200340f11540103e90221000b0300075503104400c0c0c0e1703615031501c072405a402500070700c410b000c968610381e480407824541450190729030003500000c90400d00104003003041d2400303030381c0708440c3ea07441d40403215440008a80355461820b0501c0080c400241c0400141044158000744014000f1481d01141c5c4c0069164079203030f0384030b40120400c1140070880c0b0a40103c02044101c0304965450402c003244062001c040314003e03001d41c2854210b1442c1c3d10340240c8000d5034417041a507615011410032503160781055411640103d0003001c01c2c200148a50a000e041c2c0c1e41201c9100a018682104844c06010248101106005074002c51500d03180510090006018111000c03d030b6260004000388071081c00104c000400000c0401d80b018610b01c90251380a584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 463512958 1250 463511708 463511717
    0x260a0c05090f192c031b010e030d02071406070801090f09120e0a0f090213050109030c2309090105041e0b040204051b0c0c0306011a1602130c050403110405010303020607 74
    0x190b4921890328141c00c6000144e418010310101d20700c000000100404480d03045a01c0300185180c10000542a61051042059194000d102c0c2002040d4a6401050800e2042c0c45000300d0040d80700343c0d68103114046444901140c0c07400d00401100d00d02d40200da01c010070000c002c000e409800e90307a04500071003410030a400c00c45504880002034817511010710140c00d074504416a110361b2400100082d6121400110384c00e80c9248000441d94002c07100f00c016a584045694200c0d402c2c050042d4031200002071100c911071402d100f00c500c545502040c14003c0d090500081407615090901c18001e41c1058540317407a8800720070410003c101e10810203504154125004982911070114a0300c40c04a01000d42164050004078007070400000a05050f0051041d425110140e980f80601c108504040340c0312440c0110401142090f5952503280c01c8005100800160901e03034110103c01c2120156681c0ea400704400003400d000b400711541c4d2500184608403824040c41d0304586c1d00a4136034074013420315010710 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 463514208 1250 463512958 463512971
    0xe100c0c050406030803060316080604081806030702100b060306130e010e0f0607020d0905011202031003151a0f0319031412072007260a0c05090f19 65
    0x315040292005050041c024000ca544a040803a866030096402c1ea102e80f041d08550b02800340340c3d81c0c001003282c04220140400da580c6c0e03111000aa4410070314407020400c4542440003e94411001d10300408481e0300428045103145416002c8501a0140600c07611040c810000c4555800c3c2c0301039051103102c203000c981c0741404003600d03002d000100610002e40c050140e1829000500052141c42a40c8943c200c500103442d040c000d40b2044014002e00740051300822282125070003d4004680041354810350b164002c0d40c1c3d848180210f0300a506580d085510b0300d006e00c0030280080000c0c40c240000311b41c0d2400c41300418001a50340e8400884582d4480d0040d0900f905040c01903600404422042110039540c4113801108614034004035a0480030600650f041d1220103800d21104400c551164001e0070b020303082c58005031902d1401c242032960110303c60100c0403000c50900003c41407511900028610034104000c101115000400a070280e94140041003032559440c0911042d42c2a45580001c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 463515458 1250 463514208 463514213
    0x5100326030c0a0212070305130e0c180315270c0d020d02030304030b04050105010e0124110304080f011a0d0503040b030a06030614090d05130b030a060e0106020d02010c0e100c 77
    0x3890000414690a00d170080b078640305240e00003001700040440401207291242e1604820304611b84165600d0741c0c000b405104080404689412002c20400010204d600a074401605c2d001c8019049840075400034000d81d580c40300600034000c002c13441401a014068011050010800040c1000406403080c86801170741025034906204440c00755800c41c00311506032074a42400ea0107001c0a106075031103004200d000203540041250301210304128000d40751002c3d6071603002103444001c10a02c0e01c0c002d010030003002840100811105201d4030100b07002180083d044840c040400a082020b1400f515408455600060021003190192600ae00805850703480c0e14800c0c1d0300500f10303600018199454820b030011410190320400c3d2007020010226003020364103950856035030040b20701c50050240c3c03800d4140489000c2601865018010303040015085076516807a4074040400c1c0d00c100f015170400c1c1a68000994280031300455512242001c404280c0803102090f400d4802d0805042041030840c00c0604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 463516708 1250 463515458 463515463
    0x40c030608030a030c0f03060509040f0c0b1b01060b1914040f090504020a0b180d3809011505041d030c0114100303020705010c140105100326030c0a02 66
    0x34007203a4044980320030000c50701070300424189582401217082402c3c81e41040d44070380075180a841010341714003d15115a6104800100b03081c41c100c541d03089401001c40c1154058002d0080b442041854055501c0009542800c450050304220f400110400440003c242e6100c002d40a0f088145003815100c6c00d1050040505e00660300100d034000940c4e800007d110009421031405540200c56104440340c1d5904404210300c00d0813549058a080c09810520502d003c20304221003d0080b6003480c0000c100f84c1c20300260a211031100d004901625103900305c06104480f9240d030142100340208130710313280004880703030840c0e42c0d1040e01c2c4a140c07140b8603c01030794090180390700c042ca03c0c141200d8a0f038480c41007443c080c0c014004075181300c86500001500700c00c807610020301101d4068014001150605004484840c2d01d200107480c481c805440b11408280d00b40300f010301c109038920444a0311030440c03404d00c04810114600b40c82c160900b84620f81c1080c5988100e1390400f40d40095a60b0340d0710b00d400160b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 463517958 1250 463516708 463516721
    0x40c170a061a0f070b15180106020607030603021c02010311033105032a07090b0f0415061b1b030204110304030816020f0114180a0b0705071a240102010e030702040c03 73
    0x2e401c160020040442c03d1f041c3c0d90540d05850140d02922210340d0384840890444000b8400603510914800c0c00900c03054000102c1320380b90340185404981854001c5007244240d0054499007c2000d00041800c503c0c9829070103241c010304038100244070f142c56034445d0340ea00c2c0a907212a030144120400e2038585508d280803490388890f00c1c941030b28880e680c1e8110703a5005103940001030b401042d50884074401460a4421241e03501d1099140d215502e09090007120b040340d03072044120311020b01d1000c0034045510b0380121050044400381450841d030941c8103002c10f5820201000b03c20364428400d1100181d0420b015a50116101c80044c80040920700300f02d1818045040c901955480c001c0110b1104a03a504407034402c0b90484c3c00104500480d220b92a0794a02000018040c1e20700c0c1c50100f021248070310018441d00c0c1c0502401c0220404650030380030020000d9030100c1c1754515103032200702d903400780c0c0725a0310104000740001c1110341060b901c0b0b15264492603c2c0244900c0d40d4a074008100d501960201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 463519208 1250 463517958 463518001
    0x1503121c0f02091e0916080c0306030a0c0312030c03021801110c211c02030409020903010204090606030c0809010b15030907030b130515011202040c170a061a0f070b 72
    0x4500004ca1400b100c0038901c6544400e03001e0600e8400017070381c4504501e902803040c025547c405286039100521645d0581000d414035906003d0700ea208808035107021b1a0b88003550040b134189440070801403002c0c5c1114540c00f5441c05060043c0810b018204403a40190a10042800d004a00c8039020010030309190074543c44a901030403102d0350020344500f503c8110324a880b05003c81d408408041c01042d035402c40490560010b90040109001040980d0007512158401500250400da01c903000c08040d100c4035080003000aa913000d03480841a07100110075000450b40c1c000300041c02040780450701032076a000c0d0752003104100102095981c502040044c0045420001c012600d05001c01c1c1a0344526401606840030700c2044402d0f003070307011350000150480302c0748402580265829824070000d4240100810f06108180c04103aa0304403001402074455541c1d404002540d508081401006015482620704640401d00107820904400c80c200c3d058686c00c141c584941d640c6054100c02c40d11455101c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 463520458 1250 463519208 463519219
    0x1050a0507020103330b190c0c090f0c08060a05100c020a15091805070c17130603060602070e090a030305190c0507020103050f04050d120b06031503121c0f0209 70
    0x11420314241103403088501d4290145041089591007590360242d000311066a000c09800600c0350140c240140180104503120350b1000303c400e0341d00d42b955812503d02107407084110703850b5640e10030b4003503100d500b19a11400442c0e00300a618203120200f0700e80340d101d5101c1e41c02e20140b128102d05560328814500001c0c079251005a030f034200144001804206035100d100240c404a18140e4403840f80d50203224070854655450042441d119102d62540460180c0c0b0640003107000c011118603500500c5008001d000b042c1c40c0802c0072841c0002c0249040003030f41c00b0002c1c0c1051081440044a8007184403e1255054038011600c0e44035034084d5900b402d08504c6080c0d03a10319081c00b50100c1c40d002805801180c1c001d0300d080141da92400c120040740c61044900804036040b1581d4981024000c1038250000c89151b04001000c40d82140840c0c40c690094510741340e89410704021600600e010801403100d4003030440b00c241086090082042c01c3c140c2100c12082c4252151122000d403e415815a100540000e18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 463521708 1250 463520458 463520501
    0xc050a08030c160813060809150c160b090609030a020712020406081009061b0c0f151131230a0e0f012702070c0e0906100602010b01050a0507020103 65
    0x62a100d135a015a84d090801d2098040004041c1d0041c4126449583c410000d040204250070300c050110a0050000236461407d1114020062140c00c11204140c800c502d1940213007801c1400c1890404010490070302076008000395010305601142510031a40024048400e80d102840041c0140c10940c20030a0b00c0c0c881c5c18201d04c10148250030a5107440d00036402040342d6290840250804080c1101c10700c04904103502240006039450390f9141c03541c0c01003040d22440c0c80c000405a0035228405651101680c02140ca83c6014103140d1050441c03424040070450030740009801c00d68124401c0c8985004c1c880ba11f0019204d02202c0c500c4182c6885004144204080d00c03254143d4601100f40c07420100c10204100102c1c008111085000b03c5c00190354001c54001414840725002e9846010b0896800031400d2000416404c0500304900901c000809401149400ca52a41c80b50409a220300c086a051102441c001c3e41c00000319501040580b4000b0760340d00e010b00060707001c0c03c02c024015a0540c610003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 463522958 1250 463521708 463521713
    0x30409020304051b01180303210f06030204050604020304030f271203020d0201150b070809030d030507081b070204020304050309090a0f0c030b0a0b03090a080a020105070f0c050a08030c16 82
    0x10b21840c3d0001d4850701204010319981c011908520a0100806c070800425800d0006c00e01030b66206d00420400d8a212610b130010b480305400303548d140d020f182074441e2503100910442c94107000f881d51001065900310b09601e444d8900401550034001802c0070301c07044074000c8015661510180d51070b1242e1074071500f004c035602c40c400b500c0b0b0a0004c10640050203103200f0201d0451040c040d0305040000e07070034000d0301ea5060801c020a50740c01000104c422032010441c2c07400a0b1802c1c00380c0000c440c00b40d20001740305c0c9860100607142c0e1900511803030180100160049030403440f00c1c03d503030741c00307405407030050302e9503207070301e045861445400c1520380d00c1030003c4200802480140c002c201e842080010621030190090b0041d01500d414640060744402e004c04180b000720010400b86030300901e5a02201c00701c074141d454000443d449a200480141d4441c0d041120042c0c1124400040e11850700d0702816004080d26030b02e40751078004c80010a00480000412507a403448015122184142c62900036107208a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 463524208 1250 463522958 463522963
    0x3100905150108010c0e040e010207050f031b060915060d050a15061a07060906090b01030c14010e0105070b1803042702090a06030905011e020a2003120903040902030405 74
    0x200000780000000c0d0001003150541130040307400301c0c0410b4540e640c50750350360010480504034101d01d95016660034030951022543c10841079010000328409184ea880741c20b24030750300001c07c20f4041000d9a00c0748083c0420b1200006d8501d04203a9003004001e00c0ba118074000804103142c2e82c0025200e8412030b2082c40038020101c0e07110b1040075003520f013000344c03a6448880000488102c418413441c0780b03040c41500c01041444e00517014032072140000040d4000d941ea140c000b42c40081c0c000381d62086410700103109a8842e0208440c9840c001d007440c0050380d0a60000a04910807440b006064006100100b84800c0340c03202c1c100f550040b01c0040c0c82e2219107400700707880b13a50fa80f034110820314584000c00340c80f10005442100d81c0240b000e40311004a6040c01c0d02680503208540c0101d405642e103000d09841c000d000002e551800c03071504c4000d03980310b00115009181d42d48032801c405509440414a05c501c240010898004140340142100140e48000541d8294062035000c8030030180000308000401502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 463525458 1250 463524208 463524223
    0xd11070f060e0d08010f12062c0d030204030c030318050301020d15141c030e0604121203050f0a090c0305010c08161e08150312090406140906010e03100905 68
    0xc220480e44181c043c05412989400c0a111702c0c036900314540d4061084141d48205550500c0c024900070a51009200c08101d894040c40302191400b501311500d00d8202000384118440207005240c1582060300319202c0c42d8174020940320007418854651042845a60715041020007440018000c649824201d5840b038040c0440c8241c0e001c800440600210f15103072000c030005136049000e007140760401c007103845032502c0e41c81c070070410b6052041c0104a400d00359101c030020806881c2e0700107092040341c1c2c3c9241c199240149c0b01171543c181400c002c1048048401f0a090a074850b01042000c9102d8070541010701c0340c101583c2015040b5424944c40c10a09900960071074069846024040358094090b841100c1da104212540030441c01094000b4501c103114411050300180303019030502c00f09214070002840c082c0360f00508100964046014102890705200d5200104544002440004102c50002d0b0241100804441c1402a481021921b584040104c98046d05d088a000c014645650400c55524a01c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 463526708 1250 463525458 463525481
    0x309051201062d080105100911160215090402030a0212220201030914030a0c0312060602030d15170102190f02030d110d060618080706050d11070f06 65
    0x518600c451800030502c900400c030f40c403d4007400c100300b000f402c50300d490802c00d46442122204078000031506030b5081c441c550140e4000050600c026141c02410720544001a0750400f10b5a0140181c9908050402010007000c0e070403150048000301081d842c10b00e502070200281c1d005403002c0704200e002e075025801008404042100004155902035500d103200d0b0102c02002c860885403041c22006500035003002006900c280d44a01903c0241c00398145503070040c401000020365246544800d050b048070003110b68051160b401e00020341000000b0350b5901c01c5001414401d95600f0821000c0c92000d070498011f03002c6000070181140f294003e40d4040d4100f0b02c00b481c92503035482c281440c002d000c1d00b104140c0d4400c907000746080c038421050600017004460703110389014100b0441c462200c2624420f01c001b5048079100c0f00100074100d803242903183c0164210301b2481d48034100511409402406585044401440204040203440158085401191030081030521841300103401c000003900b084070b4008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 463527958 1250 463526708 463526719
    0x5221412071e1a04031e08090607060c030b010206090309120f01061503060e1905070201141311030a08040b0c07050301060621270807081201050a08030a0503060d020d0f030905 77
    0xd202c4003d040507449548002001d128004403600502c0070248641c81000340141c500d141001010000b00b40c0350360003860100c0d001542e07910344880494040c030420000a4081c4000c1c1424034085840311750300d01c01d40800900c9444000324489007118200300481400015000a02c80280e458103002d0701c000707048805078042814074201148002151404a03c00c1c40110f0389900c0c2401420702100c014040600404215500c51000707101324410000c0c1140a01c007420740940c0b0300011810b00310030003080e03165014030070340200c1003c102060207030040e00e06507807258131030551720602c1c400c54500d04036543e0300098055003850700c000341c0c85030820648019007010009031107005441d201e002d41103a0700e0607680358241c904031800c28034505000704001e0f1240d204030821890060b00d600ea040c680c1c0c2091700c0313251101c40d0307134030040c016420420904d50081000800460900c082c405000c0c00c0d500000746407a000303038a01c0c000d0800755940c0109078440307141c00101d00c004101d01800e0003802a47c141c002c0a0003032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 463529208 1250 463527958 463527989
    0xa09050102270a090e030304060b01020a05120c1e0c27090703060609090f170909010806060111030304050d1b061b030501050d050c06030a0e070605221412071e 70
    0x84003507010f060a00417403a0003552940e669542c2e0000101090098241180315100191000900c1000002d280c4d1036a050401d489440852001d441c002c0f03e2010703009a01c40500f03450701d40400c00504d900c07500c1406c42d5450482d0581c00d1444504110500740404c01031950000e00a9103e404204602a00c1c0210018008252a08404820740303081c10700003880c0c1c40300300c030092002c550886080c018013000c0d40b2285140101c0680014064942a0003240c1c580c0c0144041c00038175070f0000030421720070004030003841c00c1d03140949801d9240c00d040b640300018080011100600d00b43c3e288940f103041e990120007040b007074800c1b14204c410020205117603030120340351138008200c03850700048512a55520070000c2c90072100312418000c4d642c00140c01d0005150b19002c0c8505654002c0c4032140c0580140c1e590f0580b030b400c18000943c0b4413240d02c009540215214a0103000207600ba0f4240c0c02070079000d5030090922134820b04202d2804080da480b014180030031003091034140c60062038140c100c07007403171050ba07081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 463530458 1250 463529208 463529219
    0x921050304140306060d02010e2404061e0c030c110301020409020d150e010f180b0d1202070902120f06121b120303010803041203052107080a060e0a09050102270a 71
    0x4086c08400068041010303408041d035546000c004964507080245450506440c2c80c884a18160300a40c0118010442e01e40c00c090951403215160f00c40d00903d49813103005405c07143c4002e030103144900300180c072032031814204079440d40f425011600280664001195519419803640000781505c00410030b034407410741000507503070515041c154141c0301c0c6440ca0481c074070b143c034504021501035110031282050f03d610000f1070941d01c071175044001c0c1e07000b4451305450700400c0000a040441075000070240510500000b10b4104407002d4095204030200804c414588a44001807091301b00946003003610b126040c0c50904000100f0800d200c116030696100c1da2900441c40c4c0603440c6c0c0400d01900320766900c00d02003084804012980180c01c140a818480c2c60724480e800d00d2141e130075240082d104045009000d21a40c07582c0502a545d1041c0c0501c3c00b006410f090800864181d04060070500a00ea214030418040c0f040030350448500301c06035000b259280b030b20004007503c001e1340381c101980300742d25842d4000390 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 463531708 1250 463530458 463530469
    0xc090103030503220f031e020a0302030a08040302010b0d11010e0102060c030a0c1205100f120201020604170d05160201180c120602071401150501090501092105030414030606 76
    0x162540341c2c0390142595500302110500155002440e800b50541941d030341c010803041400007002078040d903240c42802440d8001401d0a802da08981c000f154091001d500c08070354003006607a1000054a0300e1402c91f140e5080481c094031340044020340c01010404094100301c2d400d0050076055400703032a101c486491400041e6242c0ca802c55982c1d1040e0030400009821445503030003a103119400d810b092444071301c6410183d040310300c03c8507079a00c4550300b20024420480c0441107000142464030040b06048040e42c0000d487d0000a04000c044409030000303031400804034010346a4000c02d100c4104018a480c0003181200450000c0050155103450a580c0020500904444909400c49405200f5a20f0200101d2040c001c2900c151582c65007400110000380982ca0303c42001c4003e4800400e6503c2000300818012007181d010383d05001ca114010481660045141c00c11504003400a500b0641c0c03041450b0f108e00040c1000078814000010081000c1217003910b00b00b0060029000c881d016501c9205009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 463532958 1250 463531708 463531711
    0x915030915020a050f07080415030207050616120506041d03070b0f0f150616050a0b01051207090519140a06090920130e0a0b0a0204050604030215040e04140c09 70
    0x1000118208505d943c09484100207202c0984a010090b01e4180c0e00c08050090003200d1400b0380c0000d40006a52052000800500342c0004000d035003040c00b180308034030150589091071901c1543c640c80e01c0000780c00e40d0b103c0c0e004078140701c5000701142c02800d1808205480b41d001900403181e1140d01c0000c25600c00455084074800c502080000400d40c98081003c200900504c40095120a04000d55a500c010008052007214800c0c0c000b0b203030b51011480c1194424505800c40d42c02004200c48800084000043c0081110025500000e1039115040070040c0318400762101003180d41044407542c500c4a1000702a0300c1005042d0301002640d4850880c0c07030696007000405483d000182c8200303040d440100c42d4030000d140b4010030300e80c80142c3c20200f503c183c2d428036030304508a4100844400c10300c100b00b071041c0d03809580038500314509418440042d815000340c4c00f01034000c0400344000c02000c4003803021500a010f42d804040058501440d208582001c2468000694000d050800c8030034180001c242c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 463534208 1250 463532958 463532977
    0x204140a0c3203090a21030c1701060309020d1704150914040203180604080309010b030c030a080906130b1804020306010e011b0807081803160902030403091503091502 73
    0x500c902c1c1a01d000c1e5482c80d0400350013156540119406180000c1241e81059404800c6206100006004040107004c03106220040e10601810305210461907003407002003415541c560500107074044840c00443c0d403445007848000c0c81c1c804030390781d448501072211015008a410f85108115038490480f01160b02110600c5514202c801401041c001442c294010b10780c0407440291004829152001861900300d0603a41a50b040f0000020b1002000c03080c058617260b518183d00800c05940800d010039681c0204070b40150840c2c00c0401e6200440e51303100215000c0d0803908442d4140d50b40c0f14252511640c0c8030809001e401081ca01e440105400c0c00d009580c030495051b1249d264070b81c415801992806155035140c280c104c410340480700010070300780c09002c4060103009295141e00612100b825543c004012a61007a80548000c038440c2d48100b9501090752403491025031a80c0311444c0c01e480c04412a081100d10350700701c07184106041d50680c080e43d10207006420340000e403500c13280c1d030710100d10407800380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 463535458 1250 463534208 463534277
    0x2120a060509071a03280608210d0903020a02060a08010f0909030e150d140a050a15150203070b18120405131805010525050913090204140a0c 62
    0xc0040210f84101444c6d1241003095071000c4400380c1c000307040d15039401c01070405080d03580d010244600101000260800000c1040d03200601581e0b0300c40c640c06010741c160310140b003071701c13006080304044c8288100080c81c1d03409820706455400c10b46014100f140709004000400081c0040020403c42d24004da0702d02a8041d1a030110001c090700c02d001460b0103101d15655902403c1200c0700804c640c0307100b6522540014204c86d550350408200f007400703070358002c0c020b040c081d0300304802c00c1300c050000c48041c0126628400f50542c0d50b101c03100300b03a0841c054648040c0c9110160020011140f182c00070030240100d038400ad65080052803080c070890fa00a03405030b0354004040c0154041c803802981e105c00031040d0000f402c244185101d90b6201d0941d401107801c00080201c0102c5e84014030104600041d100046003801818110500c000c602690060140043d03036948400341c400541d00c07160300014000904802d681c407145406441c500280082d81081800110031900d52090350003004400c07486400d00c05003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 463536708 1250 463535458 463535489
    0x111031303090503061611030406080c071721070f02060105010f0c05010c0329010f0c0f0c17100b0306060603040c08071d0106050304240902120a06050907 68
    0x141008209003102046041c00341c090b038003140c0c50b40d0400503107216001d080c0e0010030b0408880b80062888400c07030010381c4544c0c402d02051040715044001650701514428800b601e8007500d08140c0f4804807440c240010604001940c0045000700362900f00005c1c4c5010f45480719901c1300201140e690b41c0890380400180c10000041c4040e610905081c40d5046091516080340052511340d80d08407054500348901103940c86141c0d014a40d8032500e00c07110920003110b21034070903030350800103000c504030b070a01071080120b0410590200044240d81181d103d400402540455444041502d40501150b40b0706d00d10780b080b10000070400c3e45501441d440007002a0141c0f446446000600050b90070161041718018841d150200d00c403c010031110b00241194114890081e809001903d040317401a080038080003000c104000125007400380030000d420072042210520385040645800400c0111802075003d00e04128006210000280502455005000400c42500e440076681d943d503101d4030405031451b41450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 463537958 1250 463536708 463536721
    0xf0d02010f11010203090a030f0906050f03040f05030a0c060b0409030221071703100b250303020d0f0e0118020d03030e0c0d0f03120605060403260f030711011103 71
    0x103216084000300d802c04820182d80e1048141c00da800407105400244e1042000c0001c1c075500440001d200106400d061040e00d0601400400a2040c000488400f00002020500700424041c240300550342000950742c880b9034061004104d4600d05400340d6041d41040b0711100c031407809104000e43d565064000b840d01224043e2160710100e5030410341c0e0f02c1520f051040794081aa01c0c0d00100d1140140046a0390f00d2614005004000f00242c00228802c0c0e400c0c400240c2c80c201130401c1c40000c541800c11503554610601d8207c01911a014803040b17028204803001d00c3c56111504010318584200000f486010010300c0c624088070b004c0742c4081c2d800001c0d80c03010b901103402513120400824a030025648004491400300340c0b00604150700b1218054000e6001d02850f40c03000280c0c00f922a100070500000745002c0c0040c100303001d24000581280204030301c8000f041568081081d0105c4044e0145841700031480c1e02c11100d400c1194880007042041e007010100b00c0c4103204a00d05c003200c021010741142c4402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 463539208 1250 463537958 463537967
    0xb18122703060903030708070c030c260a030906060b07030923150d050703110f0c030c01050103052103040b0112031724120d0e010507140115050f0d0201 67
    0x208058035180c0d10890316107050107418032401c0e50500555030781c240020001c0c0928402483c1c40c04001818003528002940950404c0301550000f0400c0c42d07103c4c0f031b6010b00703003081c0001c001c414180c40009541c10f0740f01c1c2c0640103420018001c0c44100015981c0703014241a0740f1401c0c800800040900c001171080b1255001c48162088043c0c983d100e1442c1c200e03000c689200c40b5210010b1013442c01181001180701207024450740a8100c0c0f5045c00315140415451696008501c0c000c486081c001c509a0300800d410020303a00910702560083c8485d59681c01c2a41c0c4661501d0500d440c1420070340c150049006000040340e001d241c0c484440060f0740c0c644201d81400f00c0b4039410490811032030840c200a0030982c1145e0034040d00c10300d90521004c022701101c0d002c0d9103008542e03060051070040c5a030f8003181c070701090f01d8911010504000b0030440b22100101c07100d110310080140328080304600c2c000a010154003541662110b1012580842d0300c840070403d0700904648690f5000c1800e101c10001540714 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463540458 1250 463539208 463539247
    0x30f03041d0c071e1103011e0c02150408120f010b030103110609280501020a0302030711150c010212011a0a120f0e0102071e0206071209030f0b1812 65
    0x320350140f402d00c1e0244c0e0762050756801e41810001d0303104811220340207000905407040c0c80104120001c01a180c0806001c0c840302620700da12490ba01c0c7e85850446106009222851242c82000b40210182c60f2900e00360703419410071032070100742c0c1c1c00150018030401d80d034400d51410380c1c19121005046030320b182c4c0c6000e20900c400720666001101842074480644460001410421a41c4500303880c04848020301a60080385901650456000740c0d02d850110340c0210844a1403038001499146842031070011819040b0006500054440b000800c074007800419400781a42141c080e46001c5140d9a4048e1180003074001541e86146400030422102001d0060701c030840c081220501c04140c0407a0f0030090002c80d520b1411081d8640d40009282c0104088192a400310301c10301d0741d40030a462001e8002c50007901801a00030440c10280041800c0f050280c85802c0c0110b0344840e40c0483c424152138180c100b08802e40708411018000e50011084041c04a0b8a001c4640c148003d2400d0480440d501144102c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463541708 1250 463540458 463540471
    0x40b070c0b090604110901350d11010b01031407050a02070816090e15040f110301090f030e0307050312131d0f0f220303020c060106080105030f03041d 66
    0x350503600350001081c0d5182184241181400380407146014140150650303070324020244603a5a590042c041000f08041500048410003241841298201030b440701d0034119420441113031007100d0b0b458803420ba0106180c401800c00070001d014902800c030041d0155100c20b00740441100303405000501d514818006803905211501c102c566565890300038500340075914403c00c1e940040850180500341d194025141c0822b4000001c1401c1d01f607003048801034600151004042c003001d0031a071028030681d20203411407490010002c00c80740c4954134003071040415400e0200c020a0030340c11000307103614000c07807034000300e41c07000e07018240f10300e100c01111805502c0082d610400c031081607804103100320248040311341c030940c1e00869a400d050180e40001850b0005240f00440380c500300400c40f074181c42c0c851920340c140005070044418000e40c0340c150701070b000d0f84014421901c80e05000080003684003140a04072541501074070088242400c03c51303202e100b5401074800c1841c40103030b41481800c50412280c2d0007032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463542958 1250 463541708 463541717
    0x2030a020414070f080c0708090a0305010c1e020d020a23070801060801140403020709110702040216030801080a0209150316090c0f051602210f010203040b1806040b07 73
    0x140960000e01120b269054030300b02207803000204400c1d550000404004003529080582d407600d000b500c525020701c90414008d2a000c404100c00010fa222282c00c440035652041c002e00030700350104c400074a2b000d24529034444400002882101311800400c0007903004c401540a041e0001d420345954041401c1c040c6100040c622000e40c00c842d076117041c007440000c1c1c881c030f40010801c00d02c5d041e45035003500d5465540401c5503d8200a100003c1d800140b00300840b410340c000400e401c002c00c2d100240c20b01414501a420500008a0000891130203410307140d200d11036210340206136210300005940300302250000b900b10740c645002c682120300d00c160304180004014102ca10035601280c003440c081041d6404843c080748c0351070f0616038480d0400c400c0c80d84e081151404504010704480e41f04100d180c40b400181c0910900300f40101d103146009036500007500f51908641c01c54102c803008500035401103405884c1840c0140115a00c071291740c01000a01c201c80d0b005081c0398486e5100c0800d0114003428030001d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463544208 1250 463542958 463542973
    0x906010e210a06050a051e0c1e1306020102041202040905070302040e1b100c0b19020a0e0f1c020108090114010324150b0c07170105010f0f03020102060a02070203 71
    0x403182400340c1445039003a03009802c00350194988141518006042c0201c6903003400100521701c840110221606920b0920001043d25154a0f5100b9403088040303190312042112049000340400500030080b440f5920340b003140040e5100c60803800c0740100d0044804075001d0b000840c001d0324040e040083c9150140055828841e900d600140c129034100000c0c0c07405070880c0100c134401c0c1291400c0b84100e40025500c03c101f9070442030740104103002100c2c009022159960101c1c012081c5448200c42c10440e13000d0855035400c40182c05171060034140c00c4d0b5403084032450303206051410900c81c4500700300d0180401007459026070380152042640240344103413565803402414640380c10403003118025170141d04198411950a05001780d0000581ca02c858180e0a00141d201c0044400b404a4100c1d800d5292503500d4601900741c0c182807070722651200c5800400c2e0442005001d006510060480d5517016030080070702d07070303411001c61940c07220b100280c0503030070540002d84d03603810030380007440c02600c000c040d10242c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463545458 1250 463544208 463544239
    0x90504020d112212050c0103270c0f0b04030f030318080f070606240f05090306090709061208030103060c090305030d0f0c0302090f060a140c0307120e0906010e 70
    0x7903000140c18000f0074442c0307080340c1510307460007220201400d03900d01d4941c258002c2d9183c1668070502c0c05a150704140da00c642801d0210406400382d1070b403010a0351a903101d1742c05400c04040d0b01486000b1012880070030080054410540c4d0308840449610a80ca441149003c0d10260014035404090304442602c05c090700000810100080c14280d400309045603c075100f9050003400c5814503004041e26660901d0322500c050b0f440303456078080c2c18452502d03151141641c0c0c000c07181400395481c6250144160740a101030060041600c1094425a00003080125564074101102a042260291140c8010401400801c155803c1800307251039504004a05655039501c440c9564440d842c02034100c1d90354000d05030340140b18010044400124a415810800c10303c0001382c20307c00518915115250000b0b40818050003441c0080300e459031840400d880e942c10034a003d0710b0ba40321850496a0b4a062900d500d0140d009400503a041900902038007401d640b40f50055a20480e00301c40542c0c050410440400c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463546708 1250 463545458 463545491
    0x2072114060c07050601091815020d0218150702061206150c06100b130b18180921030f040c1502030901171312030f06121b0501090504020d 61
    0x628010b03020955210801e041190800c02c040e0000c10290341031000500380d00140101c00da0340707250800e0304d8040e21030303a00d4a500c009200d40f03580002d00c2400401c02e1007001c074074240e010208034001d40c0e01e2446000f089020700303498410380380b000b548207a050184032030300080724528a9000d44084d14584410380800e035174480c160080d42a002c2154401d8003003080e2456120300f8600100101c4c00003030b0030460f05407031040385032041e802003485000000c2500c04510202825000980e40091321b00e450b0100c00d1040000104011107189103148a80702c01100c010000416546140c01083c041c0d80c06d41d200c011280e00c0c0301c0f40142090b11646803010700414004d4092865070740e41c1c1e8940c2c00650b6102040740000d841e11002c04114000c40a44401b044036060900d03400030000303680126203078402200c0c640b042d0001c15500e26440744052514101113101c3e81e6a00c0a01e4006000760b0512641d4800d100064424003d103018160006d00242d90406c024105500074000f6070300f01100210b8901c0c0c00c5440700c0c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463547958 1250 463546708 463546711
    0x6050901030b04050f0a05100f1404230a02010903120c140705100504030807021c120807030b060313080c030423041506020307110411070303050411010207211406 71
    0x10395140c1c1c2c10301840100241004505110840d03940907200d0141c076034440b0703600c44100d10701c00c010080c1c0f2241548002401e6910008668203280607542d6242080d09004841d81c820299801095002d541c03003403614078000070b41c055025416510801180d056a992200b40e8511a02c000e0501c806c00e03404400081030b003203464110880c2e080040070b0325803408003048221000c400013941445030400090000c24140c2d01103414064050302d1807007410072205411050b4555038080500700f00c115801c0c100c040b0781d1043d0401e001d40300d25541440f01030303403d400b003189600c026100e08060400c3c04c4045000100003502602501d08401e05070380c1015a0f41d8480d218004406031a41c0c086605401f80700c20614151003a42800c00346030030000100307030401502035924860101c0c0504100221941012241c3c1c4a0b0080061b00d02c030016030302c0c3c640109113805000b61400f511b0446030000340b104031020a51000031038408a0700c800c00e04d000d09003102001600d00b843c4e1004240d948511400981c0038450007004949d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463549208 1250 463547958 463547963
    0x190b040e01020706050a051b0f09010c02060a02030307091406090409060e0a05210c0d030f02040f03061409010c1d180117060108011406040c0e0a090b09010503030703050a080a0605090103 82
    0x124031403902d10001407c4503401840c0c2c400440c44c00303130700f4050080458199804401004101c0340e88841200040c2e812450700c82c8000d5002c600000c89841950b40400514051a22a1954109262142c40724500403680d00000e6404c54428800d84450380f5194200c01034841c081e04002400e0b424258065013041c040e88010b65656101820120408039035203012414443c40d0400c5d0fa0600c04c113003d800742c40d01007440c440f1017011303111902c81d80c41d026075a0465008140a948201145036a0325084015103c0403501c82c40100c2c130b410001d00f49002c1130045000c0c5088550341c01090741003001707064a401c802c68501d0380d045110040700c1c50000c40d180c49054080c0c41e00006040c4059481d1607842e04e44038052b080f40a169040c81d50070b034961241c1a0160f03800201c1228041060b0700007640480b1500c4c10341d40c403507622006c41000090000031360b901000703d1400c1502c13103482e00da80301c805140d645d2080c064020b00045040101c522400d204500c01c907000841103101080303507556400003a244c1003003038005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463550458 1250 463549208 463549211
    0x91521021303030e0f0603010608100905010905150a05010504050112090605070207051e010215070c170a03060b0903070911040e0f240109300c06080708190b040e01020706 75
    0x303000b450b0f0459240b00b000c2030221445c0581d103035180003040aa02040c030500c81845001d201103040044900e454901038070680c101001290303175a04c900d4000d00000e40307240403070440c10701ea01241400e00c03414481c25610117850742c0345094a00401141c4490307040c0380008a203580c900700000018540d0058a000c1c80003a4001d00c3c0700380c101400c00101031710b0310013100140904560b060440d0303600801d004030344880c54408490107a0b6584002d903104580010020700e440c500c0c2c1855100c01c884c903c040d0a86000540d010810552201003d611502c180c0103410751641c400581004807880d00e400182108201445c1c0c2418640e641240060f0314009540c0418440c10b200200148100c0000003c44400145904950403601d00000039217250140e014051400170a000c400c4030358501204007510302e9104540082000768603007401b580380160b0b4020540001d20000101e00c046202e41e07086070140039054031203000b00001140620081001d1008103420a44403607000540440a20282507050b010304e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463551708 1250 463550458 463550497
    0x3090d0c06030c050c0a0b04060b0910210b0f090c0306090303040314071e020420040e0a050c03130c21050105221b031205070b060109152102 62
    0x4000c2c0540365010340701000c100d020700c850520300ca000540c52140310b41010030196141c6503420240050300045c0ca0280d005040b0b1418406014201c940311400c455039105c400c00418143c800c0c6800d00540d0b154080c21300c0d0704100128840207210070003540c00002c240e003151480d02140000c02c0c200a0101d41c506482d030408002c0009040d00040d592240012035010039142c490b1540e0783e4074110000d08080004952003011050464407a40e00803211002c4c1200c0d040a04402d44ac10916554014000c0f103c07000d41d10808a03054010900030f2034010300c601c40300b03a1b09640d141044140800d00c41881034403c201c40c01800140100c0005ca21145c06044020701e81100615042c082d00391100a0b2007820502da011190805c070000101600c40c0c06030740910014551b00111700442411205074001400d000d0210741c4034a80c503900100201100d9101e0385888480e513841d0390054694213003610585000030079642019119922400c06803802401e00c0351390f01c4034034030030f6151036007213800880030811050016007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463552958 1250 463551708 463551719
    0x120c0f09020f0304030302071103070b040303030f051005060a03021c020307022a010e0303120a02070c060201090812040302101109010201140c04150903150b120d02061803090d0c 78
    0x1000202400d4415025803900000c1c1ca4169101c3c8801813018082550114901c3c0402c100401075440c0850010102d45070992901500c0b00180c0c0203100840c0401c0c5401c0c007d0f40360324500d0050300c3c40341341c040c801c0c2601549004148030b070646c040d0a0510400d80c2c03c0103a01042d600c43d580c407403121261803500680364901f0400180ca045500385045e0079404d58a014403a03480412815040071010030b107840040480c9101c0407a2550086a4400c20300d060703541c007001a030b2040381c2c0c0942102ca000722100044107036544010703030881d082200007800621302040702800306c0d030340c4d50401074020340301c3c3c4115444008085c0c8544200c81608e5185503074580005450709096909004501800d400d029010342c450508201d04c242601c51440340c800c1d0360203100380c8071001038007a2010200468001d501d6520a82419030280014640302c0724540c441d07050595880111200040c914280504a40040c0a1900c402c660040c112034124030125152008000041d03030707906c074000d440b0f118510400907002e0160420b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463554208 1250 463552958 463552979
    0x11508060d0204200a09260c04021b0a050105071707081f1715100602061302120607091503061d090120030a14060a030b1b1902010e010c0207061107120c 67
    0x1c2e400340481f0140c511140850700750104000c41d0b0050b0864005035501540951a181c403003003609218218054144c4403424004103410691060545541d40c0201030750300916030110381016034000c0c000501140002c0c0c024a115a2529913460112501602c400e65a80f040d181c5801075851f80b00660308620281e80040e6000c9e441a078005202002454155052030402580d078500207000700342c5d145088040c20155260b0440409110310302005550180c03805503006802c0c1e014074440e0b5050340e10f2544c80703a10f401d44240b1078030041d0f441c081c2455003090301124180300711010240c202181556510280001d821101c0e407941d0308600b4004015480b444c00807403410440c1d400c654203a500c1d024a03010003540307503101d5219101b0f92b40e028860300b610313455a5411101916080c205101404000140301c404085031103d0340c000c002d078503030081c0002c10008003064280d51b06031700d840300540d12100b41440498003900c0b402c20070b008503078201d50a00da83c805840c15001400f40099403000c2c1030410070701426400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463555458 1250 463554208 463554239
    0x60f0706050705280f05090f06070c0b03011e061b0b0406060b0a11070503070e0c031909030306050405090a0803060d060f020706020301080f032a0c0315011508060d0204200a09 77
    0xc0b401c0050800c80244c0c080f84010b0880c035241272040b003000813031000701b214034083d01001e0200c054030a40c680da1a00d032800c0960764680d03030b80c0c3c0c03d900d43e00200288180c41038180044019942d054061110702960300c1291182c0080c0c000c036101c5450b0a070209015890340007034406810180c0d40d4a0f03451000c000c0160038030392607421081c02038000c14024000340010040b025002011440c450740c1d2665040e00c8204030711703000c600004045040400c290249a8960032030780035158102c0e070030002c1e5100c0e2404107589100c2c401000f010542d0271f0001501c03919001c0c90b010341140c000c40c00401c1c00080c66002d0012a0300072101100c40541c00b00050202c0b0780d04105018618503000c0013185802c00000602039242c3c0003c00c0d1100d54050181c007041e2010041c4071080079000007408550b101c524500b400021441e09010b52401ca403010365030f90a84034071488030301d40566400b8ac618600c242c001d40070300010700b100d0154000b1800f07075624030070420200000103000c0f100c1140c1d1110511414081c0ca110050341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463556708 1250 463555458 463555487
    0xc080105041a3001090b010302182a13030c0911070305031914090a060e0d05070b040303021b0105070e040902090a05041104090309080606060f070605070528 69
    0x19503402422a40c0b1400203030070041c90312443e034503190b002d101e008560008465030409203035420041400e04120800405034180c03807007101c0321a0800c00007038000301056400c50f80c14601c0d10004010744240c2c4080e0305e4405200c1c895010891401c42d90001c1780240d01c603954000c65000c6a505403c201010305c038464495603252070800d6a05c0d007081c0d624000c01c1400090302c1402e400d2050500a541d0080c1944500000f00303400842181501d4019a4030340c4844040b0700549400342000321250404270042004001c0c440300d52501d509000041d11032008448000300114181642042000c1c500f0a01090040030404408004610307031170b100000622401d01782d01d8040c011418101d81c400141d541cbc5a610f54071002001c0c0000c0d040d6158100f100c035203903901603869042840c04861409259100d24600c3c19100000200d6855884480c10f0080901c550700d214041e40005009200005d80280c0100d9000500340c541182061444e01c0218000340988040040c990020070701213050310b030001c00c3d4030b44958 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463557958 1250 463556708 463556741
    0x2e0207080d0504050307170106150302072d08030c0d0e070815040209040206130b0c010b1c020d14030c030f09040518120901170108061b0a02031614010c08010504 71
    0x900c4e0001096a039a410b009880700c4d0750000e41403480c0c0740403d50011000300946240a10b00005064001cac00a61004409441b404c8400007800c7c2c22414804214200c0719102d51080310a0b02d903519421510f40003d00355071001c0c842084010705900c100e0268040075a460b101410020f03181040c03540c80c01d090710364a81041d030034034810040580d403000c240542c0980c050302d081d41e031030f40030100d2080d02a519800c040e41c403182c04102603c100005610440500d00103813a0110326032401903e26851260303051000390310072140102100029a90318150080c2049501224200340429651038110b0300710410150340c01c5000300d074400b10380c503150258135044241002c80441d0740b030010180cc1d490300000142010741c0e2b140012080f41c642d102e601c090600424034440c0429a5031155502600d981058a03002d11142155600075600040d0500700c07640c18016030019840c0c034015101201104020500079110032801c441c03104116a4280503040c14a0400d0350f0302c041c190704160030041281c800b000500c4030135 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463559208 1250 463557958 463557967
    0x314070906150e040b10110c1f03020a02120d141305070605031005040e010911122802040e15162c06070b0106030516020c2e0207080d05 60
    0x3000b1014110481407030034a01615902c01400100f8041c0c21005809600210120780107007007194414010311010000100703980101c2118000c010b070f00b540d003140300b00d006d0746030f40081000c65000b0b17401003c941440d030055940704440a008103c2c42d401c41c010081c0c091751942c200305c501820701e4645030f41c04820000e0f455882400c0d6219541c0d42c042d14080c8106100c000004500d40445c030015120013010000d00600615030680d800c18040c10111f40c084681402e4110207111038074004100b00c0b01c203101c42005100d0708600030054079034190403031a146940300491031000c01584490043c01d010040c550010f00c0d60b0b42125500c1d0303445240042c03100c840701c2e007041c4003035025540c4040c8400640e540302c4510403606a45d401480594500041e907903030f1180002500100300098644214101c4469403402c024035510f14003036640b00c201081081c40143c100403110741003445c1c029680c103030500032141c100c41c16141940d580d0100301150704882c001369001c1e180030024a20104243c3c1710355a014174009040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463560458 1250 463559208 463559219
    0x7030209031c170c0c010905010b04180213020a0c1e0c0e070f0311040914040c140d030516060e07140d210e0405070807110106150c03020a0c0314070906 67
    0x7104444007a0107030f0b180c4004507080c566194181d620580322940200300c04612458494000c1840d1660380f070040342000710b86c9407001840080303561301c00e801410320078940301400f0022000398402c00281041c0700000d07c86a0214000c08142031060640c0100c415090b01d03030f800c0402d2540c100c1e13409000901c0b02c65040001c01c41e40035124402052850401280004a82100d88954050760f000140060319000002c456110f03829621030280740160003070b0800d1503c4480c402500c1c41c18040c21502304000d01a1000007a124000501c104003c03580d40c401e4940302c0e0340e01c60060b52260b40000e1902e50004009102209080102e0140340c0c000f1180050740c81000d030740d03160001e6840081c845d00c1500801481e010749015040c0c01e4184100100104064a0450800b41c54904141c8600d40020018401450008014462601600c242502110301036444c150102c98080019504508600030025410001800c0d0381c00d1001a52140346244c8030f046c1a80c9425141103215805580c20380d007080d104011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463561708 1250 463560458 463560467
    0x2307050c090c1801020708120a0f0302071703060f04090b0106090501050910080603030f0703032903120307120203040503030906061804081308300a020c19080607030209031c 76
    0x390f80d9640d25288a000c0c195800603814040282d00c840118003808a9600c0f61145000040a491400c2d032500c81e0114040c80048040b409621002441810012900030b45c085c448805994407100042c0114501e070b0300140070400780c4110a000b201c90750140001413022035000b00000c4040c00c02032900c1814031125000013501d40e203015100105104441d800f1038a9600e09108894500c101c01942680d01c0e201403030000e0081c18101c00709040302e281081c1b04026580a418403443c01d43c0028014011101d18501d6911664000740441060003640b80710040b00d0a024005580b00300d0184028544a1900710030032400c104004003018410200c00060100b03d00c10304603060f400a030090b64407074036001d50901480c0c002c0c404d83c010b04114411012082c208030900022000b5500a901c44211741f44803e80b020710b86401404ca400c0b015801000d0035030450305101182c00301440600030400200b5130785007115070134100c00b61000800260001104021800d04101a03e80195104441c0e0f003501102c0d44002c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463562958 1250 463561708 463561717
    0x409140d1206320a0e04050a03080705030f190e0d0c120315030303020d11040e0421090509090304120804090b0303030402090411011707050d06080102282307050c090c 73
    0x454401c0c41d091040980c0e01c90100c948090905d206170b441c0e1609290400f15560000d18804500041c080c20008024034450700030b89000e50406483e40700c2545402041d00032207041d0b0340308940101d0b521062400308000822183c4402c010340c0d103400c0c80d04e0200307082088818640007080c1c0181400c107143c002c1700d40000d030850000ca0b0f4061a00684400e00203e03035001410ba2000c030045802c6002c10007040705c80d08003d4850165206a403200020050304020840c1c05d03901c03185040c00304900d0401000315003411960b40f98000214805d50f8902915550350608200910605072441040814140688501841102c0309080210025810351400f64009512060011700007011131108a41c1c1e080030341d014040491041003056490301d502d00c0d2580c4010850307005003c1a060540c01c0c800e000400c0c0f50706208988180c00e042c00d802000d05083e0b80f1140400d0b075181035080400808104403500003583d07130580034200f81c100600e681c0d181c5207414600d107080e40f485501e0303110b05a507006004113214020203c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463564208 1250 463562958 463563029
    0x270c0f040b1c110c010b0405060a120c0b0403051e03040302130f090b180d030504050d080402010c0b010f0501090503010203060906010311070206040b030a05011208090409140d1206 79
    0x540ea54201d42c0380d840d94801044120108581c1060200201900068007070300712504420020841040b0500400c000d952003500d4060300182c3d00c10050106603901540514400d000340308104506541d8040c0200650045d0b01c00c3d6095000140350b41c100404940b486550354842c035008508250840c0c00240c042079030030740d01d450300030b42e1003c0819103034106810400706560040c451034050b00c2c0031941c6201907400964444103034010301404446543c041d208041c000c82e0407100401a2411002041e52074540181c010f07410300c010301008500041c15900202c2c040d080300d5003403100c1540f4080014003a009903403c40c52082e401403080104a40740d602120f98040024a00841c5c0d001203124100c017603206091004e07410a00001d00861420386070303c0114010f09001da03080043d41c0e0b99006401b0b00c1c580d0048000c0601348208600700040c03400e030b00240500f40c050704501c89050070f08040c03240f801c1c05c1c4c4803e48020402c200c01c90840b1034141d1280c0001840491141b030580050050708031000e919910a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463565458 1250 463564208 463564229
    0x60c030a020d0920011206140d020102151302090c1c15050607030306031b030203030d0e1501080d0207090c021002071a0708041203020403020108060603040f02270c0f04 74
    0xa04000b46542c102d0f00a807500002070350783c0c0d500c0350200150404000c50303e85011441c000070f40c0110412a1140c1e004540145041a81c2c003045070040103580e81d04403006a0440c4105213102100364071103548c3e203004109200c8200034203400d91050080c0194010064802d0b01418071000424402403141d0041c01c40e07490a0004008000a0845209004a030002a0495030200d558810944c060b40300b1300c00c3d6070048141c000c48800c0c00f90345655040039400001e4140e041400750b0210b904154008140c001184400d4514901950710120b1891509a0100c0d0469018071011400d203034041c0088006845810028001000d0208029649081034407035140d40c10390003c0c5103828081e00c5128840a410182c0910043e4180304000800090042d94143c4d030010303944c003c2c881c1160007842102c04503503040e16225016506c0104003c107030341000788280c5000c1030304d494a10051351a505107207240310100c2d02c0d010000c49030780015680103c00a2145d40080c4041001100c1d0009020070740b400c842c400c288 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463566708 1250 463565458 463565467
    0x180b0d150b221d0907150801030b10090c11100902030307080a140a0f110d2304030b090109210e010c080d0507031a042c1213060806091005040216080f030402040b03060c030a02 77
    0x2f2030444c0d048554084810a8a008144061568070000c11580b50400710308a40701d0640d035175803800498114000c025407560040261900040141015001c102010309100500301d00f844942c1901e42d00401040c0006102c0e118026240d0381c1000c2c07054803c084040049c00c1c0054405005840305c0071480013512281405007a4a030f0044117002210065a8030030000b602c2401e10100c030502809400390201d424582d069480d0403040300048440d004840319540740b0541c0c040c5200192841d424420099454010401180301c907076401d4000c0c980100701030750380003c9a5003800381d1008210604605036100324100702401004804400303100c3c0c1d07107800440801c280071224649403131801c48110000748100e0300100d5034105003500d10014400b02c1d07460361a60300e078036540c14042101c4200100c80b44000c0140115040c0403608043d809031503100c40082040c071404c0201d442c1e0620070340201c000d0341807000d4000b00b08011410103006d03000340f50300241d009140c1c0d41000c800d000c400780070050040880035800701e03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463567958 1250 463566708 463566721
    0x60901091121010503060702030f03072a1a180c151204051f0203012103090f0e0a0e030705120307180b0d150b221d0907150801030b 58
    0x204070b07909402164807152100010011000b40c038142485142d100c1e0140e1000a14401e00100485110120f8515034901c0c41d40c40f8101602e090141030807042d800e000003000e280d00c185010640c030500d18013401003406005c45a215440e1491002000340c1c00040304d00c0d0300741d1000000010312102d80388045070141c40c00c1c0d414031542c4003680141510160280e6000092000341700b808115011071806c50000740c40340c0040c141d1100f050707110078410080384d8219100c00e800d036941044000408a07120703190966400e0b40d10741304107200070442e8006000c101400c0301405090074031442a010502d100002560601c0c103135464460700d0300000141041754a80c008002122541309541c00b1816540c03000008210076110f86100005400040001061526249060400900c01c81032141241c00f4503004903e00f101c2004003000c109000d54820750710b032002500c08207060500c0c070211aa03002c0c840e500a410b500e00325413074528144040c0e211540130a80ca00c1202070495100e1078082c10b4a070440d003440c000d9200c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463569208 1250 463567958 463567991
    0x40f09060204060507150510150c0501020c0d09150206060d050708010c050c0118020303040501050f1603020114010f0f0e0712090809010917100e030c0a030c020a0e06090109 76
    0x400000c040610005020501a8001c80602001800341404005601000005008443e8151180f2200c503d03140010000300944480d80030070b80c0007900c0c2c0303481c11120581d18182640c03c0b4005900c2315401007010401003e500c000c07120000d10403c0308100c40caa0341140d001e515801c000d0034090041c49001800c6c070610404201c00340060000000801c452840c0e8403004045400c00c0d9001405c95003003440d07505901301300348890301c2078540003800b0350710b850300e407100560389036100300b04030442c1c0e9805001c211a00e841c0c40d00c102c000301d0b00036000498194110b08060014410503000341003095031440e0240300d42c403860003401058070a1140076104d542c8500344151a51074410b0350000c603260a2450040c20004a0006050343c50000e8940c003001986403030120000920600764051a5840004805003524182e00560b04541d0071409807403502d02d1400146040c000c04003002c0d030101d941c01d1540c0046007400303400382d001440ea189541e1031505001c00000c507205010700c07a0b40d0351681c40300345100b0a003244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463570458 1250 463569208 463569221
    0x70c090e0a1e0308060301020703080f0603100e060a06290d0b04021303111203070b0612030d090308310318030b040c0806130b0c090402070b090610050a05040f 70
    0x84196140303264021114000401e8042c1c1103000920310b4001c01c2c0700342014020345001e40d40c942c4405a49070782d913058800b2010305c002c08466061042b103a065450401c0d5100d10040d84100d607020344110b24103202c6840985042d40d0090886410b03621800e651000041c180522174001c0041180d51605000301900c0078043c0c00b1949076000f48005021a83d0741c030319203032400459100b003c81506280c0d4800801c02c51061600c40d8030f40a4004000b2000041e07414002c484d409400104442065100264180c0c956003000b44090412580c0b4140c450500d030300590300d00e030300259200c62005120f40c0003990010b043c042082100301500c400300081d040502601144607075424443e45400071035640d09003a07403420800d541c1a0340c0c8070540403001c0f030058000300d480b07441070051a00c0c116440f2a2036a402000c4c080003002041d842d902840340701442c4d90b4034002029100d0107610102010304001c810b440c101000a48040240340f06001c0800413611500001c008540c811200028098540c10840024201c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463571708 1250 463570458 463570463
    0x10906050c0705010b0103110405041e020a18082d12031519030804030f080706021605011416050f040b0c1510120b090a0f0521070c090e0a 61
    0x2050100481d001000020340086400f42000707104500700d0740c005404682d01c500c641c0900603420801405982400d0f04481c1c20450f1a5104031868040716201c5022a0054500039000a11980301041d0030046000c08070302400c0c019026240c0500c41b82c60b039140c001481540a215540490340101140e030007800405840c6080070709040c3d42c0e2030079030350038940524140c868030b1107012403142d42440d00a101001c001035a500a080d140382078299201c011140502c0d01086880c0304c0c040114400140103800546182c0a8074642c41c2005c22841c03a000342928022010204a00c44190030030444030300724686140a00340381c0c01c1040d138405641120310814031a40d08180341c0c5280014400300407100008003420101ca0120750341005440b155098621466103109400d80e684a00500c100881c207900705490300b2603115001ca44a0108680e5a22440c140f8404252181d401030112040c10528280001c6402d9098401d411320b4203159a8900980920718060000410303a2851a010581c104012020728280c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463572958 1250 463571708 463571711
    0xe01181e17191407080708012702010c051011030a0e0c1518060408100e030408030a03150504050a20090901090b1c05010509010605040209010519050f12060f030604031d03010906 78
    0xa80b117265056450b0900d11410b000f545c030f410240c10460301c0b100c00546104038407111000800350907400455858158440a869502500d00c008005990717030700c09c00c1c01d03040e26224500c1d02c0303140542c070329022208074644a00840e0807000f00070141360303107514071002c9010f4020031580d2107203078998094070200041e00c1c90740e4001d040010089001d1038000b508010020028400703001c507402c91a8599100d0040d0721030000194002c1c084480c03094000d411503130a0341000c6403082806a0340ea00002c05545081d21001f030b040c1d41ea00e00c05205405071040320038010303114850703061038805920042541304005202d942d00322540c2d90001c008559071000e200048900b0450000001c0a85007440c40c002c00085e0341300c3c40c0d0756182400c0044c1c03d04290083c1c905107236058494034100313220f0003114160400c2c85a12542000800c002c6079020380d03c8080a841c4071406403491441034a8140107100f0081c90364441c1500c03036031140c1c0c100310000c4e07404a0140c400001200b0080c7e240d0010740042405004903a00003009035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463574208 1250 463572958 463572973
    0x3020c011d0406091a0a0e13050312070f0f0e06040e0405070801151d06130509070906060c0302120c030f0d020f07121205040b06010e01181e171914 65
    0x501c1d0b0341008140d105c6001d11030316081001d40400045d4105071107890401004a40050701024110081c2070003a40100240c038608000b0f006000300422007107604402042616070704034543c0d80e01c850560440942d80c10100300c82d080d8640000c0b841d01a92044490040300140044d04101c41032083e030300200000d0000744141d0300030442c03c0d200f811207400b82001c5400c0340307440078401900c8022164000c03d4050300000c19451211003a001070203000f0082286842241400103c0308998400d40700140129510840000b40310700d40281030a64503000b20301c0294080c0040c00d04c1d00340c00300c11212240c1341c0301582c1d9a035902165071200a4024103800d48042a800b1030240c09010091035100b0b510f0b00700703640381582d8403001e082903400c0b5801594041c08880041001031015401030468084501c0141081004002c19070742c0d20b0028034a54001c29024501d21404602c00d09621120340040c3c44040d40c8464600d2810803c1e07aa140b04940203880d5000e418810f0a0600c50291411400400d500c0141d400d00e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463575458 1250 463574208 463574219
    0x90506040f1202060402060307050a18090f0b1915020a08040f06030f05070c03081902032a04030506040206070c0305030a0306080c040218190e0f0103050c040903020c011d0406 77
    0x540c081c1260540702842c080c07401d80c1840784042000740c0314540c000c1c01c0070705640343c03083d0840320358001039072034030500c4441952071412066840d00d00c0010104e062020451740d83c50300d803000544407640b9100780245003561010014454910015081e546c100c04030406184003000101e18100740000702402d03050000401285420b901c400e4141640d9054400b8041c0b04005818030081f52400c583e040c0015245045100c00644140032a9800c0710502800f55113000d004d40c1c8990407640182c880159040301c403101c0100b40c4000840240359031a0001009040c20b2540d00c4035911540000c000030b202c2ca00c001101002c01403080d2418018640140449444d0114040c0141c01821180540e504610500401e1103691801c1d00071203e00c000540209110701000340140301912070315a800702c4640c0e007103400100d080715481000c140310f505401c5008020354514201913042450131000b460013141440c0e940c00100f900025001425402803902e001f840400c000c1d00001c3c0246804940c1c1c3c05403d005c00041d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463576708 1250 463575458 463575473
    0x2120103060b030624040504290a05100e041401110705010209090a150e1306140708131101050903070812090909010c090b030a1518050a0b0a090f09050604 68
    0x5044070154111010b81e02c5450a40003003000921707600c2c1c042103a890b0f180c0ca540c00d0a4020a402901c02c94912464030850324110348c50914582ca100640d00380e220030003e00050310b000d070a81210120b40c3c00001e00b4144484445001030003840070f4400038150400c02500d07542544030611b460070720100302d078480655191240c003039449140301910030f0042c0340100348103900358400c0e032140410f0341d01e10900726072600103105030f030500051050b0b80001d40710f0f1200f0301107071040c020604d2510344903400000303600d850b400180c4401000340c800b48881303c0d81040700c0c0001d55140780c084040002401c0903a22400030304002480c11010b6001103906003d10810301081d41008000381211110840300d4660070381c0c40740145400c80b0304400860000644040d8200854140d4030300860300548021030205880700450030748803060449501000c183c0050403000d8811036800d100e03e035040342038504240900c40000d80090040c455034003d00858596401480d540d2102ca40e025980300c075441000e07141c903031030a814400b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463577958 1250 463576708 463576721
    0x10519020708033c09130f05100f060f0801030303111306021605011103031623030a0506040b0906120a1b03050c06030705030c03060a0b0d05060a050d050604080d0212010306 76
    0x810079004c04451880c000500c0c5140c040c03690854110500b4030030722400f002410344961141400c515a41e00048403000c12a0050601c00c800788245007045501d84017201c0d40d803a020354044400c0000034130070300215561200c0c407241102d4241c500801c10164480212050307209100d00d40c070811840c071000150454011030a81d400e0b54a410914070019501c200540c0c8104114070421403a400c00c01c0003501208001d004030f0220840c5d46003400000104440c80c2490846145280303203401d101000b0840ca03a00700e40038250b44408241e90a00c201074088000c80d059800281c0541d12495105c1d036807001410082040a4155401628a402c0d0100b80c3d0f240107107100990200381e0301800781e50070a25840c182081101e0140d40d07981c1d03030b1900d1039451550425850f0406004664003103654440082e01d003c50902615042100394800101400c240c1c00700080224190300181c016205010102c0100c0c001107802580310b50820840c0d6a01c00b030341c1a410380207118a99203000c4401203d40040305000b403550106 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463579208 1250 463577958 463578007
    0x909070501110c13020d09120c12030615080604020d0c27080607110c060403230105060a050105031f08150f010b031645030201051902070803 62
    0x7400c0004011091610784440800440e013240c807941e040c03159080164004e082d0b0b4001c5510014001d072450b0b540305000300102c407501000815035201c0c01c00703001060309006131070b03aa60306040001321b2a242c0c071650300c0260140014180103d4000141043d115a01102c2c0e40c0c07060b20104020f910700c00440170f0030b90500f8039410006405540e01a4610300c9201640d001a101144001d2a15a8a00380b080f07403540455000e01d1503900070800c400482d034413854040e0014520419124410038000040911aa041d90800301111380c14a070034480d8689884200700213403102842d1050303a0b0350700c1042c4440341c5009070b030102c040035001c8140001e40850100c0e0614001c0040701c8065074644a11542c2c4e66499028003654031a002c04101152441001641c0c1029640a5090038207222007601907080d2031085050130740c800a000304a0b0501001d80d240d244d90b030024101076400e052141540c000902a01698a01605d03081181000c805014000c015201c0146908021680d603406080100010781e51001d450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463580458 1250 463579208 463579217
    0x1e09090b0103090803091020190c050115091a01050a030c1704080901170601140306010c0506010b1c090804030303050c0d1107030f030c0215150d050304031a10091a0909070501 77
    0x8c2e1011343c080e000e9803450b07608140c45603090800d1418000040c10340300c81c0e18070a000c010a06100018020300646080c410750a41c00e551032072a10100d141507038690700c0c540c5104040c07901020340780c3c2c0e044001e0316100c405038500041c4110100c079080da100e115105203000c02c4000d0404000800085600501003400c00303030790764055400c81200d80428520b040e11001e0100f04800c212024422180300695440241450405601031247d1075190600b103082e003003201d0700d420000f400320541038004c4540c091801c45903010030288a45450b0f4201d03c0c0941d00008081648440100d81c190a202c4240e60045000f20810880c40e80360b41c0c50b4043c0c076030040c841200851300c021500c4240c14028450312101a0305600500b520060200114500b90070040000e004140310650000030b9484005042d02081d115000130355440d815030412181c2c5d80003102c81e03103000703c20883c2006803c3e40000420b904a4010510204400c10040c0c01124801942c5610350f80082001c81048518000004e0b6841154000c2c1c84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463581708 1250 463580458 463580471
    0x302010f05120a020f0f03070e030607141b0304082505040b0d060c0201061a0301090509010b030d0f050d02030408071b23030f0a030207061e09090b01030908030910 72
    0x80507122806440c261500c1c0030108000240712021940061500c442c1002403103240c540c4003556101c285c4c20540c2c1c5480000c0498811405c3e5080402c625504081d01c0e00307001c0340301c0340300c0c1400b80b0713580c4140303081c0070710340070841c0e211800801c020401d0341c024281c1d01d82540c0010742d18041c441d8400007100700c490b1459100b001d0002e80c42c1050301ca0014840405014041428000d49800000e0010000764408543d41c8000000b4002110742d4924001a0030302c45a6560754509000c0ba000c0e2803000d81501c20300d925215612a95940000744040720800c241041c070b080c600325043c140c0342c40c082c0c4418100403034000410003040000300002000711134456500f580c4030120340c40c00c01f41c1109417400755000c44c1688240070016099151a10404200300808443c554080000c60604084440c4402c8002d68403c0702c080c05119000840d048252046201c24681001e401c413008000440c54031991504540d903029040059109800007503100b50800400d66030390030040c400a076140d0b20541d0000d907451520a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463582958 1250 463581708 463581737
    0x31509010c1b06180b09030403020405060301020412032d0302091e0307051315080a02030d08131202030d06060504091413120c05010c0806120c0a0e061c0804030201 72
    0x280942e0302d01c0080812032441e071442d54420000340149000b801d40703510505000000100403182d814410200c040185859030301d035105010031f40b940034000700d11a0340140810310161200720010f0041c4c1e0f0b00741c60880440c3c40150100c00703146c28041a0303031082c1040045501c0100f90590000d104068007641c01122005115070480401c900121080d82d1581012204000a150070b803081046610380281c000746080028442d00744800080d40010030540101e080342c8194a410b02c01c2558000b2181450384036440e040120101035081c80100608035000c400d580c9040364070800c140c0e911a0900e807030801020703490b007402418641140c852049150306045400c91040005003100d40141c160038128800d050541d640c0e42020130308800131408105c014540240031400c240580e4092038410340311654a410b2900900a1084010050780321990045800d034666071541c3d080f120454440b01d2201d515500d41c02d002620001c0d2207100201501c182901c1d103c14006420010812030340300340c071103156450009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463584208 1250 463582958 463582967
    0xa052220030d21020c0f06071b0b0f0c161b06020304061b020f03060403090e0c031311040b0a030305130806010f030602130b0708130e09190f02031509010c 68
    0x1c080030302c00540402294075144084109200030055250409420b203a8511842e600c1d014010200c88080c3d40500c042c40a00c0750494005585044050350580302c06a07240c558040d91803014162401d130a91420010303017154011000e86525240710700b0a110440a50b090060000740d000d1400c4410300c400010010b01180000216000c60704c158403440150b0306e042c0c070510012010194280d8010510352884801035070203009052066129880b00b00c0141c0c01c00c0e040702ca02000081500300014002c10078440b401510544100703080b9803141641c1c62001d820b00c00318014011042625800410485010003015040340151070b4159001c101c2d6160341e542c9000a035540c0200f885410756428000350140081940c540080c0815003901002c0380145945492203609540085000e54584001041da8000c151030390300c0400c01484a810344c88000d042c04c05000f622164140c20b2600c1c1c03940001000000c000d1201100c2030f41640081c252500200032403078003c2001c10450307100c0c006520340700002c1c0b8190b004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463585458 1250 463584208 463584223
    0x10c12120b040e0c060702211c18170a0803180f0d1e090b0409020406080901060f2c0c070507150518011e02030c010f02070206030a05222003 62
    0x209000704550280081846151b610204050780c02030804400c050781000100d801c0700e81000e80302c1c018010f8060b261001003038000142202010441c04911003090b50300d09400c48805e807030440b21041c002034108103080b894955a000c0c014001280801000b40190a0b10350b012600500c02c025114030903211006151100703103000c0380d032001c075860310450782c2c80c0300010b4041210784c1d00300d0a21341a501e40318868901503070030070340c0302c6401d207500050706020b82035215045540150b103502c003d100c0e941c10031504403200786c141c2c000c0901640580200c803070844c0d4622040004014000407400317060600b0710200c480c0350f01001044c0c54a11a44d840010a0115603080305007010490f0340300c0c0d00703101c001480f148140ca01007061904118021b060310b80101d02c903d056109012441d0000d603130b80d2060b03203006030a581a149a400c0440d01c1445098056241c120803a50700c80c0a00d080040c0c1580c841c04194190402200296030035440e5145400030081e258041c00401680f480102c610240c07460100355803501c9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463586708 1250 463585458 463585481
    0x30a0e0303010f210f080d0c050c1e0c0a0e0a0e0304060203071b080f0106060207060c020607111c05010605032802100e10080a180c030b0402010c12120b04 68
    0x2c4460040204c01c40f038010110b0108401455405107000e41d480c1c058100a00840a4807540b1000903090b01040a5125188082e46942801402c0a0b410000b0701c1d00d4055506003038800c0c101c58158500900028018241045e50003020721000680712b0401500a4000b11001100c0a142c040300b00b500d00400410394046078030f2a4025450700206039500c41000c000b15100070b604054607400491000c2d0103101d20b4280c1e01801c00000390052400100070300d03202c100c1c3e00420a1100010340400540c5a4038111024036410402c2c021034401c0ca80c0c04101d40e41c0c2070810b0340202400444a41c020420103402410860300203c3c22100301c01c9030071400c0051449011100411101c40489400041c10545c0c05070b60540d0081c200641d40c040b801001c511440e03000d8100e400016080d0f0100210144c203845403080451420100c2030911095594681020b012404080c2805030f03910000340446e0300c00c8000122896014111881c40821118050584d1140b00b03802100581046800340d2642080d01c02c4c0d41c040346 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463587958 1250 463586708 463586729
    0x8062d041b051309060b1605030f03010b1306080c04090222120c05091e1510090905130f03050d020c100b01020606010806100e060702090117070f0e060603070c060c05030a0e030301 79
    0x11f1112544441820003001c1150180428400c005901810001960013040301075906039540c0d08205103540c5100517a0405014007521005005014200c0746c1035500351541c80b80010380c3c503035580141c458060a201c98800c0c041140c00808122410b62120141c0c1581c881e040c5181c1c840d03124010440620400c8841001c101361144015002001c8882c1b503a42110b042020311125240d610003007080c1e0501495800d0200e00d040d0005c1210b06801d02c120742d4010049846100a00d0300ba55503455001846100074003040f00104852030a440544d0480d1a1030140d4021103000e90540d00d84000a00054088540940542400030b4295406006802d209040c0144414070100d240c0c001034941c0e440c244020307500040e00b03000070700c010f0720f504c203042d0701070500090600b8003a004240c001d4074044940d000007480032650002000004003400e1001c4e003010044075000c0d1241d440c1c4034200e98010500b0b401400c0e650600c503020842d03c3c1c009005500450006c081803203003148000035103503030344001c1c4211480704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463589208 1250 463587958 463587967
    0x807051201020405221803081008010b13020306180403020a0c0801050403021c0203041215060515030604090206070516060f03020f030121020312030708062d041b051309060b 76
    0xc034820042c901040216400c00246c049000200c0c1100c0003441ca0304030042207043c01400035551600880304020014640280040345188000c6200381e4408408141d0403070300800880e10940d9810640d4859841c00c100c1108185132500b0000d540341c4422406031490400084d012400200600030203114035050340051070120200700240000b00d404600304c00450005200c04143c41801e1a03606600600400c1ca820311104922051000c0b203001d507100c00d00c2104410508911002c400c41034942c803440c00c80d4002014071030f50002c1112031180d820005d1850040614491003a0044260710069440903035400c03840d6115070b54250224810310030000140c0d1418401004500b0700609c0105c40754000301c03500c00100b0300070340c04685444034010a080341c3ca40d012080001c20b40c0c0c0042d150350301103022200b284444c03800d00016058040d06041d1079824003207940024843d80c0725a00300100c003810800820400512000000f00103800c51104090040111040014141c10600030481a184149600703480c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463590458 1250 463589208 463589239
    0x20040f0504020d150f060305100b030304060c0b060a0909060e06090309060d0e0c060c030406030c090b040302040f1e06030209011706161403070c02131e0c0201060f0807051201020405 80
    0x1c1c22a20710301480780c2e450302414014070005d4040c0400541c819001000c1400d1108068025115150100d90207039205010070407003254088542c0451503040f403c660180c0d21034801080f0b01c800d0759001480c0040c10495454200526644610407042c9081c05940e170f1510340d246501d4682c0b20700c141e156446082031010108034240359204c1c2c0f0040220301c04a8012068540205003190030089264a540d000031404020090b0140181c100b032000c20316150920074100b6034801017a00071800064000c039a0b40d400340480900540c0005000500311840752a00341403030800301c0142c00c2c2400220b02031040c032800042e580e120180490780400820001c2d00b019a10034002c0d000d0f666038101083c0800031161900100b0400310700086005000c99503603003503441201d00500410403c0c603e40c8121140c5001c08401d034110018064042a02003440b010601120380070003240901203540080280c2d800c00480001e85010015260b01200e405551205c140303c224880b0700d080f0b024511840ced410108440c0003400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463591708 1250 463590458 463590473
    0xb0c1c02030d0b0a05100302070b0f040f11010210050c1e03190e1501180617100b011412040218040512070201030f05090708010b06070f14030720040f0504020d 70
    0xc108001400352261340780c0c1d07180001c15009000a4072004a0f500003400ea0501c0460007400d80c0c0b000c02c48000705901d04241e6034002080780070213005030544a15030450811a1710900c03401c2c540302040c01d420710850905d0840398125902c200090401c18040c2403901c0c0c1e14141d40d01c1a04c0c822a07541c2403054074444846928000717000b41c910405080e016940014480340c8040c04068060002e801a03190341c1c82c4844c0795081103911980000300ea070f810342260070392564030004000c9403059150201280e203400000040c0c070f9072410102d170900c90060202e842c1c01c213080c102200900c140d00880700c0e0303030911455504c0a61400b1041c2e41c0a00540c100442a08000003594001e109141c818940080c600488490050803030310b0683d08440550008030017042410310074087c1c00b086078000c44900e40f034107d85544140311031400e650024140081c40f81891007061091068808240d00b080c00e140c18405852000744061402c00961803060f03191802c070120701c081620075188282c0e07000c0c01300d0f0090001602c03201d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463592958 1250 463591708 463591721
    0x1060f0e0a020702150d0f112a0705060a020109020f010c0510090807020a080124061b0c0b03040b07080a09120309060e01110901030e01110901050c030f040b0c1c02030d 74
    0x82e0010485c0851000028a0b80c004101e00110304074000780364052040030341e06480340f000310600843c03000d22501e04850b00b814080c044056018441c0e001c5040240e055034209491640034075881400401e0b160281c54040d0451164075108a032215607000d030300c500540e21426240300103002d650010602e986034200650265a07654042c00340309081c21107a9001420742d60081c0c11800c480d0f51940820080c0324113400c6003005151000a50003406400e1400042c00042c85140308281c0040c1102e40074103000040d4034401c09030000f0540d1070361340c2c6000c0c10114601c8005807502c0c000100d0660010310303008400d100700480240e0003031055681000b11501180540038000007030745c1c5c081e1b44690710b0719803c200740314038800103440380c0300c803502d80d64580000340c00c560300c0c0d200486259042c43c2c407000070f86c0c5211741103520710202420880d4903558119865880d5000d000316081ca40d05001501040d41c284410180100c1d02140741210081c4002003041c11078848129540e1000da070080c010b0300030702402a04070f032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463594208 1250 463592958 463592963
    0x601150813050c10020a021c0605060d031b03050403080403060b010f0914010302032205010b1503060f010c0510020f040f050613031103011e0c0806030d0207050112181401060f0e0a0207 81
    0x5401b1200150005850400c0d4424895207008103034502804014541c0516a40000d040311020000b0503140c50241058003c4650481017043e00b81e036070030416014400365809076402c0303103100b911a41c407031408030010400c034590305022401e4002d0680382144615403010907120f901880000110a000c019000383d00040c1522034104000d104a09103201e6885444038424095000810807107040da0a100031000e0240c1090301008080040044580f104546c01201590070720b0081c41c40e100900748581091201c4190600c410f000041c0e00c07440840f10400fa0058681d5860070030902075550381048150304c2241840e0072150006401007000c52070481a141c0c660102500114400b40c8000214240540039490b0904040d99000082446540b068400350300c81015801058a0604c4100280d61000b0a00c201070420401c0c40d82440c61525a0700a5401102c034040e0018003880580b034031800806001d54060303501c1d0718000001580705921550b8008844070071090b11003684600b212030003c3d62003417409 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463595458 1250 463594208 463594213
    0xf04081905091201050a0f0b0f131107060504020906060c060712020409020c010603150e1504110a06080612030f180301060b070b0906011401171005030601150813050c1002 75
    0x59209900c036043c1e40c031074401d140e200004a44c600b42c04e504044540303000401320300516040ea403541c161585400c01d40650812a540d8104246844207a405020790344203c51711500d000c01e00d0001c12041c0d80040d030195108680440e11503035060203101041c040c1c143c405540340c1c020070204040c18000c00d41c81500e1402d4410146c40d294a6054000c20b990140803103008681d9034400130414042000e403c402480c08048003442141e801540d250b40d9000d038a4040e00078015040d01080811440c18610992060301406404415950750380140c1100c01c100c41c214001c0c052506d01440001c2c0110840740c0d0090b04000300c505002490002c08100240428416003666954201041040401d805002224401c10b8848054946040a50704150040e440744030010f14012400c0e070580c0c0c20400c6241c08494281e40300c5c5041d81c80b82c10100704002e056120540502409002003103290486010b048640399176180d22599031a04411500303804503510016100390480084090907241c002140702150045204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463596708 1250 463595458 463595467
    0x60f06040921051c020910050a0309020306010303051b21070203070b0424030b03060f0c0d0911030d180e0c0d0c0c12080732030c040303080f04081905 66
    0x9100b04500b444031007400422404980c045084841207181d91007050303c2c15056062104031400700c1e82e4401d481c5c1c5640c1c01e02c4004103030119514420740c85a1100e070b4000b800c4501d613594908010b403071948400c00c95040700814000c001540c410000d20b04030b09064012000070210040030380300c038240d0001b100c00c81e4075010340100007032500444800740c0b010345042d400100d200640005940d0040e003080318003134141030424112011030b50700850015030000e14020814969941c00c2c144e03010307501c80c140301902441d1030b00c0724002c24400d01c1500e410b541c0c40b040d0100c55a0b02014103082d510030b1134461111500000e00c4605101e000d1641c40044d8000448010181c201003d1b0500304068940000c503071000141249501c001b0b10040c040740b0340074542c0d181421001801c0c01c1c41d0080540055040d40d081c02001a0702000f03201180e401240d00a0090081013a00c2b418a140750410341e612521040e00040c15640104214014100f42c03640120b81c050715103407034619240c40c05545040300e5070440007407001c01d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463597958 1250 463596708 463596743
    0x30b07020c09100501020d0908061522050601030513081605010e0f0604030215090a02040b0604050d0804090b1c06150e070309030206070504080a1103030d0204030c0e0603060f060409 80
    0x12000c60049444000f056409401c2c800024507103000210b01404000301280c0400846401045554100100001c0845610300314000300c0c801680034183c40c0f00c07100c801884030002000c030b90710082c0909002d990612443d100c0c2c40d1610032200b1400f10182c45502d0401442c500c400350f815031211143d1041c000070400c6415103903614244103040040140300e41145081000301941400303507412100c1e01d00726000307541c10009040b6503126a2054000c0c0070703640d81c0c424506141d903050107580090100600d852910061481e0610046d003107032040c0c0590764109081c11100d450604804101d055100c003614044d81d81c20348414000d85110740440750f80c143c07114070100e5940003101c6600c0c0710308210340300855200b04070718000745880d13001410ec9040100c140400d2006003004500c01460325007050a0701108503451000034210300c01d581c40603d2141c4006400820032183c0301c003810450390300403d544d12550f9500309158950000f20780745442805c20394001a2286825030003904042e0241016071010038400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463599208 1250 463597958 463597969
    0xc060318070803040915030b07050706060e0a06090e0114040b0c0d02160302060708010308031303050d181202030a0507060c02012910050f1b24010e1f030b07020c 71
    0x41d0882c40480c1c000107018408855140140e50041021202e0107444600d56180c4444100000d800076040040020706a800c0c40451341050004c0d01809a491005090105140b002400301d4401e9000d081d0900303c92100042d8184101012901234840a4449030f80b180c1c1d800d112540010320070301103980240604901c0b64a1071002d40749420400e0032030500800e290902030703d040e1000300302208101e00c0d18010300004218405030380d00030300c112600280032050351400351000d0203684071100c503052405548031030307440c205050035030818000d0601102807040300c01d04030380b81c0c442c100046002c40c0c0c2c10800e1400040c45644070114201440c400094080c4a203205c02e00308010030700c240d03940c0800d100e103014081d14080015000c0c0c0744090401130b00d030140e01c3c0e1811010f03000d1409042800d01c403c0400344000c1e2402e1022100440102d26500340f60a4103000a1001c0c3e04207018608800c1e080b2000075645174243c81c2141e01800348001d10903440352440e6907480010380c004008a0440c026100e1064864440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463600458 1250 463599208 463599223
    0x9050c0705010203070509091602070902090d06142e140103021606290904080705011104060c11010c021e1917010b01030c050a27060509010305070e030c060318 70
    0x5e542d21103590390301c90020400d000801a0625541c907000c040c1c0f10b030301c4507000290213085600b40344000da143c0b102c410018821a1940300042e007402c1c00d003800243c400c4030180c1c6503442000040d9030b40101c0040300d51400e40c0b40c0d050421002032000004021f001841015064495414051401610381082c12416050054080d001100d0f00c9032500089080d200c404c0d00101c0380040380d461241e44580c103580c0003904820000e40301501109001402c0c00c2880005c0d0403280e25000d202c5602076603a603030b0f07203002080100160f0050b515502c005012040940c41030f60301e003c2d00340d002450100090307404000382036804080006194010100e299110044070040366040003494111400414942802d151a003554048000b080c101403525400f0003e1a40110640f002c10446141070000403030484045201c5420388070042c043c2a242d10000030742d06600000801480b1000c1c1e130284800e80307800b403042d46c0008650682c1707a4541c00003010080d590510b000516400ba540802e4030302c840301e0300d81c002403c1052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463601708 1250 463600458 463600471
    0x91502070309051509041509051e060a0e0a020c0c030d0e03330405010605030a0804050111160b16170403031d0604091112010602060106020c0301020c0709050c0705010203 75
    0x8022841500303160b000384800c0c00904060301c0e0708158009640c4100410b21840c040e040c0309a9481c186601076408041401c8081d003c0d0890400040c1000d0382e0121805011000e101107204241000409a00f8000124804c6600c60234810b0907644030444c4520294004035024a554841c080c201d10700b90764200302214101009071201c0c41c2c92100203061504001541c0c60280813148003a84082040c4c200801e0607810900004100c02c0a840d14039045000d8016940810b5262144406041c14003c124008004031007007621040b403a0b401c140210b0752141c0241c0d180044000a154081140c0e0121030020b01c80004a0120320310807407034590302c210034403d554145542c11080850f06004140d04050403c1c2070400c6150010303101403000700061628130542c080c1d81d041548410906069110010a45510070b9682950001960316100002e50303601c001d103d824014440c40c0340041c920704040c401c44004298500140c401d5504285125010b4a4040c1460310702d1030080005002041d000c2c40518026403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463602958 1250 463601708 463601711
    0x7060f0e030628050f0403050f0715060f150c15090503041e21290f0a0c0309020607200d140705060f070b06040204080a110312030601080c0903010915 66
    0x3003980f1540d5055060880800c0081d01d00800d004041c0c0844680b0756116a06241c12507484500c00c03130b074044c68003c00800420395400c0d10594070b071580b450b400c114181e8000c0d50ba4009141d40d207003605044d841e0b001c2104008200d0075524503010440c501d562040400c001c41c00800d4101041c2d460b2071441c0e000c0c1d0700000d816403404502e40c405901d40c94800c0c0c02000044242441900030100c81e00c2c0041c12441c0083c5950550788400b40820390000c200800e080781d541c114400c1e0314000e426000c05140c200d0740300740d151b0316010020b10501c0c00391141042c650740107040d1a040000e103a0394648881c05035168150420b854540c0780c05195105031040f1155840b0743d900e80520060011400e142c0304181d044144220340500c20403403104004001d0380c02c080d40101d80050591600404240288160f8204401600501554406011100c07401c020300740c10941c21198240d161ba298050180025600b8500242c8920003040c1c01e131030000c000d4441040014000100440c4566039050540598440c049846 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463604208 1250 463602958 463602991
    0x30b040b0a0314100605010504180f0e031209061003020d060209120f16060507030305060406080d02070f0b04050d0209180102040e040212011a1003020f0406020109140f07060f0e0306 80
    0x810f004d01080a1142d030900d8144078080c10840041e180f80514011200c0c00254280d5240080015070045440050050b0b401c2180100e00c1c449152a03a011560400c4041508004280c499000207427182c03261011015610312103056134200306822887c144107561168092203980480d07581c1d401071a08010301c110041090326908003840d41008150124000303801101c0c4400c01906802400b241d04460345490001440c1c0c0e510b5001a0040c14190081c034111312a242c0040041a00080e07a40301743d49001400484490740c0c3c81030051070703229a0082581140c410640d070801030030400b14032a006181288140d10010140316120f088ac3c00692190290761071950911081d81030201140b401d044240009001c54040c41c2c00003c0021046411507010b2a0007000c0d032688075100e07a0694942d1001d40a606d076446a071128024040d04036068152003108884030100701e641400210000000321040c050085146009400e072107546440303200d1b000340a070218000c444c2e940c1c2400703260311440103400481201c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463605458 1250 463604208 463604243
    0x72901030b070c0f02040207050f0706051809040c05040b0a0b070609030e121e0a060e0d111b04110c0114010e06030102070302190c1e06141207030b040b0a03 69
    0x6071005000c02080c0210942d065000c42e040600c00c0f920540c040d02d01590700c291340c2c60101c1c40c21544400b140d400d400f6801002c6210b0b94401d0042009603011404080c44805010401c1a00c40043c0c9000302000f40300c090801042c00c05412248102d80014401e001080da1594212030b240e1000c03900f10341240d59464201c0c1019008210980303a80ca00b52111300c4a1645603078410341e1038041940703815400e100c00714503d910242c10020b002c1e4186d40310005003d0b8211403141c040c3d03111041e0303484502003040c680b00d00c0000f100c00505010350108020b00b8580855190044c80028100708002c68886101044459008002401124100705076002c1942d00340d80b40c401c800c62008030103444070b44680d004111400229500080b039120300808001c555808008500e400303a038009003a804800007a450002007510089100050012148242c580b800320840d1385c0c140b41254410385011034012114400442c0040344650320203542d80780d024000054403c0e00c100042c036460116030080300c1c00301804141c504c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463606708 1250 463605458 463605473
    0x70501060302010216060516050319050c06070e060d0c09091a01031d030a120b1002070f08060403050d0e0a0204020c03090a05040209030601050d030c0b10062601060507290103 77
    0x5080014114400c85a080000080c80f601c02c8c000c0321510110305078503810074403c0a00441c0c448051109425042c040364150180040d0040d403402d907c01d025280001d00d149000e920a6000180700500d60303860b006446090000800c1c1040c141000c108407c60045007001251080390803200b41400c08110f8001d80e03000040c143c4100284403d0107000b210b44d007440e032002c00010707218a4040b07402c003400c1c0950255450002492030540103170b84405c002d60780d0441190046450010784518541054210f2344590200755101410395008001550400080b80a4030300d950091640c81d03c0c41040d109a0801a000034090343c00801c19045503800004035002d030380c5441c5860500401080c1c4065003003401d454002034560700e0512506004031440c40380d40301010300c00c00745c1c0c0d9070481d48503014186a00b41015840d91003030181c042e09000c90300101c1c214400032480c600007980d01c598011010003503820010100c400d40c126100440311040d0414070700340940050200441a020100740400d048d61450400a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463607958 1250 463606708 463606723
    0x150f07090f0b25111311030403110312090106080f0703020a050904080c03031302101106040215040f09150e09060705070c0506031602010b0103060810051b0705010603020102 76
    0x6051008a0030200001190000e0010485050060241d22020022140b500c08240102115000d520200440c02004500c203180040f00358251080002c24001c005032504071a070955440007082802d00003c0d00280c400c4007000c421036100c1c815242443c1d92103440b070300c0f07480d4151135182e0907945034007003841444070400200400551410085c01d120740b8580106980301158000c0358003071114200004e050041500881e00b60f1032800e41143e44d0ba10b4055003106c01c030900c0c9d1500300d1007007080001c045146840390704403010340003d4201518072a01c4036801c00141585040941d1252181404002941e01152003004000c00100f1404603d0f580813100c011100c0b1101d0304019800300d210801d00071a1880000c14a5000301c160500310368400d841c0c00c01c0324030903096601040c3d0104c0d000040101140b51000815080c2941e03400a0000c052151b005505030380f110301a0b114540e00c041d143e410031410640000380c01a6031076245805400c2c1c26501e07410980d02620096034160f4599204104550b070400804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463609208 1250 463607958 463607971
    0x506010e09010e0601030207080a0e090f090d0807111501030507080105070f050a0e0901030303090c050f18151206090f19080a09270b06040803120711150f 68
    0x84a0280d804001500550180910041407100f100007402d41d0b4007a9040304c83c065041024280c0310078200900901c014800765001e406603640038045545503607030042140c0500c0011000d405180b100d1502105c050a0080c003000401c0551408610000750500100c850008000c4003001190b04505003140361a01c0380e80044074980c942810800c1d407903071190f000e140032141c5181280c1d0750081000c0844030041c0310515180e112044900001c100740d0554032811403a0b2080d1280c01c4210b503a407040205d00c8030001d47d00b40c3c120300740d140f240703c000c00b200050300c6e80000810494013142c0c1c40ca0f400324000c8018041840e8403980b0100c140001141c0c100a078030090b20102c8001c040ca41440b515540c0001008500201900d2000c40d00111142c018060311010b8110390071400e000040c0502d6283c120404040c02041d0300340b81489100a9042500480d0700341c036913940003075261071035055910018000c01062801000b60885880741404010300880c16440c0300245c0b14444c0d400c210b1035081600340080c280 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463610458 1250 463609208 463609217
    0x4050a0b0a0b090105071209050307090b0102010e010903050a030f0e060403022413030503040201050d1a0f010207121112030c1b0d0201091502070806180c0d1505041515050301050601 80
    0x6100f143c1c3d2000031114080d500640e04840417844003019554408190000303981343c0034901000c00c000c240c0c2c2e401802e1002d4244c1c0240414014030003a54200d501c801405400a00c00b08100d481e141e0081c0c0028419130f001c0c0c3c0c030003c2d16200b090300040c20031100b541c04a006800001350710300400c42c141c0d8ad039a44a40d2044550260341030143c150760102e11070080c02401d01c80088001025680202e05403005100c1d00b0701c1c140a5a10b44d9600319251803900c0000910800f06c0c1803a000301c0307500c000341c82400e44486c4001d1020b40b9105448100c60390002007030b860761040e941d41089204403c10b0015003070200540008010046940344081b03100040032110300d0044000c80090b1303000d070ba800121901207416440c000c0300e01c001849022800c2c188150070064040c880c01c4140807a015480d901031070801451401c0c5d030340b012848da0800500a207012806488000b410100d41c219070441c2c2e0215030843c1c4a44100c1020801d12141c0606486803410000d0f0050010700c8100480d050138010140e01c00c00c01d02c1c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463611708 1250 463610458 463610467
    0x1107150213030609141e0604020120060403092402060f1b070b070e0f06030628030807050f060f1602032502180c07080c210a02071e1401030b04050a0b0a0b 68
    0x400c6031f0b07140304c0100041d04100b0041075007104a000f0840b503905a072120826280303c0e19083c1800b4180051a100300340307503000c5804030366511100028401e40c2d418040c0d80509050f840c2d5161000072a0400340c0f40442004614000030881d005000c000d10065202d68400d42291800d039038058003613070728800e01c68040c42c4085801038055483d00d00700d030751103034044035002001c6002442d080b04803d09540b580740d45200c0e074030000c03003448005405003030140d106d841200e14641d1800301c1d45031074040685086501c0b840c064049221031980c1a69599107020f584126814410060021200443c0140c5080040b4410300020029401e007420103011005152000205d1814503110000040c4070b40140030b070074101c0c0404c80c0740030340300c0034003940c8441005e072020391000b003180d2400c8020340e03404544014054420800c0014005804845100300300320b82e1032010868a141c120318804031420718001c00d0405940e020590f190350380b0b901c60702d80181e9203507000007400d1145100b441000c2d80241c00c00142c0a00900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463612958 1250 463611708 463611763
    0x10806011d01090513050304060905041a0102060106050a02031908040201020f1623040f0c08070201060302010c150209030601080c040e2802060705010c05030a110715021303060914 79
    0x907845070441c0c4002500043c10340e0740c0394400d0700f981c454160050140c080014005074443c1e2003040308041c1e8008480800c00c00c1c58000f0742c0d07140300c2e140040381805030304180300400c5405e004501a103034511007801980e250000c0b4820b414148460031100303101268681d41880290f5904000030600c0380c0303031a002031291111904507440e00c9880b501ca0700c46401600c07980d010410300008030028500101030018800710408000d1500130304014241440044c0100c0d000503c0f01f4070500401084035010f848000d03c41e04981c9610885003045c98501c0382c9c0d503800b082070b0070041d2000c00c0803034000d00c9040040c00803040c0c60b0702040b060310350a1071241415400f00b100780418919852503040c100c248203071511441c9040d0700c040303485400303404406400355203000c40e0b01c1c103040d4000000714421445407008000100b41003d070001c0900802d10003901000301c18442e144a641c42d6801400c52490100203040700d00da5070340d1904252046002c0884102001361a00e0114080070082541070149580500300b413280442c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463614208 1250 463612958 463613009
    0x30801150507111908030304260315190e040c0f06020c1309030c1a0a0b090712150803160b0106050405060f090a031502031905190e03040506070b01080601 68
    0xc03071005125548008004e0301d0102c1c041101401000000166078892509003014041b050100145100101034040b2100004150800300d0b0321501c000207400100780c031302c04240405143c0203120b40c40a20980307000460795180a941c8144100d124001310185a4201400401c0030769641c0d0025055501c010b03013160b07407503950020304600d0080e01e12001400c511207082c110381c0796a84060103400210041d100c4170010f2035024009104c1c03011404180580000312050080446040b9070f801d00080e101c601301c02819402d600000421001d02c0120810302e40c0311194141154081400f401c01100c0140151003000030802c070040c0107005504006062524100101d692071040c0946907442d000c0000300c9080030b64400180c0006103400100005889104031800c4009610540342c4802a03422040070000022080c003e240c440c90211102d01c0e4410000d0310b041000c0c0601c2d81205401d80414000814282c6501e0301a01c14a4001d6003004490752408010038200f00040c0c01404502c00c07210840394100c90407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463615458 1250 463614208 463614233
    0x41401170c04060f0e0a02190f180b0d051806090d0806090103240f05010b040305300f190201020a1b030518030313060306080d031b0f050c0a030801150507 68
    0x100d4841072541c1d940d04400000234800d038441e140985030302d54000700721140e000d082c5106514242e03d510030021030607065000740c200c451042c240300d58401c20016001030010f0700810b8205010b0340c901000000d01c903110500b010000c9901d44410b620690a11886952014583d9041641a1303a5020594159203404103a01d020595010320484510410120020703240d12088401801840420031355031600c58901281e40b05100980d000d10498449154180c15000440d000f440c0303808000307150001000c3e1030080ba0300300410301440d01d03005020b50105d00000ca079098681d4000d0b0f45c001a0795002180015002c002044044404040107940500009800800b100d80742c9a50103910f40c2c2d5850640002469803050740c09a24164140d214006000c541640020007550203520603609175030300d680382c103c1c11160f94031140c0c002c034002c40d03040c5003010340643c007045466142c40c58150328100540780362910300079003004100c000889281c010032100816603440d594440880c40c20078602500d5450350200c0c40c0a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463616708 1250 463615458 463615469
    0x5030a11040e2814072c1306080102071a0108122221110409020622051c020a0501031a0108090715030204052e050702041401170c04060f 60
    0x2a400301e840b42000c015000441e08000000302130207201010a4400c400c1d84054a01c0c40200b90124a43c46c00800d120021380c40c00d0700c1c0d4100d1200c180d1004820017003040c02081c100d4845030740d60f21001c24508020b000a00005004114030400060000007405000c0c105030b014a1803600400f0194400b400c01008032402048260400800c4002c0f45411032602e480583c130180e1a0b40ea2114070515002170403082d0100e5a008141d0000c0c945c0401701030006560f050340d002980030700100030b0901e88802007402c129070700004089092203107071281c01140040714010032005951180f402840110301d44013440f074026000038a42407140d842100882d40f0108d06003241281805551400210b80480c1004104014160004540c15a201220f4068000d6010340251402001107507642680840103480c0030040302e4002d40520f20710400014200c403560409001241e0040c0c854820b03844083e050512640a84001962140c18041c0084600e00e4144007003134040c0101d080c04010171500303480e804001c04851 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463617958 1250 463616708 463616731
    0xe07080c090f040507110d0e01020703083417090108011512151a030f18120f25150f140a150f0305031b03090306010605030a11040e 58
    0x1c0c004000554920514400340e0b0000c0c504401c0003c4540c0c4a03017141030150366802510000d885130201103803004520f04001c0e015a00520342000041c941c2001807506031084000801144c3c00c42c0826001d1629101c82c0f103504100d0132480905108030201d01d281d8905c04000c41618007041400007804040d41480742403403039415180304484440c001c04140d00e0500307960808101424103500c030b1801240e860f00039020005048400c2808401e0600100da019010700307150440e00d03988200c010305a0b0140a044c10405005100300384c8101c0c42c0c80342c040c05880000921464541407014180078421030300380c0b03503020601844100440454408a890442440300410114002c50314048240180c190807031481e0320070088004028009544d640014040050103451444455590000401e039000600024110f500100152000b0910003840d0141c05a6204140da04103811030000a05018099000001041000042000c1d03280d00d0b00c00c01c0d1410100035600c034100742c20152170004101c8010035884001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463619208 1250 463617958 463617967
    0xc0a0f021806101103090904060e010608010605150a1107060503041101031b0e0102160b0904110c0d0806150a0207181e110403080403030905091324020c0d05040305070e07080c 77
    0x20170f00484d0840e90002d01840302900307084c581003005011a104400c169460600007154250040c021314040710030048c130688594100d19190038680c0c0c00703150507109100a041d00c68000d0002842281d00030060380c2c03110f503102d10740f5003170990001c1c55150318181054034101c06d03038410011042800244014500d04802050140f90050b03181495480c01030303c00d01042d580010f0701c0740c2030310000d01202800341c0701481642e0640d0240540380c05842480c02d002d4014140c0c8806291148410035071204004103990300c072200503001580303282e010030200340041e00314010a2052552040200500fa040e6250030000c00c0c2000440c81c0b0150b180703500c407003070658440b601c144610050400780c4015507003000c40300703544594a2070080c000c20101c1c840d15000e01c101f030001400713004a020b0018540358015440700040d5034000c44017401c04c00c000c00c40c042015402c1c040035400c600104005040e21001d038541c181e5440c03d500744140391516641c072000c8030a266904112415500c521300c65000140e00b001d06441d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463620458 1250 463619208 463619237
    0x507020624040e0f070b0301050105070b040c030b25091d0603100c021506060f0a050d0912020a020f040c0e0904060f0923010e0c150c0a0f02180610 65
    0x41411600381190320500340303148003a41a4001c1a000d21340c01002c4d08940095036100b004c000540400d01c5040e01040050144401040a001c581a40144a141d1001d400b9489075240984500291b9074482d1070400c500c442071859001c0d04a980031440e103800c103455418a031440310791655450414620a01070318101069440d20100007064600c1d50282c41400800034520000f550f541c210007072071000841d21400f24010b82042c0c41158590307804104181d180c210150010f07903059000900000500e0f644905003c003150310940c10340340140071030307014114540303060042004045078150031601c120320340401d80c4062904001889008241581c2101081d40c40c0d084c250010b102c042c010342000c904081e038040030089500c80f00d000d0781d034016840c0c1c1201080e41040508076158041d080340300d42d004a0b10341810f03240070401386070b05812880c080340c0b42c881e040400360b0a084c038881c001c449591042e4101811441c0a9505d02110f017141c1941c0f0840e8600f1350000b0300080b2100c070341c81c070901007400c14400780f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463621708 1250 463620458 463620511
    0x4090203181c031a0907030e0607030c0507020f030a14030a020f030f090f0d0f11090a180204151d0405010b01080702061314160302030c0312030406020d02090a0e0f0a05070206 77
    0x20ba0890017081c09005180c116000b40c0a0074050109290600402d400144058000d00c02c040041c0c1165407014201650f581c01d1181c8445905881d40d8144500b030883c200041c038840799452000035000c086c5031504030504002c0d00d000d8001030b030201241c01c24032031254070303892100c00d4516004003103420708030600d911008103080514986005d001142415920424400080c6000c0c0c0360340416100c1c0400d5949a0b0003420407130f0b541819800c0000d80b6104200007510300384c0c006198003174041a0320f1484540d50080b02000c202c0003a241c1041c248035a0030001403010070312611102210a0030700031014908800d00070f4031180001c02e1101081c2006405900b440151451400c5185490b011586207150300e281a02d85803007248002c038424454144000c1003402e02142c1ca04200c184001002d01b0760300d590f51260f0203500152400b0000c240e0030301c08004250b841d00401da000b04a280d09102c860f06103810b005048800040010072810304110602810a500050752503104101d106011440c8080107072019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463622958 1250 463621708 463621751
    0xa051c1104140901020a020d08040f03030e1204030321090b0106110313120c060201021e030924011403060601140304230313080d09170106030804090203181c03 70
    0x1450030300e80400f00652198154014040e0388920740884420040b482c4040740e00310380445004013550680100100068041d0b00010508258581584c4c2c040c1d01034462080c898100d41e00c19000204101400c60b03501d002c3c95041d207074840c01520140440c050a0301ca041d05010b042c8682c03402c100c408481c00b64124010710603a14258242c0c119450701c0d0381d582d41114407190001c902654480c03045080003841318014422201100c8850520f6006000100c0b503c40040e0002810060a805660410440303281c009160100741400111198103950410b000188040102c844180c0654003040612100e40c1c4c01c40201903910f04124605540d0342e8480ca08076070041301903903014100300c00800c814a14210080301034940c404600c518190b84507502c40c03240b5a20b1002480200c04150b000d0b00a01c075400c5500d400b110b844200600214809940741d0398020740b50700545c0040b4003650301000f80041d40d00c9500711130080001180042031490b4034103c58802034000c2200368030606175610b601c2060107480e0300004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463624208 1250 463622958 463622981
    0xf0921080c0a0b040c0302011b11011d10050310060f0801032003010c020309030c0604051005130e15041a1008060f030a050a060612030f030f02090303030a0b0a051c1104 74
    0x290b038134141854107001614590204078081000d104560704d2a1504840d50783c4507980003030070702c0341020b403860044d01c1d401d02c0d1610841005408405c420015240d0044a110107036896490540d2031816503289503210315507420903000c102d0080441c91183d0340c48120b860540340c005880d8241602c0d600c03650483e890700d4000d440e815500341000d0707101e125004009018030600a44c2030b1000c421a003030401000b80308038018140c0c040700c4083e101071614031075006001181e0428180c40300d076546580a804a02c042110000c50200c20a0302c003170450308242c040d4480701024240314185400b0000d00083c1c51803807604603401008424000114a96217001d800440891302406035981061305041c2151110310440058507801e050010016841202e4014122101c0d0156625410381d00b43d10380807005880c806000c1d801d415000c0c0102c030303090fa41c280000c5000310400200000c1481d41c080a10011007030680c0210300c2500d80b040801442c0380d40e400c40a010300d9004450f4103841b00c8010005006208070740302e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463625458 1250 463624208 463624223
    0x6010306080a05060402030d0e0a14030a080d050108070e0403120c030f111e031003080702010e0a0b0d1a010918110703180e0601050904090303060b03070f0921080c0a 73
    0x100024000f0104030300340500d009406640c0e03012520031061351424041c05002d90010030500301044140d80e044078200c00182c0050646420a080c0d0311035a106420911001c5c21050340c400041205290070000d0340000c01214074900310b10b00d0f041d01c3c0609840a903080f21784040d40c80320301101910b8440e500516203080c11440070882505040c1c0c6c580c496401664181c0000d00540c000c076140d040490301502c1c4183c904100c01000301d800c42d0b444c0d03404d980003d0b03000c905020709401c03201111b545034260600502007005103c0d4441e07009854200580300c400200134900c689126880105980c44080340c0c040d50902003034154607401d14210100204a614064004180042180000c00d035105841c40f26146012044820355926080c0700d603650542522802d0109500300880d140b0781c00c042c0c218010b002e000e41000203609a82d2110540340c0c0d071085904400141402000d41602c036041400d41014051520042d0b080f0348094045090040c1150006000400c0100d14880304941c100111111039a12520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463626708 1250 463625458 463625473
    0x4050703080a030e0c030316151407030203061e01021b01120c030504140706090e090307021018060212092206091a09131e021e040c05040f0e0601030608 67
    0x1004004000f0104884c00500544002120600c1d000064030302006c0066800302d1117680c26038540030311000c40528141065121058026441041d84000c3c6c0f1401290f1409648c038903045d8100885660000e4040310520242c0800e13000c141d0740056040304400028000c50700c481d41940c01a07910000c1e03000031516040c10003c40e200180c1e4140c000368040c505c10040341c1440803192100e03036103030002d50041c0000100e5a400c00c102d07440a040c0c0709500300300c01205583c90f14130b5680219000b000140d5101d00071039017042103101190720030602240100314134400b4280b4a003001300041c50502c00c2e44c00d054410030b204170050042200000300184101c8a41c242008001e5943d072041000e40060788002d0014070100b036802d460b40c1001c10301540309500a042a481240ca55961826080001c00005078420a5810072500507211080c1c00c580400f0748682918545402e80c041105850030340340c1d4001080010b1204201194901500c00e064501c030580c044030079610302c8012401400306900440b511f114412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463627958 1250 463626708 463626727
    0x1f032304050a03081308120a0f0203091f0606020a1103070e09160b180409051f020702040507020a052802131e0501080304030305031512150901050402180405070308 72
    0x30768600b005220351203441d00e60780c41c030f20219035840005001400380c04081140c41c0184408a0207507070b1040404000041604224980300100d030011610300b40141d00030780003086480020090385046061313121080c0030300c5041c103100035114165074000505200001c59000748581d024442c4901400100c01c040c45e0710302d07040d00b407255512904641d80c400720700c1d04100411018111380c201d84058131410390144d8105000703010b10000384152001600c1b0b034024084552480c132480401404c0300c0961813405a1074103000e004020454030090601d2003554460702100707001034000b244200c200800c00940c50a01d000d4013107081e046e400c0c03081c0000c2d4401c0706010300b080a00416403014195130800d062040c0d0b44181e1250368000c441c1d0a01031500306500503c410000a0f100c2d00c020f50740301c88040250112168040e0114800144c1411884100c3d040707500412034540c1200100d607031280222009205504151700400d00c096000022012a80d012070009030511208200b0840156440641c00c0d65844154 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463629208 1250 463627958 463627963
    0x603080a0207090e010218090901110301090605011b0506130c09090803190b0a050d0309050607120212180d1e0305030714030402131d01020d0c09051f03230405 70
    0xe00914110618180710411546014429581404c5c29511f2040900445104100c40320000070b1188a0300e640343c4030410100205140a14000c0c100030a0104102e03080400160440c02002d03000c0c40b00c040348101032808500001011500032411031800a0309103041d0a004021000540111109600b0000540c00708031100c0d009522955a480030340b501c84009102410070784114000c00c40d030000d110070342401035182000040d0745041c401d0605c0c520b0f00ea500c60208250b40c210450590303442ea0110102d844040d010b22151010034004000742c0d1410060300e1035104051262041380340036660110f5902e0030401007058154a80408807a015003400d1140750051050f030003102c825000601c12850810172104441c10303207001e03541c010560b031401c2940c500d00000401c52001040c0d02c8200c4103543c0c0655a400303100521001115050100b020307029403070041c0141005510a5000718109054031801c03c01c2c42d800c1c4118040140380201e4a003d51030100041c06080c44010107400768800240300401100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463630458 1250 463629208 463629223
    0x504031202060f0c18120f060f070f1103040b0f0903031b07060203121501030b060d0f060f14010c020307230306060105030702062806060f02011109060403150603080a02 74
    0x10102403d91a030394a00381e0390700c40c0900e0301320f100802402c41100e400d40c80c00c00740b0141c201c410f40701103502d80c985000d81285090400e4030b00d2201c80c089102441401e0b0317400341040c211240d050408c4c944400300c0180300c1d41c0d40d20a910a4200e0000c011401080340d411110072a04895001400c694071410300c1d21074074200700824400c2e030740c4a1140c1040006d0b03440c004029101c002c045102d2907e0a541c81c15401005016070005260415540d148a5640c03562003001809080c1c0441e80002002d1340986c05440403900c0582107082e16131300625040250341c45016134000c0d00002880c00f90f841201a2010a01c1c00080c0d130840c5114180900500803500702c40850700621010480460319682c407038034015505840300b40d0b00c03140160002400945103124200c4064050b1801040328500c44500109180403103d49800c00030000d000c0032141c080c49542400b403d120160103000840ca406c4410300051414030a41c070006050024031291480070b86050342c00b00c00115004001c0310b503079207c1050300030345071160f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463631708 1250 463630458 463630471
    0x16110103110c1b1002070e0a020702040203090a030207090b100c1401021c0605040c0905061b0616020d1103030a1e0c0314071b080306030c0406090b01020f160b0901050403120206 78
    0xc42c2240168500d000030b80c62011319615005011880d06140407010914401001e07624055000c002510058482d807004600c6000c281c006807819100070304d0028200380541d40030b1001107080c4412601c10b55510019120b1000c11410710090742c1d141443c20501100b020312207040194408a40403400c90030011400858416100d400c014071912001000304070f40d8421a184001420300c2414882c1d81840001403d00340b40070b441c060244000b03071a0032032402c14102c8585540383c0c8906541d80125404000d1225950441d040803a14103090300740060f500d010007401d010402ea06c800348041c820003586e07004c980c5054001030600c03145801c401b02a015003021400320420014607400038091501c90f1070880f401516441c801e4062540c2600c036210103420203410f584e0b00d8010461442403640e614452a00240341c404404251840c4100003e81814080d00800302c480e002000c000c2c2456641c000d1100948100f0950142c40e5001c01c401240e07180159000202414211400003055940000342d6520465 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463632958 1250 463631708 463631743
    0x12020f0405070509120f1e100501030c0f151e030e120307020d080421050906070b040209070c1a0c040f0314060a1a01210c050706050c16110103110c 65
    0x81405020761740c80c81c60314104240c0740c201241d03c0c8542c10128007000750309520942208c1010043e402d08008032042030780b084a60b440c00100030040864500c03059001043e22050740c1028450700301f4041c00c0c02c603080b81414410040e2015440001d030182c0e04c904000380c400310071100000541c8015420030343c01910b0b82c001501c0307001c03007466095105103c0a44910ba20241811030040d07943c1c0840c101c41d80c1d500d0000b0900c041804401c00d036884447c01751a0f0140900300c45041c0c1d0909006110b00c61501410190803c21a06900c2020492a00c00040070602d098103152207661032030f214102500a540002890703408140c2e000080c003485142070182ca01002003560129140c0309114000c0362202c880c03040c0c0c0703003141c0c61005045600648401c10100c0031100c0b520105502d02d030b211000c13250700120b15404242c020880509210030352090300d0344000176140c001d00c3e00c103103230134080d4400020202c002c04401d10b5a0805000e40d10075000042000c290a4003a03854a5110940c541c94900b040090850722 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463634208 1250 463632958 463632979
    0xd02090603010e55170304050a11010e181504020f0304212106091118090405070b0a03020f0711090a090809040906060f14010908061012020f0405070509 67
    0x400e6100c1803038442003988400d05507040583d80c15001116410242961085c0100401001c0303104004021445140b003403015200604062030f0074800c058038110084e04204410a03603580a0b180c24402c40c090340c005d5900c40d4140c1d50303641100003031b6641e02303084203400900229010851608020186018522402200340086880c0e4815200c1100400b0b001d030000d0b003060304203980c5da41c11803080c90403280318500110f022529044201d0a8a90001c003d002c0340e6000103411784a40c1c2c0800070500109811110305a86041c130380c0720159501141c0c0a211540350001844076000d0b8026411a0341e641c0b1540d03c030746d48440c0f560610780001003540e5620390103520150001074030402c0510035503200c00c0d40300d041e983c20030f031510050100a00c0301c40c1c400c4034000e135248400b080f0740c004800700034004c0440840090034418008001014007286a00103007484e803140050044017103869542c8019903101c46510b601040b0980002544d1010350b80c00c85801c207181105011080d90f02600800c1861b07801d4490031f03401d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463635458 1250 463634208 463634293
    0x8030a030212010b090d30020709060909021503130f0c030c0605071505070c0b09033406020d0f0510030605070207030c05090601020325120c020d02090603010e 70
    0x140e00c9448000d030b41c0808040401c1c00020119170a1558101e47d0721410201001000241c2d2500d00148805502580c44803e04014405040c040e606c0034104000c0c0900a089841e03000c41d482c4000c2c0b4091001ea11808400100f0090214181c4240d1641240c0140781d54002d90400d00c0402041d408240d0320b0541c1d50b0f00218a15000d00c2c201c0d035502764031070512840d907024201903500500001d400d1800b0040030b1400d80700801c164802d00781c003607800280515034811151b002405040c8004201c041c488514180109175031404030000c9480e150001c03000f42e900c080b900880001084c020a03020003580c644400c3c020f200703001019030815a84500810006a16514030a03655502184401040108584010301c4035090000d10940c0000040c0102ca0803c00c0700d41c00c2c1e160307241d209490080c080e080803e505043c0418480d104a036a581d501f003a10b400d0881d9008034502d0b46885034060700400c1d041e0b001c244240c609500c44a6000303410703026039610b030305880c060041081400c10344452400002564100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463636708 1250 463635458 463635479
    0x406120603030c020f1f0512061203040905100513140a0e030f21040f1e1709010908060702160f0e070c060902031605011d01050a050c010608030a03021201 68
    0xa803034143d00c41e0508110941d00300910110501c13003040e0081c07070803000460340611181d00c1c0384000805465082c4c07110f6282886142c0c224000704028407540f00a1070070468044041704880039034003456030114140da10001040e580340c1482e8043c64200c02002451161041d540c0d002c4102c10394036140c0034966444d14004a41031b105c0304144550607030010000c284a80040d0002441d035043c002c074124102e040042400c141d01e031030403201682c2d0345800e042d080041140300d03101980035151808002d0f1040920341c840729500254940542d4021900040100143e070241d44104010f0285d48219010340c40d011030700944031a141ca41c00000564102d2001c2240f800c0001560151006207410055a036540c070411074407010300c2c0800391002940c41c01900d016840500c180380100341e40896900800f854400010b100803108030800e0b429120781032201c2075a80c1c0c07100031540f4650591a1854440584074905401003203258032960441c84005105080150941c01400a0f04120401c00e011030303aa40762403a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463637958 1250 463636708 463636721
    0x32d05041d0c0901030b0109050909010219030e060412020a0210090515160303090309090207081c0203060d1212060f0503070e010810271103190c03060509120a05040612 74
    0x44507200c188814403c552283d03100705172044051500c1c0302c41a80d92000f04034013080c04e481118123079400260111080f940e10600c0303121500c0d41d180c02c03c88a24000741c0a5200d43e405817000304007500d01548030f00b00354130030050080f1050b0001c0c10003060144601020785442d103035210b50307402074100c1070000c912058801d0680302da48602c1c8c0103210914406940c210000c00a46000710240304039034002081c100030901c0a40a901d200ea42120759480a0340b00e0341c100c0c0f485500394203101c140104204800d5481d80d80020101a9020000d922400f401c40020f55094901000e5220040d2070400002014101150030000f00c0c0d109030f0603610f14035200c1b24001030381c1000b400340d00c4e02940a032082e0317650b86260381e0010b848010001e201030714680c885844411104040340f42510f90001170000c4410626042c0030304000c0b0008103c80541152450381c80314440410b40c400075203102c0c0e0f2440040d4160005016a0301007500c501c0051340c1e150300700500a40190043d00071440011201c5510b0300030910a4405c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463639208 1250 463637958 463637971
    0x120801090c020c01021c03180506040606090603021804060f020d0615170f0406090f03020a02040f0c140c030405030609160603020301060c02120a02190e0c0412032d05041d 75
    0xa06910071046e1454180d03c0c0c130b4442c12000c140d40d40160500c44010b6114845815101d54054a502d082500f4004240c030321580201c0d02292a0040810051b51a0580b600010308007090a4110f56120309142c0010103000c40421009400022140e8014a42c0e5000d2000e443c0c50314410b10341c0d400f1001c07003151241070b5000a03900c920101408540e0030b2005403260f66106105a502090840d0342d9510319484100030a400c130056404001c80c44110321f000d0082d80424143e0000822000320074200c018104e1980d0206511107860025031460010740078801c03500a0007014085480034103110741219528840302000a00d144000140454801d11038001c5a0495820b0380d80c0603c01920b5408206021002080b044e149115210710380300140c13541d410840c0d403400d07200e440001c1a464060020f60071580103003d5210614204011710941a40005020500e9014a00800404100704070351250300100080c4000b0001010381320994564444010001d0b52540c075003240e418400388160108202c02510034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 463640458 1250 463639208 463639213
    0x60f1027050103050c070b041e06090606181109060702181006110a02010e01110102130b0c0c04090c0306150e091608010b03070512031c0207051903090509070309120801090c020c0102 80
    0x1c5804502600701540c030700c1040d6000b127000403010f40d85840031180311010460348079844400400415800c10076107200c0c402102006c6c0185070002c2c501620394842d403071300c0300c0c81050081010f81c1552a024074600300d042c280103000559007000c9164840c983c103244502c3c40083d10301d02c0181c0f15060700ac100741030090341c10785609003110720306001501d4107511300e40c0c03401882d907013031190000c5901008240ba0040c044c2505199603945442041410b081c03006000341d000e41d00f00605000060f04120104049070b0300050001340c5400346081510049141d6800100310389003010134031641d40d00c0840c03600e185490301e142a1070900e0765190100c1c00e0751486810300e80d00d40c010100030003141c1001407443c081e45520700c00703407451320745000000c00510f0b41300600350310402d074041040c2c41000b804100186202140c0400708541c1c0b401560002e20b000e815014440c00784404501103101c4a02079088641ca1a07400072601210f10f8607190010800d00003445240003450401026110503800442c0140e203200041c1d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 463641708 1250 463640458 463640461
    0x1407081231060c0e030a030f02100614040507020106030506101d1e04060216050c12011401060f05070218040b0f0601050f070218010810060b03060f1027050103050c070b 74
    0x102d40b802041c00700c050406002c00c00c1d08611007950144084c00710b05120b500e610400c078003039400c000e00d4000903070a0000040d207030410602c9445000c2000500c4408102c1d00800c00e03554101040340980030f140d00003402c80c400d40c0c4c00d00442907040c90120042d03c075800d51300108026680a02707403600d14241c40c034421407011004014256003c102800360301034002d0101600e0203403d90810701d5142d92040042e00c40c1c0c0c004450021140c90b09070759000144e40c20702c00900403540d014642c6c1205190610aa0040c45400e000e10080c542c001c40540e4440c9800501c4681103115811110507180380031a4112401078401000908950700e150300c042c02074078103039911414403041103130209841d4440c00059034004c4c201d03889561b4071130255603014041c003050005801002c44068012099070810341025001c00c000f48100883c80d10381c4803140d01000821a00712061901c0340d8829221086071a0b0942c548005a455040e101481490440704845003a80c042080e40d540744103a00042c00360f50401004a10041c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 463642958 1250 463641708 463641713
    0x10c080d09030e0a08010606031803081801090c0b030423061b04030210020a02190302032e05010f0510050306060d0c050f07120e0102030a0f1407081231 67
    0x14412403070184030b8182103c8030304088000450040081c1d0102c4150380d1161070a2085590501a1031481030a00700907001000300c50f900505045401455034040c072103500c1c1d40c1380201000b504030142c0290481c80c0001c0d05502c0752035040141d801150180d5078a182c0708039050b2441d18100540e00030740c400c04068074064940c09420240f40d9100d001c00003090350148004009030341c0d40810b00001105a800030124441e8a10600c0b1444901c5a03164505a034074400400c09618081585d41d5180041e80822072090f101b041c54003d1000c1002c1c10240040c035020003c591010300c40a117505036107007240c03100000c0348480c800b26003510080301c2c05500410244603030b20320102d180c2c102e102090200d0034042c1c00c11001c04069881904002c0b0300307803403200050010304629a080381c8021a60350081c4082c0d490000a614083d18558240c4e503041c0c00c101b0b82e20000303005503007480e05075070000d0b610004482d500c1441085034080742e0802d0300e28004120000d41c0252041d540003200c51805221801c4961540c0c0664 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 463644208 1250 463642958 463642961
    0x8091c0807020a080408060604110a17131a04020909030a1409030f06040b010302130608030315150f1201080102070f1509080409050708060319140a0209040311010b010c080d 76
    0x1034010300039485000c1e1410f00041c02e85015001811556004003c80e103807003030070801655000d0208981e02101007001c854030303d9000c405800305a81e16469448a522a058440f00080b01c4030405040b40b001402e02c00005416101d942d80a6402207845501c00d841c0d00d107a0544902c1905480c8012410070405440008031600103011f00d04002000da03a5600d16080c21b081c00c000c0d040b5011503401c0b0240340140110f241909181c42d124803500d600700081410499102e0b92403002804646000781e882419403019a07800c481d006400300c08152868880c00e815817007040d184c21494640c1c0021490707100201d404001442551215038200403024001183e9031039010680c01d40340e00c3c00820a0b110030000b00444c103040000c000a101da07130400103140c42c218038000c0500341c020301400d00c25000344043c0103c1c0d800840c03800004980000002c9641101107107810714215050100940006001040000b4160007000748000b440012000340302410541d40110b415912081c001400468140308000070784225 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 463645458 1250 463644208 463644211
    0x1401050d021921061503080702131d0d02060a050609130602090402030c1206030106061d030f16050111060403050403080a0302280e010302070c15210b0108091c08 71
    0x102c01c4141491500c0c0c0301c080100b0b4804548400404020304001801c102451080c44500d8410900798000f550031a0f8409511b84a10080684600000f1081d0501c0e40c0c055031040740690440003008004000000c100c40e100d600010400002d03000303140002d80c610380c0b2409654420400181200f0003961503051055085900140036034829500b4092100e05403581c0c40114051031074611147c2c0c8400c0d01c0b402d403608081d0000d004501070390400c201000425048010040325115040c030800d804204100860f02e80064190b000c041403156940414040061010390401e0300c4080c2d03522102000c42e041d656075154016940100018010001003010400f12006016070035261700d00589420f0110020485211524800c00c14410803d4030010400ea003009000e0140c110a090075400c0060703a4644510f0310515114104049211410000c50b8500c1240f0342c100f1001514513441c1c0c01c1c0c012000041c02050081c541d14049007078080441c0312100000340407a9101c400708416080701703426140490381d1500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 463646708 1250 463645458 463645489
    0x14180a020f090c1b070e160e01050c10110c010c0906020a0213091202151315020906040b07080c010b0105190c14010e030904060902040501020d0e150705010c031401050d02 75
    0x502280c0580540c50340040350003a56800101174080c10410625900304020f040c80d02c840b0100303981d4100c000d401885800c11802d0034242035031584070008605060000c0b00241d981200c1c504aa034030041061303103014003141c65024000f081580012078040c0c0e07082c0058000c15001d80d20010f203200c01840c0c100112203121045182c0403070490788a41c0c68101c600d044000e0500543c019400d494140740712603070200d034030505006048168180e10b40701c034220000c0d82480c044940380c00060300c0b00075441d0f840844c0c004000b4000750594a6009040483c410340129240750050b5082500c4480030350303c2601a168400f8000b00d01e804c10110300c120075a4121032418003205c1c07040440c1540041101c00b0310400102151140217550b403210a5030400048a00d10780000841a10600c828040780e6400103080701d4410740d030f0038550b085a50110016515011301d1281140610002850108000064000c04200902514240105490110080c02c006002d005641d00040d890003040d000d454a40b1010f141c911 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 463647958 1250 463646708 463646731
    0x5071517150d051b091603050c091009060806030a0201050d0e07090e01090614010305151f09060e07030501151d0607060605030709020403080d0c050d14180a020f09 72
    0x290020100d688066803200983d40d0b50402021900b54410034410180305580807a6200681c6c41c00c1c10b141d1100505050080c01090b0307940e40080c08517542d40d41160f00c040c10050210f0b2890304c0c803210082510310140103210000c1e880d40d020404505000551846250307058582c01d0074401030300392a0000300ba0182c1c180015100311140001c012449101f041c0c0b13801c145d9800450310711440c2c1010070a64486071a40044500e4450041000c12004605118801091a14070200f501d03000c04c0245001440300300d07104d40004541000a01d188558050011144040544051585e4480042d0200c030b4091145c21901185015a5201d0034815610301d0400308080e030403091001c5890012402c0c80c2c001010850ba2156110414031207032504010740030007040032440c00d5240c41c0c25a5142d603214000c41a0200300d4035100c1075401106405041a208102e00b8904200b1051003422015508110306403070003040607502084410070745c0008034100e000560043c0900380070401180038001c0c0c0b544010540e81101f03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 463649208 1250 463647958 463647991
    0x10501180b190e01140123090102160f0905070e0123040e04050a11190618090c12050108160e0c0c0303040f0b0c09030c22060e010305071517 62
    0x148100450700081c001c0541e000d00c01d50f040c501c8410b851603003012503505014100156441c4502c03559504c00c00100c1003407c064448080b9001030746815902c0305a0241840814000b00301d2441000038001207483c1d40c042808135403a86501900d11610030f0000c1400222284401c202c00c4180040c01d0010032501c1118524056458046021424042d00c0c03c039505d400c070b444036078140540710450120211044900020020104804010f0f00800344074000c20300401a07924a540c04d00c4c01400802444d2080003800a0b00030f9004c01464028901c00140c9040e241200100b40e6640001300d400300c1d618800e8207800a42d0030f000b100585c00320024180c1000b0f0108100d00d03101c410003400034500881c81200c004540100031320700501804c0c4003c000410030784050168090b00d5400290f030021810342034844040d4052035890124070401d170f41c00c02c2c156203030a007a0001115482c00c010300303049a02400c00d440341c10341c4035432841980843c0e211110000a41884c9035011000f0b080c0b881580101c82542403000a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 463650458 1250 463649208 463649239
    0x140915130801060f0806060607061a09040605060301110301080a06020c0a020d0b1b070c030f03020a02042417070b13051003060603151a130e010308040611010501180b 73
    0x140c0c50a40200c0407594407240100b242001044a1070b000e4001c8030301606141c600b030700120301c880c010044060151030721340e10302e640c150002c1c94450b0707540301c0702505a030387c1c501e024284034010342016103480c0e010b0347c40c0c100208030032000030096074140c0741e504024150307501907512024069040050803c6a6014000103603005030348504408621520a02020420380740400d2209000f81d408100c0d900040404c11840c0d0004e5a040c0010064981c0b11020b00c04118050808038a04501a01d000b508545465000660003061030550323101c03516804c4c100005151180444030100001d8034498a2990101c2d03400c3c0a040400009000507080f000d80c404100c0d50b4506c0000c00c12104950003401080d0351340780a200c8181c1c503004048080402001c400d8a292a20310700030b514003050b105031800228003283c2a2903090b00c1d08400d5000b4201d07035220603c256141d00b070103602da40c05440313082e000c202d040070710f0080d100701806000d049809101c02103117a000b152991001511060f041310f94007448580301c0404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 463651708 1250 463650458 463650487
    0x60b03070f030c08010203060a030303020d020904051801060b090f0405041403030a140903120109050a06080f0c10170408030c0c060f0601020d09030f0206160c0603090203010606140915 81
    0x240401d00101d070145140d42082c1c800c201d156042501c80364010402c01010381c0f5000c0080b01181da061800503542c94120748000300902510003655807150900c0180301c180c403800c04042c50b0351100000208131031990b5046040e1180709038004a50440040780c4620400c2c030b841d500082d032081c0102c1102d02440702c003211041c10341c1d10072268521007580e00c0d030b090700c201441c0400e840c0e40501020000c6140901141c08101100c0052040300741c0141c4500000f1003606203500403c0c000c1c8412000c4401c082c4914010503220407490040d940204603604a1046592084a01c108500201000400242c540781c0b02e503c0c0613070000b04035a8045808110345c0611300c5040044500c01c001e41c0c410050242800030009050410700d4030f800c0d040046002c0d080c4003050000d000e2500e62030b070450f040c941e110510808201c4a01c0d104001414040c0d681a0005080350103402504030240300728001c004c600d8451509a401c0d00004504154840c828440555542081c4a84820712010542d98032b090a680307600200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 463652958 1250 463651708 463651723
    0x20303070803010f060804050a0b07020c13061e150e0f33191206030b07020d1107140108191107050618120706090c060e030c09070807030207060b03 65
    0x81d4081000401005845021441d82d03015060303615101d0024101916a55500c12013088081c00c0c0000c9000405e103d00d00801c807a20b005480601020003010b80e100710078000f03025034482c48072a9503000a010750751044281081050b070b2000c100307100f0304040c203100407525420420001900603444818403041952026083d585254210b225114201c018203805008903100300e8081c00740c00814088248000107603208043c0700209860550b42c040b0358051000c014140b0360303102910031189a000d002040d03030701280300e0400d0505515078094411000000c960b981000b80b09080c601064040c3d000c1c1150300c508e60725038020302030b00150620f41101c5075020088400802035003c12040002d014030420005000496101501c00030b92440b100f007040d42c0c15110206112110031507140002c0940c204071207a40000c01041e0007460038810709489a00160124000006040c800d1140c0080c0b4030891421a0015100340d1060741e94820603200c854055020f90400b54003106e81d0764607207203001a2600c0412981 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 463654208 1250 463652958 463652963
    0x206031302010e1801060323070519171501050714100c05040e01060f12140106140c0c090603010908070506040b09060c04050907090b0c1b01090501090512070302030307 74
    0x30350354051074800541481c804078451400741c0005070044416003040780c030345411501c0b5070502162900c1c3e05501295054041250a03032a202c10b4800d00ca10150b00070007500c0c0c146c84608400c0c040d042070081c266a0242c010b17140728014040180064018030551f800200d1010060419500b49080d075541c030f0542410444100312190b2210b0303000200c0c41e0381ca0140c5144040c0c6400c0039450182040303055036221105000340000d002c0c0e04840c0c004018450600d150b805844200b00304100784031101e505074030360001c2c8220000600d998441e0038290104004560300b000c0158018407981c60381d00148028035000405280d8136558070040740d0040344a0000070300941e4847c0780a40303064501450440540800507103000010740c000404c000d4103110003012101552400c0340c0700b101996600d0421a881203013030300000c403100004211102c02450014404d0303188414150300d604648050801110080c510780318003400101854000c200703c0c1801ca010381c008a00c66800d40308441d4a81d004a455a80a541c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 463655458 1250 463654208 463654231
    0x120c041e0e1f181a060906120408070b07030b100809030901080c0910080a0e0c03060c090303190804060509120a030917040e01030b090303040b060910080706033321020603 75
    0x1842d130000c114162101001030101c80751414207290f04003040e903c4c042c06100702202007012005c20103009091050f95074041d03100003988400e182c4500018040c1144148460044029070159580300e40a40c110b10703c0b03014100b000b5801e16900c1c1c1d0044800e04400381802806420420074541381d9142e840c840840400d0340d45400a80703041089200049895014402e10181c0192601840e10764020407044d810200c00c580607030300e510078940020308611405030501c0c01200080b250031001038200000c68400d500500d0300304030582d600b090b42c98640f6042c0300400a40c0e00e0402000d8001c50081d0300040c4d1050180c0246004503a000143c18843d9002c1d0304010a5083c0e00001001002400b0f02815844940e1a0240d070a50800703039940e8040080240403d0711545611000448100d9041c00c4c4000030454041101e003026079840000d4001c1c0b10000d07a4079500f109045440009800152180c910b051918543d03260482c5803003041c80003c400c110004082d10781010601d070141c1e40308030255004902041f403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 463656708 1250 463655458 463655471
    0xd0606020d120c1e021e0f061306140103320c010c03231909030510020f0d0f020c0c010e09131a0a0209040e16030611120c041e0e1f18 59
    0x40c2d0b0300f441404e0940300c00c5d481f62100c000d21000c04217151740c1103000d03101010f02c403900e0b504d040009891019084401c6860060000090141d03014044021000001c8d8901c0301244603040400c03603052100c40c124180c1e20002000001e07504c2042802407583c060315002016400600404070008811940c6c1741060714045403100f0002c08a4003100c40b0221241844840d00e442c60381c800341c440d04009158030100d035000c15050140c0d031842c012120755240c40d610400c51030161079200030003134128000c1a1618420400f10040b654010201c01c1e134070180c0100500c40568581c00c0741e04661903602e804651460000c40c02c00c0c0c0d00c282d4200382c1400341d111240d015031142620300c1844201e0b0464000d20001e80e02c000c54010340031a003012148103403034200390301240039035926100410340e1050860703016401c2006410032845007841c0c4090804e03500c1031280110509030707084034640d840c180c500a00c90124402030126011480640002055080c0d00c2c0c00e2a40440e0340e205117101c0d941c01ca031103100c945600ca14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 463657958 1250 463656708 463656733
    0x5150f010e040624080103030e0d150507020a030306080102040b07060b031509030702030607031e1d030f04030b060904051f18050f01060b04080c010c260d0606020d120c1e02 76
    0x13031460154400914010050703615603100200b0070316401216038081d1a0600519050008118052920617046101440a820704260003599100d80034030960000f03141240c046a41c41c2e040c003c460480b07070340409070703810140103031140001007d51064440d4075214050300004080c5030004214414032110000d5038580740280185030801400408440c1054504500340401c7c0c2c042e483c00c494210701e00b00001505e6001c100340c0301c0d094001c0c04650303400c41c400420081c16030802e0038014400e0f24410385103541c150b11f860003807111150b0161130040554200c40d40b01f80b84004102c074111904041010040780c0ca103080c4006207565104000103503403a4101109810f40403800340610001013816200d400d207414a810307400c0340c588201c0c403001410010170500c85c03014440c203480303144001120392415282802901c400b00303030300d0361148103540c04050901030000b46450002c01c02d90400c442c180c88820350080a01d40e0040244088071000003800f9400445881942d9901d070072042c903e0036a00100036000380107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 463659208 1250 463657958 463658009
    0x9210304140a0b160f022a04182001050a0c0b041406010807030203120903192d110307030201050910020c150a020d0203130312020a05010f050108070f0f03080c07092a0305150f010e0406 81
    0x50072b080c0d043c000200105a007040d80100c40e01c8103075030810030390341c090744035450f00038110611400d02c3e000d248038403030010652008c04030b12507080380d100301c0c11078001d1041c0c01c0044180e401840105641608000708141d100ca008903d19a0950700c911240810410407607226102d0510180d82d03d1004055070806404200a003541d40d80b280a0840007403800c1031850340000d099105482886000300403030b4008010046c0208861032011400410840180000c20716080181d0441d08010005110300c400c2206101d0010044070307900080004140303502810341e100c0440040e0120b00b6081188035001c010404158223120b01c0c0010f02501401180b55450654540d291501c6e80d0031261201102c2d1400b00f04003205c02007180210380e80140715644801848507803504190480c0e00070320b003003401c02d00110840018021a10780204000740303204903c501c1c680d01201140d000f11585400401142038038030700f601d003c85440784480b40514110340e030145602d0105007916455889280c0b2020500b1802c100d06c40d59 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 463660458 1250 463659208 463659263
    0x2303040318080c0306060402090d0c15141206041a06130302030706090509060405091906020715050103201909020309210304140a0b160f022a0418 64
    0x1070000400e00c03d80d80c00f000a4035000081c2c0f040b8403172580091800d14036140c0030b512040003034002d00304144065031074901c401d40d025400c83d907030002100e01098446110503101600c0b5450403112480340325980b1a03003400700030802d03144940072004808016040640d5103000410510140802d0001390b207142d0b20601d840c102c62500315500703000b03071050309009988807000d10b140c1c06101264086010b40354100c0060410b038880c3c00305d101a4403e04400420700000381c00814825100d9134561448218024000046803002c0c000108014920741328041c02c08505c0800591461004090010f0301e41c200b031800d0001403450740000314107074011081040c000300078400004001101196400e0030074803178094490350b120041c0004c0004651100842e003c0030108100144190b20140c00030081c10f010811480196100864100003903203e402e0b801020302c085204240b494259881e61088903040b00d810381000101c18495070450b43e5039001d91242e0000c020702c1c0e00c2c01800340c0c0f442c0b0300c094180c81607803542008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 463661708 1250 463660458 463660469
    0x30209100807050d1e0e030a17060a05040f0f050709140402130e0711030f12060a0501080a0c2c0a06050c0712021908071e0f062303040318 61
    0x500c404000d00c0d41d030054211031884500400c001441e804a040e2500c81218034107003545c0040c80c0403101c50104200000401002c80c3c162244c01042c152880b00c52240103089542e82c0c3c005007062010003036800c00350410548210702c1c107404103c1d500056115403c482c0100c0706c4500085042404104e45c0c0803080141d040507400f42c606504d00042d410b0b4502000d8414070403404855a54400150403a00c01c2003100b0081e1a144e040e00e6131117644842884940c0c00420101542001c03110100d0182e18229170b00c6d4088413010b13158040ac588c0c60401c42e4006002c1d0340c2184040c054403a07495507003a40350542c040510554240f0b00c0320100601000c1c0f044a480340c0d007051f02480420440c0848445001507400120340701c007001e041c5560000d00c08030310b0440800004060419001e2008501c642e4080342c01c500303540042c18402288440240c00100107200f600c119861940e40f201c0c1444203921500001f042a42000c00540c100319a00340c1e1601c070b545c42103a043d0005000c0c21106180b0503401c42e0b502d0000c0c034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 463662958 1250 463661708 463661717
    0x15100f0605040515071407061707030506030607110106030b0a0c080601050f041e1809050606030102210903090604032d0506060f132f07030807050c160603020910 71
    0x3814880480d41c4d003604d0300080a0b140c0e4010501d00104200039016220491002c0c1c04e03124229a100c0c1c02a2203002c03100d8500e000802842e000452941c0319119252181d9001001020103072924441520005d0a10188200c15521410088040b44115111500403001307800001040141341d00020301c013030005841c0b1810800100b00c2c001d00d00242c0c1c0b09503000e6030650100c50451105d81092010384400c1030384982d80d482607803410b02407140c1d003c1c3d0100304054024000d454042c0c5da014105400c07403203115907064416440c218050340900318038010390b500c901d03c102101c2c81c0411145c0024001d400c0791740200d400840e003601c0303803c00b02412150360f038150641208000c11400e041d900c0300e450b080c00422090080040d030143d081a5500e4a10300e6080d0300b000c88040020001502041e100d00402a0200e0f050030803c0e49041504030340c03001141d805507055614035406480e0300d90304840d41d901c0041080c64600ca4100350380c0f042d800036401c02e0018050364500585d281f08442c00e00500080c81e407042003e00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 463664208 1250 463662958 463662967
    0xc04231c03090e10171b010e061204020d051c030b0109061205070c0204060f05010207050f0d020d2a1d0c031303050d0222080609070501030c0215100f0605 68
    0xa4210340c070381007610f03595502000a540c40c085124203141442d4000040030355a840d40702d030b11000c0800e0b4890032411001205903845074210054070500460001550040300800c150808510301400081e0480e1000f080158030716129100c003880d00401c1102c188070444e00390f48102083e40c141c07042051040b402c4c05c000660301d203088030180c091540680381030303c510380300c3c1c00190072640301c0c3d0410b050322503008204003c2ca0b80c40c0c11020040e018280a45c9000d03101d8180042102d2410a10b10301104c00001d0040c00d03001120303800c0c4030b00c0d0440103000301d070030030070b0240040c0d0004040024141c600507030707a10a61005160491082d1000010b8940d40c0301c0312210350074070030703403031942c8017103da1000c00800490f0100000d4982150640302e00801c09401903c0070910801c082e401005031b8807101082d40714842c1181c1c651038200d03101d1400340c03040a216400407a08201c0e82d4026005140344950900544403d2148050003181e0390b07104440201414016400c02e100c200e01141e107401c0039000380e18189080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 463665458 1250 463664208 463664213
    0x60501080708060103090f080a0e030303040c05040c1209150c03021306140d06030b15010f02031210180605011b020d11210f07120201050307080c04231c 67
    0x10350007411180800292000150050b40250040d00240740c0c0403885034110f0205080c02a1071b0317003001e07112100084d0f2120188100386000010342e40941d80003105a02c03d503140c541040000d20011030000140140313030345220504c0700e451207500155409007084001304001242008201c900003030a5106140c03045c091707194000c12101018040d02c40c2400d22001c4104080c0303030803400c0d000d040504440c25050000110400c100340ca905070250606e24504c4400f042c10b00300550300044016080e400603401402440e50b10580342d1042604a8201e20b404e44600d601d0b82960811400d0001c2403400507074494800f0003465a1200050850f0054131501d0003030030010b5800182045202080500b180d078901c404c800a5076941e04082c00b1400780110b01d020000039003004503440b41407110518060340a43d40002511001440101103a40c1c0c1c165900c604d0741d51140701c02da546034006480c02d0080b000034040403c5c80c1035030000641d1000109800d00045400c142e00b0003450158401a402e691000f03210181c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 463666708 1250 463665458 463665467
    0x61409010b120601031107061b020f0607050d02040f030303020c0d091d0a0e070f0602060703021201050d0303090204050c07110a0308040509250504051008190e0a02130519060501 78
    0x81c682942d40200201ea190440120b000c1c0c0001d04145508100c0040c1004c00c0210960244240940c1401448000b0300209820390312a05900c1800409402c0000021507051203580200040001d0342401820191030f4000c000d8004026003048001c030381d00188064070620100000c454440c0d09144c18244c050a1601071400d210000410079404168080821364202590b00f02e01c040740f00800807654111390364007040031820741c2ea21804d00503000724800300f99020302c07030f000301c800c40050240210300d283d182c84188442e1111003001502050b40e19100c88005036141c2c001d803030085207006041900c510860130318408211400c1501881843c03404002c200040f406400c1c2d070200c0d032040701c840724503130707200c0240882084541c000d030700110084c8080f4080d21604280a03100795013096030f84500c42a9010020b071402070b000e4804072900c0100c4000d42c80c040c499030300005120341c0b01e10300b510428061a0f0100d607039401c0d00c44c1044522a150410400f03030214080c403110940207501401e005c07551070100041c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 463667958 1250 463666708 463666717
    0x60629040501051318050f0906040803010e070c1a070e031b0f120109150b191503020c06092b0806061b0f0606091515130b040801061409010b 62
    0xd0600002044166448050304013070b42c01440010030001ca5264045602001004200d400d01d208491a40200f6103101001501c240b1440c0d1054640f8616400d00640d000f0002000b070040080040c00100980021050f218103103100c100004d483c001400c19480141074080f11141541c020f030700481640703115600d10001c401b415601611441d00803020580451070700b01d80003a440e5099070030000b0000400c40c015080074014918580104807606c00a802c2141381154116080b039541e40001e070612920341074101502005c81c0c2c0e4100146424020031120b810310b00100e4001c00345401c580842c034050f80084181705584100c00c00c10b092005151100074040d4840039100f18040c02c40070906c0c0704102c12040c00503032603a02107400c40305003003900c01e8201c0d900d141c1202d07501c0c05100c240c00480c420803554a0004640c2c1c00082c00c01146200045c8450601e401014482c1402c802401c0e00081c1c058078a002000506040000415003504050103210960403041c2054001c0c5e00c460010851500041d06a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 463669064 1106 463667958 463667969
    0xf0212090d021002010e0a0606080c0603010f1202060d0f02071119030201050715050112050714090109020a0c0501020a030e07080a05060613061206062904 68
    0x41405000d04240541c10002079001c003401480e10388460410030415200001c1c3d0071240e803049602d0039030011810756034503a0b2078809112020007440161484a03083c0e07140b510715403500d040380d10320803901d100700d02e80c01036801e00403405c6540d1076080310001c041c020000c0c4a40250585000b000f9800700350101c4050300201d00c0c0e45018140320b041e0907100c019514001601c1031650700190350560241d001142d40008802c425082c0584902c6882c0c0a0841c2a44080801106113041840c002023500b005101780301808840001c0d546100705281502d242000150302d8400c105815150072010800c020225400400c500d6503165050744584a01680790307048560b61541d40e0001510b9540707030030004d0095002200040c0590502002c60080512034540000324103584481d0f030000c40e0240c0740111581c580318101000300d8258655582601d21600d044e42c80e20f40640104031299124520a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 463489208 463669064 := by
  have h0 := BRFrame.cov_init 463489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 463489208 ≤ n) (h2 : n < 463669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
