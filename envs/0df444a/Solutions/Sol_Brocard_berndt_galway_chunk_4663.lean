-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4663
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:28.697976+00:00
-- url     : https://prove2.me/submissions/77f736cb-1be6-422f-86bf-6272a662d590

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 838489208 ≤ n < 838669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 838490458 1250 838489208 838489217
    0x7050a0603150b0705010b04060603020a090b0a0e0915040507081003080d09140a170c060f0a11040e0105010807031a0d06020c030a0503190e1002130e090619050106 72
    0x42002900035000a029401094004102c1d180d0307402194080340d000031012603040c7d6584140c00c5080c85c10707104580c0035105901d000c5003040311450028100c41813500599120083c0071602e00205881040c035440e00d40780242242c05142031006101a81507264a6203621131814140041c05040c03117406c815108991102d882c4000c0c900e151a42e2240f54041000242d0680e1181c0401022030402e100000d60385c809580106410f0300b4500740140e10025010300100d001d4004c0040407001c2d03000050154204880b03400a8940782c88401840c4d005103d800c15401c44c080003c00e0008244181c015800d0486500307807241d81e6250b0320828120120f400303503000b43c07406525803500031a41c1d01b030030340c80d00b10028460a401842c08011010807842c54201c92034940003d280002005121401a00010342e403060f800d5082c04401c034000601f684810300000134240e081d902055089074a45a0714a074401400354150546450900081d0720f0348600c000c0f620088416140841150b20085520400d4101c4145548 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 838491708 1250 838490458 838490479
    0x10e060304030c0c0308070302030c0f0f0c01030f02090406080714010201180f0201022a01140a0804023303011707151808030d0e1504050622050f16080705 68
    0x3000e0ba10b103410402c090342c0342d139100c2c1d4000c40010300160052004601980041d9115861200058500000034120781d4040e0044150510800c02c00210309031248000d00300400c122010a0003d0000d0084008050340b0600f401c50004826a0100c2c4840903500070005200000d4001c00c01a803c0e83d40c0800c0000c107041041c43c3e490f0103d291040314518452052054403c1c41c4070400540350050107803103004000300c00c0c10f411096190f03001100f81d9101240400c91a007815a08031001d080c0d41402000603018140c0c0004418810400000a08500d40f80b9518400009000380300d484080c4c0003401940301340b02c1d520f407200314111000100c45c000c884941e9400100041220350403a1402900030861313076800c00e64080400e4103241070024040584072064000b680d0008030b0344003842c00403600002e81160346020244404140c0c0410030540c04074022802100e03a0b10b0014040061502409001e0240e00030352942e05100310000c500c3c035125003200800e0200702d94650b5200c5440b404a841482d40c0002001c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 838492958 1250 838491708 838491713
    0xc140112020a030b0907030c1106090303070e0a030501021206090c2d1b01051f0612020a050c1510080102040506030406050a02070f050c010801090b0120120409050114010e060304 78
    0x800601500c0e0300c03450f000c6110300b03003000814003400c42618020080b17901c609290f0180ba41c0301c3e000e00720500c1031300018101401c004082a407680b00142102042015520f1800100d80340c0408a00c002c59011008550300c0340701c040344041c8120103640c458480c01c8100003180004401c01e061b201042070403003440d0203004020418091a076500e00c10180c00e82d40900900c400004090710030f80a546580d00041100d2800d54680c10f140d6520030380c140e03d410a610024050654002c0020f2078001c003035900140d6a029894003075610b4014559808814400e0701c00203000c40c0c41400440f8019078202400d556850303200c1d0030460a03405980551900441d05000141c046082c9802040d0000604100180762604a448504102480c80400d8803141d201412542e0300b5640708911500401d400c4200f00807554903d00020301d807088004100342600c0310344040030302c880000c0c4204a49501c40403801c0c0d660741d56074000e00c2d001c0c0000344580080c07001440c0c3d600d08030b54000c1c6a861000c4000600d107514603603407035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 838494208 1250 838492958 838492961
    0xe0712090203190f0512030f150a0b040312020106051c1704080d08011401030227031005130213060303020601030318030b040807051b0307090c02030f040603090c140112 74
    0x300d4059a1501c54000c4045144140a01540700d0320700070700d101c1d0118401420070a04e030440c052411090000108100101c0c0380c0d0301d40c0c2d0030b90400c80c2040103183c407855040009129411980152132040000076000040010254160500c14001e800a00503265500c00b00014002c164070007500880d09600c070b61002500417401940034021001c1590309090b214000346140c10032000090011036440401403080c04081a06120095800d207402d6203002045080700d00c1d0752502085401e5440c0c13003000705002c1c5640c1401650140742000c2020065441d01c42000f00120360760007816400f510030044051150109801024140da4040c5c00030441f0303134030707555046a19120340a5246603401001a011000864201d450780c0034500440400d51510a0341c1001c81c2480e54641d07040d03040000130000c501c2141c402040f413500703e03405072000241034644140b059007141300f9000103065802000602041e42070305607002980043c0904850300909032641c0c611100b9414010b42180441c0301003031071112860ba076 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 838495458 1250 838494208 838494221
    0x307030e0708030c01061d1302010f17070e1002060426070605090c0f040b01200a050613051c0c081806071a090d0507020f0f030601080304030303060e0712 68
    0x801088840d5282d0302c0340228155003100080d440720380d45400702000200c1c0b43d242244030803805101107030302c0c500b8998203e4030030000d0800c0c000d041c880070300c070119406409401070703044080d40c1a81005151511420046c04040303030446140c4a002c4107804105130520008450b8801da5001d000012500c9402c02402a0001030160b4201040020803100002079414010310380602ea20000801902c0300347d0f0104911801c60b00141405075107410b009240587e4002e110710b044000f0b01c000c0d0450300c1d000700d400310b050800041020b041c0c0d10480c3c0c280b0407a11200103800f2a154010001c0c0d03042d400100c41840c000010aa060380001100348a030400402e0303940c401054005403002440d24140359003000300d101500060010303200802126200d440703807084c0c0001c0b940d01c021030740e01800994904102c080c015004120010f40100a001d030000c0c03d40c2c445031030310000214000c0444040e580e5a0000e141c1c2c940c4180800c50000b800e0050018180606210b4240078410544802409402c0c201415005018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 838496708 1250 838495458 838495481
    0x10908180607051f05070f02060609061f210b0d03050c1606030509100b0d080313021c050106050a0b09040c020c0411070c0b0708070b04030311030c0702101103030703 73
    0x1c10009100002c82c1088604404d0302c0b0803411510b010005542070b011618005c0900f42444400010311200c0e039030100704075601080c2101d8100064842201240c202481070b6840d90341c00c1d50506507880703101d0700100d0080c0044034120000a5075002c9100d060181c410b8903001c03e800c50303080c40340c050020f40100d01034143e012100044803d003200090016084224603070100e00440e80e11803d10019400c00c0c802d14a074408404014444150342c040842d15032602d41e03201601035100480400d699049910350400219001002050302158446c1c0c5554484a02e0b80100e5071586011800203650500a02c00c00c02c8624080f02c1d1801c1a01ca8800d01014007081d00e50007085010701e60740c202c03081e0390780c3c4105242c108842211507200c080d00e1402c0110020075811004070804144452000210b00f001200c04203a448800c40c030f06500c0754030b02940541502d4080900c0e44e00f010041101c0a05640b0141801074001c503015030101c40c03204000d8649071286400b014450300300300300185900c0e00a4010318030100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 838497958 1250 838496708 838496719
    0xf12080a051b061008060f01180902030c0607030e090f1018150b0d140112060b01170106120b04050f0c2110080616020703030e1512040b010801090818 66
    0x1c2a52510743c20500d04540342c030780042035043c0074441d081c41042903e511a41d038a0f600d52a6504200080400820b030f0880c01d22031549400300107046403002d00920703108440140c40c0e02d03103503030142c680604101f013000c200c64041d11038800060f040c00c9510088601514114860580ca6401c1180040300c2d1100c5558400b480c0b603ea4801c040c000d22001400e0006003241c10843c0d461301c09000b0000107480844c14a07141e0300520b9001400307001c0c85902500c421a40c41440019034500c9034005840c090980c105041c0d40e6503000000259080c1c20407040c00c0d2800d00034030200b004512a00c20801143c4041e01c0402c50880703800000f43d82d040343c0c0c10090030302194004400050314040520303e9108034003101c076088542d48441b03080248000407c4290381000301380510b40d10445043c0d0000f076132404940700103020420b141d031456440e600e4001250301c00b200000078075980d85801c2201707041d1008003a242280c101d040d030800002c2100e010f03c02c82d4103490340040134500d486d1006103210360b00a007620303000f503114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 838499208 1250 838497958 838497997
    0xc0e0a080d18030305030a0c03230402010806030d020c120a08040906090b040507021e0c062803110d091a010b19091a030a140f04060c020c090703020307020c190f12080a05 75
    0x380103401851031052085050ac203030307260510004060402c040d00c0140207a20840c0c402c1901c50300412080c2d40b02c2029280c01e4101c1c0d00a000c45071901c0030b09240640491000034012a15400340d4020304141c40300800280016119401440200d4004441c03040042c0c00070301d451684051540a40c03601c1000350000c803a1003441d0000042c0440e44a024010b1203442d40c104d03810246034400e020b0048041c1c460a04102c00f0010400d05201c51150700300c83e0340540e61f01c4034508108101d8035250b90115507500c0e8088810340e1203451900c602d5008901030542c01080601616140f44205103500544101c00c1d4141011420034044911540000d4025402c05131038010341006030a1200016103d20041c00840c070312810709080c118101d4042144820441d00130303080304442d6440311010284c02c034903140b500580e241c0c1d07060307022410406000300c4260b10100b00b902c44503942d803113030329928180d5411010903d21280d48001c00702d442481010000c4c8030940c00d00c4444050342c0100040e007102d03030400d11a42c0e60b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 838500458 1250 838499208 838499231
    0x50a0308031f080d051c09020607021314100305060f072003070602070303060e1501020606131404060219020a1a0705160b0a0605010806130c0e0a080d18030305030a0c03 74
    0x50080e40c40f06100000d00c08240e4001040c601c01b034080c0d8844028501f0031800d00340b90040f40c218031446401a00581d202c08148080d240c1e19403001b03000e113441d5a0144014200723483c2c02c031401d03032003444180c0b60343c422600841d03802e10007082c20318058285a21907040c0758a220b03500c0710742c0c1d403030301d90003400c15000070b018440c003042090004201c22072081d500016014200a40140010406000007924065859801c44103980014144d034001c40c04540002e562106010000040c1280c071252803500011001031008101c0207401500a11040c481110b400d44404802260b071524107038405042c154600c41c10b22145150b0082e07160700081c8a1074041d00e011801d00245400c0540c50004450b8111070404101c003955052141c10302502c024139042041d424041d0006845d03403080d6070100c0761070340c1c0d503a000480b4901132150400c0388074028111811956640b4003071038031303403020b15000008904082800d82c001d1101d2261070054039450703102c0c103056448000208c40106072204852083c50750750002401c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 838501708 1250 838500458 838500463
    0x1e0603070810150605070507060302070c050607060b0f0d0c121e0309030204050606030103030c0212011805030702030d1407030305070c30030e190213021b0601050a0308031f08 77
    0x2c15100e840c0003040400b0a802c0841200c8502e5000c901002010b12007071001a4022032040101c0b1400e240141c0c0301c00050511072112250780d404079074000c00c000f55450402410340c0003641280811151900d00b0004a000c3c003483e04100c500050001245107014403042c801c90846400c028025144000051000a4080c00c00030a4601c1500460410101001145850b0284a900080645440d1b042d940341d0382c0c001d0201c1100d150f0091260075060654921243c003503025802c580001601104a030f0054200f841e200c2c1c1c07108001341e0090150385090358005002e90380000314070009409061800d40143c40031001004054044010045403207003034000b0940086e0024240c080e0a803a141e4022064103000e0250600061710b00c05042c1811600c2d0000c28000c61211a501c0707880803100703c450704510000342d4202c0d607500700d42d15061000c1030845244070303400916070030889000704942ca580d032240c003008030005052000400f0403078208001041a14030318042c00002030050700503400789403105600c90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 838502958 1250 838501708 838501723
    0x3040804030f0b191125020a1412070605071211060a1a0f1e06040e090f0d020c060405121507020d02071e15050f03090604030f05031e06030708 63
    0x240c101c1e03c0202032000b82c80290401d45480d040c81038040000030352403000020300340102d841103035142e03040b4000e407070101c40780d0360002d03c070250300620841c51141c68012480d4a0005007a8460091926981080340300703000042000079506191203c80c202070702d40c0d80d181c0b07841072100e0700482003001d00714042030400745c2004040c1c000d01d00701201261104121200c10658441a0b0f41188030300d0421001c0c80306503c40300001c00c80700d0300300d008465100001e18042001c0c0d00c100c0e40082c3d0f8064640d82044140d410125202d81c44075010001c1c3c1d8902c1c003103100300f00d035075440202d20503500002c01c120400891414000c9194089508000d031040400c03c0e421604044000f1a41c08015802c40b409095816505000340c0380501000c0008a80c0031861800c4450701c07800364001c01c2d80301c6106021038a45280251305444030051813401980d030f02c1c54020629a111101520100d001c01d0780c01e091070203214058000d0764841c420000621201c6108140101400103016002c035405001d10400851011428080d41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 838504208 1250 838502958 838502963
    0x40e1002070308041101020d0c061508060405010614010f1b060f092d0b04121110020a022415010e120a050706090e16051209011a09091203040804030f 66
    0xc1c0a4909800c1c9070b40c1c00b902210f40d1750304542102151440054002034103210b0070740c0000b40003800081d0011000143c0c041c6030004016881100200003c00005401507020354010f600f00010081c070030030041d00c9000d8680154808500c503407014001503441d0648002e80d80b03000d802c001c40c10b440240c4a1030200c9056240980310220000010a40d02180048000100100014000a000d06030b00e0341d1651000c040e200805020451140c5144584209a080325240030340060711100d1207002c420350029404a0b00180150041c210008040c01c81c00662100b420030b0940400c80303d559940d10b484201100b16415410b000c61181c0d100c410352545440d80c10814100c4004100050366820540c0c505191907121904004040005204441803010b00c42d412558007407400c0001c142000d01510346000789603019101820140811103641d038150014076981100c402c00d04440c240000074041c411004030755192440c2d02107420509140c0300507000b035500c1070081c48041d050540325a1180b00400341548203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 838505458 1250 838504208 838504217
    0x209040317090c03030d05131a010f0b0406050702010c0501110301080307020301060503030a0c0b250509131a0d03031503050607020607050703090605210702061501021506040e10020703 81
    0x108021180c000d080c1d500002e01d50014400382200e1000282d4a219aa980310980c94482c004503110b1107100d014405c0303003680410070b1100640c0442c0f907809060030911910b4580100140006000000c02c0204c2d03060f200181c0d1010710740141a001512504180502120b2540d0703100000091200070f08003850180411502450352081e5500415095801c075070005d80c401e40007001500d0806801c008210101d5074880d1242003555076129017084805402110560f4800d16070303451040f50f0b81d101004083e0000308484041e00701040c0010300003203d02001500c66110600d9004401c1c40c608042c602410302e200c3d241c081803100c1c070907680e400b501e03506034801c83c0c41d076000c0000d100e4001e406210315a4000b48070b151190510820b0345004143c2480c07032040c0400c2c4035001890107103282964819144030400158030304004d0801c40c2c03000396259411210101ca4642042d054446588007040741b107a5542c07100b1446040d51519010040240544080c1e2600381c41460103403100d00300c00340042c010207802508c0c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 838506708 1250 838505458 838505477
    0x2010b010314010b090d0807080c0607031b0215100504060305030327100f0e010c18050402074803030311160f020102101a0312041a0a0201060302090403 67
    0x94150ba20900034500805442001440b68000603000d499440504485c00a69030440741404003141c03041c0300010b880b0b140c0009281c20b1290000890f103000f01100c2e9400c01520030070003520b104442c1b02c6005400141c000050280800f100d01d80c009820031090001c0b03c444d580d0301c3c0000b4084a84a91040320302d038002008228082c80344401c0040d20140c0030071040750301300040001c01d0300c0c1c031100200c88455568582c0b01e6007400c10b8507031021200840c010000c012a144070380d00506606a04115401d144940400104042c1010300030b17036410b1030b130101e050007032800e915032a401e030300000d0714010103000081000905e011030307410004410305000342d080d411010305605004094940180c0b04052910b820446030409560700a0001502c40d08129002c00011132072004034200b840c0920f2a011450401b81120b03225840707554030042d038100c201d00304d0307020021403a000c0c9146d00a601c2413414080505841e4040c03c070080c1c008044404c500e00c00000c5030f6889a000070f06480c07041d01d06800141c010413 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 838507958 1250 838506708 838506731
    0x160611060a0203090703030c050102090612060405062709030f0307110c030109080723010c09090506040b0f1005040b040e06100810180609111c090206120c0c0d0201 72
    0x3505800c400d4251082d40307585000c0c10001d5640c6940c0c40001c0400c200c409040d07051050a605968001c0e4004060325620040c03a952070380c80c0308003603d07800d1146207000081081d034600000798207454603545840d80c0c40000540e040ba54540b030010041000d170f00041084d222042c0c1400021031060555403580081f91480c6100303e480c00302c2e016002030003a850101ea800100d80091706603545c5a0380004486001005013a90745948050030b48440410342c201800c00f9031181c0c000c8403e03410307103a000c03c0800c078607942c020810082c4c450085005410498540a0101a04185100803510300041c00c1039442d01c7c0e03881c0304108041c2d00550000003a079004100340815440c0a050341200d0003c3e40c035010b0145c1c02d140c2c0b00c100d40c0364024800c0507040c44543d014040601e109410080c014003000d2020080004280d07a4904168400e95400c00d11402101c4006c00080c006c2c0700d44100c19401504081c10201c4543d0180007090000d8130ba031403800000d0020440c1c96504000e0391042003056800440c0051a00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 838509208 1250 838507958 838507963
    0xa02070f06050f1810020c030111030408040303030b150316080a230a060513060915030308012c04150501090b01080c0a1e03060305070603050f0414160611 68
    0x190030038946080c0100d81088640d5008042d80c0c1c6600d00d0501e025515900d40c610310203a00f86035590190840341c945c0b0621a000d40100355070401d40800d0700240f00a8204010301c04543c401141c00034042e83e410710041c000b003403003a4070200c8060ad015098040d04894061f84035410b42003107428102c1402800a84030020b80d100d9900c50700000009405e00403802c1131914007441c81c1221207150031104d4039200160741e00c03403180c100400038007001d00200031105140c2040b2004c0c0c813250180a6140342000c0c40350039840041004c42c070403250103550f1940b081e401c20841c601da54918500c1607007040d40c020020303900803203031400103030050b072003030f02c0082c0c1074524041c800003a0791301680000c000c0740ca4081c2890117a6044280710341c2c0308200500f282da48180c021009c0e54100c44c1c000c44a503c010010f50802103094041d4054403d50380940708030f58042e0341d1074004a09842c412607806400c6824600800c0000360246080790445000a0680350500785400701481209495400030340050032008180f110f01009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 838510458 1250 838509208 838509223
    0x200c1f0e0111031608040b07051b01171303120e150c09031203180f030417070609120c2d05040c0806010f03021c09140106230607020310020a02 63
    0xa0809410481200040b1503c0e409625000758200e900e994080301000402c40c2101c0c058020400025200c038072078101960364045003003440d8560032000c82501031960150000000c411140d1580103030a07600c0440585180030a900c4c11424814520848001040039000d007010a0003003000410501401400401141a024011500c03006042181d01407980300410780c40c10800382a50b44603500d0b100c0c51060603941e5492080300707100f030007000403036210890040010803caa032190900d12034034ac099819203403180428810080441d1580d00208040c4a4081500090b60f005980e0008407650b200568080c0c90501c015001c86001000002c0000040c1c01007440060300e0181c400b00b141004118000d03109503405850710707041c0600348108042551003601241d803842960a400250849544802000f4102c054411200c1101b1500180300c000b8051040e801200c0f424007940c505914500c81c818200d200c8141e0b55030300180108000c2c00540c8080080c42510b5503849d0340140c1d98202101d00070b040201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 838511708 1250 838510458 838510487
    0x60405060409050606150c060a06030b09030c0c0108060402120a060501032a080903070f03091706150f0a05090c0316050708070605060d0515090f030a200c1f 69
    0x2c0c05041c0c00c0401c0001400c00d034041001e5070600700c801843c0c0d40001d128000e0121442c82845624104481501d00703801c00c1d001c4903c260941e1446494030311038143c503401540504020796021490480b455841040c0e05a045100540010702d00364001a6000482204680c100501c0340c842c00700304400d5030715208032030030300038550450200409407490501c640384955400c44c04121070440810702e00340080c411110303416072140b05895030f442c0c14500685004118030840d00050390100b25581002000704045216003441e000054030f14403000e04014100714160000d607008405550f0110359600d0300d10f0194002d44900c00310070340b070349081c1c102a40305004840341042000030621403640001d091400365500907921040101d01d5030307070380d030042029450020b04c040e10390321644031000301c1142e441501078090500e900a076030074600404c0210f82c0d03030701c1000d880200140c07822a1103004010850f400310026480e03071017550394185241001880e034055440311150310b0345030101780c58030b50b5410591310b100540703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 838512958 1250 838511708 838511711
    0x110f03040c2909090a0b1915030605010c261215041e02030a0f0c0e0103062405030c090406031a07020a020a0b0702040f0f0209011b0f170c070e0604050604 68
    0x307140e520320035409040c60f000e00400e03104000c5800002030390040b0850240291007401e032220b00301480104284584110a14280b8001c030100c0d44500ca03004d00703419203c060b180c0300380701c00c5542c0e96108200344c0000c1d0780e0940c0400d50540c4855065040c01003010178019a2000e12904007602d0201c0044180c18615200754503003040e03d401d080c61420040c00428640740b005841f0354600d01e41c0d00162014074026140103240c461920165a040b60008260000c2070b0b82c10002140c907981c0800824210880d001c018440c101034030a1210f0ac500015a80a0b00c411103882c10107001c0c5000c81d06881c0d05410849400c02d0350812000030348100303c0180d078400018402003c00d501660045192600d03131b801a0001800001480801e5480d01d8101c0340280c0804e201c100b042106100030702d002904980806400214185480218403083c8407003100542d0b004012034a01006079910074034240c0404c00c00c00c3d11004c00384005440a0300034002e0100410306c2d02852289071074104c08100880e00020603140c0320b01d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 838514208 1250 838512958 838513019
    0x61a0c0d0c05010612060906050609090c040b010309050a080717040e06040c0c17041403010b0f0f18040818040213031403040306050916080d020d03110f03040c 70
    0x20001400503050300c0a400e000d10014410b0030541d024200940000c1d0703a41c4003000c603041c1007040c69070200680c140150001c0200b9100c00e42080780e082d80c02d0703801440e50790214540818600d4280d01c0700160f41e07014140003034104419a151420903610341c4040d22120800301e0800280710003800580203600390910b1091600d0704000f00400d03608806401540036556034040300c680203005024012100741c00206607281084c038444084400d60290103407901858452003d012130f41014068080455002401e5603410241c5c00e061108000c00c6500060707001250b41d4800b811051b003000c0d118040e0b40200a65650703106c252104401c1d010b1080c803143d00580c410401102c0c04800840ca000030340e41e1048000e070302180d42e02a05803450103a070308040c0c030507803405061004000d40020040078010608034105031441c0d0b10321480e03844142080d000350142c0c00c1002d121392118801d6118103030501d00c0c0d601060800030450484030058100f01d500300d802030080d0905002852a58010440181405c03001442d003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 838515458 1250 838514208 838514227
    0x71d060d0f0b0402012703020109051e040b220504030315060f0c06320a02130306050a061809021206090a060209031c021b0a0b03010b03060d0b01060201061a 69
    0x101105030300090042d401c038802040441e84030720070609011400410180440c90419640400080c0a00c8100d0108003032541c001160308001c201004c1c080d10b1105501c040014000600002c0c012502950380e21280302071041c0d07002e1141c20046001c03c000351500050b07516040c98050102c0e040b42da54440000141c8508001d5a603028111250040503468104002181131071700002820540d00b1015199554583e0181c03040040081c00d107c42c5400b18440c1700588805c40854200d00c1044800c0a84d80c9201780e040c00455602d811660300052035003000200305548212040d0200200c3d900a2400b503101e908482c2980303040500c4620780c0160310043e10316400c00c8502c0c65502d02624000070102a0040751400c00d5650500c00c09002c801c025400c1030f0407040c0c100009445d0706a10302d6500c00804810b41c40d00f07550521028801c203031030b0784c0c1260a01c0e607400c01304801e109400050a8692100381000711400141056981e54004c061507000410741c18249802807412130a070108001e024942880704005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 838516708 1250 838515458 838515473
    0x30f09110f0a081b0423072106060c02091e0a15030812010e010e13030309080d060308040f0503030f0702010c02032506030515090c030705070203071d060d 68
    0x1128a42103400058510318000890000c80da107030301c440750b2405902e90303044160041081404080b202154100301a10322942d40034010a0003100303889880500d00300147c001c1c3d0080840401050f00b4510840d40952410040c501b030350141c0d080980010782c070003503450460400e240b04580101030026183c0b07070b50040031849121450020700014003a074840905d20940c103072480d5028003950b0811901507036101030280710b22030b002c1c00b03208085454103540c0000564200d03584030b06005003008081202e5010300340d1012000b4201e05030050700c3c0e1010400c840300114000744660801036210305400e03911350b490b140c8860054420342d4000c500981040140c520000503200403030f40150742c2428a010116900d002107494035000c00d1140c05c1c882e02c2c88120104400d041c030010300440700141c1d001e0140d81e031a02004644200002c0ca02608080c1440125288001c0e0300702031503200b6940d14020b400c150070390300000e2410740d0680c0205100c1080007404802e0f035650b5000350754060b03016142500552465540d0a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 838517958 1250 838516708 838516733
    0x140601260a0207021f171f03050c0a2913260f0a0b2202030607030636050c1908010503070b07080706090813030b15010807050d1a150a030f09 62
    0x442509180d0300103242c1074000302c000c00c89a43c11f1041420001e03200d20f412503236001402640c5216a005120014102e4004d000c1000010380e080d550035a0340187d05007522258105c1084089486002500800d40090840f88a0100b00e4003081031200b42c00c0c51401c1508100c03501000b1a005d070030400c0f94201045004041b1500202d44000c00c088010007a174004001c0c00c0071910080d454000d100074820242e80c9030300030609a50190071a0440311006c0d4064a20910300310560030f41c00b4030229215007250041364841a4080b6100c44003510703001c801a42c40300310462100c9624041081000107010300d04080007041d000e00321404100e840c0c1052071700d960650780111440100007a40301c079043c10400c1801d0003510803044001707600c254542c1e142c0c03a1029000300112541c1c5803102817680105820342c4500403190084005e074441515200e42d4642c400c024110902c0c5142003e0442d6000c07040c25100c080041c0c488500c5095440c1d00c03046c200d0001400c0d110121100c000362801c00c02c0c0031021a51041c0900c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 838519208 1250 838517958 838517987
    0x60206072111040e041a13020609010207051914040e07030834032304050d021c060203011505040605030c0d0e0105010801020c0c04140601260a0207021f 67
    0x2148240c0001080601801c4854070b07007071114101107800100342d010400e840d8043c51140a4404292808007103286903060301301c614011f5800d81a01c2c42c0c015041960050220003410320503a8070060b141c0c0003154004015102260301d8400352901000480505e003648243c070070080300d090081000d1142a03660720200d034000500f0503000000d42c0f1505000c00d0001072101044507040089030b0700ca107400d8a002c030302d608109502003101254030400c561848194500302c10704d6003060350f0900c0c0c144030034010041054882289c004e440d1928041002c92064203400c1103502c1200050f9507581006840d42c0d4052007419100140f02080c00140309154006041d298484d10130740b0f99a4590b00310700d1040000d000b003681412010752803c7c00106040406400a00d080c6000f58121480351500500303000c03c0b9204480c0210040482c1008549998414041901e8100c0c1c0c00f2200b604c2655559503030300c040141580c5019000351b0000d922030131400d148400310381005240d506100d10449c41c54000e05442901d4090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 838520458 1250 838519208 838519247
    0x2a010c05061807150f030c03051e07140309160602031e030a0f23010f081c020a0c060201061404050c0a030c1b0303060f08031c02090109090e03090a06020607 69
    0x2042c40104a460020090962203184a080408000d410b0f81d145c0c188500020b41800140441603000b400340c20300841ea0350807040b4a14020300c814840100340900a9010090401034003000307143c4e40d0000e140502d0041e00074040b04a8450030701e14a51040c0d81c4984103540051004000c5101501e40d03a281000384a21095520360324441c00a0003804070707000e41c1082900c0c1c400b1a00382d415401c1c81d061400b880c9000000303050307622070042c6031079800c4034400e0707411a500c81002c8510f1034860350303c6e16803074203501d004862022959076a50590024986c0201c0010b0b99a90002c01c103010401c4510100740c0c80c142c2d400c0015092900c0500c2d079511a10328420145511402001c106510038510001c000d000071100360700c84002450014081c0001c0c0c4101ca05011424070301190301a40407048030042d2512a1048075071101002c02e4402941002403050705021491100007000c040324010b101c60100303918084e50b0b6915040e800c020340031030541c0025046502141c2080039180c0c1011a054071401034600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 838521708 1250 838520458 838520491
    0xd080108100c140703020f0105070819020906090918060c090603040b0403120f0c0930060b0607080d0f15120c081903110a030509010e03030c2a010c0506 67
    0x90a544110402c0c0f01c01da020240058400300341a80454005c040070700b070b400203000d907071901d0404940303942090341d0b0100500000d210748800800b1650043c004410302501c0903007010058000201141e900b02c0380782003d54000100108065418000c080e8042d4801100e54104100700e000310307855000060000f40300601a5000c02c041c907004180181c280d0340323803078018000c401c2002c1084010340782e0000d444001c01c80c40380001c0303803451202640a031000c00c0d1056204c0800c45482e0742404080f032000c1d082e206156100c00c2c1c0300f0b86864210041c81e01c2d80c0110f00c51076440d41c611042200f00c980350100b03038103242c1c82d045056440a0b40d0745400400c451304044920104201801c09501c0d0444036401043c0303610950600c40e8080710030121000c4541d0007038a5102e001e40300a82020303118146544024005001003040362071542c0101c1d51040c02c40c038081c0c116418040349496031481c00500d84001c041d0203c40042450b1050300508180b00c480c00c083c40c00e410085820703035a031035445034040c1c551b4202408003030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 838522958 1250 838521708 838521731
    0x1e12170702120a060e01060f120b06011b200d1109060301150906030c062610031407260a060b03210408060a020a0c02100224090d08010810 61
    0xd0200d110a610015543e50382e40d10300e030403002000c0040601c00a9402c10200046421403000950b0441c1c1c0b9552011448050030381d1155586c00c0000c00e07190620900c2a03c0d0314248074841c2076043c03002e101d0131005690030a01c84403500d00001c121030302445207400104d070600050916448003003466094945000c940c13508800240545805422810f02c00521500006d0030301e1242c003c2c0003120f01500b901e45c0301540341c9d002203035841060118040030072090100c6520034240101e10a5011070f0340090b0b08010f030785a41ea09900344a0030390640140754049001070154203451000c1d8000000d0403104143c448801034480c0e6110f10798114080c1885075100c2c0c012103d91010f00c40c130f46c480d95a014105d03c07240c00810b80d5820603040340c06250361920403000000e030482c0c440c0c070890b03864054984035030030909401e501304103100412040b00000c501a140a50b002603110700300071540b044070046d054003945003a015a915226114a00c03108000c08a00100040000441d6044003003013110004074101d600708 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 838524208 1250 838522958 838522969
    0x307062a0c05120f2709011202031c18050105040503070608060d05031306110c0a2c01180e010203061503090a020a060e011209020603060d060b09011e12170702 70
    0x50002c83c0b000b10000400440400c0c507038008020070000c07180b00c121040024007818100c032164040d42504030009070018064038290040d80c2d0380203031009007190403001c020a036600411041c40703900b501007032800e444060400d105009010240c4428a44903091a14000001e03a45200070302c116400e20450002103001501e41d00000c428258000b01145ea56092000800304440703da40b141d500046e102c2c5050003801000421520700300400203010103043c034144086005000800c060300c40386c0d110200303241c2e281090360180741c90003000907128415081181c040c106040e00c090840c00d041a0b40b0400030030080c0c5e0b66801d00304440300480e9140a03101d94850f0412490b0048506d4041d40c0306402201c001591030344205111604078007a601c01d40c041841c600d000e415035008510095004900703000140050500f00e20100700107000b0711000c0ac44000420105480c108203800080600940004100ca0f8603011a0040300900700701c02d070700d05c0501d201d40f0f83d01c00320030004202460031040020503000f95980c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 838525458 1250 838524208 838524223
    0xb0c030c03070b040c1707060525051f0203010f0603110f12180109020f1e1e10020f060109020f0403021e150702031905011401080307062a0c05 63
    0x3010449596041074105085402c004031012500001400400709088a500138502040c1d86004000c06100341400c0f0f080e55039800600c4903000844407141210704500c01c201c08945d010b401940a05440140e21542d03401181c102d200030319015004100400c22106402d0040301126402d00d40060b40803140e00894589200c0c0790042248040003113524040115465006802032816201e81482d0300c0c6a03904042c203071403400b00301a502c15a0910700b0301203401d140d02c1c60b441d03051a486114207038600c00800201c428041190841011000035506009400d119000207000c80c154001820150681c0310b841c3e5603003005005001c0d01c0c0c3d8000c200105c000c19202c06440181d035008045c400b401140040c60391108960280042c410901d404d88080c0c0d000c110400c54501d2500600500b003004801c1c0499100c40a60040490700ea65072010952040318002c02d8a5000e01620400f56a882d1401d0a00b02c0580f180d2041c042c940b4068019076155030360720820744180c01c1406042103980025a410044e00708000f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 838526708 1250 838525458 838525477
    0x230f0109030b010906051014070210140a020f01050606071e03050d020a0309031d010f0309020d051e0105070f0801031415130314030c030f280507030e0a0c0b0c03 71
    0x9402d400440e685144c2e8103d0006d440701581d5140081c04a103034200c94280324540f820048180410202c3d025040c04d2004000004950400c0030780c2040340c40c02c26440b503100700e00600040e041300028900c404800e0240c1600003008840050601076240c95080c0481148401c89a08a0710320b43e1580400d800703041a5090b00075807070300c21500c408441c0b4028001c4e005030001100040c0c84050190300705d20140003405017411040c2d45480c1590355046080d00140042001a6440b981c00884900011002c00c10b04000140c8640d11500850ba50186907007990000f9103000c05000c0301d800c0b16504a5886041c42e030440c0c0e000488131088007100c503141410312480500d4900313850700680c00c11402070b540101c1802e0321407003581d482102c021104080030844c04103642c000d8070001c0c10804100700400310010640c105480d0040400e810b0b400c403078942c00782c20b94521240207468541d420031009503018401c6103100c030a0032024103900130540c3d03500340e405d81a41c000d0300501c0b507020441c044c0883c41003013542d0007540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 838527958 1250 838526708 838526723
    0x30405210d1d01030606021903030b0301020309070f0b070803131b08060115080c0403030c02011124060f090f09010b0604031a0105120703080d0b060304060b0406230f010903 76
    0x180a0010b0400d92000301e014450000c03032410030481c0d482442180101ea1003076001e0705d170b41003800011083c4080405400d03004c06031180030010055074207200550003000440010102c4a280c14403c1c60314070900e0b030188a6076413050100c0301c0810307041012660300c030703004402040d0103841500d81135908040c1c101d0240c090703d100c04408164505d00248083c16203102c02c1c46c80c104075840c000d0848905100f141d910f44201c4c82444200006405240004911481410001120325040c0c0d081071038001d00f062941d02e202e0742415001115204403e1a80c0c1001c4156a4841d01e08184004240f000001130498145400351400051b01460294040b0b460082d00a01407580d9544c3c1c1d05080b10302c409074402d08a81440c04070000189494482c0444842c0301401003d02400c9103541c4031203c03950440c00005c0001c40d210741c248500c1d591264000d40c41644500d1000660000640611084800c290812181c50200c0300389000c0403110701c0c4030903000342c90494442d0308080c080001241d0440955100034601c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 838529208 1250 838527958 838527973
    0xc030618030e102102120c0403150c0e19090906021c1e020c0c040f022809140409021017090a03080f060f030706020a17070503040521 59
    0x1110388600e80855030303000303660303064102c1c2e003040421030203160090301c0c0e4010401d113450502101d21480310324000d500400b100141000302000d4501c0056204403218420b4940014041c41005001005a1600e94005c217080201222985000c0c220007401c007041d078412030206841d40b52881c151346a0074003608082c1014400e040c403503d8207c007c0c0d00105205c404d0b071581000d461041815511640b51201d48034041e0100140032202040c0096100a01d04406d9018016405615484600403070074413500f841e0740165100034207000041030700c12a03202c400c241201c02604005803584420740c3c80c10744000700300c0c1103074845429000800410310b01c04000e40001c010b095203070502c1d402500148518400442c058021399901a4081e2903502070300000300420b558402160603408000482c2d640310700007910f003204591404002a16040c099405040180d000050907810080305000b50510080d40643d0310b403c14186589036070716030045005550182d42d03107001c03100c5541090391805401605620a07980307136 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 838530458 1250 838529208 838529231
    0xf0d020714030a050703031407120804030f020d0f050d0609050f060a12020904060e0a0f121403041104110f04080c01030605030a0506070f05070606090b040b1012090c0306 75
    0x89032a1449420301c0c001840384199207604000c0340e5025a254010040d1001606543e0f055a07020302d602c2e40ea40720380500b4000000003a05205140003c07a81945400c03610b850546001405055203001c03c90454100c4d2102096440d08070141c412042281d0078516101d0000f0540d010040495510440c107080c14036092011200711940498040e40098032a40c00d590707145c1c05140c2d4440312448009400c0503182c0002408900aa0302401002007040c0940b0071203103090304c905010008004007a104865142220200341740c0180c5005903000b1800000750940c54152110036200609003101402581c035000000000c1072182c048550240e5520b130440e840e03a440382c110541d40d80442c48407501103441c01c400490f075071400042c02441a0341c800020315059451001c00c0b00c511802350003140501c0814889170002030007501a4001030004510300164044113001003200784d8242110303407070040e00801b080d0344030720b40d124140030715803410b500000c50302c408a880e1994011003a0740c00a4041883c00e0500c811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 838531708 1250 838530458 838530463
    0xa03021b0d150b0f010801180504060e03180906010318122c040b010824010e060a120b2e02030f0a0206040c050a14090a0b03010612050d030c081302030f0d02 69
    0x40a0340140d58020030240001300540d542542805024000c42c5840351402d003a070501c0e00b1069100d803003220003054900041c9809441c40c4c00c10400e884604118481105260030031035291340c0c0c400c409180500410000c0a105000c03ea21400c019005000d800c0c2852042c50080c018948140d8400c07140b01000450507150070f010b0032083c0120740c410f5003003e064102030340c803410410b409058560074005240078010f06e401d8464042405090600407030700c071081d11664a00f00074011030300d01920b0350011042680394800880c2c6030121882c1c4507005031a4510064058103450300c41007200e40c0081d014501c402402030349140102c41c5a08440c1000040300070308194049282c40c046d0780300d000c2108d822601d84007001042c2d6111300800f540301d004800850b1103481c10000c2d883e0040d030654130000b03084010b03001107420b42d4035540103910a035103003032003001c1000000c10203145050b00e5450304200401803248002c1c11100d014190724420f030b280b005c400080d50741c1400300b6042c03801101c04461002e040400040e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 838532958 1250 838531708 838531721
    0x9080c0f06090d0503060108190f0204060306030b131734110301061a0d02040302090901020c0706080c2b05040615120203070308031b03070e09090a03021b0d15 70
    0xd95a0144190907400c8900410549024070416111230082e561038081c541d400c00e0343c4011071107005481d084a19100e480c14401440600801d50300840d1141c110300300340213000381c003504040419001c44500c20220300903a030140000c0c1d44001e1081d41e00d908504000d41103480d0b41000c10b85510401345000740441d00d10760408030451055905010030354910040500301d07800c0f0300ca15035881e07100000152101202000403e20f4421500c001810140c484d000b0820928044603500480c0e980003031149086501000460010645460300344410314209a88400c10300400400010022001707000c0d8030039000040c00c0c1a003e640980b070030040f91400d0304189000d402032488210010420f50400300301203e00100d10440290068000e20650386582d946110a51000300b00303808580040c0b15001d2103204000085014108541ea143c00440c20b1000b0080c00c5040a020525a43e0012101800094012420a0b4075a403c100d030082106811f01c0440d20f001d003040001000181c481d540380103005426403045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 838534208 1250 838532958 838532971
    0x309070317040f1214010c1413170115120804121509030903030e01050c03040b0903010b130b0f09060d2a12051603031d061606020d050603030414010309080c0f06 71
    0x880d60041001841d00b2240215013840c0041c0d0b0504424a0f050303480b8004040402e03094249c0c1c0744040c0d90380c11404001c000f0342071003d91a511034a0500c00d102c1ca64542e00301030a550b00882820340120341c3c07401c0440c4190710482c0d44010b600c40000043c4000d00380d02c50381e08035074190148415400351400419506007408100c01140c11400e0a04840d4400c00036210b170001048021450700b420f2008040003078011034215503040d0748034459040c0549840e96001e501d15143e05000c1200d401c080c1c10402d042c00b0b030403015400780d0946410014981da9490303201c0044c641065100c5815900400d02c0788070040008003950112502c01d0380091200006528030000d6401401a43c1c8082c1c0b41151500d000350403331101400140c00c5c00c0d102d00a040700e81c5106510303213600602c02031074118a41d44400d00856074041c141c500c11360200d940e100c0c41c80e05014290740100120042d41c641030600041620100400805604266440741248108a040b00c1102c2e11026130800325155205154400da64589046034003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 838535458 1250 838534208 838534223
    0x206220b0a0213080718090f12110708370204060b1209010903080601111005040629130b1306121a091f0f050a150b0309070317040f12 59
    0x13550f80c1c0c01013141c83c15030300b0800508101c0c195070444d10002c0c00c190344056841500a001d1540000e5806006e008031088a456000403607065101c1182416050b51040d2801c1d0008003021715070403101c440b0010341244041005007003101d001242100039550b00c2009401a2802d20041208540d103c003508101e0480042e0040e150344040c281c43c00c1c1c0341c0304940100440c0030400460b50342d6019010b03040701d1140f4541100c141040d42c40c804415640300b902d00362622503545c0141462002c03118242002d5400841c0580200c85030034004c5100240390424501401d0703983d2601d04601e5981c030b0703104081c41e005403500f0300840c2d448901c54030900d001001d040742c6210009501c69003580480c4c00807031080d030030000600b41c60802080805030b80e089050221440694a08000c42c083c0754601c542402501c034210000740ea080340c5131000303840341a560040e549809040c400c100090100181800a4981c0560020040485c20601243c0340c000c5401001104045010114007a4012101d29060714042c860 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 838536708 1250 838535458 838535497
    0x141804380f181213062604031209080a0806120d111e03031f030f02040c05120702060709050d0c14040b0d0503070b0a05010b180f1e041b0206220b0a02 66
    0x20300b5504501d0701581c412040425440c0d04a0303c4080e40340c800d60290027070511400404203642c0d20002c13240841400c1b10480c40120f20807003070a07803228159900040c00d40b07145240f03026100503030741d45104604450003007004c110700106a0000038804040c40c2204590321000260a08007495100d0300300315180c109229180520410031900e48000400716600400c100140707030510340030700000c2c0101c4002c074400c0c09000c110250130b10000c035540d01d104419550282440341428080107002e10020341c0701500ca01918070150011510007102882262501030500583d0540000400c025000382d400080d400004902500305010012004110715031040003400c0d85603452a040c001107030002c6c0100800018140a012101310080903084032296006100410030504100007924152030a00e40d0324800c41002e0350403280307082c207000300d404128002e15646800e5402d00002580d916000b4002c0160000c1114040180841e000d040d45d0907640100907900c413440d09000c0d1401950008025491458500d80d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 838537958 1250 838536708 838536719
    0x150c1011040b0a030e03070b041b0510020712140a05060901230105010e220b13090201022119030b030f0d0801141804380f181213 57
    0xc00301e40c250740b41d4003071950411103180011402080b850f0304900745440b0410480000c03a8540d01400d03c00c91040d481c00e65101c8842c104042c4841007680064080d01d171030b6400d920301e5038000c540f0b0341c10341d620201d45080080403400d2200b8070b845413404841860003114140307070501c00301050b810700c0b0b1200e0100070300050b07040e12112815900802949108240d1040c010b200541c030070406141c1c143da0040c83c03080111140d68242251451001103c200030b0395504c0b2a05081c14010040e00c000040c007001084a01c0a070380010f07484403005140403100d0340219582c17215241c0104d065400c4250500e402818110800744041d0003410103402040c40382c40b80c0b00380d02409000000303100122281d0381e5604070040c0d00e0140b0181c0e0189405407000d90000c03501030358001d51040c01074010b200e03e0044141c00401c1c4406080b40c0306041c43c0c0280b030f00c05c0c030f1003540240c04080c04e140a030a40018071200d50582a589802d01500d41000b030440f486440d00400a50081441e4100b01600f151118107004440907552213 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 838539208 1250 838537958 838537991
    0x709030201020318030a120f1808030f031b0a020c0a0920030a060308030906040b0c070b190209030a150509070602100c11070608041112030711150c10 66
    0x5100007801a8410040340f40c0d0b40c40107106006800310043d04031101d80c4900d41d034100700d1200c808103440c0010741c407424450491381d010010100f01d580321010b0504003800c02d2a026240e115001c000d2011030700000204807e01259240740c40401003a440b0161a4110804000e4503008400c6540344121441e5a000c05c3c2d240440c03280403502c0c80e03450001e05040d08001d20240d13460f000180120049660b400c00040807070347c1000110b118102c6100503004919041c685424038200c040c141c052480c0c020f010315000940c00401c5250840100c00c0c1340c00c8071b000550a1000680305000c0c0080c1c05010740400030080022200454038000c0d001003040c800703543ca40495644c1c900a134450300005a00a088004e0b0b0903001d940f21440050052500e01a036140004906113041380316841000040d008000700800c2c000c030b59010b225108000c554000082105010542d600d000e040c0c000b038600703072581c084101c0b96680e170f1640b02c503010780c0814515154541c43c50394603161800b801040303000c2420010103890680741d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838540458 1250 838539208 838539227
    0xe06011505030f040203030903070b0319090b0406090807150903020c240f12130c1e030201032a030209180105010c0f030e150c01180819170a021207 65
    0x2941c03018296030300c40440c0072048070050300580c2c242c00308218201840d02c6c240190300150405021050f52414070020740b03500701082000030fa040501d0030211400048aa1102075005504440302243d0101d00d41070052091040c143c2c01014041c4482c1000d092190907004000800d00a400f03540ca025424403c1c400260a843e1140ca0748001d09600320000c210301ca40540074002000394030ba401e04c5140000c10902c403000b0350b1400020304210481c0b070f08000040e940f081c068004d411303007170030740201d1504030b0080640240002418140c032024200560009500f075070030800548888101c40c8480715001030000d41c0100030050081c141d0349160820003c030781a0190403140d061755491390344050740d200d084800401c800f046041003996240b40c030301d6075900c9100b803070001900081d042d500c0c004100f0f00c9007154000541c02c4544800c5081c1400400c1c0310702c003a42d6003690740409809418400390811140010850344a1000718601340030311000d021264040d014000010b41209816111003100b503404106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838541708 1250 838540458 838540499
    0x603091f0f29010e06370320040f14030a021504050a050402040f0303050c0a0f0c181503021212070812060111030f0a210c0f050403110f0f12010e0601 66
    0x2007003051088150a2408511640782a1801285070003160000a03801007000d140c804006600c0342e1540580d2070a034007051070b4088d012000c151900e450704441c06000142c500c50034000f24520301c100400d6480a002d000381080e030041c102c0341c15049403440b418258015000f942c0c040c90710032030f02240609143c42110251122041030a02c403910f103503012111a400421189800d000308003400e400241503d507001101803103410084540d40c10b0262807c04901010031101d5400c0c1840070300c01c0c45034030102946017501e405070b91201d001e41c10341a2581c80d24070400e514010301c08000402d5424418140050314494815151021081e01d0380401142c0040f140b01540302e90350020480710ba54220440b0042c8003007442c82c1007804104201980c442603052104502d0a100354503001139a0516a1141e89030581d507045060541c1001d045d82c031042c1c2440314800c64540203403415115400300d0340e00e01c0000074281c44001c1c03e40b4668080000c500d07019203c030003000081d500c5500c00214200200003500060040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838542958 1250 838541708 838541719
    0x10506070f020d0c0510050c010c2c01140c010504232e021b0124060c11040e100b0a0513050403030f020c07140603091f0f29010e 57
    0x260700e8080000841e000d00088540880d507083c0010a130701c842c0b018a1408a140d2519604c440850188034259502e8410040411480c0403019000c44d40c548000345160b4444001c0101e8908143e00680b0070f00321540395000e0241011803000b03403000054215510541c0b00c0c1e102c5410f00c181289540043d81c89408130f401e0550001d185401c2116415845103203a44552450160811001402081280d1007913001e9081e1305005217144902c90400d0044890405e0f559a031400c07407902c3d142015140038542c0c0141130400c960480340405024804100003102d44004004008024104c01102e68400600581c104580d0610507484224a0014410022a8000303041c414581000220140003054010011014183c0c2c848d40f208215100d17102410403501120700800f0b006013840b2070341c095024030900342841041d08204000729a4000700303070860a0b4041c000d111804114401200d00500306d00310100d083c2505d03001000c070490f0300a0f0088039030254280c51203c3c400c0c0700b080044854068100c01541c001c3c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838544208 1250 838542958 838542983
    0xf11011a120a0c06120b090c0909060904152f09090c040b032701150512010b060f070f14030307030c020102090a0e070311130f150c0b041a09011401050607 68
    0x1354003a4006440d0f901c0c40d03400001c0d15800070000600e58510079209113904941c08141d4014909003240c00d2901301b00100c409680394a410790b00c144218840d40c109108564480a080768015042481c400b88070089005412040741204480f0000342c000c145400e20920034040450b82c0c070125281210b0590702c1130350059107151340360700840c05000380c071450200c0114001d80c1c814200000a120b14440080c8a008103058140303468200120b081d000038020246074917050940c049a95218100c40000140907006502c580090900211060541d60090959030180c118400325000200044d403040030952010002000034400890803030042103d000d400401c401001d2040c160b041100581c41607a0741740100303100c40c41c1c0d1803000958018012100c501050540c040c00809000807580c00901701d05101482c202a100e200107007061210754024007a41c80e4000405c0c24005031000640080440c0044940a410030082c114020020b02070744032440c60032034002155600c1c0c000d04940c0b509804c80c42c8030142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838545458 1250 838544208 838544219
    0x72a080604080f040e0a0e0d03060e011a12090303270a0627060e06150931291603021602190603060b040302100f11011a120a0c 56
    0x181e021090110311071005020010f444417040584034030641c030f1244041840381020324064901403101248900741414424180041408088070301c0c1141d064002c1039003495240900c07600d580c4a0540e01b0070544c107520741081005013000004502030301307102e4010760540c0c81030207100780700440c40016010309030400760031440410300d6608a134090389141805841030542000c1c2e04104111003000031940c480e01c482224a81800500280341d2100c59040704400c0050b48100145101d0350040c0301580e140c0300c0d9500b041c0c0d0304000d038080d6240a13111989400c0c0392001805d0540259105481c2e01d0015029078114801000c4000e81d601c0c0580114800708800d0303510940240c001c1d4119103540f001c6280d0000410700580d4805a810700d40020b0180061365150034440c00030140d800f1070b00f0103015003004100030001600e41c00301c00c000150480c030707240c500f20701d0f6150201c03900c1c02c010058a0540d070800444030502c0c000c4691141c0003020450300619402d0352030420796203039038180001501503155000304001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838546708 1250 838545458 838545473
    0x1104110708090f0a0f0515030f011a0f03012d0324090507120c09020309030904050403030b090415181226010f0906051c1115072a080604 60
    0x401c0b00700400400607640e6400119078842203a80c44040c1d0202d046904028504060202e0f600c80300681101070f21310f103801c0729021560b081c10310814808920345000301c401203a15809403043c411000b1035035952075a643e00c0f9104c03003040f880021174030700002c01c9142c208104800861401c40f544000200b140f03c2500901d0b0340c0b20a0350001141500b52140101e43c00281c00744081d0000e0302d40c209460051074413600f82030070004a44e4121512151041041c0f1419000010a8881000d02210081550781c0d941c90200c001d0441ca22515800c0044501848200101c0110b101c98507031072080b0811194107510030745443d1024160001c0c140102124180300c1861181948034094001540c050903035030703105d80c4942100038090b840318612a40b003030300c14000b110f268040c0c24010002254034041c2d201c0303010f020307248000219100070400c0c0c0134080c184080e074491108840200d0040b080c445d84495403401c0036003110b44030f807034100394844e1160040c0c84d45a00c4040c94000b900c42c184002c1c0720a03503882d6a10b02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838547958 1250 838546708 838546717
    0x20103020c01060e04060e0606014e06050f031f0c050f070807031404150806030c0a090516030504050604150f0203070309020102060c0c030901080a060f0608041104110708 75
    0x1107055484100c0803840341e10031402913000340e10401c4d000600c0301d010700f08181882005807132a8104038070002e0741c5419001d142581492031014a5011041020451803a201e18410b0754207001c0ba0101d0f0b1802d9a20800ba503803005080b10020b8480d480c5190f9420201500c42e400e41c0c440c186030020b4400a0680103610740c0c480022541c0504106260402e0028080c040e41c2203000c00710380e045400565441019803040040d0070000151805504240c181043c80c60b0300d61140f041c14041001200000310a55820484490306804c094254000d090304c80c090ba9000c0c200c200e51800c0da841c102d101c90b0f02840d129105080c41107400c040500b03000d1f115581c54001540364141451003481e1618600900031201d480107500848683d240043c40c10307032503c006428a00004d040d0345c1400d01c280310018042c078002c01143d41403031003480c08002a58803000e2100c000d01c4590008041d030801005c010880da60801503280c01350307008419414042c9918070400064030000090300b40c4499081c0036907000500b9100140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838549208 1250 838547958 838547977
    0x70507030e0d05070f18060e07050d110301080a05070506070309050108100b19030507031a04111c0b030f0c01021b1f020615010503060f091807090903090b070c0302010302 75
    0x40c1d180c03a03c0d151249804401e41104801400032034040100c0c00341080c5c84176004440e110180145454075174115070f4050000d01c0380d8184000000c0035030206100c0d5002a0203a200c0c109080c2c4c0f40d5869000d40c0e541c03034010720001c1b94140f0507120b0206a503d4450152840702d545903458a00c0c66003403200442e03809101410000380408000000f00d02c080051014000c04e280710102d18440200103407001b07003520000b81001c41030501d0400603111910190f50751507000002601c006c00d00607848a01d1400501c16810100c142e4800c0300b680d00280c80880c3c1142000e841e046003116014129000d045d0b13169400207406074051f0313201c00038018100c86c2900015403180740041500d501c0c20f0016504254804130b80301a080160003e408005072075552441c0c01480407001e01e411030951618a020520b1102c0402038113100c0d100a00000700b4007030f503030340e4030602d07110b680c03411349660b40d0782c0700321280c040c10411000b00d020506000000c101c1d041c640e02680d884540080342143c0076880c68006500075404020007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838550458 1250 838549208 838549219
    0xe060c0c070f0617011409060405060f0402070605041a0c040e06150a0929030c071403070f0c061d040c2606041a010215070207090504121205070507030e 67
    0x42c84aa003402c440c4003c000e2500c07664901c20110340d509440d010140c011901c40400c01c02c104280d51030b1480d40d6a8020000d440000307154840e200001c07641440704420341d07841030000407260100301d9181c11060107144100d041c21400c9000d20700780740b2002021038141c2020305041c001004101044218250412400780140300d046d00c0f00e0b03a040045611540c8204046030300311008012201c1495800494107500c29980c8000007000b0000c040607200c0034101c20200c100100f141418071646510303405030b003954002101e549103102e18059004007035014055035030750340d40c110028000380105900c1c100d181d080c100380400d1910f407004000c002e010041c540320400ca800800d01c80c18840c04640030448140b0300c1c4041400745051010071064501148501c8002c02c0030080520540c0d0700061030b1403428180b408441c0c8940e030b418074100e00d000b80c40d9203c1e4160074248403c0c0400e1252801803c207c0800302c0da03c5660001078082c64009540003a0346840004604200fa9000320f48101000b00050740300410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838551708 1250 838550458 838550473
    0xf0a0b090a0203040309300615030506010e01120f0b13121101200909040f0c060e030d030509060c0a0504031703060310061404050a021c0b10030e060c0c 67
    0x205800100486211030300700c2c0d00000740810716800409000040240c440144540c40d890030519040d00c0c9912107040e00c07400c52203045420070841d504201404000c4101c3c4030714aa9482c146a81d42d80028850f425018407144000300740702080c0c5180a0702d00c0c1e044464201c0d507494070346d600401208003c046c1c40c2d1010340894030f00000344140000213a0341c007050f556204a00c81504044d8211083c0d203029409a51501d80058148a144c0094030322035482180c0c1c148142c0d442e400c0904680c200030340e00822011510300045900c0d03802580d103e00380482078040714412010850b080c0d048a405035846480d80d4020300004a05041010080031103000703514200b814150b0325510090300d00e81003040705110b00400b20070010035041c00c003ca690403401c5603509024452801701c443c0d465019914a0701c1c011500d40300003d000e1389440e0112446c0c01c02d0710f1aa01d0700c4241740f1001100500c1d07140034940c811120450300b0080c09110340628440035100038040e01c200d450380d21074460240e00030380110307460380100348 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838552958 1250 838551708 838551731
    0x180b01051e09030109140f0a0b04080306210303041a06030c240c060405060c04031203050a02070212100e0a0804090903020a0c060e01021005070f12180303150614030f0a 74
    0x40d08105c580710704522035403603100340c02d2141020180d940741380d902c6d882400154040303000d0310060b0350402e0704202c1c4590f59844070008109510030314010049190035403080c4501c218030010003144602e028240096080c06101280c2e205610f0960345651705a0010b00810300c5490140c0704803442601c010342c46c0000c50b80c13000703483c1880d8000c8003a207903107608100100014000d003403000c00e038080340c6c0d030500714a8182580c3d10101030034001c07c00b010805a403640000c000300426412980600d070000d14800c0842d43c0c1c21035040d070b642034041202d041503003000e62070902c0007000034090000b25480710106081c18142070548000b0642541d0075001c5200b5107254001140f00c004440300980001d5803070005907201b41001900c1c1c400c16072a04500b240c5071100b041030380d43c0e00210b202c1c2c400d01f083c6019030f0702c5c402d407840e2800544401da8507288001002c1c0c16140c201070701f41c1d01c811141c0102690030f0003495558002514a46044600c1480c130040c00c20001c2c0301c001c07140700c0903540641400c1c0002000100301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838554208 1250 838552958 838552961
    0xa03030c060e07180608010e0d0903060b0120010b0a090b030a02090c040e07080103061503110f150f091c0f080717040b0307020f01050601050d0923010204180b01051e090301 76
    0x82011034182d950f1017009100d5514207010380f00101170340d14014044494140401801a0494400174106c40e83e1882440c034541c0c81014001601d1501d10031034484500a00c1c403e5008218010b80b46100d46052400092481d0b803901070104801001030281c036403840ca640074054002801480b03048034407000c101c0481c5082d000c00000340981e2007a641c619081d030440c42c04004640780c07035450005915601d01d0410000c3c107001031480e00c141c011740704010714012600202303d05101d0034014072138a0301c0c041508100d51041801500f8500c80c100d8041611000c0a4981d6803510302c003480c003a20801c1c0c2542044041100702c001020b80c01d00c5081681c001e090582c50034442c0b9006a0030880c4092800000d01505990410051100114120080016003810000648203110303c03403140d20075907141c407101400e0101d8540015044100d09110b41c64405401556900039407082c050140c84000c00044150500482d102c1c84401742c0c0e060b1210340c6002c0d440c1c2020799140d10450004000b00804200d510001c0c0c034203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838555458 1250 838554208 838554239
    0xf040506070b012c04020103110903061f2709020a0b030c03150916120b03070e04020a15140904110d0911030f0a111c050307030e0a03030c060e07 64
    0x402c2c510b1010350504c4030540c000c04120007080701d11403400d6500c54803405041c1042d074015a09080c001780301c006440710040e890003a803040540c10f006100400680804417110700004007004904040d00546130701608010044e080102a070000081c06008103071701042d440744d14210300040090a405640c2e090211a680c81120040380d215008024400c03030710320000c08000d040740101c801030b08500d0b19074040001c40700143d40c10403c12011047d0b10b09021503e0b03120302e02c410b40c094141c4616940707418084c401d070542900c089001d280074104c00034801c0c40c079014604540c0140d50360707404035403240d0003240100c1c0c004101c2154000e03601d40ca80800f0f07400c480c004102c401130380c90300403d20345041c3c185540311301074105d0041d010303402c03201101c0814100810b0911906078040c481c030004040400100d000441c002c102c00c42d0411a0403115405c0c0a000400b41000522a45d90442150708100030300501c031405110007804284280a030100081454010501800c114403c54400f6665440c0d21440c60b81c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838556708 1250 838555458 838555463
    0x180604150e0907180c02060a1e060b030f0903040320040627060b04060e12031201061106090712350c010b0603060a0e1308030a06060807020d0f050f04050607 69
    0x300390b50401c4000f0013001e1001085182513130401c0034100041c00070b074885000525203142a81c7d610700180038410a800d1440014a032450304214141d00c8103240480c6500c103842040c1c51045d03140010305c000701c0000850f025658800d10200c0503a100402c0510004155440340381d000d41c88010105007100320b0884070310590381001080300d034488841810340c21a80ca80c0c20801080000300000d009251304a240c1740510314040e01c1b000b40c0701d0303542c0f990a070030b42c0103009820400c02c1e941d8000003066070740301100601c801c01803425205079854010340541d0b21a418407c0b000c50503068500d50340400c04480044113481420391050409031048209200d2412801003101812440483d605c3c410360f00034403a0314840360043c0ca0292450a105000030b03c04c418034822a08090040400180d43c00142411404902d50046007980c40c1d042c905900c00c0505102c1c01002c00003141d410000360154400a0101d44109590b2284459648040e80032a015409084150408101080006065180c68009040160 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838557958 1250 838556708 838556713
    0xa120b15030114010627050f1c0302150a0e07031401020d06080706020f0609190507270f0c08070818060f01060813030e0607030e090a09030905180604150e09 69
    0x6042040103024041800381c490107840d01186444403c1b02000c0c060703000e94000701c506880b24107020000030014440e9907a4118001042d00350ba07803c058000403025070002800e809070b440755640340c156004540511011400a03800000300b000441d4000010800a40340f01002600c4e2890790400d10080d5010faa02981e0309a21020341005030540c14020080542030340d80c090502c0c0d0521540013540c0380d006482241510f11a05030413001c10504000900003400c0c610158401c00d001400100212000d1b000150315007070520762062102c02d010301c01c03241e210b0000c0d100c405050b12100000c84055800410040c000303041800155044e40301040800d00c034030881600c01c4050740c1015001090b460300a019403400c0542111034100003034100c2c4255007603400688030a500d540107418211400701c1e90f0001640c1040064081c4520714074643c00c2411003d01076162440d02503030310350510013900194440b8042901c1e001d03011030030307600d059000172103140d00716405050b01a880303040b1006900030030342d90310070b040c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838559208 1250 838557958 838557961
    0x80609070e07020f1b01030219020a020102012003070809070f0b071101020a021011160603090203010b010f1403090102090907020607110604020603010905090a170403110a120b15030114 81
    0xd481c444255a100c802c92000c1d024103a213010703440e03a490404107a18021040c06482011091b482541901c40d00c0b4082d0380d00320451401c0c501c010b9140c070403003242a401075003820710345c007000342c08200c80b020002d200c0000a0300c2c0d0ba40d8410300302c40b40300006d4944402405410b0b000602c4109004188010b4140ba043c0103035101c03c50316140345113289032108039040d504110030040c09070340ca14441c4501303841d041c10030004640c02040c0e15810250942c00400c80f404110bc004030384d0b6680759200300c0c14076109900801021207440015a001a12950750740001244038010b609480710075000f8607042640840058204a055000218400b00c110303045070040e40710303004204195900034981c803600c0b55440e001c1c11040c1030680100c0c10b94441400b0300b680701511600032502225040214075000ca030403214528285008144842065000b44000e03a06484000c241c1d000304d1608007540c0c0d003100c0d148241d0071841009540c581892050050159001c10410000c4680702d88081c0202d548001d0f8146500095 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838560458 1250 838559208 838559219
    0x1030e01020f1815090907050c010504030f030c031a22090b060a06080402010e0d02190f06030c050c0a031110060801060609090506010e12070b0d0b041107050606060706020408060907 80
    0x85080044070300344030700344803d4152460501d013002c07134100c04c00546214580c1d942c0c00703800361190302c40c80a1010440d881e1800b000189548a1054a0f5801d541e40e410b00041c80c0750384044059030402407010314846400131443c03103a0b143c180c20325960980110b0340ea151401d4043c007002c04481c5952416100c00310084208002d5243c190b85020103000d042c1030503200c600b410b400081003800b204407080d0080440700c0000d0709655075614a120715a0703111044d00e00341502c404480440c00c84500c00d000c00700741801c070341012640c014801d80760000175000041c4100c03591a02d0071652030b80c082d0986000c0b030241a1070300708003080600070b900c040c0c86400c1c000b14000d03180220040200d00c00303a014001061800052140a030703440302c00200701d901c0c11244c24001251307001c900c90034206140e02002041c000000c14071449500d6400c0b801003294100c0b020000030151140e6644140700d04480142590803c6000079403d14001f0068030495004400060500c6d40f140d4505160071420f07146880b059108070f404226 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838561708 1250 838560458 838560487
    0x120030414030d08072a021002010c03150608340309020a0b0f3f25140c030423150f04050409020d0b010e0f090d08011401030e01020f 59
    0xf554002d501d0903035105c0c5030040b03000301400007902500310b005103201d5100c407000b10b40e000007402d501d40041605152440000c4064003c022110319a40842d00303040301d4032418039142d615401213642545071000e190341c80391001901000c003002d040c030126032082d01400010300703817804200010182d40c0f4001144c2c1402d004001010396a0303813041401550030843c60000b2081c00e41a038080e80880003600c1d14900703104005c2c05415000c1c0d0051001c8001c0e0343d4101d00c15206124840307006210300b80714071080850050311103144100031945a40451840c203401409241020000d00d44c810411068070304082e10b91100505a0405120700840d00805144031038071880c1544018488810145106282451101c0e0195180c000c82c8141d5100d590f590445805545038034000c03800b01d90344102d1a29040d038450200c2c0605c66400e890808454403440d0000f003c07580000b80d0f0b12513641c80e0786c0783d50170981c0c0703880418610141181c507103d04142e10ba0072000c600860074006811480319561030240c0322410a010000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838562958 1250 838561708 838561723
    0x4080709110f0a0c081314090603031902190308070807020a03090b0f0f121806150405090c0a0e010501030e070e010311010c0f080405042306012003041403 68
    0x310280780104039560000007004550403034012214481d241c440e01d45094541c074681c40c1c40039002c860000340480c0c0405aa01c091030030365a0208804901d018680203005443c24125070464050740100010080c1c50b041c000b6050a40c40c0e01c5c411540100c00f690307074988521001c414200c3c0403d0740401801a01038000803a05d510511a20046c007400030305072002006010f03640306094000e2000541c441c42c0003050011100c07402080044103a4402440054590203401102c0e0741a04080404030503001c8940415403a0003100340c3c10604508151406c1000b00410300540805450312809094482d02c3d240c1000540003096001c00c0f02955625000014007035500d01c040c4141c00f0b8101c92003d1240080f0b100e401c9054a400032640080c070304040c40165100c80b44220b010f0800d070f100b035800404001c40d850080041c0c0740161400d0210310b050030340300d04032050300705204800449480d00144c0c01394803075404e0501c00f0306029a107040d020381c10044581141d00c40e41003800c1d400e041450800241c10208200c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838564208 1250 838562958 838562969
    0x30e1305040b0103020111010b0306090d020c06070339060b190305060a0e0f1c090e0105030d1d1914060705100b0f06030a1e05070f08040f0605040305040807 69
    0x3806240362a0751a80110345050000905000712041c8040103e0001d6000301040000501204c0c554100403540c02ea8554840510a0041c40b40711424015402d01078242c030f404991580f11000d0390010200c40751191490302448a0f01d003840b100e040b5610038000400d540081e40a80d0303000a4014500003403101c0c43c5017003502070606a00c8100104009000001e400b9030294044500244000f07560081301d040109009801c00140b080c1d043c043c0c605040c07001d00c50f50a0050307880d01c85115030380384149642d0034005d00c1144c0e850f400005114099901032441e251100e024a456043e1026003100050554136100408140059103004103106d19000506a01c00c07280003200c5450810025585040d51213100000000001e80c80e01d449110f0303500c2d0520305c034407035000080132240c0b41d15100d903104d00101999100e5282039400181240c0305c01056100c0c4502034442d90361552150100d080303007a100340d80050011901c0745400852400412094864540210b1003980c070556107501d02201a442e00803a42c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838565458 1250 838564208 838564211
    0x20d110909072102030c061b0c0301110406030216020411071502070206270402040303030203160c02150a0c051b270103020f01030f050a0501090c050702060901030e03070609030e13 79
    0x3840740140b00d1600f00100f00700725048840303041d1184040303801c01083d551156048000402e282c19508088022903084804000464624058140405082e00e201300c2110440720b00402c010312045220350000d00b0200801e80900348124066804078044a07020080240d17144800b040700401c11800d0000c50780d040b842d03250b0a500f000d003183c0010708141b08413142183c203900018048907411074150314903480b089009000310340f80d40d0740b03040c0a4043e40c4100c40700210416819000d2084e00d0103a0480c1c0c80194001c6e180b03ca0002d10385108810980c402c2c1140701c01d002c65010a00b00241042189601e2002c4104506104158440501c10007114859444007616100890407958a07200901141101e4044072a030104c0528000148c004000140c0d101098a0a000801039a50015001207040340c000d00790403c00d00405827000c407050301074514000e5005004003c60381c200d610a030030604400407110103a030b26000259544200309c940c0306c0c104801281799231109440614000d8000d440c0caa288810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838566708 1250 838565458 838565473
    0x807140a0519031a01020601032d05012313050a030f12020f07060533041803020706141c1d06070e0f100c0f0303061e0f060f091809020d110909 63
    0x740c0c1005000d003400c810000f0f60003241c1c024506600d10755028172b02070b085002000110401c1d501610410490750742425100b5500000c10b00707265041500410168002000c0e280e071200603a4103d41000c0f9904482040022680c181d4050f00120310051415003456200240d0300d0403d4a020007c0d610010903030360b2100d55445410a0041503501346410403803c08840030002300c20000041c1c0180a02c240e20a4100b030100c19850402d07400142c00403e84049403141c4410340c00603100010709110310007502c00c56104142e4011f0b940c842c01d4000700301035041604400d600139042c2c0506840c180003128108009400300b400d546d401d00340002101c0200c034080d9043c0f074000c01c4140f4050304940031100007d040c1e00f01d90303040340c050510a41c800400751050719006000b020041c604045205040c2c05101d908141c038480c0007a89a0003118801408000c4e500d5130440c0d5450040c4030f0500c02201003000c20040d403640d00403001690b8040072010142e105615640d1403202c81c000740a034500008089032425800f180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838567958 1250 838566708 838566713
    0x438090c0103020a0c0b060310060b0a20072106050c6907110a0806010e191401090b040c050f09060714060402100807140a0519031a0102060103 63
    0x440c134401c01c5811405004a80d00c1c7c80011900d401d80003400000c056150040c00310303000103c90000c00b030001095031107103014044a80d104912a4403081a69503a0380000c030100000b003810444050210100c80100014448584130301c02030b6a0200c4044005020001c0c81e003212551a0110b80500410b078180c00c0b60085443c1c403100d002207006410803125064a6501011844452400210307441d10b1260500464111150040a682207280c0445400c0c2080c3c401c6001810098111030440d0000780040c1000d0746412403007070307440070702600b66440b0b169019103100704c0c502c0f9801a840c01801007d15807407698900003c042c00c450b5054503484c0f00d54249035040300c507150b00606407a620303102507002d15660300e200b00000e60107210702100100740e1110802c0c0c40f00d0702e00d004151548264001d81304912209a166001c4401c800c0440b40400400e07000761a4600064001c0080e010300400307424101e1400b402441700786000892107403a800040e885610382071300000e4011250744180401e000030310b800e50565 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838569208 1250 838567958 838567967
    0x31006021c0c030815041407091a0702120f01060e10050303030405070504020901110f03071b0b0a0c08090d050a05011b050906090d1703091903080438090c0103020a 72
    0x100340140c2006100c2000c50b201c85ca0b640707071203001180024001c0000c00081031021044071812600503003c104042c200003801c20302c4540090a0389481d80c9000c2c903050442c3e08116543c240d08901603418481c008085001c07045c00d1044002070070311504154020700e000d500005030b880d000d801c4540240c205205005c0041c030005031403020380750f04882c05030300c405140b00104c807291190514500c241c42100c4080c40c12000c040010039a040c060308407030022040303495450310700d401b29205050400d41d0801c00014a64407900c04040c80340e04ca140703594501420400000d49030000c00c4801c4d103464000881803800c010f030902c00d0444c040789400540340c80c01c002d01c0016002d03002d0044418041c400c00140020f181c0d4583c0d8401c0103459010b0083c004d250240510030000381c1044910a000b48602002c4141c80c00d5408035180300a589540c070720700307691703070760398500c000c1c600301c0445c643e003403841c1c440c55245030807051a4284003180d0140e0700701003520349100010300c0e00d2005c0d0852410b0510420089040580c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838570458 1250 838569208 838569227
    0x90b040b01081602120f040f06050705060a0c05090d060209031015031e140d0207270e070b03090c040612020315220320011a130b0402031006021c 64
    0x16840314803c200c1c0c07590000d82c245000c483c1c40b128181d8000540d0108203400c035000e40161544003c1c080c0c02961560020b03245031103040005882030b40000c00117a0041e40541001a8046240c90500e003030050a4000c80e00c64001810200c03040f6401281000303240c1010001801d0002078600e080c040c40c600354400d11503014407400007a1080c0c15035280103041540180340b071f07400c3c3c41e8443d6100c41d1070503690f2845520341c0035a0001b45c0050103250341c000b5101d0144000394100d83d07502c04500148201c1408004001d011040c58107603a0f00030250006080c048070005984034884140c09401841e913105c0812045651681260440001a0350800003507140080c0d424015000c030711402040362904004001c814550780d407010241001245280d00705544440c02600071120b541300c9030840c802054140d42070f0348240c010456070b002c40c40707917a08640c41c4c000071008141c0300000c0002110402c1c84082004c4e039104845442c00c20200803030421030640e0420040d070040344020442c0541e807409100007011a0351 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838571708 1250 838570458 838570471
    0x13170702031506130c05220513060605030a0c110d030204051306120209060a081207200f040c03180f0210020303010b03190e1e0c0a12140106030209090106090b040b0108 74
    0x41d202045c89807680941c080b64100074854104d180c15228508101101d03403c10b0041c1ca005420500f01944490624001c040c00c0e69a1515520b09558810200000610080d000c1c00b04000c0700b80380b0300310080e07018410422000944d5030003503515420002405104221055003101152516004100300003440c0320f5126402c0c0e040391640e04944554000810141c49034100c5c109130f020300d038020000543d070580200140c0c0d11928841e01e48581d80c100c40300080c0c844401c000e4004540705070f4107440b46050740c408003158103542400a44414007441c0110300038030b0300c0c4048820308007000b00321040d403400102041c280d50b024401103286604001c80d2803424080900148130701c070341074070341000c10280a812800c1403040450440c0e8001c2e014840800f101105051034110038016005c5c0e414117814404a0b640664000c1c941c2c482c61001c3d640d60b0740041c4207104650b80003655940c003004c00181c3e1060080d50203044c1050000c591a420003003003904546c40e901c920340c8194544051a102d903600100c1c1580e000e06d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838572958 1250 838571708 838571711
    0x1202012004031203021b012a0206060904080d02041806150c0809030109020d0b040c060f171e07110f03091c020406030b0705040303021608151317070203150613 70
    0x3c1510400f600640151444055900140130441d440440154070401d003031b00d501e0107500b610080d0f1742c41080024030903004010040c0c000b200000d805080044a054004d07100c0e02000385440c00605400080f070b00181c104503441100302d214030b240300c0717a24055040900346030107034542c2d04011027001428992005900800034807010605c01c1e01540d003980709180340d640240030ba108008440c03a0110300c415086034215484121030401080d410b1094a100d80c1002013600c0b101d02550501141981407000203052100b5100030403200b104140d02c50301414055021603c0f00d520019164000500340340d5900192000d40d401401850b034190354245c0c075440d243c08000c800f000e403582a40085809880300f42c2010307040002c0c600a0104590f400710040040f24040e0382522680000c0003149201241240b207094095405501c4a000f00482022880d40100e444e90388801c545802e40d4404540c003410041103044a80d0100307550003541014040304d19905080711f0184603900c1c140c400103600841e03410301c0d0034949 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838574208 1250 838572958 838572983
    0x3070e0f0711010203010e01050126010618170607120216120c120509030705150d02250614010503031c0e03040b13060306080f150402130207120201200403 68
    0x10303005a0165560070b08000c001e41d070301d684503000802104802c2c410940019040c0c40d03501500302c0c0d468507000c03070f030340d100760700c07400d1030b0b40b070488200d0300514003008a521250089100180e0181c1e4002e0b40e0620318031280213804c19240030032000d04480c14403018400c10900400429200000c02c12188071000c0d801200c11251041c00c00301100c03030540206000348807103419000c0083d03041d0400060294180d040381240c0302c4584880c18400c41000c4400c01c5c480040c0d0622060604040d1600504601c1c4015400c00c6032180c1c1c90454600340c1030441d08142c94180c2d1321945110725203401d80079035000d031101303500071740c0b4200400b400c100101c840c0292000d0120b42d215088850324200b801210014840c0e015010340f0ba23018038864540c070602900c00c1c0c41c04a4584000003030302c0d40000c2042071951007404040c00d10078004092802800c88014400c82e0b0000e88582c1d4407294040d1031000d0085107006541c202d404004013800a801c440c1524001451180c0006010740750541c44021078055941c00204680070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838575458 1250 838574208 838574221
    0x10e06190f17091f0e1e01020708120a0c110319050912010209030f0a0309030807020319080c01051f2709030804030e0a03080a05160503030106180503070e0f 69
    0x1005196001211180c8040c0d05010181d0f02c0018074240508070b040c02058182200c41c84007084a0360740c0c40b080074a0b0001e200c21000444512541c07120380750a41d001516000c0345903140b20060b80a08031400207045081c051100a000c18850b030b844031195814019101d4a80081659030782c0181a00d09810303185c40185104130034819400d41e5241c5a005d44021120400388013401d0207900010034050080c860781d0b01003407100c074000561815464041c1c64640005041d070321841010742c0034840698140c030400031500d02141142a801d214140a100741c1511070900c00902403e40d84050310651107240102c0c6000913203090101c0800445030301c81400d10940541071303c003141d00c0011860042061b407800b60b0700000d1680120034903102c1e41c441d65070407510510001c00c02003010100c3c00090008081031001241841c003840c01405611041c50650901812a40c0c80518560098001d980015524070380c0a00c54507542011714027501d0114040c02c000b50030324480710486d6500a20b2517030005922800f05a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838576708 1250 838575458 838575467
    0xd2003120f13080304060504034a1f02010212010902091c0201141803071d09070312030507030f0603141e03220e1e060d03080a0515040911010e06190f 66
    0x3408400d9030941c0c007110301402014904103800031016005030590401d0041c180003071070028000cac0103005060444224600601e41d01000c0010131010070342d98208111a80c682005124500a0032080005680c17440e00720300340280015908600b80302c0c02c031003c80e504011703a00b210146c00c420490101d0148ca500c011340e20401c254490050964040c00f80f148040b03400207480c0101200d444800091900b15203551400315580c4006d8400602003080f0012040b030f034a84aa005550400c00380e25011a00e1030241e0226021503000d070f40112202410f010300d0613500d10081c0122196203e4100d20319400c0c40300300745c1c015180e100c0c6554900440070140d010004070012a41c01c0d4003d000c01700d00c4140c3c0742c0303418503008901c8180341c403a01030042100740004006260010041e900d9980c180d550706095200c004215020b44800340c000382401c1071450040d1940c0e2114032903802881c1c01140b400c00301041d0000094000c540d40c460580c001c40007001400003249250135181c00e01903c40c40c01c09510b1039a40000c03503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838577958 1250 838576708 838576727
    0x26010b13050a1d370210030e0102131e0b070f0203030c030c0d030b0a050117060a05030115140a0506190c080d0e0606120d2003120f1308030406050403 66
    0x1454060560a038524001010310b4040b040c071390410a00d84410040c80c48024803006a1901d04e80d0990a01006050040c51440c1e49200350801003862910b13402440d0076600402c1d002c8a2048201504010300444402401c41608110158050507800c125428503944110807024209c80c0d0307029240c00840d10204103d030440090394090f02c0d190301126903450380354235403240c07140d000900b000c05103101840c0044080d421210305071540403900c1c0c0c8a5035141380c0310a0041a00d07511803103050300052207032020f0007004d070440b41510007910b92500b007902034500c0d0160b80504034041c10b080c80c0148001e840b00812903804c0515900f00c1c0c01c2c0c1c058070100c2152145d100300e000403c0700c00003203080740c9403c82d203030455080c06124006441d0070b5580c1c1c009000b405a00c1404940842d801103507448009401041e400040000215078481400c407902d0782107103035601101051b8882e03003001c0100080c8070103246c20f9070f030808849010501c0c4003080d40c40710401408041c0020340801d5440d030100f02014010708241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838579208 1250 838577958 838577981
    0x306070503010b09010c05120307050c010515010e010e030a1524030c0b0f041e090b09060f1c020603010303170a090b07081f06050a110a021f050706020426010b13050a 73
    0x23507941e40f800c8080144282c000c2003020707c1a43c00c25002c216403600b888a2081c000c201a514008030b002150011940e0b010b210100c1a094040c200d05034000c1041e0840750301130711a00360804100e081000f085407520358103034400c010150107416014400103540b0b003503031000c41d0400c5601c651240c0213400709034042c1c0708a51241721080c1415140c40c160948045429044840e482002c010001d44e03d07050000c0b001e0200c40c080e03404582807030000603620f8408402e944840c07002c811700741010074a50218034184c0c02a0800c1c0c0120f03841014901c43c1c00b04034a0025401020014240843e00c061f6840100c01900548108280700300c00c00081e07a400f03048440c4036500c140781c0c036403981c02503a10080500150300517003004000a140c8030409404810004a00e103d440e0701401140c0e201e1003a40c001c0801e10880700384041000400c101420114a03940040c00160800c8042445606003001168a0725001ca039904451a41801e241c09004e80d10101c43d2141c00c0c0380c4050201c0c01e0b0756084400700c02403d400205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838580458 1250 838579208 838579243
    0x131a0109140a20131802030a05060105041212030e100b100507050a062403030306080c04060e132105030f0c04030f17091e0306070503010b09010c05 65
    0xa0022010341102202000c000d10140141d112403841c40140c9026804507440110090f030082405071019000b0300a408034258011503207510340002000312800c1294004a0980210510a0f40b101030711859800c4142400c1032407034540340ca00340140c041401103018103100c204004220f1943d0290308454100701c1c0c29010350311a1010401c1e4a4000c01710410f102c0e02403209500700401c80d9000f181101c451039040b00040240120a90301d950143c80140320a07080d4041920407402a03503800c0c0d50510140d882034601007025401d218907d450070508041840c461810714000300b29000403a440b46030020707800040801c960b8900d0525201c115048800c481c180e480d0801d40341c0d0016031000241d400f40e12241c0d20141c25403500140391080740181d020141042d5125840c400c0007807250400c0320240c0058030b00d1a810300e40c18200240e6200030105502d6149058840d00070000e140034003100350f100b0b105081050941d41840445a1b5600808100d107051201150035901804802c101c0e44106280c03a009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838581708 1250 838580458 838580461
    0x70218090a03020d02061012050106030f0506010602010b010c02090f0411060f04050a080a050d0507030e0319050f0105150d0503190c20090a0207020d0203060720011103131a 76
    0x485559445501c4816001400303000303a441d1400d44081802801012031300251101c0c0750500710141c4900d40e40c582d04465966a0b010004000b0703070507a031a211074a004030007030115517261200103820755420080c141d04215030852582d00594450401e2a00540340d40f4411040b0350b12460010080c000307d00c0c0b215480880071483d0b043e03490300e036001441907031402e50746a02038960f145030f02c0b03a071014000341c0105540c00030b85c4c014549900c244040c0202d24000c4c50900f08070f41422000c0307420300807440701c460590f08407100a05d0a1140402c8a000e200d07450100030002d45c03070080d0601e080c6400c400d079014440c4046254501c103019080054880040b4080400300000b070524401603d11004110112031610b440400381c01800b100d1400340d5035100c0b0180501d4034079500e62003540000c3d404130008980c0000740001401c0540c8080043c1841482203440c0d4401c12030809a29111890940070071130b40c140c0c1414800400c960704203090320307040840f41d840348002408510700680386001d13980011400008200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838582958 1250 838581708 838581721
    0x1e09210309010b06130303110a080406050304060c0e030c04050c0f0301080f0c0a0e0a0906021c0f05010506090a0e040602090d0308010504060b0306090412141b1005040314070218 78
    0x450007144900d008020000b420700c14010540a40102c0d42c0c03481045600800200b40185148400100007400b80c1d1000c640c00d82d2101515002900090006600031040000300005441800851140344c217003014414401c9001039680c007036104115026580b142e0105055080a40a58602e0f040440809803250703160017041390b95621010221141e88111091103c060600c0c11121050f512155403441c6170717590340f2246c000076040ca0b0008580d46a400c21001ea0440c04002d090030180b5803800012800c2e00f0a00241001c0d0b4a0682065110f441e04002c200641d03030341d405c1000d0071200c1480681d94141d4443c10410024090b206410b60000240310024080590021201c0c0c180d5130700300d8080200076200d8030b0a01d641c0c04112419a00400c410340450041005c80b103900c400c420461800c900520446041c42c0a2900120340c00d1040300b500b000c00c440300b17003824003080c0781c024002c0d58108120701c0c0c03d8500810b1801114050f80040c0c00000d845000c1d034a0700705448121140c0c600e030340c5403103003441c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838584208 1250 838582958 838583023
    0x30b241309091709010801060311040b0a020c0a0501030b13050c040305070b1905090d02010c150204060e040b0306040b0711190b0a14040213020a02011b170106081e09 73
    0x100b01210b00210f0304112041108000003654895041a550307904c042c1e081000990051a0303101260310400d44c103000000c0c070500520000c001c001d100750b014140100e540d4060002c0b02900e42c014506050800c84203060684400d400d0013203034041940003180070307140d50f44028118801c80c0c00c00380c260b0080d283c0c04a8940c080900506864034110141c68800180070000c4035180a41415142e12001c0c00340316074095840794a0400849016040c00b544483c000c2403070004a034001d900c2000414100c0b00280f025140c50300c900f0400c00400e07400303840d062620707507504c03840d0880080084090161510110140c4603040081d46445a1040d5100140c000c241c10064400c031030441300d1b0541d15040c000001e10030365401b07400502482e40a4000707450381c0d40c174189950217504030001c4001103660303441d03440d400300c102494140c0711010f040e12040340342241c041d100382c030100c0160011000c2c44100c0c000e00075030550700d40340e141e22006005000c0d40e8a0b00c40300170300c9080010f10902c8000c030b10380303a01e40c03403c443d070300c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838585458 1250 838584208 838584221
    0x30302090a0f050f0f011725020102030f01260604030c0b0105030c01020c0f010509030604080702090f1603090312051e090a051b030c03060a06090c030b241309 70
    0xc540c5118002c1e81c03249010242d40240c09019000151070491440c203042180c1071443d5407005050000070700444090403c034540d011a8032144005000402e5810088030b00d8014104034100d00c001c5d441c614151903429130f036401c10712454607000c20038a0310004540c0d541e4000c05240b142042500c01c030f4100381c1001050820040e80503508003804000018941c0780c0021500d4540704103801404d80f14480c5003c104400983c80e407054140030b41041080c1813542d051141c0d61065101d01500d503150310b994010b11041030401080103800e541450240100b5102080c401c40701d0b0810b070b240c08103c0d5071f50b514040743d84104440580028505000500c2203c07803c5007101c0600c50504002a9210303951030325059030300e850844009d0041d400040d840440022030001d072075480344004c1d00321000600c09070040f03850034200b20303032440b0400d51f156400d01203000386d4040c0e000a0302045c9814402e2400c04c4000980e1315804a01d940c0c24454404da14010a03094101070341c50f41c0d40700c11000624035035078002c0366018121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838586708 1250 838585458 838585477
    0x1060e01060504060e191805041101030e06010e0901060e09100b152a0604390b0705070e0a14010e0c0403020d080721170f1504090c03030302 62
    0x421000865864461020b50307003194900d5442081000601040c0302400a00680030744440080980202c1d02041e210640c034440800400001424038150a18540d15010820560304050400581100030354002600506560b18501018642e4458155031801441d841d8001b20106904000b080385540c00414000d03031081520b034081c04030403103607000c100c4050726040406c203101109000740c000d010b43c5100f803401c07101c2100910004ca41d11440929141c035004840455080103030f4030024580300010f884c403000196418010583e2419220141d40000e541d50203802c04000020034060f0500001300001d83c000c02c0842d90542a03424a060102c01420780d00e0350048034582c03440000503c00740c2140c0d07618460340c0c503003d100d0f05003030440e400c001c03152500310010f030340301101405144045031440b1009005c11148031032104440d20301240140c42c0c08824807c80300400510020405040320840c14144d00c01201c0400e0502819a40700282c0100794806005c1d205d000885004020544c059004142645 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838587958 1250 838586708 838586729
    0x1a0903010c0305070f08010f09020c0c04020c0a02120d020a062703120c08090303160c12050702040c032d0e0f0303070315060c12140d140c070308010e1008030c0106 72
    0x5c9003d82c2500c4a41007841510b0400705004001c00481e85aa809070000c00c03c640141d62884080c1e0b0f000a0070b0b60410b01240c4116006111010114602400303046038880f10000501048406044041c0d141d00d5500d10180ca4652915403400c1081d01400300c984101d0141c2c5500c003070400c100c0c10014420780e60750070100344940c84d01403c42c0b0814001c40301203100f2051803006619690342c007060440e0301d40d1a41150703000e01540e900c0c03c0c1d00069002c12489204400351360f40540303800440c01000305480704060702c0b109051901d65403500e007000020000c020301244086007080b031307540e0092840040103161042942406010b410110117080400254010308a50b9000d0046c10010440c1d203503030200c1d502c00c24020400c0402c040d030000e4aa4080303941841003908040e02e203640e580c000b60a0720f90205201d100c54907035076041c000c01400c0208015811801c0d05602c01c1c24000c171654060b159802c180200300d21450b0b00000203500420160303584003d0100e0030196900c5042521106029203894001c194191 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838589208 1250 838587958 838587977
    0xe070c0609050a0605012612090d05101a04020705100b0609100e0307080f0d0f03200a0216060e09102c09030f030c2a0d0e04050408041a0903010c030507 67
    0x2d424481000d1502c0b405502411503950b0010508c0d1445d0300074000c20fa0001c01d00c60241021442c02d0101d01c2c2e007848145008509100c50210019000414182d041d104500c140030300070120b072000841c2c3c0e40c5800c20200002d8a9a09480051001c1c041c4101d0350703030301c20703010302c16008119840780c4043e02d4001d0590896000a84403e0400e13183c0c5907644400050390300c5100300040c01031249414942c0305080b81800501c1812010f007020482c407239021044910100000ca0714041c580c1045003d81d80b214643c642240b09007840d60040075510401050b03407080c4c140b98049140710080749829001030400c0c2851000c02c045842144100542d0b91100f02484255100011000c00020080303807094810702c0d10072444c0d655003140d00d030000d801903046080c01801c0b4103070070005421000100f50b80c442040000b41174502221000a00e1404a00c500030700890901c400d0000160126065400303a511705480d0442015030104054030394004c25049650560070710031340d000c10581540c4880d003d9a00d9640b000401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838590458 1250 838589208 838589249
    0xb0604020f030402060307090302041d0f0d1d0a08011a1203090609040e1510091a030c04110f07120906020a1a0735100e070c0609050a060501 62
    0x40340200381c48103244250070000100140307400320003164031860318242403280f240c03a038011030f044580d03007054081c0305080140301e008049410803d03950911001c0700140300700801280007c04003084280036541500048110108640d20000348030041c0c09001c0003081202032020700c90718000a0640e500380690085010340e84060800f1046030714024000d0043e5107442d16500502006080d20514241d01c0e0051400300340c0314000025600d40555111281d0b0780031a810f1944080899241440b005580b00010704080a02d8501081c03429800c0420ac80001d01c030705a2058401881c03040c4400c92207031200004800c82002442400640c0740b003101e47c0d072070a4407511181d0907030761116001c030080d04025200020b4580c070740c1160b0240d5032203442858204440f44c0062341d11000c0c40c0f0302d8081c0c681282a104200b844102054400c10b61111124080109c43d5192125103825540080e0400c010041955024403d1143c03603080451001c0c0d00a040701c0c1d00569a00300340380141000c1c01800c006243c200d01c8040e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838591708 1250 838590458 838590461
    0x1020403141015030c0311060d02030708060a0602010614040c110709020a080106030203060d1103010b100809011b0c0b0601090f0314010f050c0412060b04020c0a0c0608040c06230c0106030b0604 85
    0x340c81d8405d9100011a09644038250940c4a07650f001350700caa0200640031400e416400658014840b0380c0380c0d41c4107800c0a1f0208441c8140365045541103a140007402c1000c00c9000000040c21501034500084410a01a040700d4201134a04444018417542d08000340001507640100b80308440c6a94aa4403a6201d400840c161700c0140c56455021440c111180b0104250b285d005895090040001468440e980302044541005104603008a1000002c20510003028004c480300030030080d10403c0400101c0c00050505000d4800140442c2002d400040d103e0740241c0138400a04028109600042e541c5d151118072040c200c032041c00a9403c2020b0301e104031130180210b900811281040b40e06060409940c44101180704000740d8511751203c50440d40d82d121803004103c04084107014050704c04841c02c00c0c513003000d203681c020010040a0f904000118201404071002d58085260000e04107404401d840c41d095225600d242c2d0b01100011100b0800105500200440748184500f92032561942c04100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838592958 1250 838591708 838591751
    0x120f05012405011101060905010914090d0c03180e040b041505060a0515042409080c01050d09110a080c04111c150906080303010e0f090c060c010204031410 68
    0x7540d5039000003886198024198080c0c0516500c000064841d40d540c03440054907020384c000018103640e40059404124454100d6600103500002000c800340c010030000e0001e6500003015080040803014214200090051040102244000013840b414981481d0351401400e4404482ca0809104a0441001240201442120020f11000441d0310744424449013058903442a40c45e560200000301d1100c84401c6944001e005400b03e9400e064800003001c0c101c4006038001ca0515800704100e20311070303a403280441d806a0303001c0070b0200704e94025140c180c03e0140003880c0c660b4090008200072603c0c0c0d4002400d500088404c5405000384600702c0400c41c800d04c104040740e03040c22184c014030700b4814525000b620700d074000003080b034200a139103100010071a481c03a0400801d980000004100160f1606075480d0000d15070703040e04100c2d080c45841c0f1555003400c0c0076928000c920104038103080c00c1c001e40c140c800843d0019036040000b07049021140d11079100180e290384103407401001d034034841c0340c00c05200b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838594208 1250 838592958 838593011
    0xf031b0b0c101b0c061a060705010e070b03150f0406150807020705101409121608060f06030a11030102090d030206090f0307170d09080403110f1002070b070c120f0501 73
    0x906021141d00d80340058000c6048404003c12286c0c58041c1c541c586000a101a0340075400000b2007540810440e0700304a61036104104100741442400880d442019034882003c10495400720400c2600f404600540540c1e80268040344c01c40014106030b9400034180c03032042d43c040e8242d5405035100d00400214008601d90100010559940b803810200d5400050000000041046095240a10300c09180020300064405a4502c80d9010001c3d40c0d0204031450700302403c0320074102245440e1021070790358008aa40030304a0250584c1c88c82181c1c4080d81200c0d98250090024501150b0710b060181d0b6441043c1c801503140d2085400c1d0640c000780100039a010a9403142998003201c108010402045d0481080c0c0e2340307195580c3e80f0010004185500a10081d445240c081c100c48280c0c0d81045030070041e800c6103500504005c031503801c9959001c51038030b0595001003201621402142040003105032a50080000050313100e0202062182040c1081c2007144568003d11131544641c5200d2055500715008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838595458 1250 838594208 838594217
    0x6090e0c010302071a070903030e1f0c030905040f0b120105090c090405070b0307030b090a1407050a05120901060e07022b121a03010b030105010f031b0b0c101b 70
    0x2080840d071094009040183c0170b0320010505544402c0d45040c0c008007070324004040340e2080d000300300b01900100c403406803440c1128030708004030001d04100080c40042c1c80c00400c001d60811a401014005d0168002600000d441082031004668110004000c0c807800e582c455245814003251100301409411304c00d413840c90192806140070000c3c00715a910280c401c8416006400011a11441c80c50155202d181c00d030b0b8000c50303031200035420301180d007070302070066420035003000900b00e10480703040720041e001141f51038510340d2030140340303000c07105030003030b1410000004080e2080c0040c04005401007401c2e1035010b03554000d1501c0d00300060303039600c00c01c1d81034006c1061041c200d0005091b011740403080281440c21f00702c4007112141c1115048401014020502001c034104102c441d09003441005200d102c00c0d4000c011550404141c54001c030103604c40149140d1007940945038201d20342d161100244410079485403607032042001141c440c5640c0d1200f4012506e00305280c02d03805e080540b600c110b032005495 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838596708 1250 838595458 838595473
    0x20a090e160f0305060c1b1606170411061303380405060c030c071407320f01170403020f0609150114010504030c03080306151224030d210b01081302040b06040b070606090e 75
    0xb880023b0304048035841d850120104e0001c0070800311800c41d0706036050682c4a40c0c0c0da07401c900300107490100b6680c0807511000604100000640002141034000481d4021141c0b00e9480c4043c0358914443c005009120409814172519140400501e40c03060f01e00b091000f900030f01c00c0c12a062000c03201514001456850800071154608190896421508041c500011888905800301c1d58a29082d102200164000304103482e802500b030061980000c0b10070080c222054041907600e22600301030003080c070048040380d01003820342c4c0103d040700c00466024907800400342e500e051400451300300b25140d42c0162004140042e0181001048407008a1201128010b036104c0c900c0c1011002c03a0881d50801800d0300c01c00d21207a55904005408611480c0d035507003441e03005541e1080c1c1c0b14400091101d0445410b04a80c2c585070703a00301c00420b034040d40190081000303031004d00020f0040d1400017441c5400500018000c500708002500503c002d030301a40e410701007241e0341e8203410203ca204410211094101a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838597958 1250 838596708 838596743
    0x130f050103050c221a120c031603110c0f0f1006030312150305100e01110307020705100909050a0b040e0703030206070309020a090e160f0305060c1b16061704 69
    0x1241e011150a1074001c01c1c40054507400c0c55481003d4103e40880705c26004901000c1c0f40c9024802103070f000001641d4142182801d00610011861030b01012040c191124152082100200c05a641c030444807002c83d031a060b81052025105c46051190200c0c40c056003400b1411349200b40202c004995265031801e2010070306145000c0101420001c00080c807c40800001c003140042240c0e480905900000240d0300a0030400242114404040700d0f02c0c941c1c05004010040e1b0700410000200c58040c0c901100220020301c044580900903002042d0440c600ba0900440886550244a662100381d8040200c0c02c003054078103a4403001848000c0050348000c000130a154884e8006003280c0f44003034418002d003500c0d04003280a69440d800d1f4400c09500c0f44140c61064072800b45010018a10080c83c510202e0654032840d407507100c000d080c0c0b00c403142c001a0760425813200000c945d180c0719940b4281d6502c0140d102030311500c02110b00ca858005007510b0708c1c41400ba84000e92040c0210780c014002082102d00c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838599208 1250 838597958 838597987
    0x152b030305130c09050a0b011b0f170a0f090909051e0a0f1104140c180109170c0112060608162a061406010c0b040c0b130f050103050c 59
    0x406454402d40d601030203900140419102401070201c60ba408a21032801d10b5040303007122003810855040012803417105000d1031038140d1000f0003a4000e90843c000b408070741805090000d00c0101075070381c1c5000052007103000d40d02841e0007145200316500d48800307a90fa440c404003a41d01c05500a0040d0b0000540c60000d040e9000751084080010010350744414401d0b01c6051f002c0a0b04641580c50511041401c80b0700d2429100305070b00d9054004072000c990078080ca00e6902809201c21150140400c040c40044580c0903000500040a2041b000d00078094016450750311a03403080d5406001c55240309030144092214040d24080d00d4582c1d4925845d40d0f00c012000300340140021030728041c4000f61000a440300c01d2081c214060f9050303080c08004680951038448110717051100314002120091061010507070f0301003650310a2a4010b0700e40082c4da1594104944000c401d07500400d100d0f0b00c000340c4103111050411840301118804802c40e0405991a8010740550704122500003e100e410000c2c400024401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838600458 1250 838599208 838599211
    0x61503061e0c020d08100b0d020301050307150203040e040f02090106120f021905030a201b010c08060f0a0b04080c030709060e01030f03031e0912020c0a1a090603152b030305 76
    0x100406d070400603940f480f120026601c00d0118400054001005000038101044810010f000150f03d51500c61038581001f51139001d503010f90301a200c4036102144c244043c6842184020303400818282032540d40d100c010b8006002c04010301c6189041200c408030880c1c0d070788240c0c1c0080940d0040c00d900d5140c000021070306a48010b01c4503100650741c0c1d07d100c41e0a82c40c41d14441d051541540c0303d40d501c80614105c0c0315054099100050301da81000d112200c1c00b81d04c9214180c11032002e55524003a15040e100264030800700d40c11069049001080c00103c0b031000040300000c031802034042c0c425160701c9050460903034102d070040d00424402080100009450305903c0c0d18250b0113458001000820700d0310107184d21060704a0150140d40725440c9505011140015002c80b82e20f5000078880741c4c5030000481d1584032507100e5a450203c403c120020724000202c1143d0316034070000c161503501e141c1000d500b4005035403c0b51442c020482d600c0140c0c107840c07031118407010310814902d4000e101105a502140603060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838601708 1250 838600458 838600471
    0x302060618060105071e030e1201110d0b040f330f0509040203031e3103120903051f0501050307030f060218030607030c030b040b060702040504061503061e0c020d08 72
    0x4040015142030611b00d48984a4420b50f280c1300100100c4013040b1110044001c540466450b1041500740031070100119480c001c41c07940c01044072606907000800409160388440350b8281061041d8440d0312014440440c4caa5201101140c07040514012440e280000c1c021503000c0700e401c050500807490110442c40e031040c40142100d28110006980805502d85600412b110303c102296040029010040e140c400201c1c50a501680340244503c00641c0e80702c074071019007800e420403210380d4418418410640a513400001f10b41420a1140b161444064140c81c0001d0951030000081414500811000304907500300c0c00781030782140c203912250003d60000194582d41a8076030040340c100d03242407042e107101f4180b40e01c0014a0600800e400380949001540300e034459480e1011400c9165a14002d4501280d01940c00003019555032801a0081941c04c045041c0111210300c00000c1207010b800041d1620306941201f05224103c900383d809a441402a150140c2c01c640c98000c60288108102c550011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838602958 1250 838601708 838601723
    0x806311808070803090607050a211d0703020a0b0c100b0d21030506040606021e10110403050d1706240f0703020708070509010e07090b0d09030206061806010507 70
    0x36055a40c2030035a401000c00700e50924020040005414040c01416480032450810600d050000d0724001c2521040035440c4070308030980e540801040d9100d50105801143c0c803c0c8010005180421003680c0d41c06922049100f07128202c0003003091209039043d900c100035800000c0000d000303e14040c90250000705103154000c508591000f02195002c09021900c1d0303200c12112490586540c001810f542009200900036800d04404001099001410b0a0700f00340320801801e10550251140e03003400060716043c1c201904100f86614004a407800410803a0711074401c135500c180030003c1c180c0b0401080b00728000700b50354000000c0c0700c500f020481300a2000180c14401030720710b402941494603801082c0c7d1040e04007408501c1c80c1c1050b404005031005003448c44010704002c0c3c540000601502070502500c0c822601c00c502141c09140205070a4000d0b2009028903511a040024400010f02400d581036005120301804103895003402c1c00a4460b03400d50f42c0000e50140e0b107800065507264040002203d511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838604208 1250 838602958 838603001
    0x14100803040e0a1b0309031805061b160323010507090b0c010f06031115091e181f1520120d020a080915060f0a090c080631 54
    0x30350326160304c00c0ea81030698500083c584107600b0300404203802c102114444404458043c031869039130300d0669004051f14440b5003505659030000504200040e03004800d00488004040100142d0041d44051407403144030280e101c07960a10703100c4c00d884d825a41c03240070917465807080c00401e940c0ca00920008821400100d02548103080d1402180c0441d030080d604400100180641d525000300d200440d02906810541002d101d01d000070f003240901c0416002d048058070360b48445456156101c508150566451a4a40b03046d103629120034902592260b01d5100c10280826155011242c0c19007140f102c0e5562080a5601c216000340d0340100c00484002c0d00ca003454600300f2410309001007203c5002da01000da11440c0d400701c00341100380e01404092039500541492404000c001c0000780d0700290858001e682210244085030003120290008481e0300d04000140c0c0d00c0301e80154170f45003c0c000c10345040c240040099100b80103c0c07030046102412803c80d8032049000c0d98030780c02c0030748001d80500b0340d558131 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838605458 1250 838604208 838604231
    0x18110301122315090d0201020a09050405040f0b041101020712050a032001090c030203240a27030c052104091113123c050a0501060914100803040e0a 65
    0x10403d0700f40360214011100310400c95031210900c81c80f0100038081c0020360400405070005403a0000c0c50090b240915503900014090140040101e9150350300314070a40a075040c10704000307400e00c0405200320b000d03125144000a141e02000504501036030007401510f6180c2aa60b0101c4400c000711075504002c010544802014403000c0c0b040084062082d26220002440c3d44149800d03e07605a5940459000760801804031005400701e06070321060035000090f002040050818450740154601d40d400c040c3c0600c52000c164005113021001801035084503168000b400240d55201242c1c8410202c900f02400b0810104050b90000c03088000440c0d150740c14000d941444014020b100c2e84480c0c1c550000100e21401d010b80705040034000e503140c84440e6030800340060050750000400c240c501e08500e801d20711209004044c08074000385584040207200d6903540700008070103408070101d10404028a40041030041141c0c40110b011106c5800145082c41d1a0050f13841304168001c10505146464540072040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838606708 1250 838605458 838605463
    0x206030a09061109030714030d0f030212040c0311040b130207060b030307081213080901210f020408101530050706030b010516021c0804181103011223 66
    0x90343c02d40c1c4500da070f44034065001050b29040803503101c0104801c0c0701b18400120f85000c0742070075140b4a20b081007444c100c803013030b400c4009208544010301003004450a0000300812a200c1c80c04990003401a4224614035004200450f180200c260354020519201040700d080140c01511480780254000250070380d2000c0400d0640d4480307a0120f82e801d5002a03458084c502c20240d054011003142c070003443c40042035442c1440d80c0300e056112810700200c040094119000d01030003c0c00d824070280140120120800a54060b410600412007240500000030600550038450100e2000c0c01610821101c0e00e014518200c0b181c0700c0810114020394424a01e0070011a500c90001040c4243c008043c10ba10309180182200d84038618681001010444245105d00c4d0144034600590129102030312942c250340b15640d4a6208400104000c102040c00214607502d02c5d60340c0a002c61401044c800901d20700240c04036480240208a0071500c80c403002004030744422845003440454030119400060244242ea1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838607958 1250 838606708 838606721
    0x114041205030a1701030f0201051309150501020f03070201080a0b012a0309060813060e03092805040905030d020f091e120f0c01230c031e03130206030a0906 69
    0x1e460740d100184110a1a40c85001916146400b02d403400c05541180c0d690031350010720b00c01c043c0c10080e000c030700010003000c00c0c61620300400c080c04041068068803c375130440c456240c41207d0146c0201070b04c402503d0000300031940865030584d65203e50f076031001c0004004001003a03015041000c4d154085a00c0d40b100b500c03000041400e10048501d01d00a4640100042126003121080185000910843c0380c0c0801c0a003030307500d0707010700c020515801c50344006165004240441e544040d545c0e00509100a40880100e088036461003140c0045440b40180320544501d070000514a030b00030000f40c0740810a50303000e0710030f00d00100c1b0b0862406141c040050281141e400000320b0003403c8a81402452030310034107400340808100701074103503009040101a210038040c03041c541485a5000d04407081003440d030000340b03620b03c04a505038995a50341c000b103680350401800140081900c0e0003c01c2c11968034002d4a211301003402c0942d030a80c40650904c01a600302501140d83e45444220003000208a4014034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838609208 1250 838607958 838607963
    0x120e0303040f0b0105012303130b07171f0317040b04090209010831170a03020a1407020906040b06090901090b031605090105010c030507060e010f060801021801140412 73
    0xc0110030b06090b080d0043c1a840b01c1c1c1400600540300d03003003004801c0c808418805a440c0191680da500b800390340c03070500c1c484005003074020540401240d0794104d800408400440aa21034844c0d90304d040040043c0501090591412144502000029000c41b03c0700280d009580c0b81030f080c107540d401107006c03507040b94104207620b43d0040f644d450ba03540e03c5010b85134001c0e90300e2303103610100848021104501c140004035090003070902da00d80301440010040105000c5512046c960b540040c948014001d4203c2c81418000560342525009200701000c25922520b400500c103031481d444003020840205840c0c0c0000d601f1180a114554503552100c06a0b8000c2801c00c2012403105449020141040114102c2111203084000f05108980794800100d054400c20308002148000506040c1d07024040d002c402000282000b01c070424076501908074032041d07803803200305000e05034031500c00c5801e0303008881c01800a500c0515900d0915072144540000c85000e22088074a41522525014240c0350001e905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838610458 1250 838609208 838609223
    0xa0210020d0b040c03051e06060708030405060a0606080f0106030c0309080c06070f090b07080d0b0d210306033306080303100e0601051605010b2115060f01120e030304 73
    0x2d40756141050300074807440d850613140400030f5250112200c58282d42800c10180c0350480c070130002e080383d1251022a88004e800c060856141d151a1420f0340e070b100b108980441f1920f00380a00040c015024030202e90095030f4580e500840750b03003003000442c0140501079030701003007544a8602c44085000d040040010181c10009403503075140011010f0301300c201c280c942e01c2c2080802c2008001c422a00310503a1025980200d1a594a45030700c1c0c0c204024191000c030b01da50110482d040001080f40d00000d4990708450b200820000040c87c00c01074007201e02510002d40b80710f40101058141c507407500b10751058008580010068040c0d141c481e81b0840d00780ea000b101482c0d20002c140011a5103201c8060020080c00741ca007003452404400080c60b501511450b085042240180030040000c01c4d08001585000608001c40080b0110384c403c06611901c51040c2c1300d4001c010707502804075420030000788035400140c41b0071103403100d80c1c0045a104544045c0c44851030790326201552030203405d00040d030189010320300c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838611708 1250 838610458 838610471
    0x30a0207050118060c33110703090608270f010b041815090602030708070e030a02011d131104031b06020a1e060501030b1905090705060a0210020d 64
    0x2a1402040e5002181440448520003c1201c01c240d41601544d41c40d250084c00c140d4503140409440041460010b1000403143c4240f441c20b00e4040c00340304219041105204501101c560f200061198103006000140d0021003444018040c1c08410380107060f1811403441003e0b400161000310000c0107440300e50340c0208180c684994024000e4161440e0200c90810158000780001f00c0324400f00580140001e2500300500700f42412a0301a00c0520340124095603645020302008081040464844c004903140b481c04c06014180082d41d03002072907040e11542d04100020113928801000181e47c641d119503042c0b40c25200b44420300030403200307114030720807151114114584000c02043d15041d0318000340301d0315401c110a6030300103000220f4641001034403c440c0702d81c542030440d50441401c0035003241d08200000040001560440d485480d03031044500703945070b44d10051401d4035020b50b09024154804034043c8a0307894404020312800380d10340100d030310080c5030401e001c1c16604480280f52030380d0f03603d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838612958 1250 838611708 838611727
    0x90109181506061d03031821010605040507031b050d1d06101505030106030b060d0203150f0303130905060a08060705130b190c110301090609051204050108130f02100203 74
    0x1201c00885043c04c40c6030300713070301d01200d0f010a5a07405000c0d280e101c20790307104003002043c0e15100065110100d92000201c808041028418082c01d560300ca2a80a0f07490400058201e83c8248508014034034040c954605090514000b2501e0f50403295004000c240e94401c1c1e183d00c40c110b0003400c0c241c0c0001d0000b806840c50110781100f4540410b5000000164004105503010b6034408200d0341541c195080016420800780d000c140c2c94001c100c03140300c1c158070000511010300c00c0800700d001110400caa8550304a840007050545a02403000070348402c1440c184148041840d64124079407001c4042c20001140c0d40d1843c1e2985442415240003000c1400068440158280d042c80f40d00501a01c80900d840d1000a13890800c40028500721344081010004280003040039081140303800040040007849050180e09140008282d00b2000300e4070340c49464100b054401010b819901210016103e00590386e0712501543c07507400506d402107402e100b6165440c2c0042e960f004030105640026401151075840e0312 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838614208 1250 838612958 838612967
    0xc032f010c11070e041703180f031606204012150e0c0f121207060b0d06020316030e061603020c030a210b09010918150606 54
    0x180001010030003000c19954101500183d05001c945400001c045a0741e501d0800b02d800c0c40358440d108441c2200001402440200710540702011740380a02910501c0c811901031310391300e10a40d0010b40700201548030001c0415402e40c444074901d40f040821a6014090900c1d0012544c040b01400e01209122508101c11234041c1036400500c0c00521030f15040807651a061400400306c6105200d5082c0f82080c3d45010440c242072012007649020364144080a9101d20072030310764125542d214001e11030710078038001c00d1070b0440281201c001844c01a00b0214442e05580781039600c484410703038400740c0b01d12031810941c54400d1004000e0b03015040042e268180100d0159013404952800010181408101c100740c20007c1202600300030220003c0c1040c20080d641a80030340a1038803c980103000c04208440c010380c102d2800300440c00c41356012480c41c015071007018221000d200506030080500c03030041c04540013039031203442c41402003400f180a42032150340e4029a54203c24040002d20b885031010859603800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838615458 1250 838614208 838614221
    0x22020d08040f090207020f100513142e05090a031203020703081806072a0f0605100602030f0a0908010504060e07060c0807120c05060a0911011b030c032f01 68
    0x3c40300652a02201d6000501c040c1460b4070318034451441100c04401c0203000e01d044070542c000300306000881680da40c66101385a09040d14060141c01c102460b460010841170040303059011403204236403544052041101c1c03540101000c550041c003225000b20218041400642c094a02582c0240c0c0d030303624500d030042c64480701408402400200500c140b80030100861541d23844651407a080c6000b4440300100f129100b403039500e14182080907071581051201913100c00c2c0c40a0301a10301408191160751141000d040b90b8440c181c01038006000c802410b45c0003c0090082c0c040390f191004038640c440f1111403c4540c107490454206590303041c403040154050010707200600345070403d400094059110540079201e0760000404050510190900f40b070b020302c1c1e59400c0c440e0800100c1da114980002c1880090011400036201038501a907614629841503184250350242503084804264440d40c00361582c40c5004002c5044c0071819402c81026001606085200100100e8940321000c1c05010340d800c40c2e04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838616708 1250 838615458 838615469
    0xc090433020d0c1b0321020a0e120a0f150213080d030b030d02190501091a15040b0d08030a0b0603241005041e08030a120b0d030822020d08040f 63
    0x281c600d851030030f80440521034031080790181010a0103d5252100c1c80b11491000400301e80e40d480800c00345812170327014524043d8a003050324051402890002840d40e107144130f410003410205032041403000110004400190a04070780000b60800d0100305503010030251039003192950b980003c0401c80c559034180550f52244c201a00074004030315003081c0c000d49a400088180a5411400410000b049401d502050480c1e40042040c01840240e201c40144507005446403031074082e0042804415103460b10841c101c185004000d050f001445580f21807043c0c2008001c50401e070743e51101b1845039103900b13004500c038900c64400c1070200c00c5070040800b50701e100d6001c10784c020b1030a900812180707600802100e0568140c9038100100040040001c8240c1d000c0703030041505400045030f01c10000390022440ca610b81600c000a112480e0024148515090107400c0540002d40c0030011440c1c4150104002d01e041d142075020f031800080c81d4000c01c2000340020000c070340c2040c0004042100680d64510a4040d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838617958 1250 838616708 838616717
    0xf0f01110a1a062404050d02180901020430021c0b01030503091002070803040504091502040e150301020711091b1207030e03030403050a03050709030b270c090433020d0c 74
    0x7880004c02da02d00d40168007a040c066010360002c40d05550b41e4849607503002110800343c1c0e42a107000781c0310501075089807003540301d004041107980101c00c81001031209448000200c000105030b168081000007c0c00024540c418503a4105040104005000710f90203103004200943e83d503141c2d0740038420604c80512100045400c000e8041c4400a0b020048804450b4101c0c1c0c046400060350900d02a800b80d00c144240100b8800540043e9a0030001d24241c45074a154031034a00403509281494280c1c03084400040c1801d003d03030b540003490311348804104e801040320f24000c0f140c01c2228003c1426030380400410602100001d041040c1182e15014190302c580084000e5400c44c28540d801604a00802c404903003815280c00009a20910900c00d10700210b4120010140a05050154070584d0702240600d69210001c203010b089001d0b0006034440105101418980e03a0f82c0d00c40e245e40440180041684810b2280f2004986c801c20340c7d03d894186004600e940140c0e0703260010b00d19012145a400007800f0712 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838619208 1250 838617958 838618009
    0x50106020d0e030c10110d0c200105120901021603020c0f1207061416060f0f0203070512090c0607030906030507020a0c0308090a081006140f0f01110a1a06 68
    0x640b401300343c058102406072154054610000001d5404924145a00a05100340019003c0841d400b018004215006074240d002601c0007114401041c8200e04026001c118200001d0414102500341c40da0700c00007010005081100210740e5880c1c0301120301e000e40041c2c1c00041e201c0060703d0318008100c7d41040448409424103088080309803a08035900c60041407000c20504c604507074040c21b04451528200c1c036403100c5010ba80b403801400814034032900c844600e20b0040000b44011380c0d4400c49000d19510b4590904001c000e000e00705e18154000d20710b01c1c440c016002403010f5034031080d003c0c10b0110f2103515a0f01c0c00341d003040001421500000e140d88210750100003030001050049515000f900d400600c4503654440341c40105100d000640e108a0440c0b0410806149428480c0d00101c03d4805510300c406c22111864200800c1411401c1104d84c03000010b07070b0341000d5600071010030aa44031b070350040c0c1c2c4c004451511034184403414950180144494202041114078120300340e020409401131602c41038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838620458 1250 838619208 838619237
    0x8061608010902032a30100501091e260d05180405090a05072304110a0509030a0804082103090703060c02031314091b09062b050106020d 60
    0x6002c0300c1c00c1c40e07003244881c0055544180c2038000444401c01b004091400d1081c802e2460341078958a095035204507a45100081030300b242c81c101b4035000b214416900d4070071042c200f480c5c5448010030442d11405403103801d100010340f080364004d48500e6081440c0e410100c1c0d01c4481c0c0321803c2078080c808074000c10100b0811032800402070050f20021400540300000c4940c3ca90808a00d850008400a0b00e140700b20900090b0030140a04460b002c1c1095101d001350024221040c4403e848054039801c0441c2c006024407883c19225001400340310000404603078244200391a010300340e6216410100b0b05801c086000d0070b161030303c801c8100c0c01995160a4900d07514003004901e896920034040100650b40710389608c2c0c440c074420829508401d00041000c0880d598560052464140c2c0c80134913401099000b002030502540c0c90f0140030780c00112a107103490b2a1128041180c0c0e07900c500c1b0070348084c1c550503404912180c0007003600d0b4641d118040c00003415506155000c0c0c90002d1800340e6030100320004194200c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838621708 1250 838620458 838620481
    0x1404020117070f0c060204030501021b0d18090905010204050604060e010f0f0c110112140a110f03040b0c04090603060e0c0406051003090812091501150519090806160801090203 77
    0x40c02000c0e8540044900c900d17140c014064819513101500b0f56001003109040540b84c40f0300c0d15002c08000381218a10803448000384c8080e4601c1e03540307040140c0180b0702004412a03035049051014803c01c001450151a5000180560000d4000c04001041c8151080865821084840400180d800c00784040a222100141040c60900780104101c44100d1102001c0e40503e2001450703000418081c8000040740d0641c007040e21040700c01e200c510b03051844121024880d001254413403c03280f8001480d555840d224401a4800a001d540e800782c410000001e000099100e600c01a40c45031801048410307141c0c003c580f07000000310505200c1c500d04802000700380d5405204c080d007140b403801c02180700421b07400c12604074050804502c0100041008211074843c0100d1001c00003c1c10400711402c1e0b90700e80b4010070842c4180710402c008900e00f080f602218400c80e84c4004035206540c078144060701d858501d014204a03040d24565824017110000411294004200c0ba014090b522421400c0d854250103800d07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838622958 1250 838621708 838621727
    0x50109180204020706110a0302120f0106020c010f0e0a0b0c100c0f03150f0e01152604050a052a0d1109040c0e010303090311180705030712140402011707 67
    0x902c5940e000644e401000020381012454841c40c0e107425071914410701005d0044d620440d00f410702400540e0000d140354404400700c60503200244d000f0240a500b404c010340d80000c0328000c150900c17401079001c2180f5130711207544801500c21000710688545201039000d18103600f8600d00f0034403134107290301741501c035074007400e022201002ea203008554044040c100c0d1049822541100b00ad00765a4000840c141460355010760403902d0140c8104c1d091041c0b000201c0d074204444822403002a00540c4903220380c045042d100340c0060203403045d5039101406940d02c034a0140201840b80c2048944a0000d40c4114a001144e070442802c4ea07600d2a00c005a42c0c48c9802c46540c440301e0b900c150341c503501107000e0210401d925009050f0001c1401c20650316410040c00194140c40700310b0301d100c8420080c810314140100d180d050f102c0442c0900615896940c0e05407000d8200900343c1c4100b142002048024030b00300e02500c00f6034460244c5011a80c18540001011018800318807401114000700f40709180743e1024044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838624208 1250 838622958 838622963
    0x20c1023070302030c040f120b060303030705070f020105041e06090501091214030708070305070c0b070503030601081b2b0e0622140607030e010b0d1416150305010918 73
    0x50780c03556405d600200c01e0190b50010401070f030084602041010344035080c45481130044101108554a031000c01d50780b8030046030b8800c0018000d0114900140110019480f014414103125003001e80704e45000e0100e10503440c08805480c02e0110802903260001c07040380144c142071802c41200703030400600407284514040006c0405404007070a451031a800d0055030002ca40c4a162943d40341800d06008040c0d030040ea00035500404030b048005416551803040300e00d150743c054055421983c821b001552880b04c001d008901409110803884841c100c01c000902e4070344021440e00c1030000c00c080d551036010080306250909980703040311010560100040720b40e4405000151920380203043c0c0354500680d8540140100040d800526502c0c0d8204c011510308d100e04602d81d007c21642c150446614280d890010683e50040d107003a4086001c41c8211181011403a0f6500884200403003500c41c427003c1400c0f80c5d101482c038040403140c0d0700106030b041c040c041c0101003104044c00078070b5500483c0c001e44d64819100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838625458 1250 838624208 838624211
    0x8060a05010f051804060b21010e04120c240e0114091903020c0904080c01051f060c030e120a0506090a0b010e071e0207051302070c0b030c040801020c10230703 70
    0x81c2e41156845c0c0d0450b40c05407007002c468544a142c109000c0031901950034070104900c03503c000102d51041000c10f46803003960419400c001d041c02011081d01d103d10b2176041542e8486600c0b2a00091042500c40342c1c40e200740c00b801c00191132030443c18181c02c59610200d99004148103805006c0740000016200400702902c101d5001580c081303190036407404100c5441c0755003000b0000c04110a201000c1e000d004e20000101c000c2c0003650342d1200d4054210079800e10f410070314484200038082148220300465004e4420304140d01640a0386000408042e49144201019032092000f0410001c0c02d200c100c1c1c000851400502c1c4206483d950180c04c418140940d69051340c60345c002820540c0b10f5400010384181c000c02d00c030f00c12002004000e4844065000e130700d004481012000c080304070301d4400c0754861030700481d11030039081c2132034240b03e00c551011b4223130414881c0501010500705801e100806440820308000c004440e2100038803000e660300700105211244242106000c0800700000300d55110105140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838626708 1250 838625458 838625497
    0x120c03170d050f15030309130e03160501050106021e0c06070218040b100506040315050403021c03020702270a0b120f0309032104060c08120708060a05010f05 69
    0x204026005503281d1a118070306060074891080011501c5a006901c0c015940f5141c545003403d040d52840781d0440b46802019545002c5000e1880758400c81c0d84200300002ea83c601a0411120104401c54800170b45407a559130713004001e05a010010300000c440c86280300c6140c004400c01c041c2d00d8450140c5464080c0c98001f40c2d000c210350f80d4000d20304001c1a00300100c81d15013000d00b005c85806c0d40440e01140e60866031100410f0078034207602910100c0e41e1058110508209511a040c090000a00200c040d485101c08018090440808505009109640c01a242d40d1240100003540745850b0303144040da20104d250007110043d2000042d481a1802800300d40c16900e0b0b0045110246801c041245601401703605041c480ca0201c02080350000850480d80c60f02122950040e03241c03400c2d140d80390340b4a010001080040d0242040c86035045c0078515090414510103121140d10404440c9080041c8241041041c1d42c5484160200540707002e03e0f04141561b122440035000c1d01c1030350661070031800400f4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838627958 1250 838626708 838626743
    0x10e0c0d021c0512040314210706093801060309201809031c02032205120307030c110f071a0903030a0302070308010911120403051303030e030106120c03 67
    0x201010b420342e1400e00c41a5210b642c1d007400b0b01f4101001b00a10818002c20300c819148886c400c0700d00e403100062145451a01000742e072203600520302060115245510000700120308080840400f400181c2076882e0040084000110100003405030010024585020140c00101c1d465540440e40d0550409980a214401030002205a0f84514035440108156003c200000b4404805041142c0101090740b02d08100459520b0990104450390160420707106a8150450300c40008461030b43d000350151060340d60081449400307540b04696000110381c0780c03800e4002c01a44071f8030807031107080b140019203032101e082d143d9240c0318042d5100e4481c882801c901d01c004805190412648034260003800c4a9655041c030101501a4105213001d4000c9142c0700000101115280600c031b6142c0c0d100210a0724082031403420049048000c0c0c000d03800c029040c4107201d0100469241c2002445c01b9031942c0180c4a085030405003560015002001c0112103003100e0340c0095010303002d1006036a40314000b0040e551095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838629208 1250 838627958 838627963
    0xa0903032a030e0f0a0305280501050a0c1e0f030b1503010e041e050c04020706020c15060a0609050604170c0307090516211d0f010e0c0d021c05 63
    0x81a90118012801c4003030401c05400034025142000203441303054180b40c0290820454041074400a0070301d8000c0f01962403c42c10950b030410303500c888008481079080e0f0301e0720f4407030858070101d550103001562185140329441e00804c45d103803081184400d1f920110031080e8000c1c1302080d8845900b040c0b5454000181d1709580c0c1003031030780308a500011520340306c2d80c2d6004200c100301410759040d074101003680308400703403000700c44400400640c01c03074018070f01190500c1c1800000d41c0032030700507134000da130a1040a140c01d038244051182c60311501d00c666840c3c100101008800030565000c2e0081c40b070510b1b001c0003951204800c3c2c07400c58129044201001125001031800d0250804115074103019812010030000c502d64811270007030b00340d680021403d1001c4007087e100c01010b01d00c2542094801003880004806c40d4026000d0250b442c0c00103400b0318000c8003258601111207561000f40e0b5180d6040d500880010410038109400484101e205890703644c02254a0f49003940303800711100c070040142c10920ac0d08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838630458 1250 838629208 838629257
    0x92403030415080117010c090308090d06020d090605060307060e010806060f030c07050f0619050405010912030f150302010503040b250f1b0804091a150c060702030a090303 75
    0x80781039142c500d08070510051407000c0900072062510354114248400040510462022001d82e0300c0340650141541c8444034507410407001d460340400c0000041c00092414000381c8100e040000f408510700c00285411016258000c00390350007a4030048082220691288101601c4030003802c19842c0c60b201c00c0003003829485581140380500100200740802500a00000c0161600603020b4074507085c0c2d00e00101e902e070b082c00e86240700040c0400b0303540f507045009988001e410034031072030001900f02400c1c1e41c2c1503908172141c0c0080010035550304039403200c0d014030f014184041c007004180c9001c40e0b05540c000f800c54000980060900401d00000807401e0a01f40340c86c0e11b4044001c8507280f901849901c005003040180d113000800281e10040380620446001581c0c81200d91002c100c0342003509080030325005240c2c0c0f502244400d01c0d0001001e82c20345602d001c400c1810304c002c000135078030300c43c0081640c036186028051b601190310800108003400d0780100b144054079458544034043c00c201e281d2000c0021035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838631708 1250 838630458 838630469
    0x41d01050106020c13020a0530010b0a11030301030506160203070f0c0f24030b012a0c050108040803040213090b070908010501082404020109030b0907090b0924030304 73
    0x203004008034185400140c1a031840d00c048a110016804001c540426801a880e000010500902518040300540e048048482ca80d000c4040d0001c130750000c46c09014013083e400410022400905c800000398046102d900d6035060308001c1d4035552556880540e00e000c010304440c2460000710384071802910900031698204e401c0022038807603020a0030310f0802c1d10194442c1941c00741e05a0400900c54000c1da116031b100070452840041c0540030304400f03a02614081b00c885040008a15000d004542c0014400c4560383c4a42120000003016140c401403215080d00403c1c1800f04000400c03001414040460394070550644034001c69008144800c0080c04034404001c0036200c0c1c0400300404683d02c510418215002039000b844682d994040c43c644071000403600038040b649803910f00918500d0004c00c1d42c0c10502c189402c0c00740c1552911a0900d00e04242c5011409421110301007011010b10300851011050456118135241440b0823001c1c4110000780030b60ba9004c28245a20000d43d0b02401550001d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838632958 1250 838631708 838631711
    0xb030d0816111b180601020c0f0a090236090417070c03121206080a1b09090f0611040605090d0204060305010f0e12031b1c060b090f01170105041d01 65
    0x1120ba03e80001c24011a1405000f495106550707180f007011078182c2c038014001070300a005040e495a0910030200800c42c411a00020000800103505800c1d00c02003001003920920040410305800e01d60750442522851090ba46031039a011204980c0c40503042500243d20240342810502d000d400d051850003031200107441003181d039030004180601c41215a0070002643e403002c04008101160004030740c1907000d81c6002e54020300440000550345004405980c0d072100700b959503903a507a1000b800780c03042d43d18100d50081021720340078100103032406034503003400e108015542020f0500034010158044c0c0110036200e815600110380070741d100ca0b844200515003090081c8481800400c0311800760101846103050751217241809035030401d200085e80d001d140203011100481102178082075450b0001e00201140080c203040b90900b000705807041d44e0080c003081c2c2000d603ca11024080010046010383c1e4a13051029550318041100c900c2e1034520305480c8111000a407001a201e42c00b044c0395001c006504166 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838634208 1250 838632958 838632973
    0xe09130c050111071e0920030109020d020c0613050f1504080715050c030115050702100302250c1508060f1c1a0108010605032a0112140a0b030d081611 66
    0x1166084040130f40d5404c1b20140a00c0c651404542208081a8420400c1c103d040c40140b1000d401e640040c8506007911a001d403c002c03404505d103041c010262140c99034400860400000c200c020700040100e600c2d00f03405002006881036820160740c100030401465024001031200c100a91610b4022202111403010041850500c840c48090b40c400e01510200651030005806507500c40d104855003158060008820044655070030340294010a06031021507111a00d1201482c1c00740781d454807100d00403101c000b003007850829410000601a650141041008410440c55490361191404103d005940b5800d82f400409a12291007480d4480200318030540100d0003034003202092403034142e8501200800c4041d40da503040580c0e03080d0724149403461300019070741d050107030000310f1240d80b0154060404501140c41c00d005401292a620b401c0458106541d080c401041e0b014464040303560415402012000c4609034050441d8070000e01400703a5610002e003002490f48038501903202c90006070112480c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838635458 1250 838634208 838634249
    0x4020d030311220506040f0b130324150e060d0501020c0318030708010c1403060d0803040b0412050f0f090312040e01080105060d0c0303031a030d0e09130c05011107 72
    0xa80101e08080f07140241c2040010585103401012581140c5400035900c0885203070103d8102150050300a0300040c9440000010200e400c40c001c075007640000301003240c202c2e0742250409041700c2009035000c242591084e0706029001d140a141c80d0402c0c03044500e5100680c2d20320303190740648958110b03030800340030109025000606070445101d04c0750040302a07900740c3d52503440c010700302c60b500da0f4284002070305104000c03403c0b03a126004540059014108444c10a0a92590307841070b80151411580600c400041006002610809004011091426a01d0004076203605001d0380a244419540c2d140001851140c0703a50400c28129500c0c8003040c829107d66617443c0190450000f40309602840d401c040005a9500d000540204d000d940141554042804c2d610120028560380d04488120004100e04250755942000418000c519035511014103075018002d0111260700941054800e001e0000a600000d84040c908000d94000f0300c0d25074540e040032403c0500d0540706600c8040603001c680760390042c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838636708 1250 838635458 838635487
    0x603021c0c0e13020a0503070f0e0d0f14060405060a1512050d080106181401170103140d0206160804080d1a09070507050d1d130b01110a030804020d030311 68
    0x32025030481d118004440c0c003e0b140341c02d034410040341c20001041080080c40076400f441d010b415924243c0f400d401d08039400004140200c1c08104140c0e81c1ca088284100304100041003e02c0802c503403200070304094109991165a10f5902601320074403a91141420002c0e41c49a4810200030310300d81001c21501c50203402c00c99261910104281d001520110000c103c05000f031304090300107201d0003000071a06181100350150a121040c206040065180b50800c0750704500b40624065070007059080340080c005000300c0d141511034064003055401560400000c66120450601d8040c81c070300b40440135035034a2805000511441d628031340c24034604005096403004e03010300400c2881c4183d40c3c195107034880d2502034505018080700200554041e8000400642c42242c40c2400074201360030305800c02d10a403002a00c0e41e80312000042a04d0f603902c156542345d44c2e204035842c1c540c01c42d043c0501040080ca840040248800510180c040d00f2654820400c244c070030303840b403002e0403040c05d00d15844a04414000d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838637958 1250 838636708 838636727
    0x30a112b03020c01021219110604050f0d030c090b0304061b0206060102010513080711120106030312050c0304050703060506012a1b0f0e060d0503030c0a1407020a0603021c0c 76
    0x400611443c00000080e50001074180c0307100c1b40c0e1400541c00c00401d2003000003804d260780300038020484c6140c1160072400c0c0410816000d14800c038050302c071590883d0000c92500e82d0741e450401c02c150031f018a041d20a90400755504c01d072041410525542e0b5100c0c140f20740a00103041c0c12240d0f010807041043c007a140d001c54510702903142640280000d4441400703039101d02c2d0b143c0102400c003580410540c4001250112070b00c10550015080d200d800700289451401c40750a90b2050300451400c2c00c1514400384244507446d4060303409803c4c5415030815460f1160341e0045400002e0640340c0d01c10100311581c0c00fa003030305580340401c1c4054a41858140e010005d210b0b5900c03c040726851305440e0704d44801034131900e006090321040140c281004c1d1803d5013034000180c02030801c0f034001c1e8643d0640c6020500074002184102168190306a0350b13101484010080340900103c0b42060400f40704550042e0384030703030b80c003001c1f01c100d480c0150315170304001c142c0080d43c24280081c03080301b49401400c0c203802c0d42060511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838639208 1250 838637958 838637963
    0x1806070b09011109060f07020d020a0902070c0906080307150603020901171c0e0d03050912061f05060904111204050106140a030b011703190306090b0609030a112b 71
    0x3d21400811036054031650043c09091503001905024840c010f420b40006804001d000070503484030295580c0105854440c04e400c03000c00f060b00001c0e0b207001e000301030308040010038000f00308104007071900c0e409a88901a00c0301c02081c0c0700b125180c28013603035802d4000c070b006550000c0416101d940c2d5085c11008600303231404402e000c4e01801d200220419030080541c010f160741c0f52110150107150000b00481540e07030341c0c01103003405828814403d96840b00310003003880010100050040d401c0c81d1840749000f100741c00583d4580d9251007020706c42078499005403002068140d9002c18000f210a4101400c2d00031056000c20603600b0074100300601c001500035004a0f48404209030030f820707a0301c00303000d84051180800f403c0603040000400543c500002140c0e448109502901d080c04088510041c0341c5002040d2640003d44500c0140400c10380c40c8555108494200e480c149840b05d001d003c40c2d2525403110b000760402c55a007a50300f1451301c4003a04442c1d01180c1c508070801902d010040203000e40314803a004d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 838640458 1250 838639208 838639211
    0xf1806010603022709010e09010914010c110d050a051812061618030f050a02060a0c0209060a150e0a0803040b1c09020105031b0922240b1806070b0901 66
    0x18443c034144d51403030a40d14050080103a980c02c0c007805000c03c1c00041c103480700541d610b81d843c0011541104e603d10340100c1940001c5000e04024400a140382c000003108055074202813062803420350410200c64540aa900b0119168030b1000c0c14101480c60094900d40c0100558103848092600440c000b4454182c040f043d001070014a4002c8881031120100c0c0141517034810000c1c40841c00c25103410920b5845102126200841c0d03501007074032500248180400700b23100556207401c610389020110791000302580d06a204601e482d02e0210107120050380c0b1014030078941c030080003a4803801c1d080700c00f404041044070f81e41c50ba141d0882c241580000004160500401c0e54665803000c04c7c011481c01c0340d0160364060646c0c03a85101c2c07012100b00c4016148002c1810407004005480b00c20300040011056004c0c0d07140140104528429600341d01d08603180f5003004c1c4400c6040e2000702c1c481100303a03000c44402d03c0c0c440b60401c982038500300c00401a44c0e0701007404a024403c01101300d122078400c0c01200300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 838641708 1250 838640458 838640497
    0x80c0f0d03020406090302040b040f02121008031602040e070803130501030b0a050a180204030b04060c020c03060603070b090a0b0313051501060909020d0f0509030310060e090f180601060302 83
    0x5007181240603074021440044c07080d5400300050b180c250094000030500520018410200b90310f1072080780e00049001e5400b0401c58100070080c03ea079602c0d40e0081410303001035450450420614128001450340007132040d5a80c2c54801c00d4014100b1004010304014012030b5503658140c2184620700d1102c0c49a540042d05288481d0582c1c01c0040300d1904841014201130442404c1c03040d10414440040a0010825800c0c040000803a128601c07090080d802207900042d240072a46c4000c1c10300201d0911540603501403418405035440c000340d60002c075042c452040f42c42e900400c0010303224003c6580100e03800c4a010041c85a030741c510103192230741c86100310200c81645202000716143c0d000d00348111004150005810030481100d60001d102d80d4403101000207100c64103195081c1103c2c4160b4203480d044d0300c08002c01a20017550145000644100e044c08401d000c1c5030b800098801c2c0005003030a0856418070041034104040c14203d080c0048400156007880da194400100290071a0f918000303400c2c020f04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 838642958 1250 838641708 838641733
    0x30b06060d1d010509190f12180902040f0605130e090a050a05012304030509150903010c020c0f0d1110020102071217180604061e1e0e01020408100c020703080c0f 71
    0x694082c0419849035080705086050303203403151140c00005520f03050108010300241c03003209042701e0b000070b0910b8070001a160387c10030001071050030391904004144001046130070310b100003417558a03003141c0b00e41811384c00e40e655110450b1700b010800d540051440c480c480607003040000640280c02102c3e04801501c41d101410b6034101e440f428155000b03004030b0307010000140d143c105176800b0000c404480086030315044c00e03100801c0c01c4503094200034005800038a14003116144c070b51080e1019600c00c4494078a00d07003a585a40005001d4101d04030321540070a40541e19146c000e405440c41c10741c000c111064410048617001e40400d060421a910001644001440b0802c034100100a4000b00700014002540d46035140c6000380b2003400c10b440c002c0703c201c10300c8841c44154081d81e10920182001100300010101940b020703141082c4c01c0b095942d0041c002885030b0180003411007410001d01d0008591080301d1a07040e8104402a0400f904c002000036905800c1c0c040081c9407070804058204035034000c041c06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 838644208 1250 838642958 838642993
    0x1a011211101215031424061c0506060f0f010f03180507060207080c030312040b040c0e0903090f06040602031e191d0102160b0d0e0a2a030b06060d1d010509 68
    0xc0d8105801a000d500e0745100324840b8a031211780c4041c7c060903050111040103102c40030302d0010403045a5503441503080259904017504810a031813410360b26071540790070100002e02809516501c4100f0140c0da10b41c80c2030032060843c014081183c000b8199409541c442ea0003d40b2882c40c1c0c000d4054601c81c0c04000209418000203c074600008001c04810399261550746407103064019009070f9024003e04804610000002c03415070050f1f25140046d50761704103003001d0164803a1007003900c510402040c4010041190003200300d40045401c00010720802d64a400700a6032806640c4900050341000702d10384240640154a5110300f0102103003085103c281034004994a940310480f05483c4404414100300070710a900113021101070000c00400c0a0244004051034005120b50a0701e612014007600c0c8510a07810b41e2424800403e214007a21090441d25160a44074005d01214014080001c9111030b44420340d00440741d0090302c1c95440340c0d0002c0b00403414041e003015034042605014203c10403400401d103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 838645458 1250 838644208 838644223
    0x906181a0402150d1b02010e07121e020607062d09050a11030c150a080108030a091206060b1b0d0c020325121a0112111012150314 57
    0x3421460b069100d4580a161a0080c4030070032413550b100c0f00914440c186001054480003030a81c0009483c040780030b0400d183c0030040e0b00954100c0d107149802001308541c042c0c3d0b0261030002c4048200c04900ca4070100798a44548000502020301d0030026503220b04052000004580010080b9154143c4443d500b400700d694100000344254841c406060006d08200e447e40201d00009003640c20101c20003011a066410004400720b110000040bd2030841e5007221615024003080c0000714200030301c808015058071009c2c06078085a0046c503103001d082081c1500004040c1c8041c1541548800059011000c081c2c900800d24441c1e02640200c2e4209500c11000b41551940040c010616401c04641c80504074502c285c00c040d40450081c2d01040100030318441911042c840c60600200d051015412180302c041a00080300c6d1095004942c00032034289408004a80803c13102410003c00001e01955510030780300180e8034050801d201d04e01400c10015014040740c0c00344000082d00035110701d10f1a2100071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 838646708 1250 838645458 838645463
    0xb0121052a07030f0915021015051e0d0804090c110111091306030209040f0302190f021e0a08010609060f1a030709050301110405400906181a04 63
    0x2401e202c2c4502003840350b0350a160400440c02c00c078020640300e12800000303822000c541405a0300c22000460a41020b00c01c1d00c0004508140740300d200d03410040010204080f404211001c060103000c8243d0b5969010f80450f202a404000c16079250f6640781007401030201000c4403404221010041004031006000304951502e0404c40c0741c0ca4003840104002c44030442c110b000020540d2864040010b0702d419a4440c02140105051a401c0c101498000d107040c01661001315001d0701c1c0e441220024203100c25074440e0780d6044480300e04000080b2084000400c0500d100ca6100301400b03030004000d01c040d070100d0295400d001c020302c04140c4505001d5104e00c06441024020300400d0b0b803000d044000c45c000346812281c18508003e44a607150700090a691603c400c0c40b004400c0018104064501040d140030810500c105d03e0701c0c90742ca403070380c184c50007178825005c80c404201d00040303060b040001c0d501c0110382d40d80c0580d0421030091843e002401400e844002100c01d41d00141030690206000b8000ca440b075039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 838647958 1250 838646708 838646791
    0x30f011505040207261e070201020c01030209040902150a02010e07053304030804050406060f020c040510080709060306141005060f040302120604031d060d0b012105 72
    0x1490708040c00001d43c0402011380303d0346640c03a04e642900e00840c01c140e150404140b01162140045424000c81c4040c8402d01c086840342040f545006036004a0a600c0001c401d007401600e0380441404100508410f2900a40c40031158100c0d0340ca04981c1c1015002144040e8003c02803c40d040c440a075440c1e01d0b6001d4154071951044c0c10301c10204030764040030481c080c40e0707118070341e544054000e0b2005a002500129a1480080b80034880c81c10188501c07030090200b450820200650210041d40328030452805a000b55110350000c1d0709400781c10069402000c00400301c805140c0d542c42c10600600c0c46010449000742040007540e0307213440c005d2003540201d4505801c0b402c424070b000c00300009a8003c664001d40311006100c00405655902c001c1c503a83c6041c080035150783e00c0c00d45002864015104501d5590420030365095000303443d0340c420342d81c1a03c10081e0000d45103660000603510304001150354004811941c1c0e0f900155411604064041c4050082445000500c0c8008180200f07421440c9018176 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 838649208 1250 838647958 838648001
    0x9050601152309190909031d130e0c102d0504181d0d09060201051506030a0207060e0d0206090715050a20010b09010506180904030203090405010303030506030f01 71
    0x70300b402d100920b40c0b044010558644c031014000001c0316065164400f02040d56200700000525801441d08c221806c40400e01100100c0042d000483d4034140054040c03400e555040049e6569204000605449000820840404040180061060824410000207100080102c0003a508500a0898800b9a0b5101c0324109400c158441400210984030600785c41c1e240e1100344e5124036204e68200c0c2d282c030401d014181590300100050305001c11580300b2001c5a1400c0c0070000140314a500110211034116400d5541e600d83c002540c1c081d002e408800b0740b030070b0300d03008c4180700455001825039a043c2c455000c0c0c0f81203680d0f070084262205501d1242000c41807441d0000c82d0034922440003841412080c0c107143d02540700710f115005046141e2003c030503c9a46d290b030f9210492810040311070041a00b01c42c0245001000401d6424210340000428046c505200103d07003011700910550340480d5018008001c1c1c2d41e07403810010003420040d98554060b00584c2e068801d03d41c2c046c000c880500c0d940300e020752a80d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 838650458 1250 838649208 838649267
    0x3020d08090703120806090709050a05010c0303060914090d0914011b0b04060618021e0702030a060f02071e0c0e1308041712040f1a0d0905060115 64
    0xd500185029141d020310358000c00024200f40c1c20030f810080799a100c48880c5091010b02c8103440c000342210044c030076004c03000c01c03d99903007400b640705892080c60040c0940c210340c6001e030060241a0070210074941410f0a6450f543c041050303403881282d031401201c03400709251400382c8055419010b1241034242091201038103500460342c4030411820b10b101251114030b00d41300c0c105410000d03a000c6890645400b801c00c92504401856002d84036842811450f000c1000c0507044000c80600b8101d04030107000c24502c0641d5802c3c031a640305280c12100600c032882c0300225410080d44026011614100d00d460a000c1480802e220303040d40329070040c0d07510500c604042c2c0000294100a00c05004624040740c8000000c403104041c100901c1031100304400450300754003a6082829014000b14504d00038041042030896100405048450700d251a0b61404056200d442d81d5100b900c0c095a486c604000710001000000180581220103010200d064440b451000300c90007001195041007030300b004078020b181c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 838651708 1250 838650458 838650467
    0x40201090e070c0f020f28060e0d020405090102430f0b0c0c0d0513050904020a140109030602041d100b120c0730020307080412050c060408012703020d 66
    0x2d40b80000e080d035803425500d03c0047c0301c40c000d400f4001c01c5004210a110800b420307110508010b0311050802000b489008404200c0224201c503000c0c0c460340d217990110f05046000e5045601140f08421002e800000300f010b0f101400007500c1e9120501d0052110700c5649101d000d4086a11a034000c1182c0b45c44440c40c0c848405e400ea002d804801e0048081250110700081086281800182611010346950301c09404a440006917803105000e64050420040140d80d070b1041c900582c3c4804134151045034980340125074122450300014445d5100103400304000862445600b0300101142e03c035000d596502051212008a45c400c0501540e014050f01d1008150084060390214860584a040291039103d1419220380782c2201940403441201000c0441c242e0007c035010003c0b01c0c0000e42c5030007100da5800303110307225070700c50043c0140c4a58422000c200051003070410001d0700400554642d9154a030b503500808182e100c91880000102111000e102002c000345c410a8054016080030110b44c1d170240c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 838652958 1250 838651708 838651733
    0x150f02070b0a090e0a0b100c060e060a06090e010e030901030b0f0a1203170c03010e0c0705060c09010207050f10030c090f091406090609010611070b12040201090e070c 73
    0x1503000d03860000c19901448405801034145941e01e10f00407a00e4141d81c41030140000c1d00c0703042c0040c288000c0201d10b40310b03200c060005031030914216400d00c055082c810000c0807800500c1500d400f4800500050301050741000c8140c0b2001c0c01d0420078401309001860032580d800b220108690000d000b54540347d8042e03400309000b07410240c81c4000f905040341c00035083c0b6100350842a941c032045c282075410301d03600c50841030920344641112501c50a005403204002c2c0414070805120f600c00500282d040000d41c4d09071a072496111040303e84904010382841c0940c7c1040b00a14011b204a00e03001a092911840c2c0b1010a28013524900c180d504107041280900600e00c616030034018401c200042491010145030014126403500207020760004422000340217000e40f07250f106589004c28440c0d60340c0c0b18034170300d81143e0160503d41c02c141c140c41111070408441c0d9000c190001c0c0d010404080d601400704800f8440c0d4400da032096891a25000c2c3c0301c0ea1032001b0b0700d064000a600043c03010010305c0060004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 838654208 1250 838652958 838652987
    0x9030a0b090c040b04230a0b060c0a0b010f0e010519081504020f1504031506081501050301050105120309010c021c0308100b120f1f15110601050d060b061303230715 72
    0x8517076000c8280c085412072b80104010101644882140030600520f941761a01419a0150300c000ca20302c6c045030110002010302504e4411389050000380c110046030b441c0f00d401450008180c030281c0c5080c16400e400f050081710180c0c014940315061040600d0080717420031050034400d01080c1820f0441d100c081e4032102c075016841c1c0b042e996031400b040c004410080d0a64040d980a1207401030742c18601803609484c2c0c180d208a014140014208031151004000e6036101c1e4006e11341602500c950707000040b5001e541360905843c000c0726604c1642803603070048886220300100e240000e0100da44520000e901c1c450f514180c1542092140403443c0c601e06049885c0d08224600c0440b00349111032502040000c581d0f903c503102815000c1e5640b0106900310703440e070b80c03922141c8024212070762400c1c0225015810341c0c080202081d0751410742c00a10707941d04c1d0950315240880d03860705071955104e20301490398000c03e6085903120b500142080030341d110002205026201e00d0b05907001c2c041c11801c02503d9409441004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 838655458 1250 838654208 838654211
    0xe030f0303071713050f061e06010921020a14030f030306062721060612100b06120f0402031006031a09100c02011a01021b0609030a0b090c040b04230a 66
    0x800c0017007001040380660001911016010340e0910251405031030004400a0000041d580c00b040416030700503801e0700072507409620100e408229401c41c0681d24403070303110003540044071103004610b007004102003640c00c10064003210010410040380a5480c08116a01035010204220311525032998014400104c24607940d041d561222403800111503842900135403650050722050101800c104010468203d80140c840c6040700040414041e1a030915041201c907043e00d0ba48941c41e5a1101e000721403000c0d01511010840e400e10060003069040c05a405920a10442c018401c1e003120620500c03080f66800b42016420314503460000c043d03e1802440900b1358010034a070315044903180e014014902441e81c0c000204001c11280301c01c01400e01c45903850441d4440c00340d103e404201c8405045990008035615502d5102c0400000d1500142400c018051352804040c4001040d001810f12010201294288246a180c2c0103100072180b45100c451001a612a00010101540c45082e9003142d21100e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 838656708 1250 838655458 838655491
    0x21b2b140a0503070e010507021f090504060e0108010c050c0d0f0c050f01090b070507080913060807080102120c0a0c121e020705090703050105060304110414070e030f03030717 77
    0x12000c464120500368004110000104400154000d450918072602402c100303081c4185600481c025488041c0c9080841002e07640d20503e290190104000a05000740306203c0652108030250340b03e4020702c00c411043d07082080d103d070a03038041c0b0305035510000b460006102c661403203c41290f244031001240740c2849047d00210011800c01d01418520340101000403400d8802c61812511001c0010b051108011040c040c14002440030303400c458148608a480d901c030288507100c1c10005107619800701009104420001965101c190054183e85280303000408940d41d815410301c4442c03140c0c9100c0000114010741d40300006100078441c050ba10210300e401c1482c90208451a5508140141c06601582c808441000070307207413865010360302c0b01c030034641440554034080219031140404bd00041400090703121046964aa0f80c1c0b01d4003d13900b00d40350020460800d000302a140c0818480c109000740205c10552100210000c11240200d0441c2c0d6a541c5c038074161a0f00071407240025041303280a210451 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 838657958 1250 838656708 838656737
    0x15070c2105090a030506040201020c01080c1b15090d0e0f2b0c06020a02030c040c0c020d0819051c14070c060204050d0b090d090b0307050304050f0a06021b2b 69
    0xc0349601135480748000b00028200f81c00007a107002d4100e0002070400c659130082254024140040c0c0c0d1385012075000141d04541d00c8001c6a0070000c0e46c5056211003404c0c201042510706002482555410345a21440b5000780f4080c01d0200da801c51010140d040341604140c8030040d14200c00c2c91070300e074100e0ad8200441c000c4580d10103003c043c1d654880ad0069101c04803900c03e514080c070000c540f0074800c540410841084502c01f83ca19034640c10003901c1102c8d641c0140c01031007110401c0f5820341402c20710403124402c40482c060a15080301319150140203d20707180150079246842003c40306507404926070b00d03035900c1500403501c2e1520744504980380e98080c4000621511007507103840d070b140d10500d500d06d00d51920f500c043d80b40c45a80c03003064080103c00a0100840d903251000c40b030304041a45401652a61641070407403038040700071010341a078800c00c0c82c20340138481954003a1020340701c2c160313006e00030001c410b15550b0f40d1147d00003110044200301c803048240445400500c0c0110b44107051028a058000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 838659208 1250 838657958 838657969
    0x18090307120306090b0604051008041416030b09012f040e040624030c03030c020f0904050a140c03100b031c030e12032202010e1215070c210509 63
    0x40a0004a034075004140155880c0d40600300810b174003524601d041624005c0050006094078418000307100d0b152000c1001d01c110144003801a041540441c2c100349114040181d03a0745141c07206540da402a000401c20604041c05202514a80703541c4160070060007026220880c110344d1590400d05004010010307a11031b00700600e80c4501c6c003070b02d400103000940403038950041d150090111002c112601003400090b5500c0707c144203403a003514004c6c00117005803020428214140c2007041d48100e50b0b070104000c10200048000405200c0e0180081070041c44007110380c0d0b01e101e0580d40d0380c0358020200001795240d00c1e900020029a000b0304903020007d4400c036040122000815030300010b62288111031074a08100302d082c0300d1281103201c1c1481d6242c00c11200a80903c0804c070246203500c0361b420700c401d44e8842d07407004402c0d1200800d50081400664511507582c811240c11b1441640c2c00e400080c0301c140100d1f100c0e07165a40055a0036030480e521711210840d03500e48650002489030a000e11a40368460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 838660458 1250 838659208 838659233
    0x906030207022d100e041109031f09170904151a0706021b0319020c0609060c0c0a1e120c12080c01050c0705010b0d02010504091805060906040317010518090307 70
    0x69229903602417120018481a1059401081c1004404202101e89a02e000071169600b070840e034141701c1c030301d890b4540c4a005469000c0c406402c0c6517614030350040300c030405401001c407000200c1d41040b44a440907a0b042640c0324610a6200700288a821802a28007000040c05031610a0600600d40740b80000140142d85d0100080042ca910102d4810350011111b07460403980c0b030780d45c001412041c0040d400a0f0b410710511000a0181a0200d50041c0c00e110030004400e00100051890f0212910341e0f030300c1c151007003914200c02c480c001c2c00c0900160003200740c1070003401c158100c00b1100a05080100d50300809500c0d240440e9a20400c0041a80118081c41114002c00728007100743e83d40e9a480c201a820344d0801080688030320114014003006070b1b0040110740481d00d05003030202d01c00e1030346212540e81d0808000040e000d801041c00304071825a011908a10651080c1c4802001842010700b0f004540024095503803c0010300c41c440003802c41c2e001070141d000016204407840d01600d43d8610420046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 838661708 1250 838660458 838660489
    0x20f030a09050a06110c040c0215040b0a0f0b03060a020304020a1a0a09140a03060b03150a0e1e420a06050d0302120903070b03040507060906030207022d 67
    0x4001c90180140d151502666000b000180b03445e484c0003000c01002038036800610b1502d403041e90f0301e512a050349402400359481c09803203040550030034509401c02501d440303c22648080150715055522550070003c1c451484448d0001d00100380554543c069500254000b031b0050b03a1105411000058001040c00c9854080307416000c2161605070703000f00a0103400c040d8108429215400201c03e81c5516035003c0304044a80006000ca8681c002c040420b05007040b4165025088218404000748422103030090f51503c640388044508000300d8a9040310030341c081042c4420150400d00c61203020300b0104201c2e200d240c0034421100f921986e00c0070003d10076504131200b0800d801105003045841d02d894852080107220035228554041410354009441d210f030030320841d042c00302c0490110082d480c00c00581e809030150a07020366803402c043c1005982c503005842200002001d981d4007050ba03030f2007402039400595010741424080029040c907800300c81c0e20782156002100d400c62944503d5681c0c030151a00980 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 838662958 1250 838661708 838661717
    0x90801020f120c091521160c0201050d0f0b0a0618060809011104031b0e07090b0d0b040504030c061107021f111f0e0a03092303010c050408100605100f020f030a 70
    0xf01d07034030b045009800171214240758080e101ba00308000c00a01d880c071090402c44901d02844080e2692006032000c0c001c8000c00e481d0b00c5e242c05042100c8044aa214080c000011108441c105555200032504040301e070303000c00b6201c0c2c10340c541000018051030015800510b00070010881e440c1c035005020254011341d106503056462118400c3c0c5511042d00305501a11702441c4d40340040c64201c0003e0b0240515108402d02103030001000700384041d0950003401071480040c406c0c0300500f010306004100084145041d111a45422542d4035000750003011a80c0c0503901900c80413041d02501c09140c1d6007805603481c003007170005c82074480314008814001c0b910b00d01101009418038400211200d030840703102d0f510000580e44046880c0010070f82020190040b211160340412109072411801e4401e02500460940c05609141202d0f1550380c116000d0016a96600300303d44001e18030748010801e40300b042c4945038000c01b00360b041c941c03428840c60324002d07805100c0c01280e400c802220341040c9154005641500040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 838664208 1250 838662958 838662967
    0x3041e030f2415170f0a050a1703101512090c08070b03060603180f030304030f0f02010207031205060d0c08010207020f030a111c020619090801020f120c0915 69
    0x500780703030b006048552401c410410802e802076004440c00707142806a0550000c81080301c4013000d10030006200c3d20b0082c01c06a0300c1074052440c00d40e5440e00002c0d800c032100e001440c034200d8104d1100c0d00f9a80b0030300301c595a10076800d04d000090800b51010703046c40b00801c400c684a014034043d42d401154801440703014044941e81c40c0c0541141440110780203810655800c1060001907902c0c1e00c10b407078001103800c203002c0703222000006e82807400b5410401c840040c04084208400e0503080304a0107401e14094948981000301e5500884c200d10504600802107559125801d01000d41d503441146c0c4000060a031072039041032600c5034403003400c0c41d0307001d6145a9000501401142080c074004410940150000c081003000740d5074004100011134880e9000d0403a0b41609408071960240d1012455000341201d42c1d41c0211030808404804130100302c001103080315900280389681407080b2139021340d01c1c10b03d040c00c003280340f1110f0348490700140485800b503070b00303201f941ca0350f544e4070300782d03296003254458003650300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 838665458 1250 838664208 838664243
    0x5030c0703030e060906040509060609130e060f040f03081f090605130b011b0c0b07060c1107060c030509030717150601080f07080a0e0303070314010b030903041e030f 73
    0x4112000f400240203002c00d22100040b07407106400e4a0980d4422102890b1b541c0e10031001c00d038113001741207803203922000c03110b4000d00001c00c07507229943c01c04040050b604280d54550b02861144020740d001080c12400f201c3c6507010a01c01c0d2036450300001d4a624803201e10407054035459100e44650808014507607980700c03c002d03500d410065801d0425007540306000c404040c070006484200c01055684031002c851000e0003c000f01c502003d000b800a0701140d0b074a6100c1402e0060090034410014804900d141d050520702240020707151045640316500d500040680d41d4088079140c111240d03480d014410b400700810a10f0140f8180c001d20510b85004244049103c4140310780c10340081c1249041c0030b06030050003481070540d0661540880300c0e0400082c0307030f00c913914102c004204480410b07232140800310501144039031503002218400c000d80c0d20400c559807601d01240442c4011307104001280c0c000c00040004002d481d0440c41d02c01e003000b041203c0c0c190b0701e48514100103800c0d20200d40e0b12014215a509 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 838666708 1250 838665458 838665467
    0x10603061b020f0d0507240513020913080901030c0201060e0115020d11070e0c070209091b0312030708090a0b0c0301050a060f020703030e15120a0b121f0905030c070303 74
    0x54420068001d10148000c4c220240180c490200042c10b03181102607000420050100d00808896540d8800c001c03901d405a030540c0c11000c0e0000c1240705150580102c1c4600f00002c4e003071a113190b00110700e6464200341000540091505840c440b0a55498402c00149000c4400002e8020a200034150f849000d01950003800d004060704d103a02413200c0f000c044110100001100400d41d4600c1d4000661030701e800c69490100d01840d03200039404401c0300100204054081084a058100558102c410729410010141c84150300b00404e454040c0034400150414826045980c0200b10340080d1482000691505e411100040b280d000160b800040104000c0c1801078217200202000e1030301c4034101e506440000e442e8026888042c0400c000e803060001c0942e10720071040c1030a0b1480e114240d5845810800c521240d01c21203140514929007540c04034035041610007811001006130150030302d40900403030340d541140324003440070800d544c0b030b001e84000440820050424040e008020a407041c9949801030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 838667958 1250 838666708 838666723
    0x3190e03071109130305030c091f081608040206130509070c1e05100b120f0a1502041d040303150305060f0603120d0902030a061b0e0a050108040f05010603061b02 71
    0x140640741e1501080200124400c5071000d4a9041c60020387d41d4507800d00d8502c050064000407680708030070b61821104102d85d210540300b044a035403100e0b44280c0e51b22110780c074072413030302501032001c501c0850001d0014604440141800840d8940340309070b20b41c03210003141c2c45030821504000419800c281f030005220807051410020300f141c01d0107403c0d1174016174a081d112002030704043c180e103440e210306811664074242d0040e00c01030070008490004840c0d0720a41d40c0e50b000a030098815600344a4982031007295402190151201d2980103071030469240011404054000c100f60101569030340c0340f403100d01c000b86900e0011030150000f070041d410001044804040302408051080c0d00829940b0740a513840429103a403500e000c000051545601d0001c03c0c01c2806904004201521301300290301604d07440060a00e050546584d100d564804c2d15041c8001000c0303c2c09018081010766001400143c6082d640e41d070b641c0d21450011614076580d5860304160f03041022003404090710040c420550365410003010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 838669064 1106 838667958 838667993
    0xf050f060c0c1c0b010b04290f040902030132040c050d06090c020607020d020604150b1519020703020906011107081005010f0510020706030203190e0307 67
    0x1220140110042180e600911000102d4203401c11070544054030300358601c1c1d0f0201d11011030420166003100d2907081d4240c4003001127404c80c1d01302074040d0000f441c803000c01588075414550b080118401c091003030117009410300d038401c0490880c0300c001c0264920070b40d000542c40000e21003c40c0c851248248000c511410550000345a070b03101d42c018900101c682d42940d000d5110800120b840340303620300a440050f80482c0119001c9480070756002e4800f5541880001c5503d40b90020550181d08071104040c00fa40110b882e620303002c0001c406112002e12440035209190450b4001900c0b031002030a0a410031004080d6101821400c210030f10140030000200ca681600c50341140000e800c09010740c003c1c2d48141d207000911828840804501c020b102e4003d8001641421422002034000500d8100781c0ca804429004103e5003078410b01080b0000c0c04041c60361030f4100e00380121a408120040d = true := by decide +kernel

theorem cover : BRFrame.Cov 838489208 838669064 := by
  have h0 := BRFrame.cov_init 838489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 838489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 838489208 ≤ n) (h2 : n < 838669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
