-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3909
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:11.944978+00:00
-- url     : https://prove2.me/submissions/53ccbd21-f014-40ac-9f2d-6911712449a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 702877697 ≤ n < 703057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 702878947 1250 702877697 702877753
    0xc12091a070303062d3c09140114090402060a0c020d06050405030d0b060c0c0f12030310090b010314060d0f050607020a060b0405010503062d01032003 66
    0x400306241c01014002d4126a020b003028440e25440c902038044140207082c90031345000d611001d0400009103040000000061280711080b02e04203a4906a40c2d83e400e54210240003141401c0b00301300020502c58901c18042d200c640c080003454207504d4680726091004c94181c555200d60340300c500307000c010794403034041380d4043c1558240344e01e009155000161242c90300c440d0140c0030134280781c2008200400440244421a000142000756805031000d10066009041c058030315540084203d00d42c074604102c1040d0740500091422403082c03004e416070703410350f08140d86a0480350340540c0c091007550203a01808a4458080c03a0030841c00000040c0e40f180e01001a0802c0d0017911400142010300c01010200000345810400710703010307030818100003541d50180d058169a42450156085002e18013405200c1c12140c0c002e004003d2074070f4105404614280d200c50b038845c130585444000c84c016180d032841900941c02100c5030b0103c001000c082040392648410300911a4000c8400c55100d8851441c0f0311060910b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 702880197 1250 702878947 702878999
    0x1f140108091b10051603200f1e03070623070e0303031909121829030916060c110d05070b090a090615090e010b161505070c1209 56
    0x40f64120603070f018840d0381c01820b6010507104589060541009a9031030b01007030600581e04582d6985462030312008500e400300040c0e000801c5090080e10380c80c507049920000c0009482c6428120382d214811500c2e000c0fa0b801c1000c4810542d05407030004000c0b0389078400003d044c002c4051004a0000791a4031005280000104810110052004440d4004400c05d58019003680c0e0b0301c050103401500c1a00114141d15542c0c0d0404004502550002e01d039200039241d40e44408001d0082201425560f080104403182c035200340301084501c015541c00420052040740c803510304180c41030070302407405102d40b003009000e58403110091b000201d000616908032000c4422840d110511312002485880043e0b10281c42141014130216600102c01d5260b0111460f6844041d0400c1d550103081522100921a03070305010814407068904c00c0415012a50040c4914481c00d000d60b0164410030446105a0380c039000039141008400c00c10507032642c4098090311038104075035624584080f86245401c182d03502c84c4840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 702881447 1250 702880197 702880219
    0x3050408040306150305010605180103110609030604060f0f0207030c030f052b0c020d1d04020409020d090201140c0703110d0c1203080a060b0d051f140108091b 70
    0x100340d010075607001d1540a101400003440100400006070418042507805d54a1300c440020245401101d42a06501202c21880c0903840c5481d4a00e200c049070b101300f074000c1800c10003070201e550280729940c070803807280000044620400f05554121243c40c1c40282425104000c140b000c01d81061400c41c000380e1501c0d1020711036031200c00c100d81901595180070b204001c4c403080845c000b0140125001c50a280a004002c40c0d00b22840407a0b0f14245410b008001c076102926007408040400013040014802030005440c0a44d241c0038a401c80c0e11008d15102045c0d628500e040c210340e401011001450100c07500941003868007409140c030340c0150f200003040121144002e4800e6111002c444605640241c02c40754800d591f8480040a240d48400032000500c0e2140068a41081e41c8516416141104141414030304840301c41c0c8028440608070370a00e080f004d031940e44482c028000701c800b4001c5141240410141c0c10000341017110041d00d45011074004103e80c1080500d400c08400400c0c4045419240107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 702882697 1250 702881447 702881453
    0x131103010e0c090619210e010b041a240d0504110306070f0f0908030301083702010c05010921030614030c10090306050c04030b0105011106180f030705060f0108060115030504 76
    0x299180b1045400c81b1005d409804200b03400398850700d05841d60344001c0c00390004510401c002c45118900b82c0c2c2040301d21500340c80303c03800c09900c81c0d00d24600d603000201d8155030f103d0034001c10f40c010711702c8105c0c4a51503030b0800c4200008801c02080c00b001c00c6c0c0c000c100c542041c01d0f0141a908204420404000041000e81c40943c402c2400a00410150080c2e07980d135611540c6c3c0c070b512a0503101c410f200d4101e6560305038112035031011079098141d9003401c1d0074841d12030a50044954904d9100c00350f41c150340316010700b404074203c219800d0ba00201d420917800a0102004040e09440c40c07035000b0505550300341f0b50300d2020f071008038100c1c040314030403290512190003011040d280c40003560030240540d8030b000c0810281407640f2000700b0035a80074295400706680d82d007004503009984a039608560703410200100d10003010010b01155001d4840c3c00b601c070005102c40b02c440c43c50304240c20540c4c880e80864280071a44080258540c054860100504015810580c4d98012808403007502c0c01059a100009414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 702883947 1250 702882697 702882707
    0x1a0a0e090c1b0102090405060105040b070605040f0219032001140f0403080c0609071a0702040510090c0c0209070903020102190c05060d0b18070c020f131103010e0c090619 75
    0x101c0140c64210000e2003485014a03000b508140b1481b4003072072800c00030038403560183c01a24115102c18071a0303860f205140e5610350140c50702401c201d9940b00c42c0105a80160b8442d05401c15001c40361404c100b45a1071410403102480c001c0403402c001040040301e400340c0c1d0b40d0002d9100040244c02c888070780d4601256a03046010300c0b980d84094009040800c03110903000340403916030f018040680841e0680c035211030301d1000441502644811010003080500e0040c207041d007001ea400040080a02421560398000c0c509540c3d8201c0c8900018019621708001c61804812042d040b5185180141d2014150b43c0003075074442442940b03050444420215404116400400743e02401000c0c1000da00c2c1c20800c0c2c9440e000d000d4400240380328804e810030044112100403440d91107906ca0f40d499000382d10381078003030298503040031180c690072140304880364080c2001401860a440b94401203241d49624000309004d003410b001d01031041d54032041203250920381d50078003901d0400b200c210880f11a201c110700180c034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 702885197 1250 702883947 702883957
    0x60c0312041707030207080c04020315120f0111070b0109050601050f031816030204050a0c14090d0512220b09040e1c0203190903330509071a0a0e090c 66
    0x40c5982d0300003940010107a02013034a00c00c40d0051011203411082c0131007040142e0104680308085601c2100c016170051816401b1150b02c40c0b14035080da00d04560301c03684c0b5400d4400c080315030780070900000744107001c1014803e841401050019401c100360305040d40000c040b8803814162400c9072501001007400e078030034441c541e0310840010040f03030100c2e1a144a4280c01e0a0380380b000768440e502d05400500149101e0040c5100a04075641b020850790b4001c4030301420b900441145078104902d1601000007403020022440303a1a5031003055a1141d01000c82c59220224007034400d02c00e0945d007441000712000d12415250102c50440c2c0c080f40f0244955585440d0805400000711005900781c0142e0549030003100804016107560740079100c815150106941c42c0006200c002c150300303500307046d44e0360900d612004090302c02090050343c4802002600840242d80301a1f52002941e004802c00b00040100841492012082000041c3c1403550100380a07002d40460109240103141d444000b51954504000f190 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 702886447 1250 702885197 702885233
    0x807080d2d17040c06140306010f0f0311030f091608030d0b040902060a0c02010e040c05031303090b07030203040501020c0d0213090501020c0307060f0b010810031b090227060c031204 80
    0x140a4a0a42420b03882e00f41117101da000803c40342201e041c450150300048074032800068440c10308000c281070080781e030701c81c914075040b081554600c0c0c00030000422000842c0584000710002c1003500304074074100d0510415500e80d03a010b40c4a0b200030010000040300b6620780d0a02d04c0c0d40040c00c80d508101082c090b00500c800254030000000386008643e4000f0700b00e44405000fa81c0c2c4d80f01070390800c401e1100f113546003198440030410034400110010b811a40d00408070380b203481e10382c9500d47d80c0c245d08a2030307800030042140940c00224003400203590400803001c68000071148000c04c4406900411103212180b00c03a046000c0d00c0704840c005005094040b607003440c598908880d0354000a04241008180d40000c6400403420552460364640c400d20380c0901919091029400c0300b0300d9541c44240d07805289141070303200b404e030074000151364220384058092900b100040020070070002d4208442600c448440380d11580c018000f00f00202c0b030000a480c03500c0460300106030300d074407141002140001400300d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 702887697 1250 702886447 702886487
    0xf0912030e15030703060503010c0912060603020a0b0307180b0307030b01110d260c0f0d060e011d090a030e150409020c07051e010c0308180105010807080d2d 69
    0x44039440c0246802544103130303c40d54013005070b43d80741e400b01420794480e07130b00080024040001c2480203030b002440f03501182d4840e85000409548e00c2d07000c02d100300b54651041800c888003208005040780c010080300d000e00307556659607001d2401c01c44505007900019100908042e41d8400074406640960144100c0405400c01c4800c103040f943c800070075403807190f1000c01030864680007810a01c01e000400b00e008910030405036050523210003014045400084080065a8840000140301d119002c00701d070107400c1074241081c518079400101d010300746014169540c0381d8408095180405d9002d075405203c1c0c4002c45081140c031602032820304450099400240d2258800190300c1040000000e20f002203070300903540c5409104003038201c1500742107001006400b1607006601c050000348134480081d07200a8440740c4140c0308003070010007030031241e09801546407544440020701240c8400c101a5803802e88a10744150080c207485245001000c40007010320111280c0c42d6803910140c0110705d000707038100255000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 702888947 1250 702887697 702887719
    0x1e1401050108010203070207061805010305060d080d1407020c030706030c030b0a0801060302030f281e0f020405090a170c1c180509090c090406021c06150f0912030e 72
    0x100c0b0f4002e500503100d4102602c078001c0c0025240740200d11041043c0d200752404010b0070f24200043d0050100204420740c0100d00024150006070084064141d84280310000140c0003001e02c24100100406402c840c15540605158421658001003030015982d0368030b40031881900c0c042c82900581842d00201c0d5018048141c0030a800074154843d00031a0300803811981001d00016075952155a0b1a684181c483c4003207003c82a8200c61802d0503010511030701c88650000b0704190f14064040300b04000300c130f0700d00d8942131401c01e51605001741c42d0828408000380481803c5a03549520600c2c2c2c0c9422100515004100b040c03802c0000e2203d49508001070a40c46c0d145401d401004221050b10f456401d141c181c120800704081c2415001644510001d4008041e450169000c2110071107000b081100c02c1038082002d02c0780d801522411006010000c00082141810701c0700703810b40b002c40301841d0401c01901d0760002c111168014518000c4403024887d00b0401645802c00300c8003540b044030b01a07003050386c4c071075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 702890197 1250 702888947 702888959
    0x50a1b02031b27060a0b0f1b10020304060e1006050607140a0c0602101401050609130f06080c04111801080c040506040308040e0a060e2202090103081c06031e14010501 73
    0xf85840c400c40302100c520741c1240e160703041901d16010f40841c5040d00c01007844a024449800c00000314221035090884002c603140d0300c2910f00340da0045404855031034440500704d80d5800c041050441d80341c060b940900c036860521010074003078003544101401401031922040204441800341300b40c800d4001589000040e2259000780d6a0580505000c200364034000c460400074003900307240c03410784400400f07280c540904902003018a20800d041c000c4240c0e55455003084e040350f64440d01d40140a114050204400700c02c0c10402160117550390f285040c08104003010402c81a141c402d120f20f00242044d80302510b454003000350a0086402c102c2e0000c10002e00401404488405882100c034840b90740c10f103d40e034008209007960382d544141c15600240ea4040703031540740002c420311910030f0022811800c0b0780d4582c0020346480310a070701c00c1d6511030340052207216450541d410041c01c00c07a905c1c0103000d80ca240da9520440c0c40f19038200041c1d8130086c031000500704031031032550b0f040c95120480240481d5071241 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 702891447 1250 702890197 702890269
    0xf01020307110c0a090f0b120f01060801140c0a0207030609050604060506060c060f071b06060e1012060506060d09031d041104140105070b07050a1b02031b 68
    0x3441d0003000c5502c0300c00c0403000e05000140c1006801e0b020f401a00c3c21440c1140c000b018280020f8070151071611480c0f043d103151030740344c20540c21942c103400403c80718208c0390b015402c5a0941c1c00007400d40c1d05000b40042003050700ba8146800ca5842103040d581c8400d143e07403c80c184099038000800150501b14020f05002000501c14000c42c02400200880e4513104200034541c8510803800100740c000d40c1c0000c07107400e0036580302c5a1014a6090002040010a00c0c0c0c1900340643c40c0211020b81c1d403100140001e100c0c1e00d8000b50b105001421040c506810441c0c0c60340c9018507407030000c7c030507500c0300c000a2030780d01c424056980b4014401424042180c6901d000741c880f4090b1a60b40c3e1510201c4810807485141500400b600c0600d4500000d240c035041400d0001c0c10803a0409031410b02504010504c0001e8003160024403820f800c0e0785589d15045051002000700241c50391038240c4000c04a4170a0140e54041042c10105604400760b02c181c900c00804a0584080c1c220a64400c60f9403000900c2c92032001c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 702892697 1250 702891447 702891451
    0xa0210030e060f1021060b03160b04030c0f030503040e22060f0f02030c0a03090c0302030a050d12060e0c18091602120a020604030809030c1b040c0305091f0e0f010203 73
    0x1080c001408251174107804000d8050021104002d0301e0400c00140c081080c41e405003a000328041c050380c0c1c04402100300070762900350700d0740110203c2200040c2001408000c6d0082e4020340f50307107209160780c00d05e180c588075568003c6000d44903101116901049017101043d404d1083c844080c89200072400c958204034009010b0003c121500d40d080419044004640703100f00e038844d4450414003410800c4d180c3d8110002c21603418100c890421180021000d65810000800002d10400042c00303900c5030410b0041c851441020b5421209003090014030144414040c80c591110302c1303103892034541c401121409000c48021051b00e8101055034188100c2034006105407201041c1c54003240d00c20745940703c2070100ca100300b40702280144c10040120380020301c07aa4900790016004002c490500341e441c2e45680c04c0040b1419042c420941031003c6800d01e051a000d81d19406800342000c024901e0004080b036140ca96130240900c1002c000801c01030303112081d9004081d0b103003404080b0b400000000380032900035802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 702893947 1250 702892697 702892711
    0x50105130905150f220b0112020f0403020307120321020912030c0118020a0311150a18060810090b0d05060405101107120c060209190608180a0210030e060f 68
    0x1442d0900d05505010751921060001001d40d054a41032911141d030042c025019807d040001500440f07050703003414009092901d040c2e4401c540d40318914070405240c640706a02c140120071120f10400301003504500246c280181c5420000c1241c87d60003da800248956020180d00600b0f51134a407020380700c000064040c85004000030815a201d1541007011040c1130b1000a502151200051000030003454001c1c402c014050044150751040052a00702500128604000a410340d02d10845030301445104078010a07450a01000e03508042000c0074400d0218014000260b495034103464641d01c924114009958001e815181e05080514000d501c0d18034a560b207071003050070050b032114911241c5040ba080035500030b03d04500c114101c4130036601c0d11801d650a45100d0b03400d214101c940d440c0d038401c00c081010070104045660303080110203428080e001d0411040400700d000c0c1018648000591038140d1601101c2c1008500143c0204030040c248050701e0340054051201803000903840b0300202802081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 702895197 1250 702893947 702893959
    0x903080601030b130c090e01030f210e091f0303030b0306060402090123130303080405060a06080a39090c0503040c030605130c06020c03010b040e0705010513090515 72
    0x8844004400743d525551000e42d002c1c04851204016110036417020301c0d010818100082e401e0750760307070381c1e40140c00b001d90080d581d000c0d942c10007000b0040314a582c8140819051640500300400c0c0030004d00c035904516800340a480102c0100c0c52483c101140600c480010304020b00440d916032400030701802a030000180684a43c0006c00d15620301402960252401030750303920001d80214940058118208404603440982000891030242031230802c5c07800b86000761201c10b4542081c4c6030040c82d2a600515007034006207006d00c1441501c41c04103529104a421030031400c0c0007800c020410101500b0019609030301210070303888031002d174400095002190081d000400c48442130344230543d0075100c1103c0040c1812449070040c0000380680d03208a401022400500705c409580340c0c2d807002d034181e4540201c009a4003110501e522490300340900307000400e003940d0a0160800b480328007070355801c0d00e00810303040c03141c003042c1030780c0744040c000c176000050041600a02c030301d0a000403000403849140300030314042e032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 702896447 1250 702895197 702895201
    0x60b13170f03031f0504060e070e090f060f010203091207030311060f0a18060903030204051908071a0c010c0f0807170a020a05070f0b06040e0f030a082503090308 71
    0x50008a04841e6801c19100a545150b0301d425110a190984074011141e00300150008156900c0d81c1c801c45014100d500c40c40809800e2440002d003005074030030001407003041802e0400040504082982d60421419a0610444280d801c010f07815070246818650b0026001101d8a00d01c0d480003841c4c2d02128040d46402090000308107103652a030b0022603008441e2500040421056261503000140744520b07101c60100b26441075850b0b02c16658503140580c0000e80210701030160f403400d00c0000e400610305404206400d4907020380030747c81d0415803107181c030b441c0039520700014410209803c0ba80d010034400020400b416a5400251222206a540c1d6000a081c03000080da190b010710800d00d50f200840e805131000d5034454030400060342c015a6500300304003040c00600c000034030b00c02e83c940ca564400c80c880241490550248030841c0c40a541034001c0764012200342084840c00310860300c40407411b190149280d80c03042401041d0982c5100300004541030030348002c1c0902c2e40b561001d0032403440307941c401c0f09513 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 702897697 1250 702896447 702896489
    0x10501050a021c0c06140f060102010e060609071b0606090c05070201081501050408010e071d01060c15150605070201111f1a150c0d090608160201060b13 67
    0xa001d6115200301507802031400004140c080c09603180c0c12103a0340b901c0321a460081e0b8a03503041c0c2d4584c40c0c00000d40358210090204003d4400c044a43c880710a00c020441e050182901c00d80d6006c024040300e0007000341d2404596564418811803980342c4c4c40d8900120f9501c0c203880d00a0040c5114410001a923242a26170440d00b8412422119031680507502d0b00303a070751141d0286103d25000020668140001040700048810080c003a540040c1107050182401500c0c0001e820a0540d1300858454140320000040c401e880d0030941c0c1600013038005002c1c01d030308212030b00c03440020403524074400d0303d2a600c4040010441c0e0f104c4020200d1500c01c0c1e0380d80c0310901d4080401a40c03101013220960000702141200340740000340383c0c8076454400d41c0c4501404211410000315182d07a406058080c1c1144001403c81031004c0e04110110881c1c5561802580c0e00c0d151000092070101c000d0150030440340c213014402c1d2128400d4200c500500000c51140e583c9800f000da958450004921540c819407100d03110070403070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 702898947 1250 702897697 702897707
    0x106120f12032a02010b091017060403140c070801020d050604150f060f0e12070305060f010e070509040912120b09130b0402120a060603110d0f02060d090821010501 72
    0x1c60444250310080550500c1e224003c00110f036a40d404540d80c1c0d000f1101d0941d64041c0d8680251030300300228420500340b41980f61740799060381101040e40c0c0007030144400603610a5800d4080f4481505c0c0c0d40d12000c001c0341036402c0c0001503002c0c01e09580041550f9140f400300754010f9000395001c54040040d903604610281c1240141c0c030444003010b1011030100007280c02509845c41502862900c10035185d034550010300109503426560855500c080014010008100006504104a0140400503602d00907000d0b03007606008020800708400130810b480740703848507006910780c1d079030000304807904900c40c03000240582468400d1828503410141c04140d00e04181c8200743c020308010405030000342c1c41d51140500c58601420803a04150701710a90303490104203120343c0c01500c2c412003011030201c0c13035814014241d0501e2071030f0070710030200303090360400081e8011054142c4580c1910381d0360312200000c007090700808861001400e01480001c4100c002c400491001184601d419071340c03d1503076210001121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702900197 1250 702898947 702898961
    0xd06090c0f120213080303070215131704240306060903020306010302040e1507021f0506010503070f09170a0c061404090525050a0801050906060a110106120f1203 71
    0x1000c100041c0300c8034007a51203440040d0428100031805860100740603045980ca14140d40031412940000c810301807580d5051000a600145c1d065a050203400c082c9429041026081b000811034441506100401e079094421340380100703001000d00c00c00450002810348100900410703540060b00e41400880ca980c054604d620640f038000d801401140c0c210750900004181815440303c8510585044a041c14116101e0034440c1400c0c0d03002e8140400604e03120110b00c1c00c0034044009039400d250402c08507076406002c1d00c0e405409843c021010a26800c001d0f590309095400c03007041c1040c2041d0040050f07000113241c00381340b0b20031215054101d54410040740d840008100d81111500c0410040002c150150001504080c40e21102090001c1e07218009054070786416803000880e02c007081c00f203c07254020210500401e0309884200f83c6140c80400528240318038080c40043c04080c2d4540c0e0040c200035440782000e05009000795181d820307103050800c07a14400c44002c80c1c0340348055807501c00c040d01c80e0041d08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702901447 1250 702900197 702900221
    0x130c11011a0f03030f0a050a030e03043b07020a0309090501050f0d03021204060e030c1e040921030213080106030302030403080c0a1a07120902130504020a0306110d0609 74
    0x300c0c507090306041080c424082e0b400e41e0b40c5840280050f68054940c0d500400d0301022549640755105104000074098402031602400e5981040c0003c105850b402075803506840c1c40441d449000e21141d240c00304170b00d2240901e8080c4a216042040038242c1c0011f403070311081d8040e40301c803c1019902c40002090300c03824002d02e030300503011a1002007141040504070001611030700660f030140c5149500100b180c0c20a030300c0300c0005869200c95040c90f00b410702c000f42c601c00d0150f598860140032441280701c1214141150f50203199620100414888000c4141c03410b00e0400c2c042c444a02d2046000034041c0d003022480d1844a172010400040510781485640d04882c1d0540103103051910710348507501d540e080440d141ca02c900580c0d100d2800903015940000341e0200d8014022210304114000a01e22072100c509030141c5481c2440c440e004d40d591010b05a2000700206022405a03a81d1020641b2000207501c01098107040c6414511090204030281180d079014080411402c1c5c0d8943c10030b01510b49109030b039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702902697 1250 702901447 702901481
    0x9090e19080a201b0102030309071701060803040e0919030905010c23011a030c0a150e03190501110721030e0703050c0405060a0f0e06030c130c1101 65
    0xd0004441c000541107001e080c1c10890418607000309010724050400d211a02503030448040842410501402460404001e200440c21460000740080e80c50415024107800d11038a20b120304880d403001d40204001d0301104003030b2503d41c4d41e1001c2c0f000c0590713829140000a0b02075214070309019040400d41301c1c442038040da55040d405203402c0054885012264050790000d12000b201d102003119913540326074407807101c000000c44120b82a40d84108108069045e803094100c2e01301c4020325580c581d001403d840078481003d80400e920700e02682e0100e00d40b03d900b6054014401c0c503103480e00d81c00c282c1c440710900a10092005070064a120011840b4800d80103100034444050184404035220032900403c00c1410005061201062001e00e004007550044800f0b6000e4421452542060300440b07030007a00513512280700d503003441030841440305c81e805a420321100d0103001a0702560208003d012001000d0604d0304000b40054910018041a40300c0728081002a41040c6c0e03000030511543c0078200d072415003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702903947 1250 702902697 702902743
    0x9030c0613020d060e0a02191413140709030c090b0105190c02091f09020304050703080f09271b0316210212010b07080f0702060d0c09090e 61
    0xd1025000740c0c44069030801c242440c0000091028401c10001d40301c100000c0c00c211100d80f04028034050b182121000740c104240302004418660700783c00000070412500300e824070401c181840f0013030098250300700c0c2030300d0364100b448000c64000185a064a0040d81d03542c407800c1e140c8000c6815100c403c1c944900081c010000a84181c0c00343c14404041041c034940007215004540014100e0381d010f075042d030200d102e00c960004000301e5400c10140140708840e019403e516054880d6900d658079880080c0c8213034400925151184000c40c211002c04200070b0140005421140300c1040f10021190000301a10440c40401c0030441e0801d0a2001d81c0d41003c42e69145654802118a92120024044042c0911000c0b00c01100341c11400840b01c00b054a400142c4500041c1100c04840c2c106034003407040100c0070004c0e0008200300c9012984038003c1030410355a0ba00b081c0c404a001032003040d40d0104074a00d00345001e035115510600780c4080b03803e410403e00c12484400d40d00c40e290822008401b01124480c06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702905197 1250 702903947 702903961
    0x20a08010c0221070605090c030f0a08030a24030c050a082e020408060f1608040305040b090f0d0606050a141305060607020d060c0f08042a08010c03090b09030c06 71
    0x41c07465a0f2803154040d071820450196070b0380090740c10942d0b180f285c40e0410140340320301c2d0404100c8400059a00001020350803182e88680109220180c03c20a445840352410b080d510b07059184051000d01030b00b140c000080e0b8034109031005074668014148120642c010001d41c20720005400411144000c140a2100c64003104e00d4201c0300340500a0070103945c0034840000c9455044c13000610680315085001000d03d0518944002c40440c100000e0a1002070414480401d50203c1036400352400750241513900c918901c00906e03805180d15400d81d1004842c10f008040000d2b0340c00c02c0302150310035941c00e0307078894079504003040001d031035050140c0083c1100c0036a240d40700f29400641d005100a0800c6151982c0c1da00403402c520030110090300c4054691a0044548e540301c60040c007500094645200181400d60340c04210440ca0300076205080803a030041040d031000340d03600c000103040110082081302c00f00039016020f0007840c0310540c2c151140400144401d034001c400c88041c8100701000d01030715aa194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702906447 1250 702905197 702905233
    0x909070e1005182124070f02030a080703060308220501050a0507022b080403051b0a0311030f0f0c09061806060703030b191403010b01080610031b030603020a08010c02 73
    0x45284840300d50340004c81c01c101c01c070501c11281d8041008001d12415103501041c03203a0400d01404610400035083c1b02d43c40c80990101c03e071449103150f454454459114a03200b24040e05658101420032803001904501204064500600c8201c50000039043e03295039400550341c0d40038a10a035004600c042022074014079241d40c1c07540e2400114022603058188004070704100e20b50b10f40c401c68590200040074000d01008020030820303240e6843c40700002c041d020b004107921158911008100e414003800601150383c0c18803c00352840041001c81761925003e161281d641c0c1000020036000e03a1203103001c1070300e80c240610040844000b4280702d01c01c40e02c66805100c0a580131040c103604050351004100703803580d0b910040740c44139101281703461701e2181090003405c1c000642605852003a0315000300c50407103980082407183c2c40030b01212009a250b110302415005850f4901540200e910306101d1400c02d03e40607400700040ea8002d40d05101041e03241c50101c1d08840c094040140543d004a10954000400c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702907697 1250 702906447 702906469
    0xc100f1b020d0c060e0d02011413020a300305040504110408031b0f0d0807030f0513020121050a1b0c081608071401060e13020607060f020909070e100518 67
    0x24040005d69443e0700b0481d14140305c4c01c0110800143d4440311154a03001001e001346800030144a01942c071540079a000622060203440f8158610340b010305560300c200300e281d0418090064002445034440c080d4074008009038054004c541c4645c0c80c04d54050104840d14050310b007941c9051009518056800701400b46c484030403800103041d80309a1a44020522081c45045591a41350300c1d206504d040c000000b03003d0b0780c1c552180044440c03500c0308200f0800340300c2c1d100c0c0480c142c084c24601c0346841c610000d0100307000d02100c503041c8582804203006000b407040e842407070440406881d011109102c0e82d001c5404030100d440250900d003041c0001c2407020000004115118803a9440d94640502a900c0c649959940c425030007441c3d640703441c100400080800d2441d80034070501c1e90340d9082c3c00185d00003046802040c0000e0b003100d903203c10104a640e6564112003c000c0001c0c1500a01d01d4031480041a080c8096665030280d41450203102290f8026001d0f00e003642c402e600710300b20881042d014030401e8440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702908947 1250 702907697 702907703
    0x301050c091c020415150e010c03020a0f0c12080301080f0303040201020322121202010c050f041a130b0a02100b09160309060f02042301050901050706020c100f1b020d0c 74
    0x2c0d4102071710300c0c0d4680720560303002042c1c1003030b0090301c020b8000b03c054400c3c203040c6842e074144660030248500299000c01d84200041d442041500e280724203083c000070300452904444000803880b50f030101480120310295048482d114201c40418181d82d0178070341c41c0d0200b650001d026900c1403150b0701900103500d0280420450300d17000010720b69640d504041030700c401c242007940e800c81c107a43d450250b00d80c28000c459501c60316061981c07400c0c0d505060150703d0321403441100b000e4118456200e1111156000312900004c1c0d4212540e01c137030320340c140300c0c5071503002486000141c4603ca880e20030b0ac01d001c2c043c0d8040e030342000b00041030540d42e50306041380c0c1020100340d280c00c0507a01c19401d000180701d4460320034803c8054400603100e50412540c08a1400c020f4502041c2914092051140d42c1c1c3c490210341c4400000c1c03034100e4544600d49440e8020b4010852426954000c880741460040160791000c04460301c810400e1100b1214089000030714034841e071b40540142c0004000703043c0c080c0242120421588 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702910197 1250 702908947 702908951
    0x80307030804260a0815010e03030d0e01110c011418070e0c1b06010510020105190c0516060f2403080a1101060b070c0b0313230109030e0301050c091c0204 68
    0x40c1c508032495150b404000b4180202e00c0031800d208600f420006c018a44900c2803e00883d00140080001d42d21b0040403900c40d0030a45401c030342425032000390010310f401001a08069203a002d8688401d000e00612080301d0a08a41c1d0400203c80c3c030710701c8100340b6180101c840034207c03043c240701d43c8001d8940000c0407418170507000c03c00000d1074081105110241c800300c5001e0580355043c44104020782d40441d000c4021a030509061011150065822001201041100084989107500203440c0c1b401800c004009120003562080c1c14886150010541002610003c10440ca51802c0c01e6400041d903020f580e040c4186881d041c4001003010008001909840c1410129465070b410f4150035511140c12803d514030740400c8200030450000000390151650180090851604010a181c80301e200c002c0070700b03a118a040d115201c41600400013100010301d4000313004030001030802404040c07060512502a42c603200024004c9000c0c1700903200d603100024909981502403024505805402c54000d0380c1c495 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702911447 1250 702910197 702910253
    0x40f0303050a180b06040f02310b040602030a0305011d15010306050a0602030711030601030b130c0e01080309031209060d020306030705180403080f0408040521010c020115080307030804 81
    0x920400e0783c496190700c6000300a05603e460414402543e0121060115260060005801c241030460b080101d903078010442511244428400c0b50070451035070312100e03514400160100c1c03d6030f4080010145207010361010700480e41e8450403446400c9600b001c00c90b0b03122000700401d06690b002c005044070560145000725000f0f481d440010401051540b04c00c0150f0300000d000820003900215030007003400300310003500c82513141d600d42203000d0784010442c861407000c1c0c03450b50741007040900301880509075400c48100c9640c1c40303019071956035120701d0605100340b0070041104403260200044402090014000e18205400d268503030f40a0341000e040c1ba81d143c010894007056903141c01e0018107800c0c140001200f038078142414040c15a120145c200c50120b00d1040800c0003243c101c03c112001c880d002d0f00c03540040840b00c0d000c04c840400124010b40719500717110719100c540764150041102c0010200ba0389016690707401c155a602d00c40d4030b0005020400c8040000d001c114004031903000c44500101241a070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702912697 1250 702911447 702911471
    0x909050601181e0e010e040b0a02070510050105030f0f030f0a0e0d060b1201020306010806012d05270f120a050a08130501030903120b010e03161d040f0303050a 70
    0xb07058036000103580d03506840d04922103440b552031160041013149410200c41d41042140c01010a001700b02412303c00603034011509030243c9604540324942c00c1070546080d142c01c501000d024040a214040c030034400c403000d07070040440103d503601100000710b00951401104d400d901081c0c0c3c0080c4401018803403803480d5100661a08000030a82b144145000078030603031003d081040316100245284d456a2061003080860798002c0d0005402c400f0908000a411440c10f0302b07981220f498501700703416400f00900400700c3d26040b80c094081207103080300540c0d03810500d2984007003180c500031030941c1c480c8548450401c2070510a0000d94000c41d8003040c3e800601054072030918084140350210303410344000070204444d402c03050082018040920b0240b02c11400d40e00d000f8a41801c4803004d0920716564020186241c1c0550503010b0022006002d42c3d521020400000740564201d1160a80300c1005050205540580d0f000c0c984c4034503400f121280303007c040c0c1e4030210002c0400030118403911b5a5204e4200003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702913947 1250 702912697 702912737
    0x60f010f02100222060507081602060423030d020f071509261203061e032a0301060503010b0a2702070f020f06091c020f0904050312060d02010909050601 67
    0x30003024240348054240c0500555074080c1d21340c0d4012410000c05105000008010030100c440500c88000700d0b0361340d4086800002c51600c0b40d907118401002020786802101341c0144e90b04507021601710241d86064511800582c0c4520007255108115080580c060051b640c9061a0b41103654092034003c3c4c98644810044114540d0f0b00103440901c203903030361850700100301040809240ca030600d02044c2182000404184d1500118035101846500c0041500d800d807000c014402c030305013010803000019000706c40000c07480d504910320140207500f05a004940f40c1414054460851070240010701c0c05480c001841d94203a488281c00110045500c0b2511043c8075140041d0142a018001d034220030003491040040d0017100c3c4040d9402840e0601c980c5040b42c0e54940e01d0a0031600348411003407043d229100050440f285803115070752080c0210240701c180800000035000712041090154003940b10b800800c0201100344034000e0009128650600c00d4111039000309400c0003040c104000703180c0e030003031503121 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702915197 1250 702913947 702913957
    0x6071103060f0f0115140c0c060316080c0a0203030105011d181602010b0307051c0b0406091b0842090d0504031e030c0b010e0a0c0305060f010f021002 66
    0x2114540300280001d103250b00f82e529005080c2c201c41210700035480c1202410312001ca00c00307132407220701c0403812190700310050004900d07512000303003500e07501d00c0c01e075414032003000b4131098200018076143d0000f002c1d00114000c83e181912160004c60440e840e08004450440c10355400341707140b50681c00d0f0100c850301d40c002e42d8625807040406042407441c0001c240075091000401c10021603041c03280f88205520003140a5040e590169041105213108910307504202910807001041034a00100304802e101083d0b104010170341c4180004000484140317080704021a0074050580960800c01c11a4241c94000108048030040f03041201e0141c2e407585003004c1c2c0040460140f0803110844c20400507030101c01d00007013890343d160b400c082d030406056031550344a9003801e0751007a0741220001c0300c190070705000f0b00f440803a559100e04120340d65030b1610b03400064010300b0740d10b00005038208007850003054085c0c02002e114010181c241944e03007401c0401141e507074800020100a600130905003414100e41800104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702916447 1250 702915197 702915211
    0x605040605160e09060301090b0f0601091e05091009020c0f0607030e0a02191e0311100c110f100c0209090d0503010b1312050c030610050d020607110306 67
    0x101450682425026594001c15540746a00c1c10360828600a400c04220b21020b401a90a02c61300d55130030001c40e0060950180c00b802000c3c0b44410012503e8071410014800c81003a41da4011855641d00c45c03440390032208040c4012a00c4405090045042401e00c95130702c6400b029140f03442c1541d55108600300e0b40103150180043e0006c00b1041284041000381c5034001320b4a103010088900c600c3e00305030321854850f030000c1c81403981e60001c0411003a40c4400501071310040391400190b044d040d08882c01a00c051204031014030788400c090700b09113070043c04484120956200d804a04c0e0b0295035040c4903034440010607038014840244044582c403800074481d900c1c40786840710840100c4a0041110000c0b004261100136400080c0846010f5804030a6a044410700f854054980305000520099011a03400402e4130f102c49003400310a0003000250001180307011b4050300c8107a1100a18034044640a000d0180c202002d4403407540141008802002424098a02d612101c024040003a04252080e5007030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702917697 1250 702916447 702916451
    0x2030a020d0615080c0c0c1509151b031602100201110a0e030106050306090a12020c030a06090312110a0f140301030609050d0206090601030b060f04090321020702060405190b0706 78
    0x210f902c40e41000304030303801000030b9070030700d04108001862079034420349046000d004024045001c588044850f05888400c42c0013420f01032100a486071003071150b0480b9403001c0940c0c2054000344261000403044400201e881c21000440715616000d00c090303c030751003070400c045650f201c10b0455240c15280c06070030a5043c1d55a1000281e00300d41c200740c00d445141d04924441e401c16030034028402c00000e00b840242d40d0040280168405001c2c042e400e004a6030700c0c540d00741c0600b80c3d03001e04100c0d0540c80300340101c4c46a15054048916003004904617040800a00f801000410505d4a554020800c0644003141441c000c0c42c07119211107c0406600203a100b103c00d80d448100d0541007101c1404141851000d85c03004006600d07265901680d1200c0622000e8144000716000c541c40d03032a0708040951503e07014106000c0c0d0b110340d2a000380006020074800c5034200301e0703490b0340d0070525081c0200c554258008001e681043c1c240070030000010804610007120010503000010300308440e601420241e40140d41c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702918947 1250 702917697 702917729
    0xb0406020c0103060b0301030f02030a1202010209042912010209041b0f050325030f09140712050a08090402042301090e061c0510090507080c0a03050d0302030a020d06 73
    0x391070002601119030625040001c20700c804c84500060b00e044a0300005e40b10001c0c0c0395400403a05140c00b050000d80803038405c3c09490205501500101100003050f5002c0218280c1c800004018142d6016200840d9043c0007400304140303030003060080b2000700302000510341031055000500b2901c414000419851040000444036500314201120501c824200140741d458102e814070002d07554480078003942402000000d408511a912001d0810780d290000c010701942c504046042400c17650301018280b0a40030080360b50101000e000341c803158010020190050140c0d9801c500c2d40118114540041c4d09200004240302d08503000d1544e1440030031203400d82400341000400380f10041c4c200103c2c100c04c000600c0103a03100c05d489038a50b40070f164540c18801ca0145042410880154900d1102c0ca0400d1000745c107004002c03072280101c3d0103e208039041002c0704010b10000d041c091202a20a0700300d059481c110078000e4000f16407203401000c0051401c00c849000e07408030380c41a04140058003113260 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702920197 1250 702918947 702918959
    0xc080402100e010507080a0210020a0302090a060516030c1b0f08010501090516030e12130f0812030f09070305060a0204080105061801050d020d0803070206061309200315010b04 77
    0x203440441c050151034404200010440041c180d44a00007000f4490b400004542c10301510912080456260342e8500b0f5580d411080d500402940141100a20860460170006412401241201c10b4103a418000007001c0c07460380c400792541c0c1101c08054451f131038a1030000c841811a8501200505450315070804854100744201c0e003141d805030011000d00380707000140012803451441c42c558582061501096500c5e50045181c1032000e202d00038415030300b01180581d02804000a45c00c10343e0350583d00f441115541e02440d5030f0fa08080c012050143c1d204002007481900211001c42d40064928101c0d0b007002d950359101d40c94243c044954035046640443c051241d21001e019890700708104682102030300d41c442502e98074180040c852a8410703a49940d9440464940c03403090b900c0385410000c03039600d078600550065110a000c0301e9451243c0381c01410240c004030035105425915400c490905030823200c41e01959910340040940f42d40c50b1088802d04024081d031080010301812141c07500b16290303480c1070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702921447 1250 702920197 702920209
    0x1006170d0905010c0f0618080405190e160c150f06080a031d0a05031b01030b0909212203030807050c150a02070206040f0302010e180a050405030d0c080402 68
    0x3003200800c001181a08000d41e80e80800b0740624642c000400b412084083d107004001402861540d0540302030b44c10f0b00c3d0b02805039002c090000c44038186c031000317601810721421120701e000d2400b0302c0300307032034040380c00704403c40002d0f2841c800035221400d0100302d028540d00c0d001c1c03e8030031306c00281c1101915a030b01c440f2011050300845005100502c000c000164440d03a01800100e0942c8004466a060408202455840d1480d20340141000341c20f440e1071590880c00c1c1d442e02490074001c02d0100c1c2c00c0110403042800d0880300c00c1e03c21a4450003420404625040100300003548103040f14003404140403510109041c000e41c2c140306030806c8401000c144c1340d854080e00300c610060070f59082c4207060192011244011950171326860001500011664403040410020701541801940141c00807a000c1020315540e00f4040903070b8000d0300e40405070781103402044085c280213109440440d20072000b0506201c00303904510340040c411015207003805071101154049550301000b11000540314014001941018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702922697 1250 702921447 702921463
    0x3010b07051216020f011e11060f011a070204060b040905040b150f01200a0b010f29090a0512033105100513170d021f020c100617 57
    0x520ba01c03800c04032024400300241000c4200a405402044985000d0f60b01ca005984900f0b0001020300d600d1142e5584001c05401c0c0d46c0350200c3d90b40c0b0441012130120101c00648a04985403004402c2d9809004200c48100703410008040f80c00c2900c1d0a800314101c01d504020b1b1000e40b01070300307000890b071405043c00d4440e00005401004c0d200a51140c990340c94481126100108001382811180a00c1300f14403011021000f100289040c00b82c619a4020040b0762541c40c0c0c121202884c42c07014071602d4090741c0191303000c2503201440040f40d060004810703559860181c281001e000304500e0b1401d41e035034003156801c05042d56956864000240c0b54002c0b8196481402030010b103118144152040c640314042d40034501d01030b0511501170a07600042c080d01c5a42210702c103103806c04d0b902416666a0b0381300300308503c1041003e82c07903015072905112524070018101c1c8480c0c20070b0f50380342031804003460020001e611032a007080c146d0207040f1103000320390141d0194600921103111407420b0002c285400b20704050032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702923947 1250 702922697 702922723
    0x30c02010e01171b0d0203040305070506010605030601020a110303131503061d040f210c171908060a0302040e070e0108060712110909090601030210021612110603010b0705 75
    0x20000d03c0b0b6801c248282c0ca96900a070310560f00340c5944c00355001101a4019901c464440c03074000000c0004041e40103014090007031052003100c3c0d4a9072074280035981c5000441e10715006178400003144002c80d0080e080512140381c0501941d20b01400404860000e4145401205d00e00c0a800c80503031042c0d41c117110754070041c8601082100f4079000400e08110749200908017034140c5462603010070600030144520100c800140708260300c100200d20f806414140c10000595108802c84040114480c8100442d070190400d924020459811020203030360282e8003806041e00f15a81130000300040c0ca9920808011400308001015098075202181c9013044c8141c00451064002000740005a9081040940190004130f00420803403401c243c01e500300d00482802d207502100c07030002c0c800204000701c0c0c0607068a0098132040459804800241d03030b142442131401d2000310101004000403800105280c0520b4441d4408035141c80411001070b2803034001382c0000c141d01d04002220030421034100918075842071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702925197 1250 702923947 702923957
    0x9100305190c0e040c050a0f03020117040519260d0b01030905030a05090402070b0a0e010e03090a14060c01021c0b191205010b03060c0705060a060f0b0c07080604030c02010e01 77
    0x1c180d035940841d40c0140b0800c1a009002e1001c41c04001c1907540c43e60113008007410000007980d031001c200042c001144400d90102d4030020f000c0c0c104015840e6000d11a540007030040403e01c07212041c04104950a940a03585600a0280c10316100100703c443c20841d50020b08007a190380721090f407002120220400746041c5032508a1080c001400130040e540c8640d50f6080c116201d411640101c2d01a114845c4020102d03888102081060b4100398021031609050318001c001545160382490b680344a00c24070079a10034015241007103042844140d0050f4040050101c6003000020900103099030000100c10a00000c050b90281c1c411901d4803400002d540304480d071201820b041034950401c0011805603460000803550b8800030310000350010403e02034050300301c981d90700d44090403206035000008100d90a029420115503148024002e82c0255012807015a811914007041c4501d16440b030751311180304d40580e110004640c482400b40604c030360b0207500e80b444400707a41d100060550b87e00c0b4070b500d41400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702926447 1250 702925197 702925243
    0xb06030304030b18010b0a0f14010e0310110705060f1816090203040f051203190605130902010c0b010e0115021b061b030d0e060c040e060f0a0509100305 67
    0x9598014010341004c03040d000c0c0d444040d20b100a4a0141080030005a0000c0103c1e00014034082d00c10318503030440c0e401c100b24810b440e48040c0112101d002000845e42d05a22951240c05080c0d240c1e03000961420b843c0c1c071001e180404a80e103090611070110384242108901c00c0c10400044d101c81240b001c4184404054896110b4140d403100e40549070303005840c15258040000340c1003003110b00b1741001c2640c00000320340f0461800e0084500340d42c0100d45480f10800000a840040602c1c4e0042c042590002070174113003400d4010201c40f0092410100607410403800741c4403031010030500c240c00c9029101005001c909981050750112580c10050108011588030b490b000400c440d030040741d1609590103d64070380e80d5046081c80c8254981c04000309008a0000007622043d14030300d64040c1c00311324148010380d101176903026180200c3d40214402c40304020052000075025107480140100c841d44004d00e601c080f582c0303d401044000c81304a40008115106120600c03d00ca0100036944030810804443e05481c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702927697 1250 702926447 702926453
    0x1b0307030207080d02070e04020d051510120308011a040e0406050103020301050609091509120c0f0c0108010e040f080d14040318060c0807060605031906050702060408042112020a0b0603030403 84
    0x204420f1080f510507c952034089400c641d44c0440000304207404c9000c607480f0300c3d0440c2a031042078000b40e590841580c0d0b01c0d4000250741080c21544c0f000355030552076a8601c0ea00c0c201d45044200660158140f20390410800402c0b031803541900c6030701850050307000252541c1188181400c40c0c3c03018000c00d102c2e510540411200c05030000781448000302c0d1810b100440c0c2c55000c061483c0c8100c14580d405103040116030000f100c2000108040e9001d8010121203600980303d0041d20007403c01c0c06401488416200005e000c1040c006a410950340b00385034542c580020145031504546040020401204186052100780765010300c492241e46081090304d8040c902e0010050b0040a480c00000c0001c94007141500c1406081d90200c402090050251032070b05000004800c440000c12508440039860240818581031000138210f11855101d4111071419040c550402c08800d075082c80c40252802511075040090b050b10b54004555203150018196070300c0c031749454084200020041802680140001c01c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702928947 1250 702927697 702927703
    0x1401140c03131113090c0b1809040f06090309230306070f27031704050609010c02030120180409120c141c142d1b0307030207080d02 58
    0x700202011488200249000c140314036030701043c070740c0c0200c0d44040b101101d0244d800c40c1c202188501000707590142c5500c4131070598060480d01c080f0f4607120b8800c091003820048441138025006a00d81c000d1400d060391100242d60101001724002482d903d403c200d2900300100c4e110028503607030a8a10503089000c01700303a036444010200305c10040c021880040c5240a051014440c2069003041021405810720304070491040348400c43d9650301129800030212104001d030781c140d440c000c0c481c40c40c0039a9840112a0b43c0800801683d06d03558540d00344100c5540b191501004072080c02810343c07078800d080c4910444030207200030740e0300680c1814088800520440b87c0580000320303a050a02003903407281030908448056101e40c40c8603129652602e0000b600c148041890000c0c103641d0042142e0301030500d8035036405a25403c102120040341d8210300c116400314690305402640015a06107000d840840c20110000501020307140c20009404003455418490300ac080c02d404001051154040708000356 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702930197 1250 702928947 702928951
    0xc080d2016032a05030315100219061409070f060903080d180f050303060306011d06090a0f11040503070501030b1c020d08070b061009050a03080309070807031401140c03 74
    0x200071000400350300c10f030701408010b5954180a010303080031003040c1c030308203659601c282d034054048590742e0500d25007417a02101d0214240c04680c080c0500c03a4001c4501c018a65042008561b4242c444402e55115202c0d124068420050706005140f00b40c50000c800c10140060b4014000300248010184003044241d402c4648221a481000500076128405074400d070383e000600030408485034408d00107000c0008050341c02040c0440541d105039a84500f070340443c4012040d0031044e0f0070444001050f600d000481c0d10741c404445100031417004896015541110482450111051030215050060707080420266010341001e007420050ec07824040000c0306401d203402c610050350188181c09086440315901003c00a40c03100718251910303014505801101800c4416501506406200c0c43c1c18901c6042444110b03000a400d00b00114156100c0d4030311031f4001441045c07207125403c0c2c0016400000c0000c03100031070182d0807690400001d40509070070b44013015160740402904409000d02084400c084035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702931447 1250 702930197 702930203
    0x9080309250b1b12070305070b06061306110c0910170114061315060944010b030304060503100b07050c0111150103051b04021201030f02010c080d2016 66
    0x500f2500b6050307181ca48025120744240c041e0b004110340c0200340e00b200140407001e11880c02c1900a0740d5110510006019000c090078203102003010820031640100d00501114503804141c46031280b0076800314404203425507149a407050140010003030005048540390300c28051500911241110f858103d00652007e864248544050010a650400c0b0342d84581000c50382001d02ca090550b0700d40014281120b00c0c810516024441d0a20f8060702000d1801002900b80c1c0501341c1c0202d20b00101c00e4042d42c1c0a00c1442403180d03503205200301003941c0420140c0010802c030780c2c1c1e455580c41c24050000030506180c2c45000900c00611500001480220316550712890a00e411407000b4030b9102103a1400052031a0034810f0001c2c0d80001c0140500410f615040b015a6151918100200004d0104030310031350b140341e410742040500501c001900442c0741021140145007504000410b17489080ba10b070b00c84a80ea030980341c1c2d95005004200900e294202d402c5400e520001c3c1004040447e20b045841440c0d401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702932697 1250 702931447 702931477
    0x1140414060a030b0601090e011e0b030f0a020f090a0b0a0e01020f03030604050403030f09050a03090f120605090703080f040f051f0e06040f0b070b0c04052209080309250b 75
    0x64650740b142801f1001440038841c001602c0d41d550451010840341c00c0250540040c0070100400c074800c85504480c050f000c6028070100656175115000c0c000d410090f00201009020000110036035142c060380e40203043d007250718503900c5803004405001c00901415943c10341d0000f64002c404a0f00110549034030040681c0c012a142d503e0b031a044005041143c080041c9502d082108030a205c000aa05541540b080d21400a071940386c403010b882d085100e20a010a42c08041155000200150440d0341c00002c01300890780e450340c60b41d4648509401c8000c03085610540801e00700040100c0003c410300030441611218031888144008110018103151000d0621003002d45c80e80494940304121030003090b1802c40740c1e001507142e50310b90003140d00400c001d40b14140c404011810041d41013040f2400c94000415001c1841204000c01140c1040d108071020400d58400d0524080b03416840194410501e0101810070854250710745282c1c040701030140342200440b50005d105452908040f500c00203000c40341 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702933947 1250 702932697 702932701
    0x60b030412030b0d21140405151207050304110603150d020a32030c03070e090312100e070206040c06030b061c0b03120703080402040b01110601140414060a030b 70
    0x260b02800000744410741096200c1d2903071082c4030000e108900c030340b681c0c143c000031402d40031107044038685400940e00324112000c1000b08218940b000241ca14200c0c4015124285141c5c4000c2c1d0856810803120310003c19000420402001a0321914006048040b99001d0860910740400c16074035840d8420180121043c0304002c2c00e40d6103034071031000249410702200c440d80e0641014580c10100a05018041c104002c110b07145606d400b2a0240042201a0040071310519003c03030040074100141160f0740b2400100b202d07922078010441410700c141901c4140480c414a00040cc80c0101e0f4024540c408640094041c040000e4031740e40b0810485d1b21514000c11200100400200e1910580c503c0c200c0044050700c55801d00301a58000790640c0c441101514100206181c4a80306885a580c000700000c24501c000b074010300d4903034050111080b040c5002003400e001c03030404030321700482a0010110f100b011011070951303152034060160401d03808040f031041c1e42040c070045691402d4501000f0304103076210700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702935197 1250 702933947 702933983
    0x305010e22022115131716030f0e27060609030a050c0f0102030a0207030b3112110318120d110d0c120f050c030a080613060b0304 57
    0x185541c0001c1c2c000f09005420a100300b039960300c4800142460700b07940550a950401085130245003480f90307401000108450003659544d003030302001c109110904040902c440c0d0241c1400300ba241e80700c0d500c40d8840300c00d50401c44c400641605440c0300300d01d100c2d10649006c0340c09006809040d050040e03410440346030980b82d9000190070b84c025681c0c1c483e05840340c1d684010502c000065500302d90b923400d4803051825192900120303100d118011030400503034462907042000400300700e01c01e9402240d1200441c01a02c286031079031042040c00b2800d400c906104200041400182d10074480c0c1c40186007000c112100325151083e403240107a1807051407a020300d1022036016102e070803a01c84583c00017400e1390440140c1901c042c2c0120b088650070005403103240c5041d8020b50190f40b200641680003100a500e0080c0f4840465410100c80d40c040c0400c40103000c60300303101c0001c0015043c1220181c60f00c002c07030b180040510160701001d4002c2c52205050803010002e07050a0800c8941013034000109450a01c001d030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702936447 1250 702935197 702935251
    0x6080607020c130c0c26070c0e07050a1b060612030503071206050d021302041a21070e120a140d12060518070e03070909020910030302071502010603120503040c060305010e 75
    0x10146203c80000a42c6004018040023190300b5103007030780c1c0500610f8a450004545601485208402260649a00d40030300001c849420350014030442004c10b00a40f02c44d05108a01d0021000b01c0220300f01009018180f42c00c03060100540603c1c0100300030985c81e10001400000c1000006801007480b03c00c8080c481c0c0310303a01103038042d02c401814000c4011b044818070280d0361000603e42c100c0a8150494511200c10b80c640c0360154405d41e0314280c0718030900302042135a40050301340c0d226510034821141d001400842e03030406c820039a0030180014161003035020780207201142000401d68a4503a080c480344c0d842c65242807403181101d480c0000755441c50826070b1140d140d9807a030b540c1442501d030002043e045580019042910030380344482d46c0d03100c20100303400b1211540001030141c2c000d0340d414411003a00182c541c001c640c80303200104a1554a44400c08201d90040c1c182001440000400080c403610340c01040c0102100e28040181c0c0d0300d800505880700002400d0420030604010303541c14440400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702937697 1250 702936447 702936503
    0xb1e0f060d14010c0504030203120a080402060306240d14100b03100306151401080603060711120d050601180803030601121d0c0f030a0201170a06080607020c130c0c 72
    0x440004c009191080f680608180c005e440200e100e1f104201c442c5940107031000aa60601086440b0040143c5440d0708200702c0703410081c56240c00c4086a101034481078510346152103a5414903081545d203009840c100401d075118240c1c50b0901e030000c0c20500c5810100023030381104803028841c283e0b450341c0b60141800281c00c40355201030412800c00d4500702280001480b15000c46010310701c0000c0d00710020005540c0d40070200c0b10319034107030095000504414002c800b2000345070001c0050703680b8285a9403001c2d56135009044000e81c0303281c1e01c2c405c110003035801c0380041c00b501201c204040e801c503150002942e9640300090059040005002502c0380006498200002080c4c0300a410f030031055200c1025580c0d10740d40e4441a01c01c40c0b800000215508010030803419146e01a5a040c0c00c8003a202c1d1980000e10002e070510300f00645d920800902808103209075402041164060324544101600300840b0101d20f80900903090301d481d00d44030500c6d4020750415100c9078407885201841131441d940350004114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702938947 1250 702937697 702937733
    0x20903070510080709060306120f06020f07051c030207050d14090a0303020c010305180a060b061605100b030c0a05091306020a032003060105270d0b1e0f060d 69
    0xc0610402d0b0550407890385442061290703950364820342c1c2c0f01000c40548406100d40040a0aa0700041c0701040c4818441d0072218000c600c05450030f01c5981c00300c4c586501c100f0085d501900207003d02004103503c2840c1e09a00704803444e065041028540300c054940000c85c5034901801a01c0302030100000e84d01d002c0c3c480e5101c00800c1089102d40d02c4c14003039103403000780680314000780c5071400081c00201202080c40080c2054030040c03800d25481d503a040014081e100c080c0b9400b48040c0100741e040d84a401c65080c5491007017001d842c2c11085601d0302030591305140c0340c403486908141302803402a00c40a1914040310340c1103510f0501c1d07444000302002c070310040b403c02900460002406810403a0590803003524100c0b100d803060004424411140454013003596413a00003001003000c1024040403140d1241d098800d42000754412980c80700080c0e11301ca9105c030403607036109a4020454210031030180d00e03000f403a5803116074031a80743c00040600142c0e001402d1922948075100004103105001c4210090000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702940197 1250 702938947 702938959
    0x3180715030e0c151b0c1315062303060414091c0309050c040c170412090503010e0607050c0f0708030408010c0929120a1509060b0d0209030705 63
    0x1056800103020b0b2020380a8188184680e40b0030b07058030b0501e021607201c1643c8003525a41820909200c0c82c0043e0001c090480c0c01c0d10078801d10102642e500407070f801d4400302c11503000038455068940c400d400d031056480340c418411101c84015034020407250a109035650b0507100d40d0303650f0384c2100040007845101a560b0003d5060070410500c00400141400700d00c9082a5954004004030340032400e940140000402941120010000d90708094000800c05082ca05102082c0311801c0c80b1510581022603040c2d40d80a981545441e00b144c2140d280c40150038190001d114082c03d0150480d034400018104c41c0410a0000350040900c1e400d004401c03501016109640300c05a80c0c5175499501c1c1c101e07014400f0154030300151600341d280036810301d078102c840c000a074070305c0480420707101490301101b500a112a04000c106100b020030090741128495a140c1200249401c0501a1019241000d81202003414504a010b00040781c0103000d03155250340b941c80c00360b90303803070600301003410300e5041c1e40283c1d0025 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702941447 1250 702940197 702940229
    0x6050406020d1a0108130f110d051203010e010f241101021209060f0f0c09031606020f1203090c060d060902040602060403110a020907050c1510051212031807 69
    0x2440c3c000e01903240030001d0783c0d603c1c1c0a807150000190200f0803080001c00e680382e4090064009207030849294800c2c0703002840540d850b44191075013401d2400120140310301c1480000140030181c04200c4443c050720448194051003810662100724810080c00102c0e06e546441c4850f0216903c00d01038500105e040e60002d41d2a4071107210450f0345544140c1c0c41107014006c03580056043c2210102c0c1074400d00444440c106d5684030008e0303140d4545d000c3c20707031943c02d40205142c03225070700141c0e02c50f5401400c47d64000c000785d0758640e1156050040c42410036190500030414400d1001000a2240b8003007021109141e40741403c2c92100014019a401000414008900014000d03008641c1c6172069002e41c03503904515010105160f01c40720920b4008ad80805039601051002d8401d02c050038540340d00c0e0b001c80780d2044d040641e400302600101c0d86506090094001480316040c1901d40589401d1188018401c1c283d0071380344004103000080c0801c1884d11a800c8001c0079603020400d040042280c80042c1201c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702942697 1250 702941447 702941471
    0x50303041409010506033603041d060a081f020d05070801030308010f0812091c05030d06170304150c0b0a0605100e01120c03140f01031a0403050706050406020d 70
    0x141c00004040d4440d11900c1d0001905003002c00480b4800c01550b41c0c40c00302c00e031500100043d1050342607112600c1c030041740c2d00002030050800003840604840600d03a20609030039140000f00003402072401d402244070342010001e500d80081c0075100c00d0410f440440100c140480c1c3c500007400f07481d581403411402c10092203283d0b900b100101e4113a034002d54480c103039a0380752812488134800a01c00c602440d0b00542c1d0100911082d0400741c80d1408000b03100000c22404070b03031100141d802c848030a80700c9400c0021855107900103845018003d284002c080444000484e2101d5128090f502c03c48520005401c4060565031003800488400d50340708919400345e00746980c1000051095005a50196556441910200d0302480032004901130580d01d404168400e015070707a002d0007003000000149500c0b2107894082004c1441c54501c0b41d07298080c038910310b605d18108408003102c48020101e9042c08601400042b9522104407a075007500140b000c65545c4862822800a100750400282c4861824200f4204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702943947 1250 702942697 702942719
    0x101407060506030c0a0b040905220624081507030207080406020106051e061c0b03030c0a0506070804050a0f11061c0b032e0f150801110f030c1305030304 67
    0x240c8020f904035480c00301110103120458030a4000c0c110300d032809000401000302260031065124020241002402c88800ea2086c2040110301e4221034003616040c030134604856801101d80940c20641c60207545600d44040c0795110880721604590618000c00010f943c58045c0c0c044030001c035404041165259540d640090080c505401064800c5258048000401002500840d0548002040c0e580b030300f00c08140c651514103a600c91070b0340483c3c903041c40c003405507014000f4003923280400026062034031441c40c110f0308100f0018805020310070288103000200d080001c40300e100740e91120303511254030454208104845c1030781c0005980000002600b03d9210203128150b5420000c1000c10f001d03801e4810f0416480d00c0d120344400503c0d855825100e84101504462a00d000118400000d5800d620340707070207010b441404510051070a402d43c020002280c1c24803d0340008801c602c1d0326820b102c116812004144000b5010324201c40300442d03420015403800e0340c50001080010101c03030342c56a5803000903030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702945197 1250 702943947 702943951
    0x60f0f0f18090f071a03090708160f0e07080c0a03021909030b0906060603060415050409060212090d0503040609052b030c020106050625062306011b021014070605 71
    0x10f070241ea01c880c68800300001e80b01040e00c00d5100500c100da038001c40b10541c20380008000020f6442100e200140601d4180174022500861805200c40740c5e080c03402d1700c40100c0c2a940006181c02c900801c20000d1540000751940002e502d40c01c0540e04da08125049004c0d000d035041d007800701c1100c51f500720000c40d000140305080307a106040904003036640346030007519000221243c580051081000035400d140c40ea00040e42c54807075001103200a51a1130121302241e00c00b072003c555035640080d17040c0441140090f400c3c0d00100210041150300c212103c014528000074100038003840d01d0344249020420203105410b143c00b0300c0d004c0c5030007010842c0c20203940c1e540d2500041011902d400c1180c0d06140c81806180c090340d0b000342040707180681d0a05012864000e10351a001488a840002c0001641d24003d03c841c0550000d5034410007842050201d03540d10001d00040c0c14400140d0700c401440c4001200c101c0071036011107110032580706100f025502010611079642d00c44500007043c001300440703640614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702946447 1250 702945197 702945211
    0xc030d1509021216020312040213060e101d0c0a0e120f0a0c0819020d051e07080111030402220e0f031e030606191412060414060f0f0f18 60
    0x800c2036103426016030b06c034422028180e505001c0c02d80014050304000116242b010800400000d18990f1000d064030f40322002d54401c151103d10280030010f00d142050040302520440c0b00c5030406041000e00004103108124618040c0501520a0b0002d580c99481a0124107510000da6030242a1071820760b4890180c0c641c11291054802e00124560b00005141c51a240c0c058031007407a190255020170401d442d144500300c4440c4140310611182c41c02d20420382c01058001d00040c05003c2c1044105400e6500850428000c02001d00c100300150340d0b0b01c4208011148104e00500d2100412070011019081c1d00644500a100341080c43e55203038070000007420300c4941c0340d00a0040c091881d000002a10050324002c3c3d00c080c00b0302c500c8036a0b08040060482020b190b08006140f801b016485260341e4005900d01038114a000c800c000b003a0403e4020b104801441204940d0245402000101c06210303010340c0034083c4400383c00d6062151107000c580110a8402004100c13103204002c04440914011140a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702947697 1250 702946447 702946471
    0x2030c0d0305041a010810050a020406050909090a0c1d0a0c090b070302160f0f140f010503072f19121101150e04030f0f0815130c02010615050c030d15090212 69
    0x4d000a908ac8295400d070f4050399a036170b1811f12038600300102c8079005049010b540c081c1e1900c00b0001118038132a04018002d003800700e280b981c2141540b0b0300c2510010484299a414100b5250445034805840c200340c51314201c8503502d4800d0341c1000c0f803511030762516810712407629000204a000c0c0c070f10f1074101154007181e4145a03203502c03a001310340e0820394401200d800c5001c60711071074941e6020b91f024580c0300c0703440c2c0b81038411054002c2612416040380b5225801c0c02210841c0c101c0203031030501c10b150300c010400c910700075415016503a10384500003009030301d030411001c205c4200101c030081d0401141141b101c007040710040d44030410403400c0801a10100c0120304210384440c9031b40e00404064400d00341540b03425131240c1e501c03890b80c1828107048400c6948a2281c001440d222640780c4251000041c070b690001078914140030141000043d440716003020301c0010b000c030b40100280007040743d1101c00700d0000400d4941030701262061000d13445c1c20107024140040f402c43d5071001a115000e01c03401d40c0d000d031313 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702948947 1250 702947697 702947701
    0x2116091a19092111010302070503460e04020a20030d2d0902040f02071218030206041406070507030b04060b040212041112070801061502030c0d0305041a01081005 71
    0x1540b6462010b60f18010002050fa1841e440198003035405030000038022000d0303074688203030310a24030714070055410b21244600e501070a040f0a008403600d42c603905009010324941071401c21074054003044419120710b204070740005070210101c0c81110645d4500c1c1002211501894800c6c2c2415126000340c11090501c610f00f541c503e152042d240080c5903281e0458000650150b000c0a032080500480801070b070b04503454a8080110001038401060400e0203100004006003040c1f000401c0010341809510708407400d14000d1026a442c0404c507421160b2461495112902c0c14000c01d10322b0140c080050424020740f50300005002d079040e9928441d0707100b00c004000e1303014604200012402a0000001d40c102e00d5030011303000481003c0407040c0070100420450107903c100c1405464805039420907141c99440c1c84003004401c8401d00e080303c0886040c00130354140a00034454642d038036044d4005004150321400070805102c0000c2e02103105040f54803109a003980c40d144c503144c1c2e4190095001241300c0c50500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702950197 1250 702948947 702948989
    0x20d0c0503091522030504030f0b04051b03101503140a031e0c12030908130303110102030432010c05040e0703060e060103090201050f2116091a1909 65
    0x1483d00c2106213505070750342c043c1c20041482181c01040c00440c14090200804000b1410009040c0c0001784a0441182c5510b064a041818022240240c5051000284040d070080d43d0100c1c0640c03188400032400161031007203641c0000c02c940301c3c5d44081e217030107162140031000c0340300403030340c008014007a1b12940d1003401c01c40d50024001e031024a180d00082c0032004000006030350081704141034521450007103106c11080d01d5020081d40550482c0c020900c00d140100b04140e0015442605840e241e03000311301714075207601c0d10740045980ca00406081180003041c0504030410b1002038610700c082500810400c0d8400c03001424582c060700801145800322400298420711074003031103040c1d9000c0a20f00c561901d4080c0154094400368004034180b00c020700500c03600f82900d070041d002c112000001800f80b04005038269241d00c201910a0161102d40c0c0c0050b074905420218070401c581c000d101c1640040c0c00c20f42d64882a000380524030180783c001600e84400c05a00486003000d5502c0c6000885d03804404c06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702951447 1250 702950197 702950233
    0x30307080912032d0903041715010b090a0905071713020d0809031002070c05100c080403031209020d060501180e120318030307020d0e061c090204020d0c050309 70
    0x10803044880e4000304002051085000c0012001c07007410388070303010100404d4822010420044400a0240d40041030400030004841e01d0300119103074160280500440300042e9021700710341405426a41940000c60400503210301c42c3e000010104004204500c0c101800003d104010846006051308040d801013181085100204907103698000c0c203002c5a07000c5556075070100e800c114105079141c09241c404200e101041e0004001d118811a0000c41c000c1c201000c0000840c58070416008205c0d5858140b8002400e020444054a8060401c442c0c00460120032401900810704004c1d00302201341c2e86601002902d402050580c0c220f19021030804d0005800344040311050000c02c6401d60001c00f00100305502c00b002182c201070070186030a0260000500c442ca9580103454000060384580c891910750399009400c041a400100c0d140e03031407c20114401142c2c2d01c00b00311142c070515502c0b100303a03046544d40c0d41101c654105211052001c01c1a5400151041e08200c907039941c980525020161030013049 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702952697 1250 702951447 702951463
    0x603020f060306060706050703110406020105040b070f0210020306030c04020d0c120c050d05180717010605060403030f210608011d0c09010e0415060b070302100504031209050a0609050303070809 85
    0x504113900381325141d281e050103008060141000c0c5030b40d60300500420701e8110001e1000d00307040d4001003114109803820300c0c1700c03e400034100d00410a500218440c0903501040f46207980c1c0c3c640c000540c480d183c01000a0800350145022544588001214182242140c00c008024a21620348250820740d081000042e24170008083d00040c004000c05054a080c5030f10694001491102d0340c1030011b80301b00b8075460f041c2d1a81080b030001003151015a503c10f800d008080207031a0507500309050a10391355000c0e02d99500b041e05041400b11012040c440c1b1031101076400301948d90710009100c62aa200d005900030314000030482c0d5034201c0c4001003505411b00098000d0000c40161100e0030aa2a1185404a03401d01810031242c4040e009916841c017069405443c015002c84101560355206074a0040e10f04200c44620038241c50500c000c0001083d0003003044032401c4420708012a0741030140c07411300d040c0b03034180c80e00900742440c0103055000d0080c0000a1361041545484440450300c2c0d8803420b07942c8402c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702953947 1250 702952697 702952699
    0x60a030b0a170c03070b0d180206070501020c12190338030d0905090c070f050703050705122e0609180318030807120c0f1a0c04052d0d060603020f060306 67
    0x1000200c1118032194000a4520407086221842301a15400103206a000e66001d8842d40e401080f03401428006010244a480700e00d082c0510f04908003000d5055188400c05860902d0717030350200d07942440300d02840b00711583c102ca04007509000007921001c0ca50713506812124000c0c8030b2541c1e504c44c000d01514200c001d544004016071500e543e26020701c402c55211100c115001c1e185041c0280028008004000c0914441e0001d42126801d0100384818503a41d030562461680c1f24800110603440100c1b00c0740840e03501c1e00c101d4203000501054074405842c4d10b51250b4941840c1012550403100502d503644c0059200b90f55801c41301100b0694842c1000711804043d0440008100440004106851000081440d400c0000800542ea242d1140c0001c0b540b2040c0d900c407540002440b10b21b01c507107d403268040f42c0413004d2410b040c1050080b40c04000c450b2518071040d000e8094030708040480300c0480c03280c0400100b8902c0041424680030018200030711003203008400201002049161080541340b00b210 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702955197 1250 702953947 702953969
    0x605070e032b050f0d0b06070b090105042001270b070b01050a12170904090c03030305090c0319080c030d021b0c0603040b0402040b0d062c06090c060a030b0a170c0307 73
    0x1c4801740c0540200040c040c040c2c0e0002c0104807030700018900b000b000c1d100b2002ca100004403480c0078108a02c5054418504104400c0000c050a2243ea08029000019900c140072401100d1404000d6003503104c09030000480380401150450410148a014a05880b010348044208650b60144029402200c8400924421103910880000300303928016008100004101242da10581c0d20f8205080c550354000742c00003903d4408000000b40d04100c2008101000e0307005100c080600303000d0801c6c00380b21100003410800002400c8160302d40c20015610f0081c15840704654549400111007090500014148405e0142c2c0350385c3c01207480c0c4802602d00c41c1c0d0300500c19000f5179450b42d0802008004a4085550101c41414164041000c0c2e10914103400d0280c100800c11620345003443c540d81d03140c2c419070202075001108101130840042112907003158151512030b1502902c00b4107502074003100240a40140c5110f400143c050211406d050314002602d00380d42c0c008061006154950100c0d00034581000f03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702956447 1250 702955197 702955207
    0xb042f010201150e1b04120c0303021b0a0911070c1203081b0313020103141f051e0d080d0c0c03080f06030a120e030604060906180f0605070e032b050f 66
    0x4180072405d01a0080c140d000e28606502e80942c1050a4840034042d04c88111b400d0703050041580400030061070081c0d95003040003d1741001c0001d400e200442c0540c1030702c141c94100e21344402190b8425590810313880400c207545242c550036118414003620704107400240342500841c000030008040e85d00c040f0200102c0901e19550390800764611034003810308030b04066179010601d40c108060184140603599071818074806400030f00030300c0107d940c0e5401c240d1080861400c00380c0c03045201c03491040d2103107080e50310b001c0400302c42c14000c465001d01c942d54250142044030341032615500054201c0300d80c3c401c2d21050440d840d00340f401c44c5241c0040f6003203601540464205000708610100c100a0140313a403410001c00520140420b042c04401c3e24125246034654590b441001000e01500b4142d07103000c9612107480100e51114144a1b0340d1800281400741da920228140c0d0780304a410703414841014046500f590800104c881b6900e9040417514015007849281c058014480c408448004403091642e42c284 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702957697 1250 702956447 702956461
    0x31107080421080a020606030705030714090709180e011b020c010c15020a0e0a0801090812040809061206130501080d110c21060a0203060105070b042f010201150e 71
    0x4159006288588030300c6000c0382e440010394010090910001e154042d0903241415020305152860940001d40b103a0006403050151400c0c98060420f0000c003220003c040e40c40351a008d56040b42d090304503a65414007d00040c40c5001c03a03400c80c40240300020001c0080c1040703019041060107041150300016000180e081c40ca0390701c58420600100d003d216011819241c004040049030f121020020205102d915207802d00d151220681c001030042a000344204915035803000030500c100300042d14440c003500b000c94180003802003600c00f14070001d4030499030780c1800c420b49070302d42c0d008407030082c03090000c09101c0d03480e4075150007000d040360b010a0003805c01584440c0c1c00c1e5074641100c405041e0f03d03c40c0c020101015600d40501c0002001e88405060030540d000c80110f081880090280ca005401041402030b2a40e1207411101080e80051024100f61142d1a05403660700c08180c8000740404184410200c40310100c0b01c5c4120700f03009030002c1103010030003140545040380520400001894410002d544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702958947 1250 702957697 702957719
    0x405190b0f040f0b150304081204030c060f02030402120d200a06051623030103121b06062c0c03041b0905010f2930070311070804 57
    0x160200108401040c200d1100450122440051200001ca40311080c001040c01c210402c40c1d4208800e104444c1b942c500380e00d805913a84551380d91010b840480314005401c0c544a02b0002a01961291050000c0c080c2100403a001e07402c00d480503032041c540310f161198050400104070450102c1c3e1b88541d0f404210302c1600d0702c0482c0b05007030041d81c51b00031305005000242031031261a208024007400950400c0280310004e00050440003100a0401c06c0c008440d00e4010703400a0301c2c1126800711100d9615a409401221005607100c44001460303402901141002a107030028810b480e44025070303502e014582d0090750300c1c6054100201c0305803441400400c45a0316840000c4d83d105009161241c0940d0031820070001d05038141d1311030400556580e00500c0349010010700480180303000120150280070001d4030551a103050850310310780e08400180712840510b4005004a03200040c0094800502c08000c0e010310034600301d80303450000b450301c841b4030748120100040e6003445070002c1c0c0d4241080d0a00b4001c1d51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702960197 1250 702958947 702958961
    0x28110f01050c0f010c020c0d170901050c0d02010606020d0e0105041a0f04060c030e0f1f030b0418060e0a0f12020c09130b010e130602090d061b020705040519 69
    0x41041010041956a40c1d0b00704820500388424400005100032a040000d080c0a80b1a240520900303952980d6000308201c1030000c0d40700303101889042c0e914103401c001a1524030602904404038003d000c00105443d406501503001c0b603010340c082d1154401d02c528100c40c80400c00c2e05440c0402e030180130510803140b094000c94400400d015583d0718000038600c0c01503454002d6800540003030754491800c8101580301c0300c0d141c10981e00340c50800081c007043c40015050343e419483c4e04119140d03c2c3d40b03d840144130b90420104003001500812a00a03e45000003925149034025555a41007140b02014400d0000d001c030041600045071350702c400522742e141d901003104c816040382107100325040e1082954441d1166409040395103592a1504050300c2c11408810b4140c1c0003c6921005004100c100107050350004140342e80a2001642c5100d48c0001402c68000c078030303001d4042e03850252a41d400c0c1120020700030030400c1c19021180707041e50300c0c0100402c0d42c0c0201c50221401014408000c40c449450700810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702961447 1250 702960197 702960199
    0x714030a06030807230606280e130506010b0f031b0d022b0c020d110115031217061008070507140d090b0306030604020f2128110f 57
    0x403030032030ba590b120f040050300030404c241c402c60341429041601c0c1c44407202c44072110300120094000d40c903100340043c0000004070200c0300744051255a080f41d400c00710408a02a0001600789604c82c18641c0d160708283c00c02d2001100c00344190f01c004601d40040402ba94804425110020f10716500d000308205040510303403505071681d00901098204009038009800c0e000300241850b070181651800110310b10564501ca07082840c074100e00702103040e138042101d032040e16450814042e00d1009007141401460b43c4081c0c21040103041a0120401401500b8002c540e492961005246455440309002e20340c0d007942c4860344256402d08010107540200b0701da40e4000c05900f440f0303050030302d16121282c980c245909140308039004070206c1c81c10290010455400b4091904c031142c21441c1c1400441e40d520006080039106482d100803000c41745d603807011403070708034820419500c4101441800d02c2c0d50303a601003402c1c4006030070801559203400d07054101030b54880380c1020b0308418100b00c400500c148101c0c1d8046031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702962697 1250 702961447 702961451
    0x15060d05030c010c030b040b0607200d08070f02040c020d0801051e1903050f07060504050409020a1e03060c0516030f02011128090815070c0f030c0c0e0714030a 70
    0x442c40c0403028800e0a011010700c0d01c2c08580c01c65501c0800c401c450f030b41c0582c284180414058000422441c141800000015080701003500300c244000544c40c13100030200400c0c6000028040c0108602955010b41040c8251020b102240611000344e071036080c20071210001030041c00c010405898250981c06600c948048000c442446c08004078001c030400035880c001c1181d4107071081003004801c1084004845e80000030b01151428214002c18510440c4200d0380301d961100d0043d019595036100b20401816092401d5046000502c0d404041100510040d1041c40c50400c1c0a0300c120f01400498140303100909495803255203c0e0303016540400d6203081c00003150742c0c84c448000c0d5405158001d2103c1403111120b5407a090030a04000410440d16503140100007803044200040c2c038000800c441c0c0e80da0040301da40c215a413045d0040fa015040440080c0041510000300b20916170000b0030a03034402d000300383e280c610b5030704e8040d4458142d00507503030304000445042125007034010101c05160030244130000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702963947 1250 702962697 702962707
    0x1a1f050f13050406060c03090806090a060f060806040c0e01050d080703230307021b06040f03080f0708030a0e06250f020a020a090c200c10031407120b0315060d0503 72
    0x80b0f400c590704d036001100483c0e285064a010b2503006176015004110000007462039240401440c3d448004694005005644401004d40a614282c0061010f80010382c100c898511306401c01614995031341c4210f2610035410400442d1605040043d290145d0300803580741e15040155808590480ca50b80b03d003a44106440c0924040800c00e500440c01103015034000c4c884120306d042110182c141c08030a552040c002040108030158030401441c08890300708131350340c1c0c503000d164040e040031781f18202c2c00610b4003e0000400c40c1403840c40d1f1000001c148844102c42c42c650320300481300045003410460300c07003580d400710503c401d8034070450303800202503401d10545180d0751f01907001c01c64038078a40c2c12201340b494031003030382d01c40c403580c08801e0051031000001910500c41da240c44540c5c0303c00404040350702910121511181c2540031703410103505140840d42c0c0c14214505114000c0c031090850000b002c00c3d80c202800c1040901d80064402d69034509402900241e840d0142000306104429408562500003842 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702965197 1250 702963947 702963949
    0xc02030c100e03010b090f131e1226150a05062a030a0519030b13050a0c18050405041406010f03020f0409050c040903121a1f050f1305 59
    0x203601d6200e50364031400030200e0514101801c0d5201c5c40b00d103600901d58441000010b0f1048020250006000070045508116500748992130000180c810080024008401010001c072a041c0c0041103419545501c24140d804900c240c9030700d19106446486a01e000104100d0480c1c183c81c0000140001c181c180c58556400c08914650001c1423202c000220180703a040c40007000c0d10103814004091005035182000030030000e040d50092404003180d106458800c4009039029a020010980009003a00e203900c400403804009000c04507820381006060103c510752107801003007000d240004010487d81c0341c5040500380030003000c0081c010b60f580d19003500185001c000138000f090182c540060101d032418154018410089102c0ca00360740a24500340c2000c01160011400740e510500441c0c0214403402c1d58102101e020001c00d46100c1300d1841c000c0800e0400e480400c0540e09110152400310341c0c40b944640750300d100c0002c0d145d10004100c0030041794107202e00107030040032101080c050b1a0001601c0708 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702966447 1250 702965197 702965209
    0xf09020c0c0f040f06090e0d0e03062d09030d151d06060405060f03010f06020615010c1a2a07110108040f0c03080a1b05120d020c010c030605190302010f0c02030c 71
    0x43e105440140d1380d115401c0c1f040c0401c0c400303031410481900b401d080310701301a03011030380d02e0030001c2040106c1070404402244441083c2444c8030311000b0300c1d482c40201c5c1080201192030340d100d071422691062400207080b81d02c02601042ca03080b1880140f402618800000c4180d502c00c4009165513401f0350300304000b24240d540c02d80548a41e101d424007485e01c941c10130b0041101040250042001d65014000700300c00081d0040c0c4e0485212000c1c80c2c001c4c07071190145443d078913240c401c00081403040c0501081208000319100d09141442106c1c030780340039094070070f007018607540304403000906030051424041c42554001e0f804250014410300d0486113030741117600c882d481803101e60030803200c00740c0001d002034600b60301608846840058651001101e4000d40d111030703807040300210044517000c004c524450503d0060307050344c1c007218100c0001c0c020854503240050003042d803030194070b2103084054005d24105090040d80c0f81540d606840f20804c46161007010f0398001c0d01902d040340e06100d96050510161284 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702967697 1250 702966447 702966449
    0x190c0506042c06060d0e0f1c031406060d050c04150302040e060619081803040f050907081902090f190f05060c06040b0703021306090f09020c0c0f040f06 67
    0x841d0010801048550803001e0030304449110b0314400015400303006030742d66441c1c1104c011a40396000050301804076002281004100d806006040c050b100007404150045d01074245180600c0d07604000034810002e034040140402d4640a401c51300a01075599181196030000360015099408a4101a1349107032480d6105180500318001075000303c0c00300002108020100d41104048070f8050070020a01d440398040800340140c40104500007011411141103080070228542c90042030301d50702e64482d40075540c00e00007846210300840340c00c000620840c1c424021507015140c2000c407861114107184a40000e5008118100c1d0b1200031010b036520140d40b0400b212005084409a80c0405d9185c01c140056490040d80418000c9c0c00070081110049401304100b80d000c1c2e880301440405488400c1c00301c0003030086001101520000e510089081f81c1c0003c4101d040b02d403081520039416407500410b0090f03004033105848103070301090f02c40300180b421000410400b4005800001d8500d0616130303080640f0a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702968947 1250 702967697 702967709
    0x301030602070b0f0105010c06090312090f0c14030319090e090d0305070201020901141b01090819030b1f170106031d030301210f02030114060f04060305190c050604 72
    0x400602001040364186a0781e41c015000d5804134110342c50000080c103800802c40c4c00402d0b19035152005030400d405614044146150a40208500e00180c5080c1c1384d941d02c10b800903142c42c03c1c03c04000034400786080300d250380c4910240c082c6080401d280005800b14404d003203004140040100c000c1406568440164455809840185a42a607488000d8112140680000d045900400c0013042c02d0b41c0040300d2507500700c2d40c0d10300310b66114240070302c0c0c0a5544420050b0003035542042501c4047c03042c0e010241c029131030201800302e501580b002007a030840704c02541998000d4145080310440702c0742d40d0402c03140790756242403c04a00017075540d007411101090b00305002007a91021030f03041e0510807080032618581020011455541403032a20301203100c1c07240c00c111282e149001c0d954204404801c0408940394094000d10002e4040105061010b1085501ca4052051200034554a01d418080c4900b1030350050090840c20b69920764041d000c003000f020680c1e140c550343e0000216a22488014001041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702970197 1250 702968947 702968951
    0xc0603100312050d151e05220609020c0102040f170a06020702030a06050f100b030f060904050708030c1b0316030206030603071e060f110712020a050907080901050702010e0604061503050303010306 86
    0x1c2402e096171045106c402c400c60341a110f40c017040c06191919a0550b82c0014441c58001c1d00c488408803290182c07a840d0029008a80082060111340f03405401030b20613101d0400e00308195507100c0c24440c469503200d98008a441d8000010b000100d980e41e8024580c250000d41541c84400c0315031590002d441056400f82c0c0b81080c50340c10424402c1c0340f0481c15000c0c2c601c1c00012031860800042440c035212014101611442585003c00c0400c04100440801400f58005480c2c48525402c0080d0f03c81c000d6011300c80c8280c0030400c1e03100481c40c0108880099011443c1ca5103070480c15502071004a800040c03200303030184151940800d07000540d092039030821303e0780c04580140c00d00b0044001c05001e05050340c202442070756030091800110110f880000c0d510600c0040c4880003103400015000d89140c0d01190b0418030340d50501c00f000341d0011403203101d2070280700248819180c3d003100302c2c02c03207540c041009541d41000c4007160008010b600005003000340308220404142e1130780ca515080d41c2c02171748200d6040ba = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702971447 1250 702970197 702970199
    0x13150e04050f0103061803050909071107090f06090e06041113020c010e0d09060c0308091f05060301061712030402030307060c11161d0711030408010e0c0603100312050d15 75
    0x1609000d01403458500203d05161400c665070090f22300c0c0035410300e8070b10a1320000b00190741a0710030308000030883c85003000ca5a0392555280012300420700110040c00d45400c0040200700ba035058058104150700e654020b118542e80d903164130920341358550006602c160342c05040d4101507107500282c030f140180d01000041c50880e40440c03901e0400913500c140c0a2214116081003600d800050100d04a901810864815a100c418240c10305802a000146920102c401100e1344001903108510490003540208085601c0b498042d84128003044549041d40c441c25588000c400e1050285401c82c2c400743c12681003100c2d6680740c01c2a14180315804001500303100d0700125484c8108010343d448687d03085640816810402c00760486140d0540748290144c10b800402d055600c41c060b01c40020100f070003526200d5498042c810701038a4541c030280803034420b01384024240d2400300e00f2039019001800d10b01c8010351035503842490102c400340e6008140141440080c0c01801c1c20300960400940d0000c05003442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702972697 1250 702971447 702971453
    0x12070b0c0c2b090504090c0b0a0302070807030c1a010e010b0a0903140303040c140303030c03070c05120c0d090b0304020f1f0302121e0a050604061212021213150e04050f0103 76
    0x28603e03910451049045c05900d201103144a0144800d94800d0340140342e5030034400d0002d40c060b00c00c0d10801090002c00065900505600015282c08644500d0f000c035608107421005041d4800d01303020b42c803484201880100031103030300c410061184090307604008030103580c5ea459000f00e02c00703040101400c0d6000001048100075a050051010340060402d021030b6070205004a0740d28080182600a1544004041500c0340d00420426031030390303881800c480005a104c44d515560303070009240c41c089032081c4e88030101e04c54002d40f0080150340c41001140d0465a903502006049181c05107883e4104490480d007404e403a031035240490708142d942d28003589d0b40409440e01d01400d1001012500d10b20340c0c3c4145c26922006000311607810224000d408a42c1c0d0b1500d6001500815141d80480881001400407004001190038101d600000b25002d807410603904a094111501c614180443c01808411052082c0c08071003004461124003403078a010740e500102c0108049072000d54403d1114020300c0010010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702973947 1250 702972697 702972707
    0x81807080c030c1c0f140604032a030c08030403140f0414100c14121210090618020c070f030602070501050703020f161a07090812070b0c0c2b 62
    0x11a00c003a5a01c0c1c1e03e05140500c1d00d06030610080c1d004100c00c11806002050100da01046c0800e2440c1d1010344101341800e180c0034000c4031445660100c100846d003100202c000c08100c5e0300d0902901616000d031155002c2d034840300f007540024000c4050000900c0c840182102c4c5501030200c29407025041c954071070501c4c1030030440140603460544100c05030300403106050383c000c0310311128a03800807111907903d4040b2442ea0a1506080103403010a00109030f0032501444070602d20b000b00f05003032200c01a10380310401d60064900301e0140c8000d111011031030b1900c0d400c06600600e004000102980d040300d845000c040742c403180c00d6005603002600402c0a900b40030084c403502d6003101e80c1e030404524003002e030303464400213000e078015410902c10422030311010300070640303484e10200c2e00c1c070705a158141c60035010180140c5082e00501c801441b504003241d080e500401c0880e028190001801541c3da95240091a025440703440310000c28003a865000c6d40444079413200402140742c0c6024081d030f12900102c001c02c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702975197 1250 702973947 702973963
    0x3020706090902041d13050609030a0801050301060303020c0607050c0a1d0a1416050f0318070608010b1234030c08040f02100513030f060e0c090106081807080c03 71
    0x1102c90700c1080104206240303007070300c0041d42c21161405075055442850355002c41a1140d406460b5004071020041c83c140b0100043c440c2c4011030700c1c0e1040598a850515003200d61600000340540e0007103c1505140c40c3c0000601030192048c002c03543d100c404000424200c0038154400c44100810a98941c107403075501d64200c0e032100304c9020800005442c00c0c1040380c5c11714042c1403080e21b05a0320302d9951580e442a0211070310050014070856880c00d008403c9010355090b07060701000c6004045005c00c81500c02c001da00e04890002072803504010410445034000140035003100501401c4000d1070080c28a08402d04a1070580d4a038240e6101084607809000d072203103e0020020028000c00300000107842c440c020f110075805886c1d8110380003a4400640e01d920803259480121403800d13200008020b401c042c1610740e94402d00c0203000e0048a1148182d50301c41c1403190300d1b445400440140401d520510100340d01900b00e09854181d0855196001d041125031340003444c25801c0281c4401d4503040400c001c203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702976447 1250 702975197 702975209
    0x721050913090c05012f07050316030507060e040e06042a06081303020316061b0e130525030f0e060606070308250806041a1521040302070609 62
    0x3202c52041c075650242d20a800340142410b010384c1059805004011a0300880e03d00c3c2c00d0079080864400e42c01c3d07195a01c100138480e00344607200c0d00b90036402220094806d1400c40740d01c200200742040c103040c0e05a5003001010107580d00280d885071a08008102004400d000ba402524004440e207003e0880c2e8441c810306036500101140c160504000d0940e10120181d0301c40240c940018108419282c12803d40c4100100b009030808204d180c002807003400c0e13109403034a1840d410a65466503803088140c0d500e6101c00704580d4806001050b01920910701d40206034086880500c402d40c1d078001540701360054030000b10384000250788245105006209100366055202d10500401c0141303400310004209129a5034010108200385022403040f03413100309102d0001c44124281252008490b90042a4000880c0d40034803a45c248011202d150000e0404403201400180290892018140c03200141783e00c9502c00290f00d2444610301860b040c118070200b0700a038030980c00342407000e180084c010040c9500c2d82100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702977697 1250 702976447 702976451
    0x1090902030714030907080706020d02150712090c1503020c01050f04050a1b150302310b09131a031c0906140912060a0606050c06010306020721050913 66
    0x8011159000000f4598042d0203000441d81d076030304d0214403410240642d00000c0644070384440440c045402040d03015001c441682220261007034031a20015441094031200b0108071500700b0b005610078650018259a406440c26400e03083e41c0d003203035940004082c540b0f00c001030f9002c100080c001800b80034140d001355140020b100c0130305103902c0d01511020300c2c400c002c100c1a0122040c2c01c80128442c10380c4014641c0050165001d00212005400380d80400941079040d04800e420120488a20b0035030100100403620118540d410403403a4806640420619540102181014000062103000700b60784040b010051051000d070540c285440c203000c43c140c4603800c90590360a007000d9a4401504801c854240c504030b0b074101c001c20390400082c81040041e941005081034904005800006c1ca14080d11714a002004842d50b944800c80302e1380901c0e6420416508940d0040011803403940203800c0040c0a480c5020074110942064011241110340c0003001c01c4020440a403940b4102079000180c543c00e200c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702978947 1250 702977697 702977701
    0x30e100b21250306110a03060501080708011505040902070f060c081e060a090e061501020a0b0c090102070b1201030b060901030f03112404151b0c0204091509020109090203 75
    0x12035500e9003098590300040c10110703600202c201d0040030b0908000c54000c641041441d40a5014203440ea000110070300c042420700350001450351190084900c5007103566107904250342040a5645059582d456060805c0010310000c68440428802400c4641c861240266103440750302d00101940e4104158409200c58030042042d0300c0da1281080208040707601403007005a480030001008030480d600002405480c08400411300d80000840600400400f180c0000c1c0c0000c04004aa4038a0400001040c80351303148081181e034400e0300c020300b0903050705005648920742c07100c0d03260807550085405031000e031000c10010028495521403d541295050390180c01940c11034840040d20121a9001410054011300c1c0348400e0700140196000b01c40b2103051228009142c58010000305e83c01c1e1403c1c0c131601d4410504007030a80700e511030301082d440340062403001280c80303150030754038a507017401c060380c000b521140748500081204070111159820403000050540c11800010301034041a00000380c46481041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702980197 1250 702978947 702979009
    0xf120f15011a0d0216060519050906221e0b07080105031603080d090b010b13230108370515030c060f0f0307090e0a1503030f030e100b 59
    0x3200c09112107444096a0340b0750303498141240d80000310300549818600810710448051a100d000804107034440b06020540341c04c041032f40c0307605081e203e1140c40110284d442d9591113001300c141c0ea0250080b00c2c02d14103180116545c501e11a04a02c04031110b100c000c1c100205030303402c01802400f600b0240c0003496181c4500b0300034040d030b80c164000a442c580b80400d610b18844200d400140703043d03038030101380c50455940b4041e1842c03980001c40c031078009800c40b04001c10b615204e02c900040e48419003003c0194030106400564030420050110181040c00c4002599145a2003000c205035660100303089442c01074941a11088881c090804006000421012070a0b5030300007903500d4003100c080307a2481e03440078030201d030000511581c2c0c0070104d91030001c0304016005070031200110803180031070b840441d41e40c0e9010450303003218000d040951042d20400c8042c070100b40718143d01c2a0f9003841c4d003070000c0c40c0c0141195040c940388540e105c4030340c041c2e1070300c03183c11190034001c2003075401c082d64020500c44415912 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702981447 1250 702980197 702980249
    0xf06060616150e010218010318080c07080a030f030e030702031c0e0d06050f0c07080412110306090721052a060a05090915010e0f120f1501 61
    0x8207505049035108916020b000b203155111040d01c89140b420807590b480410030328040d4101ea044640740811940c515040343d4001d004103400078408140c000e4101030ba81d9910a1141c12034400e8240522400c400822000410000d03070709094002e1322200c0d0102107581000303082c0c401003000e0440c00d420501103d40140c40000d001655152602d1190304050344500084812103c0b640440d07a00407000318280d420f01510340e20207805600e034100c81c00700f45d640b0130383c00b01a548266100182618001c103c10412211070201204180e40f1413802d030300d001540d8000091500034181c0c1c420b041504807030002c104641c2080e4a0320a00e00c8041500c03001a211500c40725103500f41c803000070100c11300190428200d03100840c04841885401003046403500503084d4020324581100940d00d0040700301c803002c54a41c0320501c008130013075807050399001c0440010354144810520405107464100d280800c0b00c08419600f44481c43c0c400d0500002003416400c54000c0510814043e4031440102c4400c0c504030211801d49 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702982697 1250 702981447 702981457
    0x17070f080a120e0d03170702012a030b0a08011a040c0210150509010308033418080102180f04060e010b130812040801150f0501030b0604091d0f060606 66
    0x40744078890b032041d4160069401110480080d980601d25102039402c2541085030f0320342e0840c00c8111001c2c207a42d007001c00d9003210300c440d585419800d900840c0e40d500100501956001030514078020480e1035034013012412000d05038000b44807903512480035250051689070510340e0b11000710740a1202d0f014004002e034507071082c4400c800605481c0c3c0d41c05140d03440407000e00c900901d00035004070465a034038200103000340c000340c0e04242d1681c0d0f1b03030403480b005801030a110303540800b803120501003500c2096400d03515014160000d040019120300700083d40e15082c030140c50f122080c2070303088100c0b04408003000304448040c404180704920b0103005004618100840398151448002041d81e81c0760005042522520185e000410038440c00e0f90080d11032140001a0040b50031001c024042e1160a514112082205000d01c1200340040c04d000c005130740c842c0e00700c0c030b4020704041d014130703d480c1c0c40300351b00b0056501c4180e815518912408085c869010104010b48007180700002500503800c000703001504074422 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702983947 1250 702982697 702982703
    0x5010b0d0c0201020c0a0809090108030403030203120613110a0e040e030304020405190c0201060302130e0c100903080d0911031b1302040905090730080c011517070f080a 74
    0x3a031070600304058002d41c11180003612040071900e01e00b1036850100015072004100380d0003401002d00000b440c8000005840c241c030b615802450608400289422240c000200441c0d80030072620480b25807041c0398883d5800e0f2030403051015598007000716014040410042110740920310b0100b220031090700210036240c12a904450201d1603845042030011030790780d0000c008088030b28008400c9101501548040c04603403096072212800f041c0301c1c50440444400722070300109500301f182c08100614040048060a60300390a1a0030401c0d1640c94101d00303500510348140340c07540c1d540a1039040c407492144c44041214120300404607056018201c0361880140c11115020f035005820801000c180350301510040d00034204d00300024500b400260340c0c5d903145441603205807208201c0c0040d03808008001051040807607080b01480051030f5941c41c109600910150440d95641d802416440200c0020135001f00b08081c602c1c11154015802d171410040d0b581d120a42c1980305510810454101140c00c4e880660 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702985197 1250 702983947 702983951
    0xe10082401020c1e06030a020901090509040209040609050304230a140d030c06060e24040203060a14061e0a0306080c18371a01021504060f050403030b010206060405010b0d 75
    0x4944c0780c1042002c1401d070020394400004000c11440c0b15180d405400e1030700c0240d0710b114040c0d96410900c0300028080e503010390000749010024000c50501c0c0c20641c001c5200c0c50490b0b2030580e540740c1401013805d14501800146000041290075442c0801c4514041c15210015281a820000c0040c8a0081b100e8004080c00b14106204050110039481203000f0001c1030314400c1140b41070031180140d55002d51520f00d140c10350441310070140c24244252032282c000544000132090401201e2174014202c0c1c0e00307140d4400000c018003c00d4403043c210450300c026000445984440c4440e8000d81030b9401c5810442c0b140d44148409072103580c442d800d00301c21580740030b000700850304c41821520103542c100708090403231030980c0300324014215226401aa8001000c000308036081034195a42a211000d20400d401a4001010048088903940d00241c10511500001401030f100c00041019203008450a0300825520302d1007440703551301802150342c070030030498007000258100785490100340a04881504025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702986447 1250 702985197 702985219
    0x1b0602150a181103010510050f1e041803140708040b070311070806100905010509010e2205032a060414030408010618110301030506160e10082401020c 66
    0x15841c0d902c1448041c42d40784801d020454642494081c1c10904601e6500075840d050004100540044002d000d07038100802071100d030101e03002008a01003501a01c201070002e400501c205903a9984078101403426540303c103070520046814080c0c030100c4089407103100d0360010002680050340d92421101903c2c40d021400343c6608a03810200c4208804590103207240c42108000720746a0720028001c0d01c541c1c4030b62000b8002d96115074500c0140c500a00c100c5400111040040c4422801078000950046044010541d00e9212500c00c80507200c0c40c3ca003d0b80d80c0d03000000e0480003940c3c030b408010703030f00516401e00504890048503400d0341c031000140046c0102e0303040b55100750488401e00c100d500400103400207000c0d840e00c03001c122116992801076084640c0c42c014041080c0030481060742d0480350084040c2c48241d41d003c1c402d0400030f844103c64000c0100580078002140e03580e03943c1d4019508140d440209901e01015580b403551204001c01c84d501030042d0700c401c4540c0e40042c01c50381e000000c0d1001403200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702987697 1250 702986447 702986461
    0xd020d0c06051b130504150303051602040207020a0603020a08060a2405040f2d0302030307140a02041d0c011b061e020406112a10020a0803131b060215 66
    0x4080c040203c1148020004401c0020010001c0c030800703803001110300700700000040000f0400107007a4480240420010f02201010b6200b40e010075a0503800500b000d8507180c03103680000c0c02e11660303401ca80e0220340c0c0400c94180c00b80e440034003d0381c000411341c0d540607498202881204c10754291174684072805814280d50341594401c2041d14000d0016200c1c886185440d034410064030212030340b4039000300701c01c2c2d502a0b800340381c2c07050300800300c0341c001d030241d484c040b107035201c1c02c002c0c2685c9030f038102c00c6204e103045020042c4c0780c1c0d2103411030f1501c00c20100d101030885040d00368101013500050a0401051094012140b0720b0b6043c03040710b440e40080b00141034140714500581c808681e1802c955043e2000c200051803981000280c41011150720942d01c40b500500450b070342a41c0c01c010001025039081c1e00212090514800385808081e86004a40703c00c0050f03035a0005c90b41c002c594400319400c14003207120030440c940d01c3c440013a2110290740380c400342c101707a0001c0d80c4840c8c0101d041c818504413408a02a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702988947 1250 702987697 702987721
    0x103200d0204020a0306060e030105070813030201140a02070b0a0509030306010e120706050702030f01021306120213180614060a030506191d070c12080a0b04020309060402030d020d0c0605 82
    0x64036400b070001d40d240e54075440d0240040c12240f2550380070607003070384d141039480c5410311071030303204a8031070b15840c4503030300c54400410102c2c000c40c1046085d50342e04c80e1304544c0d40001081c007074401c10082d440580c0e82c20a0307103006d010104e40500601d8046080a0a02c005400c002c03041d00c2c0d00039401e02c0d00d54030030108000014428080d061342d903100e038004d4140110b03030150b1200040c007083e0300950445400722480712009080b4030030800d0540d03a858240000f41302003481001010f10361100d224025040ca1426412240c40744083d074009100601c41c0035402a2141083c01000010010b9440c80480b83e000030010802c41c0c4621102ea41c205a03440c00001c40c2c65540f8110314030b85c000380c812580c04031a11100c886040104030004078000b959203100151582d40b290301d0310031689034846441c541c5014102070540b00e16101409030044691511020080c82e2124405144180e0703a24004005034106801850f0900c1080c01c10b0f01d045400000361405480e400070221310794668404d90006032940c0300d405c103000f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702990197 1250 702988947 702988969
    0x40c020615040207060f020711060301030b04020609010903061d010f020406020c13110304030e0a051c02040f06080d021e07030b0c13050612060910150e030c0402040e04060c08010320 80
    0x6060301d4824000c4004504e5409023034002d1149200d5010b8581c40410010180000d110050040d00103100081c01410240040c2080d2001030600242c0030b5269616103059540b0079401d0780601d4101c20f8030040b401000d000d03000c01010340807021460107081c90802525070f0459941140214101620301485145503400303c81c29400145c0842d44905040c03500400e1414003801d0588115600003000c24a07123042c0d00e803041102d41c03010001c2d0346902c09600f8803014103440c2c00d00e000225610280090b55080a0060890b0b40c051030307004e02460711000514003905080c0c40d03241e40d0950321401c1c040c00021401d03550b9603040094010801d4032041c07a141101054412a00300c1504407001183c1100a000001e0000b4010241240c1d0195560784060860b04c0c110640d104510b070803401c3d811024609070141040c180c10342000340507900c20a04940115099038002d61100200c01c5a190820080c006107100301c1c541c8201601d000b04c0c1c20352460300c51180050983e413940c00e000711801d404d00e0744c641e25008180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702991447 1250 702990197 702990203
    0x602070e1e01151106060a1511070f08070e0f07201603122f0a02120a030210050c07020f030a140102091318060510080601090b0f040c020615040207 65
    0x14a650f0b19604245042d0103290b8400c00800c03202d10030055030305004907a0500c04c42000c0d0620140520704084c240001071442400c3c410b01107420003644074550700307000c284003402180d102402c0c02450800c0040c40e000883d030003070309610f80540034000b0040f00d004140781c00c809a4a051906d4008045120000c2c442c12200000389103e007541c0302c060040c2c001c519070704a0380201ea1083c0058400201500c20001c80034551002011514003103145e490705003905500f030046002201c0803204035502140038a240000210b01c01e83c4a0000c20301010390400880395008802d6600348042c0c00c0110501c1054068094003d1040c882000c0c4540d0b1504d04000c2200099040080c0350391007961034a901e0f00031b5100088080c090741030700310004114000307401000118545c0d44150064000705483d000d0040c14050b1002e4458071860034002040201000094040e00e080c207000541002d041c4100281074841e105041d000c0c50030320004903031141d00450714a80c00141c4608001030781602000060091190f40402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702992697 1250 702991447 702991501
    0x110303040506162604110609091b0d020c01020c0d020f030d0c0509031e010b030a080d02070602040509150a0f060c03030506190602150f06030703030c050a0b07030e06010b040602070e 80
    0x13691200e2100c0d100140640e008142c0d800781d00101906000240c03040885680d0045c440001107503c580d0042c0b0303480140013603900c10609040ca09440304060303030701c2084180c0990703401242080901d001440b07002c0c40c924160000703024a02010450755205d000e40144040311715500e880c1035002034000d03421681c2a84005080d5030a50344100200d003203600000c02c551246610b420ba42140600703000441c0914160040b00083c140441c0b01d800380c0103035002d00001c071241034084c0710009032030315549030f0740c0e01400001d404509808081302c2802801501e0758054078022881080c02c002e15600400115425501440c01188a40e1180080340314900000309081d00c0d0254804000354413a4080b0b0100c410354000c082001d07040c0c6540c1140307071030888141e0b802e681c180c0100c5002c00000c0d008408040d0546d1094041e61010501c1d51164030880f80c00b102c4000106e6112241c04000316018002c00340503020021a00341000d05001c0000d48d90702c9a8041c0b4403e108404011680f03400140f402d2104611411190b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702993947 1250 702992697 702992747
    0x4030f030507120e011418060a081608040f02060304050a170408060a020f1209070f09020a030f090c1208040b04090b0307090915050c190e0111030304050616 69
    0x601a6000a4040c3c454098100101d030001e4401e518500a6080581d035280e50342d18981e9001070664000e840d8146201e40c0800b8a03070307054640202030201e1702c0107520f07030900c20302e0035940150503081801c2004041080c25801c21000401c1240010390090b010358030140c4a5855182c490b1030500c102a0280503a4004900c0760900004400144280ca104000303444e03040c0c58210703000080e80280500e6400e03006090104c94039000303000388225408888441203031142030b907030143d540102e50710341c010502403500000d2040d800d54141c06607210000701084100030b401410303180c00d0341504890085202c0f044424491400f40030000d000e42d4003030042d955150303540d05d580785403640003009005506406405002c01c0001c003180f240c42462405a0400c51025000d07481407020002804018100c0c124201e0500807038441040a1010303841c1080700d6203034400307040c9003070002400c13030300600907240c0c100d40c410810880092004103626403c04030044120071841c0c0030500a440002c0b01805441c018048414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702995197 1250 702993947 702993953
    0x60c0c0c090103060203060a050a030804030602030702150702010b040501150c06050601140f090108090313060f0c050d031413171b0f0d08130305120903090604030506180f06150604030f 81
    0x20045001c2c09040b5640401135a96205010081440d2f03c0040d05140e02408100007240d40c0740c0065611440c144155590920401441c1c6140142582c4040061f07545004010740b50819103c0c3d5405044680c0c43c2c0c022015503040002c1c2844000300c0001c00f055241d9012540e164080c004140c5107030a2800440d484000b03055031032003543c115035143d500003a40f4a000c42c841d42d1002c401c507508200603894103c00c0c10304008040c0e800c03010000000c6d0401044c0101800481c070240a1494488080c2d9004034001455030700c00c1d14403601c003a18401c455032404111000240c022100d80030414401000c030b6446140c4801d0141c1080b0754143c44d041c19008911030400c001d03c0100b00c08810700c2d2242c41e090749030b4031642c044030050038201c20020045403040101c89111001a092140d01095040442c0d15055141d03021441640080d1b208a4140d8041d4007030009a502c1114004e803501c40b100018001101d801800c1a554940a03105180c101409a2004507903220001124060760700320010b50101d007503501d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702996447 1250 702995197 702995201
    0xb04060e03060c040308271302120702070501200304051c0507091811130c020f0709090206030105150d0218031b0306160c0b0901090c06080405060c0c0c09010306 71
    0x440e41c8070740520b10010300a684980143c0303003582d82000c0610306100c540d00e81e05507143e051003109001c03c51801c2d454034450b5200300f850481075442c01809626403102c202400c0c6841805000f003c2550810081400640da01100c444403144c80d5421000308220101141800d5100d981c1106070018084006582e401c800c203840c6c0101715202c0c0c0111820700365984911421145607000030012058003082c2c3c0c0b400300d0b02c00300d01d8401c446002000b26070480c14560f032101c11200840e000c84096000246034031704604051000c50024146034009200c03044443e80002d15070721050003494441c5404c03082c0301c81c002c8809000e40f110001070210841d9036050041c1c40003c0c0284003003240784a0b22402144c000600f039142840031080c01e020380105101d40340d00c0d0035213142d0000101d9110400c5030584000012a0383c1c0740721b40e0f000d50101000001c1c01c0c0014102403400c149150410402e10003c00700b4880020b1b000030b11554803100c40102c041d00c0d07034030a02c0070905004a075040140e2001c0300d4800441032101a07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702997697 1250 702996447 702996467
    0x30c13090507050c1c05030a050910050f180f070b220308030a061d0f0705070206040f1517010b0304020d020d031805040c020c040c05120403020d140f0a180b0406 71
    0x90301285c80f8581c03c0d00c08080b0b442124501940001c0090005c20f81d010b4403504800d402075111000d03507802016032058401154070403038034188142901c6c000e000382918081c0c40c2c6004c1c000107102411901000c20300840d540c51a502c0340103040c4200040a122031018003100710306404500f0541c2e1f40716030b56410084c00d65001a10780e00c6255182110008600c1e00c105030b440c504141c584000c1c0c031140d86146c91015602d000401081c2031103800c00402c801030f42c1d58002480a04401c1004c0942d150405601c0c0c8101d010307035000340080c45062100500d03000c2e2a104124110b42d88a1040d03940c03603884c0e04c00b14101c914450802500b01094100c0c100425404c0220400100034186080c0085a83e40007040305a0300f030b215402c0b001d070700424680c94031410141c00c02074100c101418114a084160b010382114103000310317010340c01a0003a0303c0441d603c5621510010745542d40d0501700e41000c0d801c1d8411304880c40b030601c0c20014000040343c0c0c8070451032403003d00001066540480368a59549403000b802200b42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702998947 1250 702997697 702997717
    0x812010303080a0507020c04090804052206050312160c12060e060924060613080f010e01020307140901020f010606020d030b09090a0807050f0d120b0306010b030c1309050705 76
    0x92400202c3c2442e50b4415070384203815560083c5100401e0006200c01441400d101b621014000c00000c80c40e511504a6240800c0000613100f9114240710344180848482da0071143c0b00740c00000ca014240342d060300556040d54a514400c0c400940a440c08031300026860384000350201c144854002400880d41c880e01c041140c180a680180d540d0034201030b1aa020b4482c22034480d1480b1414008260300956216403106002e07180030b1410310b104510359480030a0360b11214043d4070858902868034001c1c0145084900010029810340c01c140300054501165840e8800d0400d501050b070070550784c03080240c0c200005003880204125030b19554020b44802c66884004042410590161700600301015424401c90030a07020b05221001075903900602d0f0300400c0c0039202885440780d61520300205100340024071455448400620303800c00100015103840d0700c0c041e0b1081d0400001000b0907408001120b6120085ca40c1a9590704900300d00005001e02a03005642264542800c0050458025004081c050320b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703000197 1250 702998947 702998957
    0xe0301090606050f220f020409090b041502030609040f030c0c0e0601110a0c1707090501090f0f02120105010f021e030901081f092d091223070309030812010303 70
    0x1c040001d1003081005c080344098603010700882881660000e52108010031100340c0058501b84d0743e02880019140c0500d002d45040008505000400c0139880d1a81000c024428040d803c51a09000040380410001d0006d4040d5101d0745801c001c1520407400d0013412503201d1494115a41c4840c1c1c000103290044a17164003107032842544080383e03800095440700c61540041a0001503042c4603240302d2a000349070702c0d01c01600c0340f8980451480c0450090750f0113008020400640d1b1030403011410f041c0c9000710070044202d8030400000360107055481d03141c4d055031001e00b81f800074001518400c80c609105c0701c503403200c81c1005440c40b0441002c080700130300c0210300036601c0078041e88400d1801101e403160f00182c2080c651409004104501e542e03004282c2d00f503410341d409000c45900410344ca80e02a00c103032400002d269a00e03400400c006000302c0785850a1454904445d07141548080103200a0020741c1c080d07542480071500b134081503c564500c0c00950750017900543c844420f0b40129015803c01c1c001100030603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703001447 1250 703000197 703000219
    0x207050907090335070804300809030613050a240609061e080a110d060e0c130605100e04020d09140f0606010c0f060b090106020c120a0201050403120e030109060605 72
    0x41c140c402529817403900a00d0182c50203281540d2600c0c0d001d402c0c40c020075450211035140d00c18648070b900d0b070354126014241d034541e106030781d60402d81071141c020f080800749621a000c80c400700310000b82e910f04882c0d00051426044048040010a0001020300c4015180c1844808941c8c0c0407203401810480c2d10741200c00842c015800c075030707070300140c502e0042092a6000c0300e40e250114000744809205650042d10114841e600d5441d08030507280d02d4044202c0d1540a124001002c1c144410800c031281914002081201d0a040001d51405051036820040022081c141c1c641d560319541102c0404142d08020400945140341a000b40240ca24088a02d8026070548801001020421520400c0142d40702c0e0400e401c10303640c3c503045070f5106d5000c0c1c44c0130340c0d00c020304901511a40082030180000d6002007444510400411205949007085080700c1c4d0000030803900140d8100c0269001d0fa41d05c0441d95811820008d000c64010043e005244c2c0c1c1582800042024020650f2040301070b1041918400003030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703002697 1250 703001447 703001543
    0x30b040e0c04050f0c0313060e0a0f021c030f0e0402190f080f01031e1a0f091e30030c07060f0507080601120b1f0801060f02070509070903 61
    0x1104200c85c01714600e00200005180d0140340300d00c03410040e102d070340b0006140300300840c610310b4609081c23011240e404800c0640000e516081e19451461406004080e24002c01c43d035009003000701946000c07060000c5041e605504eaa2250151101c3c0d4452581000c40342801c040000c04200907030080b01c001c503030148042502c00a8104145050300d400c13014207104010410719580240305030000c183c0c0c0100c0004101410301e480d11031040e00807070a0942c1100d49003800100e8030308014010b000007510381c60014403011800804034603000c1c2c075156505d4000c810010140d100c0d4084c00307c00981c1248000004c01c002025940380080c0c801680540d03810080e90071a140710700c04840040e01c2c04000325014a0001d503980d841420341c101e07540310522010420888250105480300403500003202c456005200340c0f050343d90b02c8456680109210314056190034a10080a0b48500f241d000c2e45010b4902000080c0880f80138080b800019944003001c1d103080300350103421079121b103807280030f032a0800307c4141c82c1005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703003947 1250 703002697 703002721
    0x80f0114070221030402061b0f0d03020903120f040803030112050106171f0f09200409020d0f051501060512060618090406060816080705011716030b040e0c0405 70
    0xc80d00d0000c40e40f603d1030b004848070502e02c3d000100102e82c00181004014099a00d400207640c00c05590401054086404074540d420201c0440785441090b10603c01180c41d43c0d0006880340743d03074404d00c000d00d98416440071104014491900001c0340c07880000000210400c500d841c0b008447d0060b4001c00c1010388a40052042000c20034140d4900d62066201c104507949620f032444400d90749030000102c40b05002883d0040d6030120005030303680d5014160032083c2803030a401d81480c003c4112410010a6284c1d40005c600260300c0001805131080c0c030021604100042040d040941c4040341043c245d50381d55480201a40c0c050818031680500d040003068460034160240c420b41ca0826100c0c07921032624074103208181c100203200742d412940b20400014a4801401508000c0c1c0c41e04150054490900c8a0f0514118003540204d0401c20008018400101c3c0302103c07a4200044a0020038192032208040340601081031030107030302600d0074440070072444000031b61090b0203000741c4081c0100c0c0e4800341c500031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703005197 1250 703003947 703003963
    0x6040602060f070306030b0a2a170c040302061b07050414040204150e150103021c0b101d010c03030b033705030f0f0409060e060a092a0207080f01140702 67
    0x95401c070008203c201101d600301e2a088100071115249c2500c05014109d00d2041681d40ca81c0851840710004540c005154205940514800d030702c1441d140c0f46130701007a4240b2400c01604114084074004080340c042c00c0c01040001c2400510a020f1401d010500c0d6102480544049105600c0d1641c044a04402c03200040c0031600128090421076540039280c04112100e000280d0406508202c071343c05100d940844602d08402d13101e0002410300c400300a00c000c070040311740e00c8006e20041d0f540b00130f04c04d1201030624903140303000e01e0040820785841c94254040c1072180c50065040c090002c21030700f00345949623000304500c2e41d0381d01035048400001c49072108601a6038041d14030741040212484458481c4d0007410490700e00d440c7d051030503070340d003940804075039041e04106c034940c1d00002401041d02d40b510001c0040d2070042d104101601e008840c00c0141d45a482d008042c801c81c0503850107420740280442402004d5200541c1e04407140c0540540c001d01c0b240d180710340020b0000c804507a00501c0010030003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703006447 1250 703005197 703005203
    0x3010e0f040c1703040b03100503011113030f0c0302030316060c14071202070f0f03031d220b04110702032503140307061a09010e0c0405090a0b06040602060f07030603 73
    0x4000c3e090240c2d030f6208200c1c1d03414508052008000019500b0b01003002184248007030510398501c00d047c402051f003500e0080b02c8603051044148040403440703000039020004c680d440007442104980300c1c07030100c40182c000e51029515000c046105440c10401c0b500c02d03c08903106200c00c00c01c0d4034180000f0340e681c1481162419188800748040c0e00016400582c1140c100381078012180150350790310084500001070741140c1c1000b03c14010400405401c6002c0040410500c007001c99822500c401040e00d001030190828003a0710091119030000d8803036800700c00c03000006041030020441c045030200c100da00c0100b040b4064800c1c401e9000c40d1351800d10310f0034020071011030051200c1c3c1c5142c0740e0201e00000d1226410690008010480000c2c0c03c52090030000c020441094080c0c08a000802c071070381805922803141c0c1c81610041103014031141e030803602541e1003100d04050940310304e5000e00080024014130360f04940006008600d141d000102244101505105041280c0d102c45084080d110544802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703007697 1250 703006447 703006463
    0x31b052d0a030810120f0501050906060616020f04051f12080f030901230106120902211609060e090c03030307141306080108070b070b01060e0d080f03010e0f04 70
    0x60000030b441107011039081050303210404d050079141d030110710907185902e40450702e100d10a51501e040007000c1c01815440400100600380034038101c2d008ca42c59104a000d00345583e0f10000100c4210765039404051000e10015104000c10315001980e60104440d0340189030011052180008120980300c403d241001e902c075000d1400d2040311a0003102c1904058064410b55403a0350003042c1211900e01c03000e55034071515030b0808255141c40e1303000c0d02840f1803000f02d400603410524101c002d44c03985600828540008e49254002d6514040030608103a0049040c800030003000310001022021500300a00b80c944002a2040d59101c242c0855944d071101c048082d0150028000180424040d4080300181143d521146103414507190740b4500440c1c030790700031002281c03003000107001d9a6020002400a441c059000b140307003030080d496052240205105640030440f04140034001a15904060421241e0202c3c01a458403200041100942c00c240210242c208042000606002013240424041d903080008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703008947 1250 703007697 703007713
    0x221a04030822080a052404030c2d050309010f0f12090c0e0403030c0206011215050c1e030105010f090e06040c03021c090506060105040609090207031b052d 68
    0x60380d203210b90008015032428045480000d40c0f400184071098240c2e1088002c0e00141400b8900043c810501e50898200700750600200b100083c0c00403828642250002d03080080402c044c200d028213800804c1c41c3c00040a4542501c0e020000000054160008240c0380c4010108007810115520004031030240700055241046000142003a40003d40c02c0703000d030b0000c405d4280ca0700c18010070031109640450009a6980324460415410710900e0301402200c00000d01180158403158280340308800c0542505070780f4804100c00c0c0d12000107d8400b008006086510002c031082c1494950b003003442414003040c0c051190303c4c80940b00342200c00c29078109404160060b11500c0c01e00c4000c00c0400d59020505608202d1007444910140241c402c0c03031a1100041048241454043c1c149000603040a05104040c8000c0c0700598000d4980c03400d85000c07060068581d1194101100c0c0e2a00c034440200450800c0041c50051040128407a0072031403080c1085981e443d207103051103418414240c5051303030076046959 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703010197 1250 703008947 703008967
    0x702100f140c07060c0801140603090a0b16090509060109120314130612051618032001080601020a111522080d18060804050102221a040308 61
    0x22291001000024000602519075604034140c00e000350380140580401003510800c001c03140c01a4400060311386003044495140c03420b800c1d5003050640c4514480c1601100240280400300160b03190250000d1403400c04e03081c03a030014141044070203860340c0028400140441c43c0d007000580240102e40c1a51403a0201d440d00c0c11040603004003960031800c0011408201101440e0f50703000c0c1a50703903504681d103000c036458280094403c2d103d1140382e1404500702420410b540f00010280f00808445040505000106941c4800403500a0b00024050341000319450142c500e0303d50030003002c200a80764210a03498907801039035a100c01e14001014665056510009410310300034041088400000481c2080062007040c4180b450140085071020324601041052040400c00da003410041c41c201180301c0d81d41c5502103101444240603180a101c009000310301005425412603902c00c41c001240044405a03615103c00f042d4540704050030301011901003407049500340100d8084a41c04030b0000c1c41c00720184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703011447 1250 703010197 703010201
    0x2030702010c061e0209010f02150408030709080f0a0c080a05060426120601020c27041a09060601021c1d120f0c09150d060b0307051c050114070210 65
    0x40b0381143c0351a143d44420343c0520b0182000c859941d009070300584ca94081c68001040410811458003c640c003e81c55907656100700142d5a404c00d400800540c2d4036650b8001c1600c11850a07442144144205840300c10700c0c58000c240b060030360788180040781c9156a20180e55503a03103c0b201018146400010101c1c0c0014044a02029104a0012041090204071524280c2900f00d1840d200983e0b459508100040d03906101010b2400780c1201c1d140c242d443c1004030486100f5a244402d40803c1074000483c00303103c1002d0340c080c56512000745d0340c1031130314084000c5901c03840140e6006015100381605102042c1c0782031801c3e00900d455544680c2c0440c05102004503e090414910350441c03108004000010410300102c104c8568101c0200941c80b1800d003845980480201050b52035030400881d00255541d200b00041195005030000c01c2c220603100009003492980c2e4406940200070400950b4003881940c0e117143d00901482c000c10013080860b42c590039040d411035510380141c0088400e1800303510a070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703012697 1250 703011447 703011467
    0xd060e010e071d0a0f090501051903030e010c020d05010c08010b03150d02060903121803010603030f030b0a2c1302010e1005040b0301060302030118090503030705360a150203070201 79
    0x50182c803c06410030008100f040b611904224111a0321030030510071214103009507401482c00742ca091510b6840c1e04514010504640001010440b494101013a139a1054800079250340d001441d50b0300d14003551818034000d00d070302403910020516020000509000e8002564030510314254070401c2c61556108005842160703640482c0d1111045c054448075413420410020252054510107680d00f40302007094410000880301148240e0410b00148006035002507246000c14a03401c022031801403000019005106a4100304240040100303074003c044265100c855811407403c2c074041140c1c95010201440c030f161414080e000c01d0700c4030800f407418208900c0c903480744011450003038141074841d020841140d2007a400580025000f000500013a00141c07032201d05c41d48400070422a030b925070b40d120368807400014624814002c0200e9098041341c0e03411000400b080610442d04d04081c1d42c41454200710760314400e141d00400819502107034041003034041e104074448a0b0010b41c140141035004481851070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703013947 1250 703012697 703012727
    0xf020601180c1412040c0f0803040905060111010f0605100c020607080a0512040c051305190b0105090a0e1b0a090b0304140d090611010c0507060b0319080d060e010e07 73
    0x150b103c558036810004050252602080c207680390ba4101828514594079468003c00002e5090b040100210313800042264115041502c01150b2956404016241d1404980d4806071035402c00c60307080c5001e001584040107580d421282d840e04005003010498200d441071a001b500302d034040040e840443c0d4050060a0481d001d4507089280035010b007030f00c400c4040240d8003141c86483e260000e12040c50032004030120908801c004206a1500540403400b0441c03440034000ca0a0382e4503040030060748240e08a0320b07003a0000d0302e03414045030348900035071888008480b4030403034551960401221a014104488550100d030b0f9940740d81c08d0401c0c807603045a52018104462522001180809a15041c403050791402900e07140c48041e41c1c50940003400125414401a10b640d03d043c0c10088540c1d04282507445151300300364006400415680403d152009500c030039088009002c08081c00c00c0b54100080800604c0034005105460b942c00800c0582c15080c06010580c540140009400501c6140d034102c14183c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703015197 1250 703013947 703013957
    0x41503050a11130e131e2612010b03240102070503070b091002010c05030408030601090f03081c05131e06022208012d1104150206150603270105160f020601180c 70
    0x45410740c0540c00c4042287e0f9050760320b0b40070440d03221b1031014104941c01003000c501d010745103140544448840034180d94040c801c0d41501c209201e00ca9100f001007401411001d0111040f05440744070110340b0390000180140b01c0c2020122000c0828030600400c403001d2510b031100c50075604c840d91180c00c0e50b08001c00007810041d9082c000504444070880c0f1600860241d018203540381030215082c1e0080d400b1041d00703011582820140043c8c40c3c60880c1e5404900d030815800c0c848003031000c0001d542701e10104405842a8000b18a1205005040185885102c210190469150760b10103140c1d00b6201c2c0340040c94030388400c48040c020703190004034540c08008004500002c031080da40c45020328035001b42d0050800c00c90b42d0681e00010035010810260080d440c030032821060350440c0300080c2d05220040000400644200c1c0d010040f82c004020741c01c2400c1c2000003400b003843d280c003000c0c8079090168403c1000852006a40c600e82c2d002156181c140c030301c44506041740c41405544000a1b1200e0200c08003002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703016447 1250 703015197 703015223
    0x312030b030307122706030e010b0d0b180109030906080a1b120e010525020f0a05030a120c020601090b03030f03130b010803041503050a11130e131e 65
    0x1540600003010303c5845980344100d07030030001400808452040036031184070103010000d4800d1207111440c4004445052a0115001d8508015079015180d240400c54200c0b0ba80f100b2107040000c907030311840c42146441d6054900d031550381409402e031111441b0240100320100410320803d841002042e600000e5a540810310300e00d009110402004040448800034440e442c0d10380c0402401c0c00f50001000051340280640e042c0f86184d140d400020b085200c2030641c1b29441d100b10980248040380200c0083c006503940480d090034156101d0b800740c044070000446903110701003d4815449940f854074080d6000b01800da090031050300007000a0355200340e040c40107103d84600c40001e0402148502c0000c00c0002e00c050492410b070b2021a4180c000a2198005102c2031120900041c224034a1034140d250105032600e0f941c010400818101d0324040641ca0000346003190240710b0100d00d4112020117100c820190f840d4030940ca07001542d410010f101125512440f1290207811f4001c2c00c0b047d001d2605401e0007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703017697 1250 703016447 703016449
    0x190518090429101a030109022101080a05191a04061b0315050607120804080f04090c090f0812031f030302070602070503010c0e0d0c09231f0312030b 65
    0x42c841c02d01c0da655011100c0000c00c5002a002c0b0b24000003404220086003218400c48501c0c0c449000c14010702c5041a400300342c5801480110030300c0e0544080034801d98038103503112214203449200c0140140ca075407043d01b13130000008050101c44001d443e0003950151341d0054000c03040c840c04038007600903100755480b2240099030044416100401c080c03145c800280c00c280c100040421411154009480b5500034000c100100742d07d6503040480030700900c4c002102d59a03610f032503075070703800f1700311000464400110740450b018209901c2210000c803d920340c1000191f41d9480c01c1c2510120f4083c00405070001602030a140c1c40b104040d41d001600714207403003110080410807440c1079000d45e000703800683c000320f0100000d6805008c5403018090070b400131b114042031904098050702d80700c202a03000d00d0030328440c0800d010003450101c016141006060100c6035801034420351026400e108804580790800204491582e1040c51550640b001c0c0300c0154818955145ca84000000d02040381c1810703203c640484076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703018947 1250 703017697 703017743
    0xc0302040b0d0506091506090103050c0910091406040b2407020a0911031609050604050f040e15160203030f040206030417030f01090605010c0203070509100905010b1905180904 77
    0x441d2620384014005110301c0302c00b4054410014040501423040d010045c00031030f030b012031143d200c45401c1d05c0c002120303198141010300c0c0382950b5008180003464000c0301104008100d054a0050508132000d210205030070301000314000c48085104421454003107605040040640a040070030b00050603483c2003980c481c00d003020755440341c040c10701500d4000108058100b21402c1038801e42c43c54a060114142841c0101d89940714600903184144900d4889208680e125046048007038032131000e58a810b10210405614020159015000421510302140380b0f28400401c0d28800c46074111039200039125902880050303032004d0400c0e108200a00a0030550b40d440d1002180a2048482001001e6240c040b0b04001c460b07a0b60809410805030012280c0542d07000291802903032000c4444220320340321801e0104d1114a03c3d8484a5003504240001881014100c080d0160307620500c1442c0101d0b11403401100c55100342d20401c0d0b0089001d2807080342500340003912a910034800c40c1161003510b01c41701441c038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703020197 1250 703018947 703018951
    0x14090f07050d110c0f0708071202041d01050601090b160b0901090206030405061e01060e150c0f0309040509010c2c040e0c040c08060102491b0c0302040b0d0506 70
    0xf4000b040068000281c403020002c0154401408002e01010790400706055106c005511072000d4142091107088e05540ea258821000425480f4070b42500180d011119070103000304032000d601050840d41c0006600500c82d04885a181e40442200080f11007a6103c072122180581003034810341d030719280c070401070b00c820b0700030b6010724091801031000d49002c040ba81952001908111a1040000010401c035604842ca03d00c5002085842c80c400d81a412042500c0703008004400c511442040040740102001000031310030048141c2d0180019a40c07030348642c2c240c6800ba00c6800000d0340054284059204c103d54400a001d407905241d11110910400201610f01a015989464001d1a007503101450980300394000c6a00d82d060548071803406c0030006c0e4440031000a00b4044405074002c2c0f101d0140102c00400341103500c0c1e0000d4260150400d41c1400c6502005c400d440455010307078590b24400c1040b01d0040055900190500b0300307508550030710003d0300580c80204c1e0455098464140000c030107000c141c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703021447 1250 703020197 703020221
    0xc0b0c071a040305070605120c160605040516150909060e180102121009140702031603090b0307020d1215150509210d030b060403030c0212060411040614090f07050d 72
    0x95100c080c15000708d04000750207882d050030301208100c1d42c00b04240c0310343c0741e940c103035004000040c040d03589060040c101184115214082103400c1400705040fa18901481c220084690f01c001049881d1300182003110424050758088010803070000b880c05204a40180c000c9903150005400c0240c440585000e40c3c0d001e456090750040760000038010456a44114076500880700f240d0340050405080203912803255280040c40d40304400688024140030b8403540008000d281d02a690380d1400c210025203d01c00e551465002171065890320304403854600a030502e030a40c0401c03400b00319140c08003080e00e005411943e03109021090004040c5a03441d101c0001e03c06105a03082c1104038000d03000e50782000c0451021005051404003034480c0b688030304065134280c1b036050605ca030901440d8000503004581802c01da400507c2590200f0081000c00002060107600aa81c1881015141d044200c01e01c90707180c500d59040b401e00000188411064014243c100800307040036440c10140749000f40903100d5043d044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703022697 1250 703021447 703021457
    0x7060c0201021c020a0e061e0304050c03060709060f2d0c060f0213030609050c03120a02160e190b030f0609151b0901030b09070305040c0b0c071a0403050706 69
    0x10303c140d40050441650001d8004a0840c901021404060b01b800e500c2883d140c01200c01041c44100075202071a00c10500b40130b000340301c3d164a0189483c5a5400411036001c2c0079000f20004104094080d111000980b90243c40301d460000c0842411550610b503286084400400d10180c0503c2a2040f01e1104081169540303c0500c0003072400c148060f200b10305d240300c105520400039404030404070041d102c2903940c81280881c18a1003400c146250080002903203a260041035561400c10008400502503c3d5894080d00c082d403420600f03441ca03400d29813013208070007600b01c0001900c0d03021030b40f440000410485000034181d00240c2c0802d20340129000d0315040d95000c2004e025030703400b08200c5140303030215a11400d403551400528180516480313003510700d0007040c00b00c0d1001080c0e010303070881c000102010f003030349109141c0f00d40014050882517805403250340295401040044c0c1610480305003a40303210091200c0792a09032540031441c4d0000d0120041601030202000041050100c58018100c566079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703023947 1250 703022697 703022707
    0xf05070501060512060405010501080c1323130b090601140105090a0b0a030e010b030a030e010c050c18070e0f0105031f050a03060e060a0218040203040f170d2906030c07060c020102 79
    0x4401e0860b00b042c0c01030144ce50100246022550301d000380d03186080e818080104010000f00311443d420105001c0c4842c3c0d990303802040210459545441d02d40d05406221000c5031500d849074080d4854034203000e000030109921a0002055026400500c03c0290241001e40c45546d01c210340c910b26089600d24100103602c45039940c45031381c0c003406400a6042c046024014640c82d80c0d80103454007081c2411181400b00700c0c1580c1c010b0010034411405414006403013040224113203521084070b01c6040703130354101062220054140324100b4504e482255141a129075145803604021401c003045020188243c40707103c00320108440d04c403e1a80001540b00c0c1070082481d0744408512410300320014260f6031150f105120a0b6002000d845100000c00d90a8800695a40302c0d400e00d040154200750b40545090f6181820f8110240782a004000d00f1030702078000c00c244158113001040222034004020110b102402e00e0003020f1900e500110342120003039204a203000b032565a40341c1600d4500c40190003603540492 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703025197 1250 703023947 703023953
    0xc010603053d051801051501080109020307141803010905010507200604170415080a060b07081e070506040b06030712240f0f2a0f050705010605120604 66
    0x1409010404821403440542d014520300070000c00754610620040c0c552001c40d001d0b403200c200a0030040c291030001d01140c80c01c2603c86580c0300000e451280040c0b044000041c0703850035482602d00424250b41e810880400c103c0e9495a1360704694030460300140800e980c2c209680d03007440f880040b64814800480c262070142e4010f44030014140d000c003011100c1d540c00040e2224041282c0340d00c0395000c641c40701c10006c410701c0816180200d80184603540c0748844e40c0c0321000c1e000901c243c13007004189014054241c407130f4800d906038040d480004040c64400d000c45842c92080c04035000e4022051294503040c00c0c4540c031280c0c5040c0701680c0c29a00d42030180c00340308440c1400e1015001602940000810005566a4007030001e0003094001000001c054403010300c8100f0f42e0003490309080c0b00c91090214000020300e4000500000340311a0540c2e011b074a144100303c0c10503e03051503800898840580011144201b920f5591082404407400d568411011400d55503046100c54651b407550b0062903145000c1c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703026447 1250 703025197 703025233
    0x9110921070e1e0613020c1c020615010905030703080c010207060914060906070f0e010215151f020c0603071b140607031b0e0a0f0b0c0d080405060a0207080c01060305 73
    0x181c110302d8040100f038200304140e1a084005c602943d0444001a0f0b61010f46800b00d0920a107500841a00d480c1000081c05160340012600d000300d0324410b8102c188002e0600650b2060090b11a036078041d001070004102095011005e000c003a0040400503191030601d50340c5100719004200111031324417202c5081e804400c01002004c3c4d01100c0880200140d040c40c0201030704131003810300e05038104030340d14400002c40e0f4401d0020780160103000c12508003900700403071403480c10040c0c011154010303040c3d00040c01800e4428200c490141001e80c010b0140200c1c8002072000f00e40c4010807043c284844001d503c107200070f01004185215010b05011441d410720070b02882d003003150141c920400c040c1094043d05880f44503640418050f0304a04000789102c01400200707980d00d03420b1380107010120389140000b504200c000001d114071058041a01c50a0b1606070003502d00d584291000ba2180c1e210340e00164501c03155600409070720f406040741a052480b11082c2074291f50250300103c480d0782000f810008003907080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703027697 1250 703026447 703026481
    0x70302150f0f09010e06070e0f010503060a0e1b1903050105040b030d08220f140714090601033b0c06030a1505120606030709110921070e 60
    0x90030400d56080500340c5854205014200b1070b1514804800300d14120403d52000c0c10348141c110956a040c034101d04050643c81c40030a0b41801070f1620304022045600c500300302c9209100081c0042d51440c2020355aa102c440700600071683c1d0020326918090501e2a8400ba11100c43c50000441c031300c2e0302040c0c000b0140d1310103a0015001354203202040362684e0700441c40204203c02c1d80740a2400d0f0340c4001d0505103026102c0c0c0482410442602800c00303004c9480e13a0810360300e0080086004845440e0599035a601c0e144c8203c8444000031400082c0d1481c10b400a207801000514002c076049403070002400342d81181507180c1242090490071550a80c000c0c100540000b042c0300098958440d03400c0c041010f81c400141801c0c002940d8050100078401080a0500134103400350034440210385601e000d030750b6a2000d43d000d610074801d280001030a40024043c441c8246145001c083c01d04440340140480110043c0c4801e01c036107070100b42c0c282094005c104100003099141001007182c2803c1b40307600307207180320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703028947 1250 703027697 703027723
    0x60c0a18090f0c031806110f120406110c030a11030409050106110d030c0e1504030b040c06030522021c05010e0d032003060111030d050a0c020f010504020f04020a0320070302 76
    0x4020f1205400d025079001c4043e1160408804591f101100b002d5030403e1040d072070b06c155101c0001c14540315942416403520303c034a20030310f410088409441613241d040d024040c0ca0303210541c42007005000b07a510841410313108605545c00c41c2d0806c0d494103245010b4401c241c0040d0000b69200761003804030310707080290050705032060800300828680010300a106401c1d501d450b50140d0003051042c0054120841190029600f11000704240d041900d00019030400ca403060500207800c0401040d1040344480144450203544018485c0c1743d4000e84c04d12210442c100444074685030403440143c0071031001c0c0118010741e006840a0003100c039040310302a0031a01c02c8500301c00e008100030056080c12600004407134111200742000001c9191022490745144520880c084046007010188000c8001c25040100c1e01700180d0252007058054000b0b0600720780d41198060342c01018201100308606095004001e0070324145400b1a4070120b0307040041c548420540b400c03000d210009016014594107000e18120b1440e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703030197 1250 703028947 703028951
    0xa05100303080c160c0303050301030308150d1410090302060709081f200705010510090b0d031b05060411090f01080703110607120816050903060c0a18090f0c03 70
    0x10031518000c0000c68000e1595900a000040620030b45800c03100000034070380e10505100190ba22480c004203070760400e200840101b4a0032010840010403900c00002580000c0e10f0842040495141d02151400044056005000c2c1000c0c0c115540e032140902c01009001390010103581c10140c00c000c0074526541d000c80361070703040803402c00d030301360b1600020401b01100c41601142c1c05e84820f6504e19440030b030107001801090f000588004001c0c06400440c0705815102409020594402004003550010340542da880f00d8048182e80010b8019502e01c21081c04401c3d8403494464982d4586150441c1a0f80c20340d090300221440c1440352810300c407d41d500c00030240c450308030703545098001d40da5070103a13000003003c2107601c5c590710348661141020743d11190740003d06401270000c007143c054001a000d6642950086008601d51302040c000d5045918041c0090300070007043e61108603100f4140c0215040100300995a0000f10100d84941d4100001d0200c1620016541a4620108c0c0c11a5010321172201818 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703031447 1250 703030197 703030199
    0xd020a080301050f0f060c0d030b04140412090f0e04050f1c0c0f0c060c0507140d0f060b0d14060907031110030b030f0c120303010522180b0a0510 64
    0x19084020340b41102d109542c1402003600c903100240c0304441401195400c942e002c01e01e240c1c03107030f400124804001000d0302c0c00c010000d00c4409200c2900d4025003100a490390100c04980001c0401d550301003944402d01c0c000401c56110864408200d019500114520349480240b000b070180501450301c00c4141003009000c03840202c4a10308620034580c40c0d10003881106000e140922001040c0d0b155515480740d02e0210464540402400c01164510190384034803445201113a0314001c2500111b061200514420b2000110b942e02d465080c44c11108603049625034070505503d84844804100c0e0340e01c501045a44010000c1449103800c0e001010f95407142c0c1314a90420104c0c0745003240341c41041c81604c0540c22041c0c1c1001c10303400380c04241000c42d0903108002000301c003450040380c2890043c00449114000f0510740112a90701e0000707003e500c0c0d00507440359284921614001e42d107450100e079a100801c0d88680d91403c501840b1741468103842100c088008c000886003944110340d4486e41d080940041c503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703032697 1250 703031447 703031453
    0xc05100b01080c090a03020d030219060516140910031409030405120d05040612020c07170f010204080d0e01090e0c09040516080c130503061f0b0a0f08150618030d020a 73
    0x2a1501c1b005c2d01480c0032504100c00c1c98801d2054100900c0020020b040c1c005a030f00d0020000c0104a49080242e64504040d25100d44142c94030036291507403204550900103550f003084401c000740c0000109050f514040b1b151000c6a080100340b01392003c1c0d0141d611140303050148000c10001d03026208e00d9412405050741c1140e041400d441c01e68500e031031b041ca04010b4000c1c08000034803d410303100e000f42c4200d00d00010a400c04500042e912260007066803480c00502a049c1d0a27800b85000c0e0340b8550300300c880d005850520505821104c0c0718145040050306649030003c03040108240c07410883c1000004140e201c50601d40956a00500b00445c0d041c2e030810076480041040310081c1105280817000686401c0d02d1400c10101d01c090f04c5c0c000c060381c445050034075121510010425582c0800103c0d40c07000075031102c15005640441d441e549034031007641e000d103030100d6001600074250240d682c2901c68881c00307034480e4000340003c0615a0304920344041410100340c9049040f000e600c0031944008550800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703033947 1250 703032697 703032709
    0x8010b1504060c020604030204150519140f0d1a16210f1d03120703090c0308031009020705030c1006050d060b0a030b04031701060e011706010c05100b01080c09 70
    0x464103a80f80c031002c840001d2000908074880d46e84041d610909000e050642c0300b403155444001c0366011100c0800c285d10614400e1441c0b0313103900c1600540740402d4041003035414030741e82041c066240103001d4802c016856031000800d0781e003c440040880e0b075031400c2115410103203451005001750360030300500320886922143c0380848407a02113129161907100c608a00d80f00c80d0084000c1c1407196000740e00541200742d1040d039940003400083c41c40b01ea154003160341c690180c0304070b02219401400014006066480e00760440c0d001401030450f8405040001519408a2000d024030364031400c0a035550320401c83d00c2d5480c0c10307410350040324030615001c0c00708503965880303400c08801c0307074040720200320503580b00c000070b000403070070b500140038010140f0811080590040c12020201c4001da04400c150340ca0b002c04030740c09903800c850f00d4003140e101c808601011501500701948514145462a0101866541c3c0c40c18155080c0c3c000c02203d0721070140200c19a00a054258030602e100180c9051500c16400511 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703035197 1250 703033947 703033949
    0x4120503091c03081b1b01110309012408030a0c0f120c02031e30070b0f090609060c0c01150b2502060a110304120b0402010f11100c1701030c08010b1504 67
    0x40c40400c580c80c0c1b00c2a8050a40000c155007211042c06a1a803810719080b5001c0e00859000081c00c0743c901e41c00c900c21562040014058501c25030043d400c092a089003036a099034820300a4501101d440e19510001e103030901d1540c03007881b01e50740d501d401c00402e10605241003107484e4026400c180310842050240b00000313003100a0400896004a000461019080044d8840958000a100000b40c00f0301788140c4600160140382629000c3d12140d6895a420341c0f5490180c03011095074100002080f02041d598002d0b06d09690b2070b00c00040c09201e081c03001d0303405000c0ba81c045080e0ba10040380c1c01e1502c100c040303035040c0310812403045080741801d980d00085c2c20b0300c1485044814882800c0c0b500446000400c1a0b40c0034100e0060f20085c0e010140c00e040c03041d050208e0f0124002031149403100b040a124480c910200c441c000c0090060800c07440c02000904101060b0b0300801c03070040c03510076040014000c04c03402540600b8080d8189405c1c800640e0a50b42c40e022824029900303401c02e40c840e50500d1080760 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703036447 1250 703035197 703035217
    0x625030902030a021306030b010e060a080708060c031b030a0509010c14090402030414060103150f020403030e130b041805060709150509040b12010b101404120503091c03081b 76
    0x1415178140702c07810b000741b5486d08082c1c4483d05038800810450307801805075010309400c8484441e5541d43d0351006a903100c0c10b0040000d40d0704400041083d0f0f44042c005950070194200301111220401c01540c1165041210712a0303a194898040c40b104400070701c9464940390035450182c690501002c0250b95078400c8100307041c00b542d0300000103000d1003217043c07401d0035514021090b44c055580d45e041c81c0c4541001d80480f0764a05240007030100f1b07040d11030f00c2181c0840380c0c19140c110449044c50200440480038120211040d500c1d100e00c000c0680c0c8038403802c001e800b8a95000010500903040113458110000c000c041031048001091251422034040e00304802414034001e0303a620104000b050103800b291040c03d070856040303032001c4185034064000083c1040151140142840c8102c4121200403001e99001e400610400c0244407204a2103c01c204517405142124a013603081004a061401c502c3c0350314942c0301456001c1e00800d40c1c08040e40d600030182050203030391140344455046107071141e00426 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703037697 1250 703036447 703036459
    0x12030507141e01060e060d060903180f0f0504061202090702160303050a02060f01140f0a03170a090b0f1b0f060c0406091a0f1b0625030902030a02 64
    0x41050030381148546241e40816600a030100ca82011031486003000d80c841d0075401e2100104010121120062050f0030007000316a00581c503403180401803641d21b0f420350070032030519410001809400101c000402e02000c154071070742c1c50480c0d0740b1050012600001d202c0c6040c00410041c00118002400007190119403503046501c4450060340b034100c21460301ca1440d51602400000d0540040140501030340e00c3d0203032400350f0745100c1e281d04014424046c4030610b8413031003002591801c01147c041c01030300001d4001c5012a440361074880c10f1103800c2c0e01d0f010b030147c0d001440080466015101c200180066850541009031403941d0545c02d00a4416010191300021402c417400f80f4201704407208030f01c0100c180c0d0140e0a05070032910065015000d00c00101d401c0c1580001e100905211190743d880c003485009040810045001c20141d101082e034982da5202c0d502801c0c3c00d568244900c0d070065820f01900780004100740347c049080b00056800301d01380f40ca0184044056100401c8501c070007507040300c03a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703038947 1250 703037697 703037707
    0xc040918060524010206040b1807170304090608061003020609010e060c070e072d02070320030d0311030f0402041b0c05061003120f050417060a0b0901120305 69
    0x600d03141050303405010740303054107000a0024030f0b40025080c5220030040d03c03501030540b1448005a80d00d2800384d034000c186011000024407000c079035010200b003940800d025030340e050f540d030111441c410409800c0414030360000113042009403424407480b001040c515004d000b4601e88503071345024200b00c0344006070152100081030100ca030b10641030401220b400604140e11107942c0d2408070380c0c2d1080c0340510980d035842c0e00301003080c0390b00076280d1020480c0c580111400c028101002c0e50004102010700b0025441030180110004405000c407020200d02382c0c821101c0521090100f51400842c2090003041c0351501c2012050020980100c95214011400c1400035407a40e1000c10020301840c000c2e881d00980420f2000545030b440140c10b6a85402441141c0c0e003520303500000d11104070a03110051120301d00c0f2141c0b80c3d600d03000700d288031408403440c10520b00780b9650700200560f44070403e60014a0f03420040c20001050501d1240440c02c0c1001d07104e50314598141020801c40d2601c000000d41030120210b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703040197 1250 703038947 703038971
    0x50d0b04290901140f0d0204140403021f1505010e0a0302090c27030729043002090105150c070f1502030a0e01110f120315010203030c0409 61
    0x180d03101d640321140c1052048250306041141e6031540780000e1051095000000b00080400e500e50291040148811038219010042080110348034034101d030001d4079885510350540c0310740c64880c40760f806034024010321688000c1c0004080601d4941c003010a25065042811618840c0844155076003824054101450303400080ea0300c650075400203501a075034204200c400030308240076100101c0000700071801c5c04103814610307031350300040041c040c0c0661143c00100410544403199000c140d19410307904801200414142503142c4c0950071482c0d500c98101214400c170145000d6030120000f28111000c2544042d43c0002c0c2aa00180b00d01d074810b003903505c940342c8079012400884c2c00c081692412030320302a50320b090305500381e4401d00c40c00304001d2882c0b01c8101d03480c1c0080700b1680c15510b01e41d180c2001035100801034407241c200b080f50704918810300b413107114040c404012194800300400303981610791501e0810701d0705010030a001203045410520034086200e0003582500e099907180740c2d001c00c82c8400d40d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703041447 1250 703040197 703040201
    0xc0b0f010312260412020111071707140a0303060e010e0f0a150b1908060d0503041505090306040302060121110609031207062a020c0f190b04050a0f0501050d0b04 71
    0x40760740f07039a22244a040c001080324011519550350500d400070301504080301c0074031000c0e00a04502401e20311f0100b49502c1800c1c410b50061401503c9103c52095880030000100d00d441060042100401c3d90742c1c1c4d06000003030107409980e004040ca231011200d50301d8030040e8201d045101803d40501c454aa21144100e00103901d500c202501100170032689441d6030080c5003002d040059122008180e030b03800030401904000140049142e08140158a001d18240b9003007050045180e004007000002d0000c5207180c0c1c2d0502403075000313034001e81c000c24580d414a03031031159403450300240204074810003c0c43c00c0010651140e4416200781126641e45500e01c00001c24100064446c81000310400004c980c404c0100c0c43c0c1c003d05a210b0001d0b0010340c4402c0c20500744c0d0140c030442c280d80c00940d000c03a150010328604107103401000c034409001c0d032954000410400808103542e401c8218a0400420140b11030704201a4540c010031154915142c1c042ca44400a0a1480b8000310b4040c2c61352036405d0031165032202e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703042697 1250 703041447 703041497
    0x5101d150301090b01020106060207450b0301020a020d081902070b0115020a24060806161d010807050f120a0504020f030d021e010e06070c0b0f010312 66
    0xe000c03008180e41044990308541d20901500540c0c0d4134086040489510512418042c0d0340c0e0354004005682c00c0080e50516038000c030b1942d400701200d541800d512100741103420811102e41010a200540600030314109844211948500030780c0305229100402d6400120482c0d00c5d005400c0c0050707151038120b568400220030340303550382c55940006981d46c108012000d141d0304070b913020054850901000901203071100b261610103091480386650360a040132500e250304003404001c0800081c981d41e41d442d01400c109084508800c42c0f146a43c05844468001d84180660400c00131210000a80341340042c0100902134000e200300000032a8141c0882c03555801c0356540d43c480200e1700903500c1c28000c0c05000d801e048030100e00451070580030401f02d0400007160080d20a4540150041e21a04914011480340d0050921141c2d9250006140318040c02d1007040e000b540345a496100811240c00c1044800e603004e4101c1c582441c5080042002c107030f02c0001000071512610b4142540401d100c803007041c9c000c81d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703043947 1250 703042697 703042699
    0xf01140a031d0604020306070c030906140d0e011b030b130e030c0709150e0405150916090b0114030c1204030e090709030201030f0b0603130614010e06040609050105101d 74
    0x45500101044000003c03154402d070f100320220766080c0d5500904a4818001100050104404d407100b804441e000b4014002510b400040d0282041c03166440c2100380c070b070401010316199542d0ba08030090490154507002c1450710720705003400380c0b40010000c1103004000201c00000c05c3e960342c049500644c028021109041c3c2c5210448200945a030700c0f41004081c202080718044042c040001001280141302d00e1240b500240904808029801f40d0340c1103050050110300203008075404048242004000c0341e02801480c140001d411002d00009002030400d510344070002502402002202c00900303003166003052903030549488a13116458150f0b1400801020b06a01441410810600f00d80c4041c454045074001d80c0c040c816140601509011541c64004c0e042d0404000c10008101c2d2511212401025100701d20002c0c514401c42c128581044003030304200621001402404518a06070080c03402038609030404100ea54580400100008110340c07221003130021190492140648104000c021520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703045197 1250 703043947 703043981
    0x90c121f02130e0703060e06010f1112040902031503030403020d060c0e0603090a03080c04051e15040b03161d09060a0f2c0105030307021e06040b180f01140a03 70
    0x340f40e5166600c0a04211540c0c00000c2c03030a4030000f1440c10f8804011301400b0181c5070060155007182d0101c84c0f014240030032817100d1050801552242c80ca000c010401012481c2c00140c50741400000c1401d6180d000c10124400c2e0300520091025070340310302d60300c03480383d0b48580c0c001151510b81c2c0c02aa84c44030300e5420982d0224022080184a08000c122090705c2403203030366030080c242c0e03a02400c18400d0045014035600a0b041c0e41b403040030012401001c3c51311540082c004092150340c2c481c1d4030384640c061f803c00d5007445004014001c1580d070b582c0d984690340395141480a8040d501011501074141c0402d440c1d8803a200c80c3e0301040103916500c0c1200003501140d118102945c0d1548001000c2c20b01050300c400b030380d6900c00110b410b01285c0c0e1200306e06070707400103015620b803034201c1d000c01c540031070050040c450a0142c030140041d951b98110081c030081000340d000039194400515091034030001c3c1c0003802d01800e0308112035080d580e40107118600b000048072840341c0b1400c034007000305c0c01440d11001c6030240c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703046447 1250 703045197 703045199
    0x170a090c06110d09030809040c030906052508091207060902030d03020a3506060d05090a060f0e0703140a020607260c060f1803070b090c121f0213 64
    0x1070380c4842d4910302a141102141e081e044140021100941d1611010305041d138280604240e82c07800350000c03107003105280780c082902c0055866107011181c00f9603e00818045883c0d1803095588240141100c6403201c0c249032115143c400b43c1e89403100d0610125100c40034000545a0811400d40c0c000d0900680141c21070702e1030030301ca40d0064004e40c0060356085c0450815020495035907005d54000d000200c0112990480f03004440c903a1000c5080038100a074002400d004824948405c1d201d2644140300c1d04c801407503101040c3c1000c00c103d80d81c507000000c040e802c0204801d074001b000515a021203071300081c000d441480700d034401403e0020500000b940040d0005012051080889840c211840700100148220000080f03c1d0304610400c10224a2504820005003400160001903907003c80b126800410109445402070304507070048004603a084558820b0042001c8200100306d8034000a49003084003524069556548981400d855181120080403611044c20b080e01a10100050034039a1180c1c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703047697 1250 703046447 703046459
    0xd0c050a0e0d0c240e03030a1706150f07230a02092e090b010305010f0605031b0a020616030e0703020d0c0e090a030e0103090f0615030b090d1707170a090c 68
    0x1a13a80c04003900d000031848940f107034240c0780200c01c4030018486030311082039043d040e9002d4100c8610003006a940031030301c80c116481040d00480113001142440341c005540f4103892a040358040c48010203035000704410900310040b01400284540701e1501250208450382d10b070403280941484183d40324035068880c402005c4050309a988a50545c1d6454105100000c6d1180c0110102c0348248240016800403800402200d405840195000711a448021034214a6180c0c908440d0344084a0700005a001c04200500107540c422080070480540c0780500440d40c145601d99542c800a00010b88680800b49c0c040f010012004c0c5900001d00c480c0d41c43d940e0f180b8042d810030392a81040074040e4003048400650744d28544c07091090380010341d80894990303c00300340c0e9148e030303402003140d03100441c1001d01c02d10f404004501c00c403014600c01d801c0000140845402c1120040c4403105002000c10007011400912510300d0300044200983c0c401c20301013024655550b881708025004003c3c0c0030f4a030300b03408000810b207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703048947 1250 703047697 703047749
    0x30a110d0c020c0d0503030106050f040504110403110d12030b0a0e01030f0b0906060306070f03090b19060803031b030709120602031005010513090e030409110d0c050a0e0d0c 76
    0x803046a020b03a00b62822040503c413001124500090140d0400c0005102c881e02400240c0a074002034510a81030031307180d001080031941d158082ca0302c00c40000ca4100108a43c007000701c038051805840034083c1d45006c3d6a034a8a80c1c0340d0300035480070315454006000460302c0c0c00042d08024151000540310301e5a403814190b40c1f8404d06202036401100074400100c1da68000a051806008090300401c2c65581d5040c08450b03802260614404168032107403108041403e00158501800140354200c2e0701c801e00340e91802c00c07640c00d0381c00740b14150014401c0140000800d085000071104854072250348ad82c68032002c41e9401140d410501c20344075003401040900940368007079071143c41c88c510f144403400d85500c010754075405008944a103190202005001d407241c1c6401c404491805007045a09242c1c4400c2c030601900c0d180b46c0d485d4400d54012540011010f0940907078611242541002031521003c03180050145420001003401500c03c400c84404012403040200010040c102c07402a0701c410900c13a49034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703050197 1250 703048947 703048961
    0xd02101d0a0b06150a090b03102628110307030c080307060b0405012103021e0a05010b0d0c03060b010207091b0e010503010b0d11040308040b040911031902030a110d 72
    0x20241c0070001c942c4142e11030080031140c00175a151180c5207650318004849915520081c04041c9640360414006014600c80000080810500302001c0070038020301403c51512005144541450005001d1a401441c2483c0800f001c55000f228400c501c0c007003000401d140206c150b200810521001c4000038501101001808545204030424440002242d04100907960280900d81962403064201d02c401c040421a5907a81d9202e40151005542a4a200901003400f8500c0070219080100c49808010081c0b1402aa6140c11119540d608810b52a608049903885c040145162b17500c001d110307102c2c1c0c000c002c9080140f8816806102031000004a2030407510303111101c4010401120002002e0b40c02201600e050b0346258131a0342c00c0c03c40d0b4900b52000b40401110400e20264108000700110f00341f0002403000d001c1401c010f0b40c0d41d0740703001510011680801e21046070b1031000d10a12040d02160201c8404141d50110050707165241c201011000307219410b250300344035100280d450b0412403d500820 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703051447 1250 703050197 703050199
    0x12070f030b03010603110405041b0b0405120d0c031b0503030a0207110906151e03010b030405210a0c050102120115020f030f03044806020d02101d0a0b06 67
    0x10101c1c0c0500014142030383c0e803038000280118107042c203011b0241415404181d01074010b07100a1800211421014038121341508000c841c0c0c0c00004c2d0500150900d5003840a0040689005040000d01050014601e20304400000d0800100613201c507065060041035140755600038003540c2e664100711903508002d5010560481d232000140b10301d5029840d080341e4192103500043e00a6404a902e89000d02e41540852034420380076619403000c001304e00801020318041c10030044215900d0a00e03060044c5440306002d0700c100c240d61028075101c00c400061003a14000c10726030078005400b404500d01035000e4000d9202500360040d2020000500d60b60120104030a14243d4007a999142107240c040c603240e114074a5640c0f1061000c10100c0d0002d4010500d03450100310a0101c22016002d0509513528410b8074a0304c81c2800b400241c01401200c80401844014111400140038004100c0030181d100c3c0544003200b8600c9a60722120425140c403246444084002c00003a1040483c1c685018002103c00380c4103a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703052697 1250 703051447 703051451
    0x60507020a090e1f0225060501150e100509040234030504051011030d06152609010216030809010f1401090c0507140f21040b03060612070f03 62
    0x1a0710b003028030640706034a580c0000b43c0725038800c0d03040d4445010012281407290590801c4000014180909a00c420817050401014a120316040840a40e1030680001510000707018881d0500e6800c144c40000b40720341600e14051004014400365080d0107154030494002d4000034030030742a60b42c42d0180c0d401145c6100c0c5d503611244e03006450040a640c040710000d01107202044180703c50300d07180c0d45914103080c0074642510b41410200c200c50860708030424001d44d240d02c5a0301481250138030702182100ca8443d14209111050701c3d10101c424014035403030b00013001d5240c000301e21070840030b40485800440c0505081005c01d12803070000c10606081301c00d944594604500c0320b81d80d4915004a000b0900c9428402441d40d091400301402080395103812014800304100b4403001660204820405214400c003619081c42e04c1201181451b00b5070b60310003450b60008244001e40005007094030113655018810503102d80d200800300704144a41615401824503840800083d980c0c0194428002d080e95901 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703053947 1250 703052697 703052699
    0x103181a070f0c0609020d0501021b0c06030601050a0c03020a0b180c0607030c1b1a030402042d0903050d060b270a1401030b040912020c0a0e0c0a11030301060507020a 73
    0x49800600c030081c40b07000140500c09100200d0407540215050380d0008042c42d0300c800003a5038090072070b80801d010000820024074401c00318881403000980c174001c295540d9240d0300e80200020140c1c45080076100500501c004418217040c820000ca240ca0750b0311189605072402d00a9030500c0c1c03a469142100403522412040c4003141c1040c600317558000c0c4e03044e15540ca900c1440c2c2d440e031850310380c0c0074003200302d06e2414400011900c41428881c00205010340d40c0355900c0c02c1c20b005100a40d00040300c1c680c80d9158044406e0707513400003880700d140d070010312200000d858000c47c81c080300c035482101da4001881d0b0a0400228500d50440c0c000c05040840242801407141d03c4221341d90541c004444030382d40080c03118800c100492542c0c6c02c112000c041403400240c001240c0b00010101e8000303100540702c40d4600040d06042c3e60301080420813406085a601000626110044240b030800900b002102d52001c10100c8055028940c03881c0030f18540e4084ea40c50f580c42c5c9400510b2904103a038281d201e00b050406c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703055197 1250 703053947 703053961
    0x90f1505061314040b09150406020a03050c030411040f0917030709080703080d050a0f02120403020c011b1103030f03010909020312040b090909120a02070513020901020a0b060103181a 80
    0x80343c0c6540c5401010740c141c0c0b95455032101e0719041401802d03808140601e5102a00141101c5061072090b40304c1c41740103803983c1e0501c60003411200c00800c030342e802039003c10521000c112205c007000341d2068205d40225144805a0110000d0243c1b40c4004241d40740c0c03080700b2403800c0c907001d02031845520f280e629050180c0d0744400c036a41c4c0325000d00c40039102c21000c2040c01001481d80d00055403000c0d0455020a4000320b0900f204104c0e403080e4200d40d4200030030001d000802d5070600c40720176424800d190201c10011600d903048100300b05c0100040540c00005552401d42e10107105540031015060031103a101d45c2d603103610300301500100000300d00c41d0003485040510310f000f0100780c1341070b0742c0c41d082ea07039091809810038007100c0b000113001c01009204d420111441065448000d000c1100a6405020b41038500418000c1001200a00d680914014011000da90b6030000d070054420350000d000f01c0b0036441d508016401082c9440300040070074170000741c02061100384101000d030130711040342d174000ca550350340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703056447 1250 703055197 703055201
    0x2030c10050a050703050618100f0902130f050109060522080604050715051b0a05010c0e030111040302061603110a030504140a05030714030f0106060c0219030b010504090f15050613 79
    0x82d038031a40303e0140300c182804203401a01150f400703150203110f01c0b03040cac1d1501c80c44009070704540d024050546d00000c005a81c40700124082d07004245010002c80000e08200002e421000d40b4010700c020030401107451f11520303400c100290701d085091254800340c0c940340e103401c81d110b2710102d1301039400d44106040007902c80e14000d0381d0701c03404c202079890b00c3c100881000c441003a2030040b45011500d2140096540200d44203115031040f600007500c410718110313034020078903095600c0da68141c03500180c2804100090384404040780c1038440300d444003401d603150038035041d201d1824101d44010f291041918460030903030041c0c0103005440d1102140980d800c52842000480c60740b41c022140c02da002000d00b0440c03003511545810f003020004095640543d5104000c508503a015030114000a002c0c40343c0d50f0540c20140480701d007682554640001c19811a1641c66215106104043c001c40e0758092040900a00c54040400c45a11010840c0c03844040704408014201c2521030922400c4c46070840707242c1c0d403624 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703057553 1106 703056447 703056451
    0x161113240e06090a0b0604030f030503100e2701020708070c060e030a0b1902160b06090a02120a02090109051f140f0d090302030c10050a05070305 64
    0x485440900e03254081c0910001c141c09000642d2140b8410560101103904040b60043c921000f01d19a4482c59101800019049141104242d449001980202010842c6418040c2c41c0d1280c04490b0400b44c400c903526a80a515035204e4004c172802c141d074442c4d4010001420200c89882e1858158007a00d821180c80500c540d060281c1900004071024103607040c2d0040c061108140e94800b96080c0240c00c00464101c41d0f694524003051680445208141050b40c11210079814500041c60802c141c5040744200600800070303007140300c2c40c800c0d189181d008000381c200c19103621402100a6004482141c100151484041400d07100c019032460407011010640401c050b101030000c10307004841c6241640500c0401005c103000b01802c0c01d82d07555100c0884006500c1d14103180981c5141301e4281c0c2c0c08458018681548104030460340507610a440c541001c0c4115501d80404404450381 = true := by decide +kernel

theorem cover : BRFrame.Cov 702877697 703057553 := by
  have h0 := BRFrame.cov_init 702877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 702877697 ≤ n) (h2 : n < 703057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
