-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0746
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:33:14.623952+00:00
-- url     : https://prove2.me/submissions/86135dd4-99ff-436e-9f67-f91404373408

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133992805 ≤ n < 134172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133994055 1250 133992805 133992809
    0x1107060c02091f150201090b0a1d0106030206030c0c0307021002070f090e030a0c02060c12070b0f0714130302271b0a0f031e050105010906020a020303090904020607020d050c040501 79
    0x3d21000d640120030030440c800c06400e0b02c68580100120020031071440d2003034008100c503070762221140c29141451145000900001c031625800c8514080c071034891414140124001c030b0ba0060500e40c0f6545800302190f48640c0300420b8401c1a110801140c0016212007c10000c444240d90103486414104081c0d000c154000d548030701000c0e82003110596604402000300d480751139990404149203e0385101050b828000c5d1400440c481c0100301c0381ca540c480001c001003603920b1003855885255501d00c00f400007901000e81e43c04d40081d1100815640190000b00106075000460391001c540316075035400100c0030007240840c400d8038000e080140000c2c180744034089802410034203004100c0c02030189920800d0141c00d52007406c011000749801c02480c002d40c400007254840c83c1541c0070356444030620801408007840703070700d00158000000260140c0301180030a510340e8002e01a5107001c44240800540400281040e07034800000c0001c0300040e9500e1010f0208107200703801824501071201e0420045650503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133995305 1250 133994055 133994071
    0x80307060c14131202010306030510021e07080d050405030f0a020a06050901060e1603060b0a05090108010605031e0a2712020c0109030308070c062d090c0b0a1107060c0209 75
    0x24840c1d100300010782030300703c400c0d01d842030200034041c0304a0004802902060740054654026190034940d0201503400401c3c1c04105500c040d00368101c0c152074421107100f820340c0508480404d100d8260f000304140c002c5900700b8003400c2101c1c00c2c0305220750906c1582d488009100050780c00ba815010800c010750103070383ea026140000070001c261030701c4491a01c040f8020005248011000c1341510028080d0340a04050640b4013466900d48445400241140d84055a00750124240c1c00002400340d10400460f8450f1208500d5a05081c0c0c0d941d402d40643e04028204004aa4a40c820250f44804072060324250018502c0c04a83c48295418410720310040c940c800784c00c64018050110059801c4290701c022070b40c0c5840e0840c850b9480b00e004032944400850001c040d24203003020005003414034801d44002c1c6042118200000c85466410b1086600e55030f0020481c0400a1003041219240da0150a0441c214100905820015402c130703420207400f9000440414500311a04007507040100c4040c1d802a02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133996555 1250 133995305 133995307
    0x9090a090302070506130806010303080603060a0c0e01050c0c281a0a080402040b030d0809070509100b1c020c0a21081f2411121210080307060c14 64
    0x1141e20020345a81460081c2d5004010014605c09001c0300101504010040c0b80280ca0b06543c49260007001d0300310961f001c0748648a510b010401003100e07442880c6001b46581c0352100d12303c0b580307801500da54000e40b5420407980234031290882c1c030b40c450328a85c004c180803028000001c0d44848500700d41111081e0840407521010262401c0c02c0750700d460848034007292509101005076100c0c07000a0103001d80404441e01401203c03299204150041051405002200207495810342c0310b0382808800c413411030300c40510543d212810000c4048850090544011568540810412103140319090381e101441414107507221a00b0181844000c1c511640079403d92a0fa9048608007118010404100a807110350311001c1c3c00c05000c030b480420b503a00c00040200c00ca000403081e01c43c00b0040b000000c0c0b10340000104840201403412540045600300345507030461541c80c01c0c0003280015151100008004d0001d013219084003007580002080605000c500c2071307002055030182907600520800401c0e201d0b03104c40360 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133997805 1250 133996555 133996571
    0xd06050a0f1a07020a12060c020c100801051002031306020321040f1716051b03060408030c0a05091309060b011d01050c0a0609050f0705030d0503010e0702070b04060509090a 76
    0x30b407080d04601d60680c0001907602e6a440d40001100e68110350f021030145240c0390038441c10488143c00442248040d5002d4401c095400000c1c083d0040080d20342c400010201c50040c03085240c01c00007060b015200c0c0c8112410311203000348403850742ca02d6802417405684042000380e410f881070019a14005006140035103141050360740c644540411920091600000b00901e030805141315081d01c0f5a208620440d4030900c0301400d0140e00c43e034020f00622403007041210840340500300060f40d60300036035100820074039603039848021902d1600441d6403a410800200b090701520f41e107040000700d400c035500d00005400040f91605104a601072910345060000e1784000104400d4140e111401c00341e4213084c125524400460300d2414145610801440941b508200d68140140010061000f40300c500c21207070b800392200f0030035990b0448101c5c01c2c00050003c01c01444924285032a054201002e40101c2d0b032065200e038211040d58005410403c009900880d0100319403500c00b00a5070000c814481c2044860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133999055 1250 133997805 133997819
    0x8090f01020405130b010e09010f0315060b0f070c0e180c0909031e0702060310081905030304030c03050c0703050318121203040317040b07030b04020a0c02090712020d06050a0f 77
    0x40508800fa0905c0e556010364400c1d9002d07002c0c92590b044001d103803801c20341c2c440300111800c0c00280029910b078241101c600007245410b100e01816a000b1500741420800c031680821990fa00000040380c83c054200c2c0001044040070400c107001d0844100140c11411100ca4120f04d88001c00341305074803c1c4084d000b0b000e40414003000311070701c6000c00e41e221b42070801001d003041d40e241b146400094022800004102c0c0351100203101c0c80507140c500e01a1407a800d20802c02d400503511261020702150010800318000a00410642c401d03180b0a04190b0b08000711100708508144642d4029034242c3c02c009407270f044000d00304454101e0b1100841d0380201840820f650280d980a00d04901003000f5000004101410b0180108850400301a2030902c010f140c00d2130580c21100040c0d950001181c1801c6100501d890980240e4808084a98404505280701d4081244e0b01401800c08000d0103840010500c078401c3c5070000341184161190301080c014904000d02885000036400f1002004001c034045c0b28070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134000305 1250 133999055 133999069
    0x9060f140c0a0504080303090a05190309091d03070c140a060c0b090109050a060b01140306030316231e06070206010902090406230a0e061305090708010c08090f01020405 74
    0x2411000000391a101d90b00e00035241032050380c0083c5001d100200400c52a0b9600040103240c1d0340c4184141d0f0350300043e5a120f2078100b0003116009010406201e02880040c0701c59002070011814050562070404030100050b00b11361011a0a84850802200c140075105902545001c03800040e075031403540c1c1c1c1c80c2c200024070f4140c8140c8020402c094100105055260940290500c8d582142c190381d0074121900e020b1004000c101e032124049592a611038400700c0e4a441030300d109003800b0303024524008501c0c42542d00500341200854518082483d800390b81140302402441c6800010002d04500d407a20815a129555a410b0440303294070107020010004c0c1d000c1030725411142903420158403081c1440014002e092550440034204201c5645100054031481d403402c0f80c680c0544482080c00d03121140c41114500403640c41d500b0130400e44000c0d801403007ea000b15440403004c010742c2d51031510380072410f094036402e04260000480210520286000610403a102010300e070008510f014a4030001c1104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134001555 1250 134000305 134000311
    0x5011e0e0705030303090a0f02040e03270301052509170703200a0608040302030f0f09010806030a020f0d0204020d090f140307050604120c06140117060103020a050603090703140109060f14 82
    0x15840c234603000d0115107458001d209960343d48020b803070300c80808004511820380f40208100c420150b0000009581c2018491580140704224001c00081c4200706071001659240c00450304101400742d00103402d80402e040c901039107501030b0282881d10302e1400c01e820702e4030081000d0014028640424001030f0b541c891240120350040c01c0c01c41856540c0e080a9003980109102c2903422180010301d01c0380075240030300801c2204800d880c0c0328880c0c0c60700d000345a0380e55010b0100a4000b0507003004c6415034030b42078507019102e601c01000589000d01c040052410383d002035400301c4140740044039803420011220040c03020320303806030700860a048040c0c80300d07940c9810203071001d08400504032110f01c2d910320039225240c920790404800d2014901c0043d0b80d40008509104121608028400840f403031200416511f0480743c00a152450681c104020007040e507102030141c030410b105651001002074825803407001083c00e440d000294002c02401c00c5419503c0740038001c0456031800228050418140f420990 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134002805 1250 134001555 134001563
    0x60108031c11041208040e04080307080705090306071d04140f010b0c061311031c02100608060f060d020d1a0c090d110103021e0702031b090a0905011e0e0705030303090a 74
    0x4c0d2200950908602e58070582c2c001340c0e180300403c0108000d00040d1001913026480603941c1e080e0b9680c818000300d8040c0034031142c465040d0403400200d104a8071a020f240b9240303c01010705003141e1004400501280c4030465001220036201c030400902d1103040400307c1c01040c0c1c0614a80c54084a81880340c5c039400010541a1860518103008060019a01c420404140c0107421501c82c11503801111140b950310340c007072000521030784030b030809030301114041d0318219403525000700500d880c1c403003078500500320060005811141c504986400760781c50003016081240103200c0c4c0841e0304010341c044007084000400d4140c80d80005c00018049445c2c1c2c0040c58011601b042d00d031003000c1501e00040b0040c1c80741c8541d80c90b91508079980d001103c04044010704115108800b29100c000e4104001180c0a00c00241a5804613034039000960604403078129003116407003607000081c2012441c0710041d180d6100c10102018980e2800328111404c000c11884d401303014100c00850442c50249016a0b441e01303a018020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134004055 1250 134002805 134002829
    0xc060203090304050a0e0a0621140f01050f0106020c010e300303010815060a060c0209090109170a1205010f0b0c0715050304020a0e0105031914060108031c1104 70
    0x814012080c030544001d00b00007802c590070319540700078000d84186c2c19904089400e01e081400680b075440d405008842000c0300d5880b2031034011035110158a0b50044244540398020004200036004080c42403600c180007494440343d0a5050003002868881111074032410300c900c40c002e01c6d01540d940440c2030750b00044040d18902c80304030b54608403d9801c0b10707400351442d48408800070408034000700f4544d10019092518200503912704040040603281486031802280349034411034094149441c25030750041d0084004540c0d5942e595134446000440c0c40250f240003400315444100540c050003070b00c8031105411302840154100486610b0a60750343c46204498200040d00c0252072000740100700003400001d0018000003141d100145c003552084800300c0c441c6c2c20450000c940144414003c0341030340c10145c01001c42560003050303940d18403140442510419480c40440d8489042001100d0103003882c40061500d5902c0d40b51001c01880123619003255090902501c920f001d081e0200761070440d48011422 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134005305 1250 134004055 134004061
    0xe09030f030c0c2b0311120408070f0b01090504210e06030601090e0408070b091c0f0c1e050106090204050d12050702060d051906080d0809160608040b06010504060c060203 75
    0x1940c9801c401c0e450300c002901511480c0e00c4503500f015500b40404001d903c1c1400b00046c5020143e5061164150b005100d052500114010818580141114070f11480081c40c8000450300c413030441074070036030002083c0e40d2030707904000800c007030141c600da0f51282c40c1140b8600b4440008018203828465040e15028513030100000300d280e840380034910002c0c8a80c090601c050300b010f0426100340da010320f1050b201042e00c200444d41c00b40000843e1003401d41540604818409810001c5031400e0703410f088903080003040070050700410f5181081c003114650004085021050518045003510201d6205a41c854410701c03040000fa10b4011120001c01d078001c00c0d640c1800c10004081d100d40c001c41c0d1000e5080180440c01150051550780002e010303128402080300035070150304d9020203890b82c1d802100201d030809040c140c0c07401d01400140b80c01500ea503040c0d0f101c04410302c11100c0820682e901030300025150390180001d005114a400e03400800a1030001d14041c1880000391504540e0b03503004042c95400000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134006555 1250 134005305 134005327
    0xf010c050a230904020c1011040303050a14040b0c0609010c05041a0304080c070b07150501060905010309020d050f0109110405040c1206020c030d02040905090a151a04020d060e09030f030c 82
    0x3110000e0300f00920854a5a020441b403a694a00a01600c19001d184c4882d02c1d0f8132000180640e42105d42c165035070340c60f2076013001c0c1c201d070b10007007200c0280c0b60000c0900c00441c03000c213100042c18800a40b00c0003405c00f481e01000b01c900b9105405204c00c180002000103000d10102440303c840c03240441a14180d40f905c0d185071481035440b82d214100803e00401801084904421004003060b6004d4040300482005407816030f0211042807107140085000418204100d5000ea00944070403400107249042030344e0284c9401e803d1220400c5801d4841e55a40c0d4424104401c01d00d0100850070113403010021403401d5591030f02880d01c64010300044013900c2210754204092074040f0740c61003081d0000c7c2c030345030b0891100b0301010350860f0140068060038100086d40e001c4002582c000c09c9504000b140b0f4140c0f904100c039078020003180c40c000c0300950441e81d40c40715540316400240a4074415100020310755150000001c03290b800034080f21030a820800c044980c40341c00e082526000421f0104041e030300c04490746 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134007805 1250 134006555 134006557
    0x80903090607020f04090c0510050a12050a090606080303180a020a030b06030331080118080d390906020303040b10150801170102040605190318050f010c050a23 70
    0x104c140e10505140340c0c482040b00c0c101101049800540e1020012800d5000030b449901603290403000050703091200008038a4950080c2e500848400740001342d0702400e845980540c0e40035009411154000001d1001d0941e0072640e40008031180302c090031050b40a940081c3c1000c030144009012101c100000c268103135070034821181340581d0b10040c080111000302e1482c0b200265010f09145101e06c030540055025818042c4008003618000048038142d103903911024590480b6090510059564111034482d0314151b90700c10b041d0f00072101d000c8088001c918012490701c0034040c0d940c00c01084a070704014554000050f070350841d81c0f103030b500b600c80c1e581c10b1007200740700700242d00c01400d03100042c110040c069005045141a1007610011900c1d64141078103003030a030b102e00d01c602000100c04111480c030361403600245081014451074041409684c4040038000141040c3c1c0c00e54140e04000c1c022440d82209225001404510b810880d00b008000b15015014414a003440716041d05424400c00103208444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134009055 1250 134007805 134007829
    0x5250503072c01150e10020d11030f0a23070506070e0f04090b04060b010e03070302040f020906040f0603240e19020a02010903170103020619030603050709050402040c08090309060702 80
    0x804000c000e61356a240150048622101c1c0300104144002c04031803410300030b46441c200180c940051265440c1004100c6d0082c200c921800b0302404140301140700d126202d401403070644459aa000441d41420075072101012041c8003241c10001704018001c0019400b140643d841506803c004441c50340c08008190070b450401c40070350380945400c0b594010809445003440c0128000c4004103c0c050f040401900c0703074445002895810b03842000100014034003034000502d1200040f10150415111802240054102e6000031080d006014004d10804e03915225094000215501d840420800441d01d030003941d10b00c2c00ba404a400c41c1e50f00040040c40c8030030a00d84009501c072000c46d600c03e401c3c50300a00a002401c0101d001601c50550f0341d0340700c4208540036041e05d40003090549840d07503558009c150f8022071b6007080c2c18103842d0007000010030410311448000b81504007001c20704d032401d0301c104411980b203002d000060006031410b215075120000155100c843c01640d07455030f0790000e800007441ca09a9a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134010305 1250 134009055 134009129
    0x703170309070315021c06050102100902011206030b04021801050f131b081803270307030f080403170a020c10030b0613030b06120613030e0d0525050307 67
    0x88a843d0241c94103074003c2030160340901510480300011203503034040c1e035522300c0340ca40107a110710b90301c860544056118400e094030505006403200382b4008020f040e03a580c0d50040e10142e02d20401c000035402e1142041095a2076042c9000035503042800045d4440c030842c69050241d400c800741e40401c0c045980c0424030050355846500040010140000e240c01d6003143c44d0f031700795081d40584c90240d92000081c1c80c16141341c044981320400070311a10401c0c81c003c51824551520852170b0020110f401c001680101d64000c3d84415562420340c1054400d4603840c21900d0004502044480d107555408911080300000446491041480c3c01d4400c41c054103881f4032055215a0010321a0744d032440c4041410100d0b44110f51a1616981d00d404101f40c1c40d041d45440e003c1d5030840b80005685120320001780002502c241401d2200803058004211880344281c822500c65120b102e02e081b001404110610160020080450340582040040703521407080d0f1040764001c0c3c3c0880c030091031200c01c514000140340c1e54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134011555 1250 134010305 134010323
    0xf0e0a09050312010504061d0a09240e010b0d0b0703360b01050303070b0114150c0102070c080c0a17010e010207050a0620090d030e060a021e07031703090703 69
    0x440a1210f018000380b00751449141742190020f4000c40007207520002800da280501ca0541e1801000f030003400b4646c07030440d0010f01c0203040c0e100d812005500b030110480401d8002030480c10310380401d4210b03105102c0c443d200740d0079090320200161055100340d078011074516011440f00a550800c0d9844030313032106000d8517045840c1030306400440290201c40101e003d06054a8a641d84e60141610b038401c00b98083c016004e02c0d00180310400384065449000540580f0b2800c08280100d11589190003884203046140d40000382c1030240007220020300d01520044025025020b01e400c00650002040d10510309400150b10f802240440203500040d01e0040c580000d6541c3c204030b24220340c40325403003042140e20503e070100311500c1c0e007003a86055117070161180c0d1051030540748200300191a503ca072021010000700c0c008041141d01e80c0b201501071581c4070b030000c116480115030703075000c40e140f10800e07015a0391001c082000400d10780070104c00c240c0714400c0081d0307807502c69680a500306240c58001078100301c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134012805 1250 134011555 134011567
    0x30c0b07020f060c030c0714030c01020301030609050f0d051801020c0616030f0503090705010809031c15060c02100804020a0f0b1305010f020d08060d020913050c0603010f0e0a090503 80
    0x5000b0868542e122402016110389a45a030859030490000355801540c1e89030038411b0800260109641100328105041100e00f0100d0410507142a680245c00480e541ca80b01d14440707080050410030144000e070707000301400c0c030070400440040080c01030355611030b842c9050942145443e4001d0242c030540d501c02404040c4c0e00c01c5034040842506010482c120001010034003818039040c4602c0c242c038002c6081e0030142101501d05070045444010281c00410b0381d02080004400d68004203211505511800c1004210041310325544035407440c0c998010f1080c0003052003c00010399503540040600300b07031814078450b9900c0c1c50004c1803013501c0a400811140c401c0321070118441500c200507001c10407009525841564070b4900450b40d096840b42c00501503030003a102d16038840d004030401d03548128054401c174500e038119000100c800c40140d81c222a04007540b00640c061110500c0300201200c400e9403220b02c1c40d40b4012001ca46104c0920491814000120201d2044402500a0f281e9960840304498850b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134014055 1250 134012805 134012807
    0x5010501080f2a0d14010207050a030909140402130902090c0c070b0403022d060f04050a0e090a06050405120735040501030e0708031903050f01050616030c0b07 70
    0x40302c01030945641c0c440c00020240c0a503040320007034481c00340102d025000041007001c2c00340d2190383c8a0215060507510020002c450f80901c0501300c00703402000100100041802e0280000c4100d41000400c82c0c10800282400f803624200f068010f0742c183c030000c000c1c01a83d440704006142004009502c131060740c0600940c220510050720f4241094016a2031041e07072092407252620407803000035001117061108240c0764000025651070307500500d1295082c558034030001403c0f9840b41d0b01e4100c2122002c6003c2c012070910004400203001078142c000214107100b100243d440846182c0203080f16200c07400107040000c14480121104040706400c1d888440c07510700a0380820861451641201121004041d02c031461240e001888001440d07062500d410a40118050595403c0d07408140c031809100094114040004011200c800034595020100d140002419502e01911000203903440703600501560703a420003225003e07510f28011300c1b0704460600c3c06450450f5401030152002c0642000c00540d070b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134015305 1250 134014055 134014063
    0x70203010b0d1b090501050d03120b150d05130c1505070606030f0209150112090c0b030708010501020616090506031806040c051003060f140d0b010b070606051e19030501050108 77
    0x500203c10651154032150440c048500074441c46500c440010701000c003007406800b24101020403500041007810785c0c038000c034003407001d8a240442c41c20381c00512581000344070b00c20103070072441040154045c40035681342c0da081441c0c90300500b0018007803100300207100c60080f0102c44500760301500900496590741442e441c95800303810705a01650ba24000a410780c503100382010a8207c05844d0f08082100c0003807410300401c1195000c07184216002000b10390b14822202542c0314030160341d5000000d40c10714000a05058014041102c02440414601c1310140c0021001040d14401e4071802e44941e511003519007002c000b13100c2c030640d40c003c040c2440203009003031070b81005030f60023621050001d0300c45c00011000c451007882400c100c80f034540010b00c14203800c10b80f551411306004200c10300380005a02c5034803444800b030b400304085850020720b0781c040003c540141401000d0841c0d1103c40190303101d00c090700c03030a070f046c0c130382403003002020040142c01244561020140d50400020049503840e03446141d55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134016555 1250 134015305 134015333
    0x3040e07020114060102032d04050301020c010501080c0607200d060f1b090e040b04060e030d0b100311030a0c120f023103061e050c0703030e071208070203010b0d 71
    0x503d542c2c020008000d13500002c211b40c450240d13440d503a80103e01000c0702c400003921030790b02a900c2140400001802c1e6030f09001429004148600010303482d454004440d1800d000796083d6030107100300740216004034800d0300407603440c0e854461207e0901841c07580014509201800300400d03c928142c035564122801e6401058042006850000071000041d010f86d0007419a12922654814001c00207001501c00000c0603002445030b000030174103015481940f030654108840c207056055031001141070501e481c0018039014001410100b045030082014002c00303100003041011a6a1203015498803103200d081114048010108200200d102142501029601c440b036000c042e00003c41291044070300c0b10b450080c03843c84500b900d00b072003841d41d900d140280002c120ba0101030f55641420301c44007080c9010303071403003404040003d0f59201054900941141e814403140c980d16032001070300340712400b030791494084c1290308108541d07200d8140e0310020b4054506111600d801c0b41c1d140006100f0803154034000e0b03203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134017805 1250 134016555 134016581
    0xe0d021201140c090303160c03020603191107030f0806130f1d0c0d0b070c02030a03030c1106060a0b0c030d0212100608060907080c0702040501080606040c0206090d050c03040e070201 80
    0xc2d103404403c1d161a004074241c05606030810400406410b5241084903e841d2090700590640c2d960303500000c8007034200b1034011500c0280e01806000c46a601d12584401001042100d41400c006480c000d00c10210800c401003481540c07804141159685140c200c5014441c45d07091000840303440d8084050b0940510580c05251810b40000e88140082061035031040b0250000f0301d000300c1354031030989400010f08400180f000c03250140015880502c200201c045c002d840100d42c400c2c1d010002414080041c00c00d50003900501c2c1800b0783c0d9581c50300420121036815800c2a162040c000d041400e510880c68000d00507440011103c585e04181a50240310b00d981c600c0031400303035580b5401a00c00d50340032141c02c2d03407082d641000500310902501e940d5412480449240382810171a901080485400303802c002080c0e0300510801c0400e10701030080109943c920b20181250b8100031002e913079120a0120700c1c8082c40b00100c4c1060004c0003c0064900a02c580d00c0105034a04200001a0003442d21640e040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134019055 1250 134017805 134017841
    0x9060c0e0109030b340e09130f080901030b061b0705030d05030112030903060f091b0b04121b1e09060506181c060b1008010b03070e0d021201 62
    0x10300c00d50b000d4900141181e4020420412641d13a40c131240050312941041c0542c442c00360100507030901901c1100380700c0c1003001d40303643ca500700d21207082043c403150051102c1d40d140003c4401c01c0002d448a1740c0014990b6111990584500c1107000680140805001d080d810640c086a0010f1010b0941482c0035a4440403040d02e043d603403204249038540f4600014400420010001003107041c2d0348112000c040c6000b0f1500c54102030700c0781e03981015608541490140e55403a0984a13040c044084c50b08410b100c24900d180d00540d150029113503082c010361160400c080c808010503800e10650285054501a5104203400c51540b101c0d250205407446041151814801940105002200b842754105481c0c004081d0307424100ca031600002c40122480200d900306400d001e04022500d80d402410300e1b4079101d0800031800041d45001e100e1403554007000d040420018800400c02021210110f0b50840c1481c40c09841030f40001010400c8800640c9009400c80400c0181c6600c070b00040d48190058440c4d04010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134020305 1250 134019055 134019077
    0x8060609042f0702100e010210060602010e120c0c0d080c1203070f08130b060301110a090303020c060406050a080a060b040e18060f1305070504060603020406110102160209041509060c 80
    0x16201d4018200002c0d009105d51510080e80343c01244c0034120601c052045600308002e803100340041d10360a9200d2009070f9101d0110900010050003c240310300d03a4170511504145010004642e43d0440b0380e03030030707000b800421001e10078800301c02e00f11001040501c0031569a48004c4100c2949684112503110000d41606041041d941c490303a8182d0007071000201c1e0640318a0307982c0b1222141a0060700007940740d941c036050090341c41c107214054008040e49813110b0000d07501c0d41c10081d003424501d5554034418401040f0900000b0740100540d03245800514180c01d1560724001d0220041045820007080b0400200d030000b403585903450480e1207407001201004201c03013000300d507036940c102c2610205000c2c1d001030300284e810340f02414111001d60040003203466030ba80d610080380c07c0b030b5001e810040c00650005401d1000b06e8001e40c482586a5041008602e003420250f8400708e100020780d8024850140c5c0d4011500348000e0080d15030543e440c0300801c100c610060303e0001d00600105421602103074601d509 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134021555 1250 134020305 134020391
    0x10908041509050d060b030313080714060f04060305100f0801060611150105120a1e05010e0f0a080702131805010c091d040c0f0f09050c03010302030c010806060904 72
    0x11004560f0040e042010f0350815544d0000039205045615415100511203584c0308e4900003001002407205901905405007011031850152580700000f0340030305404c019441c402c044613002c81e021030b0324501d0009031a45640c2100c4484218135408043c0682800002040e8118103500c02800c4079401e80300c511618000700002511410380380a2a404c2a03040e1004208906069140090400111040d40c5c90321895a960b402010158101a0810030424030300004102091141d42c00200001c03004145c9a004980300c20707500c7c2c2c400300d8000c5c1403c0e80410f0900841d2104020742c6841030744078074144a00204680007e44420f1010303c140c170250b09100240340414081e81e0404266030220b034034124102d14a0202400000d40a0421545280c81010009502c041082a0b03000b80c005a2404500707189003000340ca003550006810403030070f00c40c2000100b00503900061112041c42c0f00b800c004101c0c2d513454000031260302820580300e41181c248080e600d5402d04a65132081144a1203040401200842517 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134022805 1250 134021555 134021567
    0x5190b011d010320180303131203140c030a0311160f05120f03150406060e280b0901030e070b0f0304060902060f070b060f010f05090409050109080415 66
    0x801140464000c5944401405024560504040c010304004c2100074044d410403081a4844100300021007001c5506520400390080c40c9940b2802100114140240340c6544003910038503228010299144152640805020b020600e0f0212640703104c1070b840d28441c210341c50b10395104102000000b1300d004c541d40c80ca81511429182034030002244180640c40075650484800205e41c2c060380d1030303c540916002402103490007401e1002d0704000e00742d22400c29171001c2e001e0703404040d411445036003803000520602c3d9100796100c0040d0000c9840388408101c5242e06450642e035040108050380600c0400f1540d40030041c000c2216003402e030382c2004507108d041d9445440312664025906488400c00403140a00f03100d070301454000f4000c0030b0001d1000ea2641c001585e55000c1c0071540301c80340340483c00c902441601120254051000c0d0b5080650b142c2003400280050420120b8100340039000c603214240c1c0d00c40741e1100c504c0d65403103402042403030081d051004403600729220b61081c074040706034555071043c4508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134024055 1250 134022805 134022821
    0xe0307060503060d031101111e0c100c1709330610090801050f0103140c09220203071e0807210602120406090201080108010209061204050a05030d0519 66
    0x5500c0506540312481000804c40c0b40c01d005804020800000840d060f0081c81114000e10700920156038400743c0044102d00c500d09103441d05903911090000360742941001c00c4032000c9558580340000c0710317001010180d80d07410928507034048140003002008031030301002800711003d0004100071156200c01c40b15a500980147c1e6400c3d10810300301011031030b981012200800d091400e405e110600320b884034052030840340c0031600c0c1007886585a0040007405242010a445507000c0005088040940c002140010001070030500c001c5221211210100b48000c2e151410750703600606891446980310440002c1150240721043c45d00d00600001659120000702c4800b10380d0010b5400885441c8807071503562902e00c15000b540c00b1502000018003600702252540c0c4560312850300007403a030015000041c00c8550580203c043c1e83c0c33041004d201c3d50303a141c0c82611101c0280354a0302556a0343d5141240c02c0c034030205c9005006203c0454070782c070003c030b181d04020f04c5031001914400002485551407402d881e100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134025305 1250 134024055 134024057
    0x309080f030a060603050c161211030a020a0c21140106050a06050304050d080402010807141218010f0203011a0c0111030c030405060f0402060f03071110240b03070f030905010504120e030706 83
    0x3c0082e44001481d1040b03100400c3c9d01c2d8102600c1e02c00044010702c4c1964404104000160840d0348171104015040c1c0100015004000f412040103404650803070b00d00b14035580242815100e64003456620b18250807103c09014050854011180d503103030060a5030300207036001c4915001d5414105411446104114804c90301603580005c1a254071505650707035500c500034940c42c0d060800c45000320701280c8100070f0051000105015820b2200003002c0e08486600603500c8003070b030040004104903070103501900c1c0e16252106501d80e40f008903c00580c014075411300d1014885002108101c03141240601851003607000360b050740e01030fa0341c01240310186d10040310020b50241c42401107020400d1210041c0d83d10560354141203042541021201c1d21301480c48010050282d158010041d031000b4a12025504802c6008020b183d1810006480d6503400000d03d03413410064011316150146210390449560150040d0081140e8105402c2ca0900755050000010200740200c0202d802414009194822901c40e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134026555 1250 134025305 134025337
    0xc0b01140d08030a0f09030f030e010b0307050f01090807120b010803040602122514010e060c0a0f09030c030501140f040b0a150306050a0c2a030309080f030a060603050c 74
    0xc1940c1e041d985400c06000f40c00410341c0d807403690b1810411703840fa200c40c140c041d48401100940050004050785c1141a200000344d05090b640f15042c1ca00040c07983c190b1340126040103c0c41000d10040310100201c0d8801c050611480200244a4000811850045024a00342d80f50380c3c2c0c0741c040d490390300d104520425005901c9080343d168805044000f4201d8a10580301c50703150b030354a0302107002c1900448403080c0c50b040054103c4000041c02440340070144001b0038050121480c001c10f00708110b000d1031800c00e0900074462030140f001d51040e000308028542c031140209186031030381822030003020150700c140072010b9030700301143d050701402c1c802078461940308070001183da40d88282034020303019000808100000c8400c0100015402d801210712460710342500041404101500a0090340921103100341003c8902c480030020142110b140ba550390141000f040000181c980340b00c00f446001868010780350044144840507145800c150704449281d90280f0181c0c950814480d818440c81082c2080080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134027805 1250 134026555 134026579
    0x2011418010c1401141005040b130903050c060c0d0524130b060c030c01060f081005090703020402070605040b0601180303200105010f0602060a0213060522060c0b0114 73
    0x1c8684140070320980f00701004100e6101da0000d503403e54244100d10100c0007521070030011102d402407030540041c2002ca40502c0b4101c0102c0201d8826000c400b4500d10310f41c0ca5545040515000b00b04681e00c10008a08441c038501c2e025580282540029403c0400141840d0208008982041450305400d841e041c03211442213004007042825403803070120021441d25008024002d42e6160041c1c08005280c1015554822450781001e08455031500481456007260506008480000811884018003134000182c4c030344920004924100c12584002e50250000503071600304001604800d0265108601584658482100548400884030405150031459001c2040803900c40c2e042420b104002d01c1e489000c1c03200d044038403800e4803000d03003280700c02c1420321100f000129410403401d588445100411070a04228520180c6034a0b400e204030380401201003480b80f040040320020104c10300040040402e00360395000041c1800514800035a84041f1900c0005815601d5201c3c0c81c060340002403420680c08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134029055 1250 134027805 134027807
    0xc050a020904080307020d1707111005131b06020a080a0311030c0a021e031c0609090503040810050c040501031a030d120c030204030804030b0403140a0c290c030a020c06130201141801 80
    0x1444460309164544160035040144002e01e2181c540582c0300b101070202045810704280f4070008000e0010ec00d05044010304108684d03021039180e00803603000c40000d60311561040201e02900c0d050b11400180341e000000e01842000c800010600020b03141c0030380306810851654004030541c1000c084105d034100300320b400e40f80785900002100c1c02c003141e0400150f40e40c60b05252412111440c0c811140da43c00010203020100c810130000072440c0c250750041c0120320700b001c40c80720a8061407150341e043c10344440d207040c1c10581c00d980074103001c48094100c4040300007140b8001c051062218021740b10342d141240d46402d16202c2d0084809490f04180c030189000d2455072441c00c1c2c80320007003060301000312269003410317041034180c000d0622001c40c2d85d420701d07202503a04101d108411103404210b0b0203031501e00b00100c00503840002d1076106040e04070700e61722a5141000a800f91007211601d1010340909001c0251000010018900542c003c0e69102c142d6190320010111170721410808549014080351824515 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134030305 1250 134029055 134029067
    0x40f0507170a0204180c08130317180a030c02240f0306010504080703050c0114090306060d05011b03060807050312160f1505040303050609070f0c050a020904080307020d1707 76
    0x2080b107000516141c0d69501340362034107504440d4010140c0d104c1024801d4141c0c0850600d03045031243c14101c8800490b580d014003418800089140c180c140d000c00030f4010701d600812034501c00081e00c2960262040391a00504034001e65204910410f4002c4200515405c916440210052018086d6240c0700c1d05d807a64a8154100406850411208000100713402c0e40074032032200150310031401445074405000024110110b182c0880550f1f01080c00407003e160740000c0d155401c1002644c02102c0e0301218280b90b405000700c0540300000d0080d02034800704542d4550b00820807a0030b0402070312000c54881007050b48955544880124404007030102101060051041396a128443d1407010000881c80c0d450001c10343c040141041e04540d600100400c1c150580102c0d94080c100700c980d0040f501e41202e010340b051000c01042c0041140340303003101c41003003030410440580680050100c01d442c5454904000d007544200d0340600140110304540201074011844241d00213003403040c050a99407045822509 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134031555 1250 134030305 134030311
    0x20a1502030d0906180b090706020a0804051c0206040b0a0e0607021f21050105040b0109050108150d05010501090504050f0105010f14041407050a09060804020a0e18070b09040f050717 80
    0x3529504c42d0001c0800f05145d1202e0709107031040400340368500e00018510300300341d5950b0000d01035401582802c00064240012141501e13000c0b12480164085a42d90100000003840025000440042c01241e030804842c0542250700143e51402005040c0f0740502040b401403078402900401e0184181d4651600d114031055a451245810350b4a11300d030f0600c041c09000340c071078800760680c0e846005005504007801200c948801c207003007610846141500080c08000010884820100c00c10a6000b15948048107035040c1a04032000303100702e584518220b0002c0c0701c01d03507044a2601c11300b4044404c000042c0541d0f8126040e0b000004801c43c80c020a010500c0d95141141d503000e56600030745900b0b03820120b022801160280c0c0d03150348030410608040c03c0b54415801007401c0c48030380c404000042e038464007590143d50614403205400c2e03d9490001403058558110400940118030340480c03c0000500a040c0d00340084400740251580c21940200b21030055400f00000342e00c03081c0d006025030040841d160 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134032805 1250 134031555 134031563
    0xb0d150b0105070b0f010303030b06030702150613060f0e1b0d020901051c0617070308030604020a021203010801140609010303050304020d05031324020102040e130203010b1c020a1502030d09 83
    0x203d0705426681e2041e030080f08030f0f40b0b07840624000005009040d0305101e11a207003481590428554203204c0c00196841b03040f01080007109210708009262520b07280714503140000b43d100140030346a11114240034181190142d8992070843c9000540d40545252170b0b81818080e00308483d2030700464650000180d80209109414043d0800c44100104c01c14032000b2401a2005400035280381020140003194065100d03141e01a0b11004091020032140d0085940001c0125030042c1e5866aa0758140e0510076030a400405200001c03000049803181900b1280c0c40740c0074800503180310340e41c1da01040101035007800040d0020f40e00b8800100103080c483c101980d01f6028a007240d04124400d040d0b0140102c45403c0b4035a81141c001801107214800c8620220b0095540000d500f41130078140069a0b645004058003104030b10620540c05545082d4002d1205420141c10827051f014405003440e5614000003049008011a890014582d25001f408410b484030039809145001c8031400d07142c02a00900700161 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134034055 1250 134032805 134032807
    0x50102073509010201141806060103053102030f07060206091903030b04060b040f1a07051504061e050106110f0606150f04060c0213381009090b0d150b0105 68
    0x3800f40d2420801b144140122604102010b0003100854145400500050f041c5820101441800742c11840c0c0401c038110004450142ca0080701c0c0c840400d1100804069014019861000c09001001c01c51105075551382d021a25140c80341e4049558030303001c044c68559000302c9004403030000f0341f00e40c101d802d0200008201045ea1030322540c90107640d600c41e034058500c0941d40c43d0200b0001003426210519040e84552490400303160391562a03c50f551500c18807900c03087e00c000281040001d500808078521a03c040d500306040c28501013005210038020000400d805140901c000d2200095083c1b1003d404406082d15858402c140225100706000e2080316400a011201151004002404c000c1025030340d101e12554250040c0b008001c20b031554100d41c02d0401c00510b0040c007034103020001d000a000300360055584d2290340040c0c0140d51000b0b1035840607011206044196000c0c0c0d40d1019110010400c0142c1e412013000c02031008140700c4010300d090b0900c1c0f0314226104180d40807400010781070402c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134035305 1250 134034055 134034071
    0x3040506150429010201180213091403070303090c080303040309060818060c0306040510060e2223090c010c08090a0312030f0c11031b0118050102073509010201 70
    0x111101403c100004a6140c1c09141c80e069170342402003242c0012610801c905800c5a500401c03070488094110720891502c40350000c0401c0700b000542c5070740f8020542542e803210b91a240042c0034011600703041d502c80c0721500000c66410400310489010b1903142d21481c0d5904e141c18401c4d80c01c403000030200c4000d0200b041000e200d0450a0100e40e1282089003030346541c0e4038041040000b1540050722192400003468810311026030810418000a03130116403080d42064402b501c05c4100c000944c0100a030b50901107010311051003007040198150f03204680501d581c0d620b031912961031003059806400203c1004070b5002140680005140c4c484014061510700d81d140d0b206c0504000106081e4400a0b40e0342e104452184407500c41c5c07104035505490440600c041116140359a8000e0400040313548150319030040b0710031425405030030f02c5010041e03e200000203d05006000350410300058400c85d403420ba200c20040f1201c00c0c0604c0214580504203442d0703048060540745a00040d000605640d41c500d90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134036555 1250 134035305 134035331
    0x30d020403061401091104030803100302100e01030c030e0a0807021801150e030c100810080607030b03100b0105040b030406061e15030603020a0510020106090203100509010605030405061504 83
    0x8201450082c2d9022500029400f4203c4072041d05038004d050151405480412556003a03040303c0849403c003482c0c0391691103075503c2403c001d54580c4000d6000800e034004100140c3c000324422a144802d03201000003114801040e02507400300d240d05400e030b40114001c4c200185911000e00800c80c0054040c0105194a101a0581290a8104000b9031500b40308118030a03a116020312203010080d4094600d064500d40851007000c03443c90b9000c144400c0f100040c0b0041000c0c682003004140d940112041070400c180040e0050008441d014000d0140003109040f540190180c124051010703556203290602d44201c010359504043e00803110a40c441900140c4104810403400c0c0b0010f800c008103060303900e0510205040c2c40d94514190925040010810143c0d03521049401124020b03900c4042440000004900502d0160040e20107144080180310907012244004d400f175880540d400e00e0741ea62607030015a194002224020026841400043c5034616179035404400c491014001090000141c1c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134037805 1250 134036555 134036557
    0x2030102070b16050408060c030c0d050a020d0b0303030f131b03030e0a0905070e01030e01060f030b04020a0501020a05100c030b03060901090501050106090305150403021e030705150c03070809030d02 87
    0x7501c2c190480802d2000300d04103082c42c40b80c004118107099241c0391071318919644601c1c0c000c0068515140210014043d00c0c1c0400c100c0e1041c00722420104540d02d4940f8442000b90440246003403130502e80180c242a03400e0010072039008400a03440b442c19681d4114192200c20614401146c0060803001500e000b505040e01040c082c510a444000032071000c103051041d124511f521003400c041c00e0106001400d9080f171191644841c0a10300403a040070b240e02298054452540050070110300c4100000602c80304040341402103100b265070034401c50352a00126602c4599501c0681503400422140c080201c207035000383c5909a0500380800d0076030446d800a401c024080f41c0580c4165100d84d103050400000b8807905000d410103041c020340490442e102d00d42c0c0c85c00d040011005041d16500450203250081000d41e4180c49541040036101a04840c1380d5200d8100a408613104e201b080c100e241012241440f0038468200500528115510800701702c641c4100a0a246854001000b0540602103140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134039055 1250 134037805 134037817
    0x180c080604150305031819051e0307080d050d1802360901020714060712021809040c06020601080d12020d0605060f04030c050d0c1a09031c020c01090f09090f02030102 73
    0xc0c0780c0d0803085550f081404404e104031001000c6140003a14144555581d001000c03d821710300d548040c840040c0d409c0424501442a00400f000348a000d28200e010b560050003050740401103031091140c1082d02071075292590800500940c0003010044c99006203200040850702040c1d550b0001403140c403040d403554161901074558086a940020310201444103c20941032700f401d21a0080c0000d14015100403c0100d4074800c84c02d6107500060900d003801441c000300c00004000038040311403030804d490014014685c1d441a4005401010000100e0740c60100d040448055030b6210304201900180c0e820000b503001440c0110b070f01d40c0d545000f0070303076854050282074002011240980d0b41c90450412100ba0400c43c0d105a118108031120720300050800c41001d01121664542010f0460041c03a094001e40501801c0341c2e05486642554804107001d1408450ac5217142d80a4604403141d0704011a02c0071194011001c0f0492080c40800210149600551f02c4500650140d20005256030002e420380e4880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134040305 1250 134039055 134039077
    0x3030304111302070c14040b030705060405011b1205040e0f07020a020f0d0501060b0d1401140609240703031a0d11030102040306020c03040302100206041a101707180c08060415030503 80
    0x40c0c6c400d41501c0c10184100c64003000e00310300801003280b0300000106544141d02840d410040d0b120a0441c03070b07070941c60b0800113040e8081582c0c1c020506041000300076030003e114075520b40341c1b41c0c804541c2d081d1642500c1406a2115400ba007442c45140d001d02070221401108603401185602912000c6103083c801c000c040e000d100121030b039035101d115404090318040550b0000ba80c6a42d0010000040b100840401c0a9019a02a5168080003002540e6041401c010b0b001e403141ca40080c03e065500c2c41c000b80701d018401e0f00c0c02c00c4150b0b011080c0075005d0300c80d075607508c0e0040c0391801c115000c42c01a9400702080303900103002502c2c044d103a03647d00d03080e6049071603460300517400410b086c801c62030840f00c61103c98100d44000e007028030b0903860303000c500203c4840000344a4000c001003a8440500901c0102a0441c4e15180c24090059025555100c04905c201d41d508208a00b80d10600c84542c0199002c880e040c0c0c0d107112081c0ca0310720420004006220240c0c2100754100d000000259086c8083d100255103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134041555 1250 134040305 134040329
    0x1404150201060303020c010908060402090a090f08130905010311010c0c0503070305010b0a0801020f03010317040e07020a03030b030c18090a02150307083103021203010f1403030304111302070c 84
    0xf840c60003914001207510042d050042902050083d07401c00251141d1080e01180c8410642e140c0601c1d90000700082c4a020b030401c103074452000c090128007801450b080c1517210041c00e2030340c0d580d40920110364003030000619600c40e2108010045d889280024041405248107614a594a400081c40c1084580c4101d940e65103911204610740342c1701f6142401840768600075464000b803590303852540d00c81400300500450080048130f107250a4101603030701400d030480468000342080200a0f54580e51988100c0010b0308241074142d86007008103000f4000e500140181030700c0014000380d0041c24000030070741869803041c40503c0000da1b89070145600c0c21320000034069640d0620610050121000400e40c210400716010907100c074850003001c051102d0b03a40c41e2002c3c00c1122501d412800d00c20320910120310070501100100764004429488001c803241e4403810100801c0800030b2607168001190064272802c0f01c0407100700d807420680c4c0c1012aa48245000610700780c3c095450048090090704100c04e43d4035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134042805 1250 134041555 134041559
    0x30207050727110c2122241d01110d0c0b01120201020c0904081b03030105011b0519031205090c040b04180312020903010e06150108090a03140415020106 67
    0x2c040d00c994003030780007100c0070180780403038580d031a99880c030f8905003d4003007903400405882c1244101d03084c1c03102d031610500d00e8100d000300c100c44002c1184890040701c0001102d1100705011480009203080071300e83d15140e0501d00113049611100c0d182c21003c54a050000301003415401d2101400400c40d12040c40c2c0318150394600c2800d0400441e00b05801c5101c84210074075201c000360303030001800401500c00300c544107011340d03036450a400350340190300291065010054503403603104008000b03107040e500b01307076500800a5481701d03918414080340079002c0e11070342000c880450f40d492200700200106001c3d08000103c2040310183c8070031600102c805c2034643d00813610044180c5000d0045080e409002c40d01403055502c00542c3d14018130300428020b0034080200009840762030281c060328102c0c10000c000304012420283c0c1592100303000c4440000070010040060b01660046011300d02a92413030b00103180500c000d66050714282841145400d58010078000082e0a009641c104040c2d00c40c980e00100307410f4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134044055 1250 134042805 134042879
    0x408011d0c011b0210030e01090609050f0304060503040609050c0303070503030a0b09190510080d0801030203010b01180b07110d060e070f15030b060d090b040b090a0308070302070507 80
    0x8411101c2a41009840419203404060103490012401e4044454030590107a030081540182505070401c103d55003409404014064940e0000b8461401107003540c4070070640c40780d4076031640b185005440100b074040c4041030210341c065000b402d038103100c2c0c821600b841d4040000249150805078007214183c4c4000100f084003c07690042a4281209640c0303046681091901c405080b800c850318030203021340e0317080001c0310403410581c100000d0180900342c96904c00b03d1400209954401d000c2680030703608003078001500b54421100f515030800107031615151a4205021184640d004070016100314020b01e641c08020758075410302e03802c0d02d8441c81e8001100880ca408144c04c21102e82c0c807200e0004540c80080101c085502d000d090042c915140004c3e00064040000b01c40380211950500c5062820645600304550354908500990003080030740e5483d6107008815a03120408a1300500041c400e1001c0340e8020b001360007500302d03a4031a000b0380d00400d4407603010301d04c0702510140c44201c215802408101d10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134045305 1250 134044055 134044063
    0x605010e150102010921030603080c0106030618050a02010807170c0408060f04022b0b090706020709150b0a0509090426210603100606031e09020a0303080a020408011d 73
    0x607580038002440303410b084e51502200384c18602140c404e9140d1550340c20452900c03c0c1c0c082e0b40035580c04061240c0720000c0030b0100717000301442e010854009260103410701303010081d10b404a1640ea80312005100c820201d90044074040400380080c0d043c0402000108520001000150310810581403005d40300d6181400d01c61074064060000c000303401c000c1c030912000d6143c4150110b0f10030035013880d00e281e01c1d02c18000480000048140544408220f006002c0c0030b941c0810304100300c82403071703080341c0c1d00945800c482d1044402c0034882482c011b458290420200880101401403110a8140503091070428008124082e03c111021680c456002c08980c841258240316000481142030141c1d05046180b102c841840c0c078106040c0c048e4030f2400c0300003103055608010001113990002c07c2848001d956500150140c6140c03441c60800050700d0410700c440e11620710803007600d107800509084c0720600e10789045e510b01c480076198001c0c00d9020040821041804d0240c12409041c206c1d8062503004010041418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134046555 1250 134045305 134045341
    0x3041a0f041a071715091810051302030a0b071407170903160303020604021c031209020604050a0602070f050909060a020d02072108070905031b0402070605010e 70
    0x91068800280408a540004850402000140702035507a4541d40d00644000460516035920075000804105c0703020008948002c21800c10344101c3c0c02a10354a41c2510b00751142082c040c01a803003104201148a103d40015801103080921611205513603000710b802d01500d20019100804501b06110038141e1004141c0b141c51a4403004605152240d40d54452140c00f51601d0f4030800808514400c113075500380440801c40300351a040202030756032450082d440b2a0115000d912400d6820329451200c0000a580520303103130701d55a8410b010000b08105d400402262005903000b0b002803101103041d850365890b00300600b055030001d288207440c100c003403804455603400041c0214100014410300243c00144079030441500500961500e4421215000a00451002404c0c600c40003444000c2001198081d2204050341d507201d0204d82c0d10300c4000da820840a115294241c2d11412000c20032003021103580150a0b002440941780c10b00030b85482056400a8220060005201052045803002d20507040383e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134047805 1250 134046555 134046571
    0x3090c0f050a030b0604060b070b0103060c0503061c170318010f1a09041b030b07110607020c0126010603020306030f0705010c0b1f0b030709140901091e0203041a 71
    0x80604080114008281510009011341040d00114020b9079954000d50041e105060015455002e2030070030000980082c4000c0c0c880340d28100130030064078801d004403071041c40058030003020851000160390780449a030100b5a8610703006480c14240800b0600203602440306246801d0f080c4c40031402c401e08454050b80c403045100d203800070000c094100c1c4031845003902d80898a8018941e01c1d410588100c04e010030703810881c6501a0804410001a00401d40c05182c00340c1d190f500142c0c001007225595402900c000015030f100c042800f1256210700c1c08500c44140041ca040180b4020380101c4003030300002c0c0c0000f801320b5000300402c8620300b401c0040c0040100c03450000c100b16031500c4d00180c5282080400a0040c8599200050141c544407036581210700c5600c9080701c40541d1422445195001075683d107000502d0b0450004819042452580046800a0514025901c3c0039041c80c02002240c40b010b09201d509420003070700b0003440c8003070f62050b40986c2c1291044122a8204c404090001709204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134049055 1250 134047805 134047829
    0x3170c18011b080912030d1505181602010b041b0f14091e0315060a0503160902090a120c05030115230402040b07060f050c0a1205040f0b0703090c 64
    0x2c80c1d8030a0701158003555a0000c03500f1365280a028003040d44028a0a0208514800080c01c4c400b080c0b078070f07030240d0500100c1e8604000300c00d407204d0412000481c50220105031503401d00118480c1c00508411a141c140030303000015210b55860040340c00e490030282ca1200030843d02c08034810f101d4108915000201103850140c84d40c81038882811601c0c00746482e440d01500c41002e500580310b09a000d4501d425074010120b50600744000c810311b811403002c45010f8082d007407e08000034070741000900b181064004443c1107022600f009013880c025006015a00d0340040c1182d40007440c00c61800d05602c001d400f4210581d0030030f040c20281800c0d0741c605081e01c1900075030311008018261080c406000514a07003040030104015080000f4064020f940050420480009140e0f0030003030a036010b41c0320528003103414041c0d55150401a034250141c0404035000c0b54030031844c49400400c0d0703804241e10602c00c0e1050b5841800326140d030300108074103d40c41d102180c4c1d9050a10244403d10a2000c01098010108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134050305 1250 134049055 134049077
    0x30607020a0b0411010516081c11090103090f0b0f041b030b070507050717010617010204030201200709020711180730020c0d090e0411090403170c1801 66
    0x40c0700c542c0c50081020348003100c0003044078016841082201d5294040340e0811019003154140060190701c5032503a150f10441400c4c0c489040307030b044d000d03010116007030100f0541001c169030010b40184c0b00a0b18211048006803480f0000142d00ca0503031402580e026521106500e800e14102d401c0c5481c5040513000ca50441d10b00b040001d18800708642c0c4000185003031515078140e071410f180783c241c1f903030800b440f400e81a85060001c0300f01507100c43c04a6450a4582c0064070686610300d00700e00c00d5000c0680012044901000808030010500d10582140303421a0000b84e6030b00b00090890700b000f0b0044441000c43d8840320342034a044d40b014210f100c0320a6440b103860800c0c00c00038028109182c100c011200341c0001526500004110300801089800410340d91101b14481c00ba884a00c200554408908090383c0411105100240d07a4861a80084034641e11100c2c40200030400c100204200c1c20448091688805804c0e400b151034041c0c2c3c00006403684071680402d03800503483c150710a0904025040c800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134051555 1250 134050305 134050313
    0x507061b02091605070c06261512100f0606031b0927050f07081b0301091d010f09051002180609030c0a0314010c080403020307060b06160602030105030607020a 70
    0x40d02d40000d050016901108080fa10a40da98001c00c9805040160000320010704560041030040c91041110030494141c02d140c0701844140c03401344d07002020a03d007072041102c1400c1c04140c0c0d40c074140c0781d0400c803108020028500e0040d544026451907403281c0340c038401c0080542502510b42c03013102001c005034042414580080014807180b18282003003492081040280d241c0103142140038014000c14810b074903144220042101c42500d410000070700090008080051000e000c06078203003003841c500e20750392911742c09102a0188614424504101190b0300c40380c0c0e1024491120000c10000c00410780071480d00300141040d201ca65144a01d5004008402c1c45c612100351342c800c0d0640484010761100440e078046845c003540040c54680180000b400030050180e02d020650982c0303880c3c0000e0145058008080391034032810794009002da031003840901e0000e000c941082a03900d03000f500007414401009040d00f001c5c3d04498003070320740a40c0040180b145007414498140d00c2200d82c00244100d24203135031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134052805 1250 134051555 134051569
    0x3060902121002130510080a051b0f04080d030507170601050d0501091a06030106140c0f01060e040506060102070b040303030c1e0c0624050d0804030b072705090106110a0f0507061b02 80
    0x150000b08c4e64920008143e0b0301070340c401c003102050030f4100710b880d0940e451001503107030300600a0100724400c5800c214400382c803074003800b44aa10071f81c0c0c5402072a0ac4402c8460003648014118034140981480084514012840780c1402010100c0c000320710280100c88503403031803280615181c090704080005100d600d4100460424419800c40001d503103c000701409030030400f1078250400c3c0c84d400d1000009540001c1b010440c002d5019500f62200c2e502d90b14016681c50081e44a01e01c00144144410800b083c001d03841640081030904100a80700111029024908452407210b8041821504560f0a20500c1d01c5034000381020200545200455250074054aa1a61042e148508080300d0aa01004280c0c01581c006591103014404503041c40c00d8040c00d20828440f1007030b060761a44402659010011038041c04440c0d000e00032070717070341c0e42401800c0781d000c50214071000076807003015051000550541144034009005101070b0601c20708040300141159940f0f815400000d14108149009d03a64070b031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134054055 1250 134052805 134052811
    0x20109050c0d050102040905041113090c1401020109141c03050c040515190903020414061f031104150305090a030203040e13080c0604060605030a08040306090212100213051008 77
    0x1180c0950510441ca080c3e0301900c1203810881e01d0904240030303c0100204804440785e8410100d0b068018030b140050828112000745002030541080901d00f044400442c110340c2c100c110040c4004a08050b02e61640ca441c11008803651200b0350103010001c1003000300e102004550209032409020b141042d00c0101e907180034a000d204c2c821203900d10102c1d07280ca0714808403000101419200250154000d0003e03055072058442640103070700f44920980144400f41e409440307100c0041c00140c000b01012080c08180e4520101442031581e103080f60040300e81d04402400061401541c000f40d11001c81c00020265031002d410b4035200c0e0f000502c104006600403058605840488003020100c0c1c4c0c44584c840f806148010015100304400900700014100200f80c04c0d11030b42c0910b00c1845800c1d038038401d05550303c284950241c1280d100380400e10004009406c400003882c0000c0c021107800c1291404681080d403617408ca840c240da400501081420301c6052010010501192601c90b84002c045001c0e0001c1002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134055305 1250 134054055 134054059
    0x10c08030c041508090c06070b04060515040f09020a0e0405101a0607030f0206060307050a05060f0d050705040608090a030c030513032009010902030c041703160606060807020109050c 80
    0x4800074803039030080720a58004000b442200c10b418940e10101810301c0105590450060141c0500c0c00c03aa4100403089803850b940c0100f0041c050380c0d903525600c00a09015004c045076001648030503410782d540340038185905044c5000054005442d20402c0440c0b0380551101c108481da100c10080400c8012800d042c03d101d00100204851544070401c820701601c4244003913101c0e4000c14814180759003c1e0510303242e481e4907000c6409986811041550300e40180c8103072507011100040034001418803c024028440d41c0700b8203641010079206501090780d6086440030b00003070001c00d040059075030143c2070980100350304006d05072002254400802d02c8902007030103000e0060014843d00c0003c02d202a010046030410742507400300d940003c0e4200002040e040140c07103240000004280407040d4805c80b405800b007070b103420b8a810300c1c1000340c40100c0310103403d400240c0401d010b0301c10360403450081c5081c1c552003994001402c5050020282c00d51001a0170001160f24204180002940020707400d5942981 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134056555 1250 134055305 134055307
    0x30609120a0309021503090d02010e03190e0301020703080619301506091401080a1205040b04081006080c0112150305010e010219051303020603060d060207051e0c010c08 74
    0x42008254003800000f03200a41180120b80d80300340d0a200340020754013813282072040d41c0c1c00d800c20031800c038217982440c482c50030030383c00401250201c08200c84402010140794104840c1c2c04055000090880e008641c003500498803040030800c0c0c83c542860540903c0a0744500390203694204113041e1009030010800c1001040603071460b00d02c040240348451841c039408207a5000326102845540c0180c4458410900341500380006042c62200d01d00d041410707a1192402052192580d0301c90004c0140c0206618091082c03c20020034182954030041020f021004014090303010b112001d402191003e61011107290025500301301180c0e440b80c441408030340d00d04c201040c241d45024100314200103541c4018069841e00c80c1713800c030501040d0050034101c141034007021164000f05006441d00c1c46403e1070121034152040d0207100518102020715008840546002030552103030391040201d9005403005c0d5400c2c0d000418002442c101c0b8002c15084aa120000e403280d1a0b8030300002e486003082d0b107002020000c3c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134057805 1250 134056555 134056567
    0x40c0206010608010b0f09030618100606020c04052509080606010309031d0111011401150c0c03120216120506060a08121606060608070f0c080306010503090106050406060203090a0503060912 83
    0x4c8500075038446040090079924641815000004440829015807800c0d00400c1c50bc0d0324100118811901101c41540280010031010000c01001b00ba00811140080f500c0c2814001c1d0072910201407681100c0e10380341c8690b8503060100040c58140018045810103003015000c0b00000c0d404080e50209185840811600900e10390040c1c601c2e003510000c54106618000c14568400c01c03020142c2e048945507800e0b409001c0b90114111250400c11101521300102202d082000a0300c08140111300c8a4610655104044c45051240c090115a104250300c0b140540301c1010f22500b8030801e41c00500468456594a107010320341502c2e03040240350803c58503070200c2c860444d0012090450701003507114204000694980c14003030540360094030315000250b041c030200503815000d140a110300c1c80d0042c05030360460f40c0308001140c040e84000c1c210f440e55520b800f400102600c0d036024810142007290061a00c03003034148140481131149034040351185c3e024006002400d440454200c1c2a081c0090225954030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134059055 1250 134057805 134057827
    0x7140d020109051e0901050906030d05031503030d0501210302250b040b0c0d110309040506120106080105090d0203180103200403050d0e040b0f060901090f080309040c0206010608010b 80
    0x41803543c41160072030350140440c41000f20b05006801400030172030b030084059883d442402140581101d009805901c002480407242d13002e20301940d840390302401c1031400803c5070030110742542c0108911070141a1184010711030703000061030700e50245401c1009180d12803495100259a2071089185407414150044000d0a4a4280003080301a080100903e582d407680e56210f1080c5510400103201c0501400b00c00c0c4407811710a200500050310040011400c120600d010070000303000140425901c40c441080c0394000040a000f008010304c0d485000107024500105440d060002d010011811504200507486048099140310b001400d000c1c83e0020300c4111340d41410242101c04882c030400751402203800400c2100000c0c01d01081060f0b0350f00c181c251241d56041c04141c41c104141c1a03400110418081010b0900300c0149c04c031140140351485105903900d60100543c840750700050142d0f000042c41c402181824001d58485000350700c010021503244c07050040c000041801200710000300040c00e0b880f91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134060305 1250 134059055 134059067
    0x2011508010b221401080c01030509120403080f0714010504060606020a051002030705041e03020102070603020306060a0c0512220b0421030311030f0403030608010b03070509190e160807140d0201 85
    0x1042540b004d003220f96160481190f0302c10784000c00c140041c0c00c1c000050b03241c12021551090860f03450500f40e01b05402c5a5841c3d000350404c034046211002c05211904c0403980c25040320100d0000c0800001d51814036003010810f40300c0310f030850b07429544914281800600000341101071841d55610050300c070b80380d41004a401303100c0c40e071000701034034003200c1d0070b1212036038046214049030710036021514040e5a03800242d0030380c001112001e40c029024441001000e002e030081310714107172052003a954001d611482402d42c075003040365210000c03103000f061105080e403500c0700800038082041989080500e840e818440c50300042182030700c5402080035a10816029070015040b5104400d41c803a201d16003000071300066501160140d00182c2042000220400188500b1508080c0a0043e000c0c0500b000306104d014480036204d036028110045800400d00040d100c0c050190512502820b070705c40c49014002c091a4854114031340c4c42e0070040040182d07420103281c5012400d01510300c080018000d000607208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134061555 1250 134060305 134060321
    0x9010c110307050d03020f071a18030a1718030a0803010501180509010b030a0f092607080301060e100e010818010f060b030901060f030803011a040f0602011508010b22 73
    0x444c1006104004160300172403170f078014844c18070072241806e81d218041000c841e1540501030082008004103101d00c0c8001360b821084140113011036007080138a5491240403142140c400040c400e0100e9441d8040f00c0c2d01005000040301140204102240754a400409100603c5880e050118480084a1a20300e08180500a01c0005d040c0c4400d0340c0d40e0400c582e1194400c5420b03c85180c58201074510000403072080f010170039000780301183d101048140c114180c0d1070800641c94034840900c5450002000c4000841c00b03009690b591000012001d41803128061140140c0401e0150400e00941c1c0c0b41d034000c00d030310303032244080282c07031003042c1e040e21880d005000a111403c0d0b0310f404d11702c01059461040c0d00941c0140d200700c0007004516a0b40c44c2c4207503403c406020042c0307041010001080b002c1e07449404a4103100342d459100b0328095031151080ba12840941c81040583d4481f06840e80c00c540f121311240c01401c1c124020b00c00340f264100010b161550f108202e81401c50080701050694480b5400405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134062805 1250 134061555 134061559
    0xb04150918150b0909060f0403051b160302030d08090a0b070e0904030305060a09020f0d0507050f030a05010303081b12040318080303091b0d03140906070803060a08010209010c11030705 81
    0x1940203880304404003d01242c0c968076002e04200740108075641d60000d0b15a106460812603018203856994080340c843e40516000308179119034041c0410942c2e0140f0000886c0d03002d103000288461301c0d42c4145403c00268100e02014000d0352810850080c1010035181c0b0501c1d070055280c812540d822074182c50440b400c504003500140c00000304070400d90198000d9018540c200c0d0441c0403a81e0b02d5000600340e01c1251800c1c1c50b2010305220f41151955550030142c2c021007641405406d00d492018018800e41080303502d004015143c000420502d0b400c9170025400c12201d0400140442d4a6500c006042c49180d4941c2030031444000028141482028031414006291100140e25175030781c81050b07034942040c0d40c418002d0040c90304c10208490b006658541c0d184010341414580103050310301340c56004040341c8a5618082c108445407032543c0c0c01c8001d1803060301c224401500c909000007802040a400d03002503017140e00c104596441c45e078000d800d0131449a0301030546055034450302e011030b0410403940d001da9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134064055 1250 134062805 134062823
    0x1e020f1605010c03051b0901080402030708010c050a030c0e06030105060307030e01020307030c021e060106050a0512070809010c02070806150607050106080606090a0c0804140115090f0b04150918 85
    0x320400106400c18103488210b541c0c140700c81d4403558141001d0f018100b0321071341456030802541c0c269501945005a00600003402e592819039104005400c0d19000c1e00400c0c00100300180050600d90180f00c3ea1001c64070601d0310300e02c903407060070120390544011f0207094460b10000c40016450380c4260131a68440312048025074403402e010300d002d400303041c1004404002d409011603000c00780c51800c21502d609081c40009140b16440c01e0001d44641c0d0080b0401d80800004001c10303004c0c0843c58140310301400041d0754030720765860000c2c911800c45064011a2046410031003080028803000600d542c0c010750300a6480280d0f40e20700c00041c600f80300d02c45004115500f0580c00184070030012550798440d5000740c030740c0c4003995a00f41400049a00444140c00450b07120030201c0c011032031071004841c035031000000004408592030184407000041d540010341c581e07203800710003913459494040c038011490250360900842c0b640000b400c44039429401405010342d0785503140d0390304184201048480c01d030491030384 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134065305 1250 134064055 134064097
    0x3030e0f130c12020f0702010c14031305011101050f06040e0f010f06050f0a030b04080706091a090d1d0f150307080105030c0108090a0b06010207051c0b0601031e020f 73
    0x40002c1c1c03034030000306008510003050800100c900d90085841e0314440508192410300250b00550f90000400020f40b55001448240c1c16840d400b0001014208501000c1c0d804507880c100004295810030b804000040e4185024400c48260031103131b181d08440c2c00c980216912084042c1640740c114018226501503003810100182e80c18580d00a509071501035030b0b03415403520500c0600803580102d1000500508c3d181e000100855085005801c0843c841c44003c503058083d0b460711140c21403001551081d86480340188544440c04110b10940722820f82000c130303107020b440d8a404c4606c03808103a0041c007401030303601c403510590f8a00d0b6088500341002c080b42a01c03070801d010000c040c1c0f0800d018940c024420141046180d60082da0350342c1c1304944810091500300802e41d18401009005083c4505503c5545000310f102d036140200345800220040c20a04584c107181440b5903840b4016040307906262600d542619244902030400b145035261a1001da80c8040c10340301100a885025042102c5444402030307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134066555 1250 134065305 134065339
    0xd170a0504180b0a030609031205070509040c03150e0c040918060b03070b0a03025e0302060c071a0903060912160606170106050114030f0103030e0f 65
    0x40c006442d11424121103107003040e01080b007191000c040c41c0380d108880b0102000055a00e810052603a44a41b034600e001200c0c1c44003a2042d82c03404c1c0c0d0b2140203d0000714480d14a800d191081c141c3c12082071a00740400780241820911038056801818154150940024481d1401a04550042600010070815104000c4823110710902a18040750340c0b904000c03035403800d840d00141c4c0328269030700300020a01c7e001c01c6040030380007940024400404c0c080345074495a404000035a00d000d1b8108001030076426101c103403000070311501c025103d00044c100d0b00151446100b2003488400d05a07507060b1141c0781d41e0340e05043c04a217801d50603032040424405401511404007042006401c0e0402d050301101d034103031079040000b42c8070601041031074a021002d00c04102d03280301c0c0d1445a50f10501964000070242e40700d1503c00d43c40754000342900c5a580d11040200040c0d40c0c0b09008104110154115a00314108016942d00c000070601c00a010414068821046503031501454800c081c00207003104c3c944a13440302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134067805 1250 134066555 134066557
    0xc0316020a0b0309030406030e011407030b240406050c0709060b0904050a050f0c09040603020604091506050301030b0f04031b140d020307051515090103150f0b01020c0d170a05 77
    0x100e0041400403000280c40030b2010a6038016411031001d10b007132608141c0c041b030041444240e550860b6498000d22040603088400903401000c84e0354000c55598102001c0c001040e403101004000100724007041d4a030480c0d03501c15201900d016140142e03541200d100b5052a080e9a40c0102940740c1c941240010321040c00030040880ca4802c2d18184032595032100e030881141d0301110444404006a8001000301241c40020301440c00b00400004225883c2e0b00440c4668000380c00c141c0c482992000658260000d80c1c540f0b0006110b0303490414a1036046640744551003101902c03c062500c604800f080405015001d120310102d05403510804c0f03406181081000c0c00c11841c6620007600540740c1060040344044111101c00350450001e040710408101440d96480c1c000300250a0403035130b04c51820240d07560b01c4001d4021070203402107039410080c041c46030003103c800c11344120215240c10b00d0542a40d801041c2d210090070201c44c41882d100481c200722003081c590a810742ca4004000a00041c4160488 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134069055 1250 134067805 134067847
    0x9080312010e060108010e0f06040f0c02031305031207060504081e030402010906020d0c020d0503040e0403051c050112061e1d06090705150a090f0e0103050c0a050f04090303020c03 79
    0x82c0107550b0303403141e6005440c188420300502d2502e45101001442c07001c10044100d41240c8080c00000750070751980860022640810400001030304001451000c91850507012809000c0c21005800e0b41d070350100039a40144501070300242100c1d100e10000d428422103a003510025224007020110003160f00300040790303c0e84102e4003240030410100000c50800c0c8001103001d0710320410f4840c0e1704018641c0d0204804440c0190048426200c200400b10f00301004031480390141d8480d8454076282ca030740c43c51707416178142c001c00440c82107440c0000411014900b1a001c40302103411600c0042c00320a008031000616802c4641d19030bca50600d0082c1100a0003152a841480e060f42c0541c0c165031600000301c2d032501c0051017682d6006041da0f40036511502c030f60004210f00449410850300141d0f82d8548000c10907074a500c0112600340e07003030040050003170900100489c844100c580c410258106800a9500221f409000d8040d540d11140c850405000b541120b0600504004036511003884128500ea80c1d014a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134070305 1250 134069055 134069069
    0x50406050a060e07030e03090325060203090a091d01050705091201020405060d0b180a090b06120a030e040b130906060e090607030908090907080a150302010c02100908031201 76
    0x2000c0000e418a5081c8101d000b50750050081010546a84ca0b08601512901030a01000d000070004d806413660104411620400700a524104ea40e003103403007800490105a0001c002c4d034004100843c2d40343d4400c1050020380d03612810000d801004403845c55860070a24071503006543c603180074458165008000303010311035000c8540d25030039004410402d0a0f401903109250308035509100300b89440700e19820500740700d500030f00500e408041e08034102144a000b50f0340c8034032407039503142d1581c00e200940080c01da0080040d211541c61550307080b991582c4502c00f030006070401403044031600c2176641c0c40d02700a0b0b000703200038108807500d050b01460b04011b007260b0350100c641910f4414001007003501e07851658800c40c1c45101038101903440300c0c0140d02401007090100e41c188805c200e03c1c80150344220702240220490703525828185402c04c0c0c0f0070304071424111408600c00da060700c10070041c0e0780901c0c0264017540c141c4600e40e03211540e44e000c1c2e4891005401c46800e81c0004141c50580841b800c0030b0504035242 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134071555 1250 134070305 134070311
    0x20a020a0210090302060409050a0213030b1006030612020d171b0105010602010506010c08070309030b07031506020303061e06040b0a0810050411030a0207030e030105090708100c0f180306060306050406 88
    0xc012010f580700295480002c0d04502d05100030090300000d684550b40c00101000007519020090f20302403803211b1035400494102005600f03008800e40200300d0f00e07014000c1400c0400070142001c2c0c0601e101070720004001c0c49507142d80e0040c8200a1602d4505562060b404296512112103e545541c0d0b0207543c4400019980307403030000a00a44140280c40c090341c0103846442010441da100c80c0e03140d80c001c65003a001d201140790004001040c51002d00c1c42210036590003d9080c16509090502209940c071040c00c43d0b1040c0306000455541c0c01004422441078540000250b1040b400b0078014001c50344405400000454040203454014040d20302c190b07e03901405282075211b40c03c1104907801102590000d02c82440003a80d070789111381c0201540d0740213040015000040000003829120100c0e000c442c0c03038000000c10490b17070004100010b500c441c8803200303224004115400070a4402c2032443e2030100800307000c422820201d5510703800003454108400340304498480c1020790281074151011155586 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134072805 1250 134071555 134071579
    0x30c021504080f0105012909091311030d2a08041e080601180f0b040f0b130216061e0c08070f050909010b1c0603050a03020c03030c06010303050d0e01020a020a02 71
    0x4010710581c0d043c0d40c0c00d50500c2c9011509100207c011424080003041510002c100258040d80c0d03401c400f501c900d0340d480e6019130b04030b86441d019110720006181540641d201c048202c1800b03410030040d4589044540607a031021520007104602d012071080007030204140020003080c0c0e000340740e07561076802954900181c0c100356514881030344e4480c01d104030031281c411413402601043c49a0400c4002050001000c02e00240c1360b0005800c40e0091510841007559034540064503040c290855040210789010450400740300104210010180e03040013040c0d40c1e910380c90854061000c98100f51048100241001207d425210141920fa02034030303450080b91f804010b9541030f901c520103c07183c01601070413247c0164601050030410750003450390420b440742007050311480f0310070301d124682c01540110000d00c032006a03424080e040542800303115000750820000c18004110002c0ca083c1141d5061800700d42d1409800f41010003840b00c40100e10142d400084e01c040c0c00380e400502000420b00807640c003801c0c46 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134074055 1250 134072805 134072833
    0xa0b150307020c180c030a0608100903090f030309031e0b070203040e1015120617010218010305040c170a0209071d010305010f06120207050a0318050303091507030c02150408 76
    0xd0681c81e03103403241c4d2108100182c405907104000c0d60304070038818008903207980ca44416504120b08144d40c03202d0b05580b01a0780c0c05066016030702800a1400d915001c1c1200d056071001003021000c0e010240c50b00d282d0074019410340130b41c5404003d406412442100e043d08002c3c42c001c3d120382c480e104e82001140c86c20085034640d40140da00c40119011291100031945036028207485910482144e404190360303c520016191422140204900102800041e0380f00754201010810341500d4070846d0425240800300030005000724091307000c2d0b0b0580c621214440340304980c000c1c5004840203009400c0040f030b5091101c060740002d0030101c0107400c01185072410310800011802c85070244580c0070070101907407081060502500c801d010b14118500054030f0000683c44091608140d00004c900041024088a002c13110404020000c0c01c000c402840c505041e400000f691590728000b0b030b40300d800c4000745c0c440030580112550107603960302421140f01070030039a0400d80641c00a00c6500d03a203000d0b070300d1303100c1201c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134075305 1250 134074055 134074069
    0x41e05010e0904020405100b0d06060810080a0b0a0f02040e04061409030a03150b070506012c190b030d0e010f0c0b040f17030a020304020a09051501080a0b150307020c 73
    0x2000000d44002c2040d5119001c000107404081c0c1844042002444081520300d0480010541403100c0e42c0b0110300c007441e0a00040481800805500600345c50003014005120045003c0302c00a0b040380c840d84090b112040d025008001c811104100c2c20702c0040d002491010018210340b00b607014400402000d814900c1c402a864022035400500e60810803075076004074000e034071407804d1441c0b107040c0444080e16000100880ea01c424025940e55000000400040b1190f10340546001c0b00d0100040449005030000d0343d007854080c1c6002c4240182254500072121168484d90b0118001422103012080310007024002c20400640180041da8114440142da8003404020881c1ca40c0420716000c269a161611843c80420800c203c40d414101c0103a1492005140051405520b0340d5500507a81c1c1428810440100143c1c4e0001c08414240380811643c2014003128242d060401e003090205a5141152030000b002c0b9009038590002d504140c5202c0c910212020b1842011035400b00c4140c0740030102000f400e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134076555 1250 134075305 134075327
    0x100515070c0308030c040302030a0f02041506020a030305070302192304080601030b180d0908061612050a0b100320030c0a0c02011709030723101e02041e0501 69
    0x40d0078850742007000002d104900444d4410103000151b424292a580040d080100c13000c4242c6060b14012400000c1d444c1a01c12440006c900c01c900010311494820007030f4450080385805002e01d42d55a00090b48540290101d6101c40300389034070400341c1c40c2c2154020b4240b40905041c4160414214403000304040c4082c104e07016604500000c1c59260f29603901d441c401003008040c0108259400310b4141f8640041120b1000060b603500e4098615081c250818600b400050032201c4800c89038408681c4103400001013030501c101034034041429600c1104038000f50040344203294101c0020200f01581ea507055025a40d00c064844006504802c014040c030124041610712000c0c22401300b14400100740507903804002648181445604000300010440d0f06901c225800c0070710390400038241c1c0c100402044180a6540034040c0350102544606105136a841705185190505555500310020102d94140b801694200540155901d68a9140c1c1039401140a588050503071a40700300403420358040d8509440c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134077805 1250 134076555 134076563
    0xc080f100618090807020a030f12080412080402030f03040902090f0a080d0f030b0405010603020307030506031501170a1506080d020102120a05040609050633030303131a10051507 78
    0x3003000b0420600e00802400004981d03181e0204821801a201e50312100e000750b0141c0384030070b036140356828074146029040049200300706820007004001050205d102e00d160b000c6280c14411940c60b8030110307140c004003460084542c03201003070026142c64030303070004c01c885070042c1c8580d07a450400ca424045420218002d6241c96080800120600391007103500d250f41000900d00443c035900008003040844e0400e03048480040e4000082049140c3c0500405402c05400d80040109034940740103000f00d20810b000e50003403020641080e0030640301c1042003074145074210820030480c44c104038101000340310030f10803501f060042e1110383c500280181f0942c0c40f0f03146808480465540c03240115001443d0080c030031140d560350781c001400480c804008852050360100d025914200c1090340f01c3d10400d6240b6002010400c2c201c0d10380d182d6032804020f90f50024003c41c40c0118442441c5880c5e00a0285101300445041c4c1401c200500903400c0812003044400c20b850310009030300c0c94015404548105840070f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134079055 1250 134077805 134077829
    0x1506110313091e09030c0c05060c1b0112060e010608090d050f07080d0207030206100b07030507080901030b0306040b01050a090b0108040210020f0304030b040506070207050102060c0a09030c080f1006 87
    0x1041c0d542a410521580744582e900c411201041d10f15401141c1281da8158009480716a108003007003100f20500014140440b00c050610000c10340792540c548154105080b1a1511962078405902490300e44021003441e0350705000e081d031601101c40340140309205110029440001144980c0004229003100e410385589591809600c2680413500e5401100300b01c410500405c01d89034580701ca032024010307843c030a81c0503007a07038103090b00c0000328801c4903001060603650401500300001d40240444445039800100c403a04d503040400141c008040915109402d03000c0c0d6401c01040041100d0380d141a550111130007107005403645a100d08440202c3c3d96507020402c0c142c0410701514044030001d200d10114411114552080c00c10541580c0241c0d100301d4800c020001030100b00841407240d00d500868510040c56200d141c000000d50300c0201900320120710070005031500f00e80e44110700a1300a10381003800d5054075a60341103910f0b600c0c0000081b104a90049801c4405010014016070049a030303441104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134080305 1250 134079055 134079059
    0x3060b130b1e0f0a03060b0405060102011109090406020708040f0e070507030e010c05010f060b040305150906070809010e240a063611091903030516030e03011506110313 74
    0x600350030000c2401c19a80f281c80380d1800e01455440644032130140d44504004200109411300740300c10b443c03002d0071003415039041040c01385210f8281d41c03c1d9680c0000c00c86140340e043d19141001d00007031141c050042c20b1a9070004010541d1595911700d0f408948612201c00490790b66807108a40314018420003d00040c002c43c1e00e501c41b503200d0b201c001e4440e40607100000700c1ca4146a075400449099902000c805040030804105012003031103e008500c0c1d40c2c8080052902c0c1030803416482c0c403001881c0b030703091001c0100031914062095100c41c0d40400740c00103c0c0c007100c0295040d03040020000d8403020900507032000040ea1070403a40034413812508d100d1b6480c011020760103c4e40810700b4142c00003000a491044645482003072901035403464000c0d00007801d9407480a0303400d02500462040000d024405581c00420010b0380c80401c0742d0b4001c1d001007016000840c40c0c80c080707540f0450703503d149600d5824404400007c072548015401103800c2c5031501302801181480c0c041e16401a200c494000280303a03042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134081555 1250 134080305 134080339
    0x50414060706020c01051501020c04140105090405030d091a010b120f090c180403030507091206020a050405040c120b040603050604060e070b070b09101b180f03060b130b 74
    0x2410710148124030141c145488010079508503034044422480390b4015642600c8107503010310043c5900301d410b0781c042c40142c60f001c6003a10003103018821280540c40c140c0c005001d000003030081e01c81c542400201801096500d0500552241e10070324041c8030188540000518089500103d84209100701c0790a50f60355150408508240d500403c40900c60040000c0d80010740d9404140000880c062141c002c02c80c2040e007402001c464000306640148000900117205282011000f64401580003101507902c000c1e10008441d580265880706401074245246540800d0304a0001582e5203120001000318100700801c00ac151041844040c109800400229020900ba03422400c1c120400340c04031a02c4035a20541c480f0f89038441d00003601c450300c01c141445240c050604c9400d00c115174405e8207016105640040641145007080342005000d00004070481540d81c1d921518000d1004c1920800f10396500c3c1030080142a490001c4c9200b001941c10019200449100d255a20340014003866070349101041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134082805 1250 134081555 134081557
    0x405030d0329060405040c050304050c100c0f0203070b040902030a0b150d0b0a0f03051e0109020f09090c0a0f03020307050a0f051306030501090305190c08180a050303040e0702070605041406 83
    0xb8600d03800090801c40800c60b030315107004692001c03030190342c1c2a90fa032600e0f0622a082030340500300307548034040801002d0031956115283c450300b1078102c0d0710789030703490007910009252442d00e40c4201c0c010300010400088d130200c44d50185104030b034100b00510059010300c0c108040f165614038042c1c1c041d0300030701a8604002407a0302c03a0480c4c01c005410076424603121910792403104243da1048070254004045040e41b0000400089201008200244401000c55000424082d000d400e454025481040054500030042104655400000c0d210b2014251600341005410000b03002c2603000348a2180700045a0421a0820f811103001c0c0d65909120743c00c11302000150307000c881601203610380760744002c00869000c1c0f040f403030550300c00e440310350355040c420464107181f050031010341080c00480c0c1814404900d80c403007200e6513550b0101c8200440e480680014402062682041d9094440801c001c1034600c11510224080c01041d000c40d0003440d924401140e003480360303010395622010100ca040719581080d034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134084055 1250 134082805 134082881
    0x108070b0c0a020d052401050901030305030421020715050f0f071406310312150b0403050f0c121005060d1a01050f030d08010e0711070b0405030d03 65
    0x2406a07000c2d10071540000320b50300107840081d28240c11844004000b07100c0c2e01144400760050b80b5a4824640c5440001000300805107c05001d01600100140c10440780b1207925510301141c50340b4001c0ca4040e441c000350744608a0040b01d24070b44001c121060b141d8081e4054424040c031010025150949901800080d50032400b41180c00f03000c1038581c100d205409204103485904002400c10045652012080640441403503003c0d005100390a880042503003c160003919010034103000c9140f4022034035030b480314105036004044490021034080208000032132000303070902d5600c04071400e54484108000d80059503554070f203001da0080d0030880c607000d52074200c3d542c8050000c1160740f42407a1a03c0c1c05000319123401094402280790750052100e4a0040e0100303a0f0f0303c20603001011030020b01203001d09800c0041c003402105968040000300014410341c0c1074420306408101b6545160354800f100f003ea900103024107407280c05012920424a442840b4000d4016040703c3c100080484580045084603207c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134085305 1250 134084055 134084077
    0x906030f02130527010602010f0f0b01020a0f110a0305100606080105180a021b0c12121602040b1206070e0319030f0309050d020f07090204080a021e030105130201020f01050108070b 79
    0x55001040c0040e1044e41e00d00914154002090700c08040b99064100c520758040e030b0303000c01d103403003500035003a640000d0701a200d603808441d0100010047c10940c1101ca031480f015a88200c5580e40030003000004104d00c04241c207060800d101301a29150251030380c0b40c0900402d0b4018281550040032400c405905940011401500601e8110704003400d00641602d5840c0c0c00d2103902c00c3c04110310310304105000690813040e00c00600b421629a40071030060b4890200c290312416540d00f44202556155401900703102001045544810f4402e80500e446000c00c662120104107140c00320201c40c103002c101103055944288180201c0c58481e42c05079080e500701e100c1041016956600500002d000300b01e501c2203400b064008041c00003503102020301c2c0500c503810041c0d11900500040145102c001510400160b0403540800d120300038a01e80140320940300f61b90b90b455802c03c4140210030f036841c0081d400c41030007a42500e02e0000d044001a090f20b40171310400c98203a00c40a0b00700303d04984000508151040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134086555 1250 134085305 134085349
    0xc0105071205130b1b010e1002130801060303090312080c16050a1401050a0e0a050d0f170f060901140d060509030708030a05090607180e0c0c030a0906030f021305 71
    0x3e03500c1c03448560241e40d0001c896110000130760400303610f00268080c1c068082c00e0000c2c030150390800120354070345a01c00c2d0010385194010170210804500b292569000e4010070008020a03a03403802c004000d09132610040e01c001003041190b1500d41d00c04c044042c4209000c01016140003120301d00400a0704504c1c90035100b900998080c03400103210706603039082c14080b6030000f044506215060004450780b0f01844001c641c42008032400083d80454103803040720031420701d201c0c1c0f10a000350903100307048014000703412400701c0400c220303900d503068241a00a400690700200036a032164845803003403201641076030340200482d03040b0300010069000075500070550001e590801c801c03039454000360307041030300d1043c98113031280d0400c045040c0030810150300444a00e0400b80b0311408240191f6a003103140940800b622000c2c0004041c000440c1c100c3e00ca0380d4031a4211717a82c50500c100c0040a0307100c5400f5007070000341417851040f036030750103402511041c480f8070001381d10103441c1c1800c0140281c04100c601884603a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134087805 1250 134086555 134086567
    0x5031207020f0d020d050c010e0316150306051f0201050a020a0503040f020109080a0b0a140403120203280219091a030414061f0605030f0f07020c0402030a090b06030c0105071205 78
    0x240c40959030105c0d440742008110035078512002402110b501c07421075010342d00c51000001506407003012603040361150f2041d610229600d04003200544447c1c0c00c2250465003040c10342c02451036881b01100c041966030b0082102d6200c1342e10000581c030444070b01c0d1000038001d001150218101202503001d1a105040c00d680241d6110344140c08d000d886d400590300e40c4070f800d0420240392441d0007110f25041312003041c41c22034980350380c02805a8084101030305109e5408000542c9200d40d041c144007900d910000c41c241e002d0f4440c103202c4007030f60248112040a100d0200510701c00350143e0203034000d40d00c10040b100d0480806580c3d00c00c1582005000b91490342d4031940400a1036001e2041c0f0f4042e603620302c208030b02c107032039602030744208169540806c0801908004002d011038400d15102e8016095010600c02525102ca04034585501010580d501c03520000c1805603032245588405043d6100b0070800680c0c0e40c595080607100c101c04086d007400304e6010465840040c5034104a5542d840b01d50910901303020b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134089055 1250 134087805 134087809
    0x6060804060222090b030708010e060414120d0e0f0604080d0b0f060304062c06061507020a0b18010201020403050a08031b0301090b0f10090b090a09020309030a0905031207020f0d02 79
    0x22030160f000b041320b10750b5100c0c943d6070b0b4102800382d0b101a000721b80090100d00c480e40d040b0703991501c004101030007251381001c4046a0720300520904d500703c1249000c15407202c1c1c0440c0d0071002820040341c800e4407441503000300a00440d000c50325900c5690000009800c0c00c0520070300c007001d0b1100004569100c2c00d0141c01f4009a95000c000e903014502070000018245c1000d000c4201501c41c1e0240020111584607100101a40000c2e0896225005071400384040000b80500c031070a0152000007584030441c01d202290040079640503140410040f4048240010900c0059080b4031036070101400907000030f100300011031407850045801c075128524401d24000244884213068100781c1040c040d0540315011880e0070f180610f0b0000b1240720840b6079420329440840d01810300c1c140c0d4410110301650204030780e801c0ba0344410400c0002e21051105543da46808131502d80c40798800800d0202041d0700310404150350a0003d602541c0c0d44001007010300d040d42c680c081055000382d0030100d50f4000c4104405000503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134090305 1250 134089055 134089117
    0x170d02030115180b031609051201050402100c0c0b03070203070210020609150c03060411090409031112040605030a050c0d090302010c120507050702040504020d0501090f15060608040602 81
    0x82104403580d160b40c1408600c024034803002010b10304040700f040802403003a4001c19049a030403025100880c0c0c0e56121900041d40c000308542c0c40039038000070100b0308080d07111042d0015407082d4800c6820507041e00b01d005050fa04281005005841400d01e504c09014a040c090000c6802c07451900403207040006c207900151600441d9000000181c2000051119040381001420384d803540812007620369140481d400312903400300412152040751210448031050f5007500889461410183c4188248841824081e20700d141ca200440410b10401d007510444008840580301603a08954900d407440e2070341403c410140002510b81e0780707010420414042011103d2140da00480e110703800201d076040d40c40700003074025030000060200603030a040810001075803000407600c2950341148c00084079142c074004203d0700031240c1401092503181c00302d180244000100008238075480b400f92100030f0740d030b070000300c03000d171400c6200d81d01c003203001c84001c00d00040807a00504a4140e00c03828813403007486d02610444c1c2c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134091555 1250 134090305 134090309
    0x40b15030c070303050109020f18010309061a090901020c1e0c03010c0333060f090b0a170c0c490311090f01031d0307030302031e060a03170d020301 65
    0x420880011180c2c1095014000c80e801851180000c50a00c0c0000c04003000c14840d804500e8078140c103002d1004441c2e806644040840d0f070304030804004103801c0090380c0400c9001c848055100c0d5000b500020600f02c014001c07103202107200d502a02003030b0324400e02e00140e07201c00780480140303010b10070114000352024401c0c148881210307640800d000380b500003180404801c5150910b01070000c0034840c3c114210340030511003107581a02e882400a43c0300e240403641140703903400190143c90005101c000c0c659008401f43c102c0c0520881d0856140c81d5050684564031894110783e0b0160000c09240c0c2d03c0c1030520000d180840c0100b9078403074400c6040311024803d098044024005143c1c3c1c8150008240ea152058800000340206424900b817503103000a00c004449103000c2c0d04158444580584402d550850040401c100d1000c99450360460300e0b02401a4004841003a0450001198510742954903034100c0e0046401400c9403828505544a188040b2485503409a40034810041c20584a210f4801180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134092805 1250 134091555 134091571
    0x1103030c10021908060114090105040902070c08010507090e0f15040203070c0b06010207081011070f05060103030e100e090a0b030703080d060f060816030906090b160201021602040b1503 81
    0x10f81c0e04601e41081160801c2c2009007020401143c0c200405030340c014040d00703440e60604003001c4c0c5070050000101e446126942011521300d00101e00c40041014030440304050301d041c403000f8416555400800c4072250381c2031040881c120b46e01c00100f6013410340c090303100e07410040f6007006c22205103082c0c02180c00d9034800d80e01040050010703d1600240452900c406800031030034400313072007042c1c40c140c42c0c0c80d40d070707c4604800484e803030382c80780c8040d003c00b0140f0131100c00c16401200b01284d88401c0c00d016440e00400d200c00d401185007110b00c1d962500d00100101140c0500340c8a00078182e030680103204e0b5009008240c00100c542c3d607068a07140d0740c0c2c20082900207600ca58850b540c2d0341c1103000351034241c40307140d440b8003c2100b507207e041c403803103801007149a07122410f0002c0203654170501c04218050038400c0d030043c00f82c928000da000d0030302c408641102d01c0b0305c0e860041d28102e0591340e40100c0c00c074800c900846044001100c194001490a908100c41d00c2400a242042881240c05d00d0f1b00d16500a50740e041d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134094055 1250 134092805 134092807
    0x130b040b04020715060501052a030c06090d02010f02040302010c0303090c09110702031507090e09150106050403051e0303070e0303070b011d07031b03020a030e07060207081005131103030c1002 84
    0x2604200d04d0141714080c0c5028a00f140c240503441c071001030322003a9226280041c82c0310791845100498100142ea0006002504507625803c21172003061301c1e01c00c0002004010350802882100c2c50845d40201d80441e0f071b060b503da071102506510110010719003c00e0448841d90354410000e41c0c140ca5001d480c0124003504421503940300e40e03204051400d45504020360301d602d00801080750481e0024160f000325100c01400808a0740d501000c6801c2c03120782c10000c100511402c001048140d07111001d131059911643c00c0750b144030720804102107643e400c2c49008a10758170810016a52521501568101d440c014044a0600030b180e036440d41184800d030403220551290064030a0b00d4030000030740c00c3d0411402d0908001203490402d0030b95031101c060021009054001507402d0050740300f44d1140c104840c001c42981d4485031650340c02501c1c0c00052049540c148a078949007141c03d140e0740700e09400f609808500d4450312019964020200b8110b1202f035905010a020507040300c0d0b000d1054400130740280c3c2c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134095305 1250 134094055 134094083
    0x19110406120b1309080706061d010512100f020405031207060b0d08120709090c02070e1b04030f030203040b1206090c03040b070e0a0518040b010b09130b040b040207 72
    0x306051108074903015018104482d040300c98a4080340c200700e0b40700441c0003041076001c03814601410f200c1c0b131000604440ca8001c001456484030502c0c0c0660780603400031450705999580400075500140498030080b03800c00071020000003640c0d84041240da8000502600303042e078860000381401030764555840022400200181040700a1103405e1b40c2078030440340c0c1c4401d1425510fa41c22a80501901811215040e00c04035945902481c503c0c0002c069450060100d89261000203403905028401c0e0f403d6250414041421100d6000d44335611003101c0d0116070405240d51101d20391004e1809068055000800000c02d9440704540100150710140c0039101240c00c00e0000c0c4203a0074401000d141080206106000000d03407507001c03040c0c03c4015494507004111850001600750305055000301c0d80006884003842c000840039400c5c91046000b451400070f030b682d0300e880d8008a0b103c0c10745019446a41d90f00246d140750f21340c0d4054004190040d0000032951440004902242d100300c0d410b5a11104030320003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134096555 1250 134095305 134095307
    0x219060b0a051f0c020f04020d0e0d0e150f070b010e011a0f0403140c03060109150509010b03010b030a060f06111c0801150309081207020d050309030304080319110406 73
    0x301038010581a01c0c042d0001032072490382c403080d40103120f18604111800201409664403099801540a4010300456983d150200f01100a0500c00500f5020740219840e14182034002e030000f10081d4000f4250010f4044100d07900111a40000f90008580f10180030000101d003d07009207602800030080c1102a03035043c403131500c00d034202880b003080c82c004042111000030418001524100e036071064070000081440c54100b4181603600300d9113a00b51080b540001303000601343c0c0140c210703941100c0900140c0c42d180c1c1c051040e0000c0c2406040f0f900c1c082040104090131100004650120f9485000502c59403500d921000c001a81e6118800040e01003200c004000014094104040c21248405c90030b1034902c407001e40800414030505550b4643c10b14442c3c0c010340240c0103184040d500200b541c1d615a041003400842e01c10a54140c4010301c9051070550310340c0d0281d000c44c0e02079000d410003181160b407556580e03070b4268402000d4444403941c100c4202e040b0705143c000d04004a900c900502c1e145e80c14240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134097805 1250 134096555 134096569
    0x1403060903030411060d0b031c0e0d1101050919030503120a18140115090f05090703030507080a09170708010f062105011104080313090b03060f070219060b 68
    0x221800c540e8108009202c001003141d591144245000c2e42d8a94803440e18882c500000c0000000c1940c00d4000c00800d580240190011411800500c2d201c2112541c00403040c004040c8036201e00515001241c1501117442d80594090000341030000d00342e40e8005078001480c03c6d09910b55100300d41d0b5038004034480200c10181c0180c5980000d820381c00f04054225042e81d1040b06c0045213010f05194029400c50100d0f1900303412030820003403400c4090f0415942c6980f04001840700900031000d413443c00010409400010030703c0000ca9030981d071603e00740426511000e80a40c0441149024072102c0f03440080c0c044c0905105001b0b0b003401c54090221140792186890968a41c0341e41c491405280c0031051000e010403107901e189900104840007440c005078a400b0340101031482d601148544080380000b41104008028100d4024a005a4200a40d0303400b0107010b0f100071000155040d00b0210010b1203c4001d8200280e00002c02d01c12200d003c404a109400b10b01d42d4603206680c520307180c0401c00054100a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134099055 1250 134097805 134097811
    0x3090301050a0c0804030c0c08011a120c0105070615030c1710050709181410030c050f1503070909020c0106060201060f06141608040905040618020f0d02011107140306 73
    0x450306003e2100d0891000b0501400240020107010b40c00403603c040c030030f4003603003000a0b10521000700300c01485102c1e00e60780c810f42c071040d81d44940c024810749005880301103260480c0140686565041c14160744d25034002c1d1041800c219546a03070030304000042a642c684e241c0042156001c0040003040c00d41f640c81c2800022690140010308003400d0010450b4805118400c5442c6805e201b0855465028400c0280c146801540000010201402070070140b038001031088a2003040c507405155525020b010201445a040944c00078840001a01c8402c00c44002c5512000e9840c2c003c441e5500d40061f030007260800300310503405a64903413051001680911aa8025025600c100009940ba01c10001e008203940190154244408036201c055503040305080c031030069100c400951a540c035a1600710080200301e5084d164141011105d0300c044040101007440c2d550041e14483c2c4158402c800e1081440181c88101d04003d07000070030510000c01400f001c809010070b070400c0c90401c41c4003801c1501c5d00d4005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134100305 1250 134099055 134099071
    0x160b04110f030c03030d0e100c020f15070206010504020d0e0a0308340e1c0305030a1a0a031101300c0f0203121003062c03040e060d1b080309030105 65
    0x403c207004540d03900081540d507071101090340800c402003030f150780a0034001c0890f1040001c80c181b2000610980c0c02141800b20a081e440445640c0d2066180d100b400103029106080983c00c10300040c491400d16400038032408650703040c0825003103005400d203841e04407801070a40000d0310344414042114803030002141030102c103001040d5502c2c800000c503142d0105425402c1305020401965140903120404d5820710142c9064548450041c1c60401421517841185c80310991440e181440340c00710000d11000130f10410103407117020300b01e0a651351181d075078025811041c1072041c1e03a141050314011501142c50300301a100755520080ba02501c0f49003c2c0c0d082001d507d004c2c000a00715608900780d0001c140c680c040c5908100c0ca21035194000e54503864007881d040039045a00b1304400301744000080c06042d10000160202642d0b00703400c4111241c481c0102d0080c1074040c4400b8010402c0342c43d0140011030b0a074050480884005201002e00120010326440840681c0000c2410003440c0340a110345a8402c0603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 134101555 1250 134100305 134100313
    0x8070302010c0f093b010f14010219140607030c09060f0c06110c070b1209150a020f09060a0305060f0a050a0608270f0c04060312030c0c0209090109140114010b160b04110f03 76
    0x3102c00080d4841cbc00b000d180400d8450000c440405002e0703850140800c1810786003d50b030290070703c120000c0c040c0c0070500d4101c0c00701d01480000030300703944281d00c0014210019558030401c008079981e00c4018010080b15003120348411311060b182c104d01808444000c16407210030a503030700c0780094000c0022500425034509034210305c00b1807031902502c1b1141c0b64800418400140c0d58500010603807540e00907082c020b07411640100300e00c407a50b50958030460151904417051090140d01c0c1c020400d62102074010785403c189006010000075004010b4a9001400030001d40352a0509112018a2840b500d4041240d98041040c1c44502d20342401805401c4800351070070b01c6001c2c11a1510f41d400f0319030441c07420425640396010b042c00d45c481c4040c0a001c40d80109411460f09052000b14040d00e10f44205942c40300d250705094106d90014403d80c8035407a00d507040c1010903868a4141030550b008005250150301c5c00307040000014404038040c5105a220300031081041d5842c1051000780c41d600782c0001d0003030784 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 134102805 1250 134101555 134101589
    0xf061509170706110f0610090e0a1101050d14041b0803030606040b0d020913020a1d0a0909030908030c01021201140312090d05060408070302010c0f093b010f 69
    0x30300880e000d0b058920509191070020000d5203000e14285511030103900d00d00444042c4840d2141c031207070240881c0c0810300140b0200f00034462880d101c100f41500104010a03c9019102950040c0040e00c60042080f80004045e040005c10034201c40044500321080b0484400c101c60a407076181800c00905080c0c0015420740c6400004550103100390b000d0421701550104070032460180035011204401d00180c01c403042030802c121a04040d42083d004c12001c070b60b40514400c10a18400500d50704a80000d002c10365032460101460024040317035030203804000b507501c40442d0041007000200346140c1c908000507501e28000340c02030700c01d00301a04161034840c150070900342c076641d00140d0704100c800d160106960341d0020b203001960000b00e54500401d40d0050360104418003a00001820101d03000303400031302c4801d460708003c503130b4000f010510703402040e04c8001c00e2250702061030b801c407031a0032400d903d42c45420780d942d00180070790f1182607503c0d42039039030a00500100c41c2801481d4000d041045040011507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 134104055 1250 134102805 134102849
    0x70206041104021e07140606010c0308060907030204030b100602070510120506011b11090601030b0a060509010c0609050d09060906021203100312050a0e0603010e01090b01030f061509 80
    0x26091000c075520841d00490740480d154a00c0c180d402d1002d031951070f51595422985801d60030b02c1907451001d60540905000201694064103454071010781c10350340c00ca032a40d20002040716070311014010800f050760a003c00302c000754011880900403128107081141081c5402d074002d107131074680e80180d40102c8090f000381000a0308401d866504070f01c44240801c0d250b41e001c0049800000d484048440d594141d150710701800800300b07452845820903108504555501001075003900d4100c00329540008419800304001ca120b10003518005034140341c40c08962215845540030340314110800d0325260070000310424100c0e00111444014100c80c288600700c00e20300078020351214490380c21031551150000018000d1185180d411015580c424441c0c25801c00003400280590004583c1c0808540628043c002a1410a083d64100d40d00e00502034003a81c01d01100b0303c045c0000502c583e05140c1c440550450600b010301501e4040e220308601c41010a40300701005050104a900c0b100070202c880054003008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 134105305 1250 134104055 134104073
    0xf05040b09041e021c0c170706080c120c040501020d18140a0902030108030a08180a11220203070e0a0e0708040503040f0e06041d0d031524030507020604 67
    0x70940203040c1e030041c8059001c503078007600200704009512031500311001c62421941a1520f1400d802403054030001a2150311441f490110014100d0f420b0b44480c0041102d00d119400d4164401c80744484c40741080c0007810b903920300d640185c40d04041c00700045028403807940d0400c0421145038540c80c00a41d0220810fa8003040504c0d00d0180001d01c00508820512940f254068030004218003a8115569a500c0d42032a45981247c07236903200042d95100803c681341003c002c210444250300016000f1000c1a6640810001c5e02c0690b8640200c100403420f6081d02c0b400e540030011407440400580c2c0c038501100010800640100c07458801c508000d0f050041e0000841603580c040c2207814566040d03140c0e070030401d245010315489a004d1a01c03941c0003140c020212182280a038000303440134410103496402c0b11003e0905903401c2006ca501c0340000c041c031188640c100200052440034105203040e100c501c0648000c840885031079620102d00800711416515101e585e51010161000c4e101c1800c0c1961400c420f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 134106555 1250 134105305 134105311
    0x80a080702012703080d02040806040f02010306050d120f1413080607050c03030402060a200a120c11300303041707020105180307090c0c05070803030105280905100f05040b09 76
    0x400000c41c5036113031b03400503604032009003690004940d0203107424602200020088041203001900b00100000c0600b414642020f00720b500183d2103c041592030012902c0700c98001c0722904200800c0040c9000001c020001c00c000154a1440d003805401d0031810f0b03141c19400b0b00444108a02040020007040c001b00541f074000754100c0741c03c0d545601444007140c080007021680c00800f080121812242d5500180c916000c0d84554803285503005c50850513104031071003a00203031200d030000c0308000807480d0403003200f62510800c180c8ca0f8241c4141080400032001000e94040c520380c400400d04c003d000751108465480820108941d02d040d13001d600090160051884060100e10203006400242e5410b00000002d040d15450411444180c50001000d41c1c2c0700e00b509031054050310401144141010003142d05881003e004800f080040001300182e500d03c120b2143c480801c9042d0100b00e0190300d0103054000c0c0340000040c64000d0900500e51100111a40202d1245140c00d045803415164440131541c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 134107805 1250 134106555 134106563
    0x302070b0414010311071b0305010e0102030601080103062f1201050f03070e0c070f0804051801080619060810021c06061b020609090403050a030c0c020603010b070c080a080702012703 80
    0x80c200c1760581e8015450140c181c1c010640d1040300c40040f20754403120825404c0313038001c00082c0300201c0301500c01800c078801929070078000f07a5002c0051020502640104150501c040c14650407201c00070700c00c540307080200c0120440a5000103800c8010b92015a101d405060103c400c038510180d41c3c000240d4420f400d100d280700824000000400f1082010103449a06401c1501402403030550f01c0e0103041c40e0300c2805458412802014582000d402643d2924142c8440f0401000a610b990084085600208070a1502940c65a501060b100f1052001001d50000500050b80f01c00d41c040b4288400c44248038000100c0f4039100c000c00a05600ca00410302d04090f010246c0d042c6201400866080e00c40d0403903280e0031401d02e100740002c041d0300000400b41c03060181d40400c40d17140d40c0030040315400400f1300e02a500c0304003800188503501440c0d0080016030310403150140d0440c4d80304119401e0107140c61050755540e4011030301505551f00200b02c0621403440141c001e0003001202034000d21244103000283c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 134109055 1250 134107805 134107811
    0x50103060e010b0304060509030c10060e0117101a030316050d020a0809010507020105190e190b07111804150501060e0d060e03160b04061b0f0806030106031505040302070b04140103 79
    0xc1008d681807049880d0701040710306680c03d02480302c150b0000342c0a544902410900d264000283d442d01d000000c40a0700d2581d4090031116102151140180074994a109120240c401844149640c10002841442098207a0500540c4242030a500344601017200d40c1c19508101d0448002802c09000c44011100c00d08086884c0c80c0103000403030340b80c024409038440e0500408400b500c0a81c0255034200f25860072a0000400d0281e06220136014845224100702c0860501c81013000960542030009094401b61504410400003040880c100d2000d4034103441550f41c02180544400c5c09010f818090400d1303062120f451015003012805022601d9409484982d4903801180d00d08002d00c11100001da80c0d88903400141031030700b0100d0708124265070071135100b454141d40204c45803698070070519001854844c4600709200e0346c0250741342c0c54004d00d036541c03555840768040700050b96011410150000c9100c0081c080c60030b80340c080e142613065013114200d01c805000811450070703401492500740c0001e00c0d000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 134110305 1250 134109055 134109061
    0x40806091c08040f230609010e07080a0602030a090203060c1905070c050913051b0112200304050a020d060b0f030a1e0507050301050903120a060f090b06070b0403050301050103060e010b03040605 85
    0x5c14181e00c4072803c68082c0c110340c6a06a042100c00603a50707005d11207450080050f0703c0d100205a0340c0b002c40f813041c0b86941d0005281240412095806168083c203c888003050fa0901030b80086d0034240102c581c0f05515202003840680301149002d04110382420303083c001d03c3c0260343e0702c1c0c4030381c0b900061040c240310745062000070300500c00340003030743e0f0310240e0107802c4401c5a42440f401c290300035907242e01c00340040c1d00e103e4015580750590103072984002c220380003640d1558601c1409081a40010019280351140020440040c0c603a10384908469007e0040000e1580b072480800090b0b41e030004141d84254410042080890344002810540c0206000b20b2030048a8500d002400c1c510f10790f0140358154070b00030170490000004002400c5100c1c017400c0c0302c40c95a46805503101114400e000748070300f04d00829801d0000075203643c086080040000d20107030502600d81d490007842d02c411030741180082c0011004004958050203400d02030200d041180d00250b04001c045107890000034409401a5128804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 134111555 1250 134110305 134110313
    0x1031a010b0706020307031803080610091a0a11160611030a020c090603211905040609030204110d05150306130203030f07030e06070b090606060a021c14040806091c08040f 75
    0x250441c1c541c0f80c0016000555235060103031000d801110014000e19400c1140703001244141040000e03a00301007104000d00030f0511724000c041e0400184c0c08140305d00301c00d40340c41d0f40300c007080f00380320010140e008914014140132008090a007154000e0345a90b20900612980940101d00c0a030325030340071381d4881c1a5a0b07404000900d003000503440300d6460f9030144010703911a60b140380100038009102020f104034550000048071a071040388900c200003050b100041c0300520b06500000307030317411160307403202d0400707060075040d030100c0c0c40070307141c081d800c42e0031500c0d400643c14144161580106c00f1800780351102d20b141c002c00d031170707200314100405001000120541014010960f82061910140500f500d03824240f03442c801d0240203990303210291085000007046440c059040303d18200b01030340a482d03000011440c20302692480440c120500254400400100c00300e0005400140703281d1000302014100075214504041d0858402000341c400c40005840035034011071626003296000885e42c62007031903428 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 134112805 1250 134111555 134111561
    0x50307021905100512130b0403121506030c0e10020d1808060f0411100e130608030a0917010c17041103010207031101050609040201120e0a02120601031a010b070602030703 75
    0x340d8000f01c0e006468034081e5104001d803282000e00304a0302c8503511101c0b0b60740710361004500000d040b08140d400090000c0c0c4035242400d50182909030100d900d801c1080520503001660b0400e43c0000d640c0c071040f180c4607610000546407104261070000c402030030f00100a44035104051800240100900603480550580c000d8400500040e410703501c0905004030840608042500c05403000c180e8840061564502814510070408054440001056814081c81040700001980f20141541d43c0000660003100b40006c0c800701c100c5588407501d950030303c1d10000803010040c500c40d03881d0b89000c144881043d0028110201340300c4443d121040c6994510300b913462039544000c071940550000c9507c40426030420f04860f10892100c009002ca550780c1c1c4140441c614045030081d00040700c84502046d15085948a004c00105000503107072842c03400c2d00490207542e580002500a548500010010300c1a2001c524a07103022080c0c2d04242549442880a00c0c0c4c003030494050304007940040400c52050080d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 134114055 1250 134112805 134112809
    0x30a0203030301080c0108180c0d020117040506072a0807021201110319022b06030b0405030c060f070c03120f051e06010f1211070503030c030703060603090503070219 73
    0x20200e0b9540e603190b00125071030f003420300039a50114040c1008142c0c1b291420480711480e06100c401421031041d03440c1048a8601480300a07410301880b0003500c450500703548072140c4a80e020b8001080c860904031401450040c0c075201300c9009042c0ca0494a018103242e41903443c0003600450300c6900c80c0c080c0c0c000078203640b803c009150155031900030110b0a030280100554402d9000c3c1241c0380c004007000000b00d00b40d01c10701c0c0100010f240c844140c0107142c4011208500c06e210341c2c000010f5403a8403561500c1c40c2080c1520141d840b41d0000c06c00e5001d0a10030810b5661002c00ca188140041c1000719011f0a8a4603d82e03009060107010088184100c503030390b014014031113a1000c18021424840d0340705000800e013841d81403221001d0400203400354090700e0941c840a0180c0e550241410054915000230302a140241490781130070040000805d108102860040c0c032710325212a0740c0d042c5104050210340c12a8405e00506060189960201c2d9010041c1d494550301590700d400c0400054181c181c07241916 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 134115305 1250 134114055 134114059
    0x204020c190606090207020112090501020910030f0b0a0305100203190c110c04060f03060b030a0b1008070503070302060711150a05070c170309060a0507061a03150f01090209030a02 79
    0x507184100c480314030280e000c0100c500910b800c0044944640e610010380c8244030019002c9203801d0080d520103041a440009000e0081d000142000315103400a100c00d1104089000001d84400804242c1c116520601140380822103200e40603514558401b0b44980c0490b0034803050941c048000741c018603d000c1a49100056850100250000000d0141856462130580c4009105441e501030003410640b00e1072090720b1000c104544400c0c9075555031005851f00896180c0c04d401580701c1800090100d6044500840d0990311000c00c01e070400002e1480c11460740d004a100780e0008000700302580301e020448003003d41152100c0c0b15949110f01044401403040b048034005c1100191a12546500c900039241142c4030740c60010b003550f6102c2049100c50310741d0483c803c254004000007256454981d00801101d1103d023841810910703240c5882c021150103c10450594910040da080c080ca814041041070202079140301540d414045808a08000140141503685a00080b144c07200d6508111001a4941c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 134116555 1250 134115305 134115313
    0xa0e0c060c07151214010f0522090f0203060c1603080a0e06040309090c05040807061107031b06080105010206090a0b07020a05030d0c0905010923012601210317040204020c 75
    0x1103c80c00034203440105407402006440c00a604215200d1400454100c409040c03540c486075003084c0030495044100303144244007410080c0c010003941014010141018051400015030075458010b142c1440c00040c0700388500c20080201455010000824141d01f5400d0314122403250350f2107038500e000f4010381400100a100381c000700170825510107500002d42d82c104c4018040c10412000a403403d01a501501c14150083c6c84240f007454801d04907100c0c401d1501045a0001341d07070341c5402c0c60829040034070b10a94242082c05100150304007920300c0c0140030070310082499240c11060291101508400144150741c030a0100303ca03070307108024140700300340c110003079a0352002d14020010003440d16282c01404507a010b280040c0c03942c060350f01c04003202c180b40303041a20008400d008201c402121086c0e0341c14850307010581407000681d0340c1700c00510b1100602a404e40d506154041c07055600e2480e140b070003182030341d405400080e03002d01361003900d05a00714480c155403264800079019014030302c16955a882 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 134117805 1250 134116555 134116589
    0x604020706090609151103010506031b070606050108070c0b13020a08011a03010e07051305190c0e15040b0f0304081b0601060f1d10031e060603050a0e0c060c07 70
    0x101c41d0f0000003d0342c420840d841c001d55100030f0030002d54a80d403511b0f440110051004020b5410520021540507400b441c8030241140008508052600030000030384034907984503828403e95070041d62562300001a0b04111220030807940d9403409110005100e03051300028810010115168074001c50060041c2c64000d00c440c030007031404400c0d8100e0305488180700c0d60800090900950011546509484c800b410070078040c01d22080002c05000b01404110b084a120b04038449001340a20403000703a84411303595202d1070840e2070100080700d030040f0852480140d04020421070501d2003000c58008500410714070340c89a0311070818087c00c0c083c4644020060f19112041422a400444ca4074141c0da650b40780c0c124400040c81044401c00b60ad0420f8080302c28038542800d8917441c200c1204461511103140214039460340c95808601407d0310080a2202c1c0e4480d042407040a4041c0159a400032015100300084030018006603961070000c010035000e030100091880700300b0401e0080c0c030054410400c2581c2c0c004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 134119055 1250 134117805 134117813
    0x31506050903071d06101e030203010311090c180307090f0b12010e0303060f0619050901020f0f030405010c1a040b24030c06030603100509070305160b04090203060402070609 76
    0x64041000c1c9807003070160f25000b003001030040c400c0e0300f5462800a012000e950b40c40060001510308049a007040c000e00943d07a509001e00200100c1941455035000f5071607514510f00310900c503940108941c8a2007402041107014021441950800b0840c02020b098846400c404203040008542188214504144800c00940099004242101020f46809503801890741e0603500700c500f4000c020702c4a801c1000801d41600c2d00e0200742034540390043c145071908030080c000403c12610520102c01084003c070743c603501c1d580c0500c5041c21071900740014100425130116030baa1641b003a40242814800c0ba964400700b440071600b1080d945443c40c20762203065060034249030f64101800c0f910003803034100c800c0381025a600100b0102c001118042d0040010030310031400c2081c9a00010621034152256000410795401c040c02440d019040a0000d40f1500d8154240b060601100da200d900c2440c03400501045000c012000326011201d906c43d005880b6112440040c000c0c0c41090f84c003418070b03810061010140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 134120305 1250 134119055 134119057
    0x90d050a0e130605100c030903060c03230a050c0f0d0e0c0607060501030c24080402011b06150905070912051203090c01080a05060303040b070c0f06050301081501050d110103150605 79
    0x40e131000c4915800742c4214000445025100c180d0060001c0c0005504000182c0340d074100f20300c2c5d000d40341008559141081c6e40c81410039100780485013111304074024012410810301c52250030100c1902c0c6a4a0640c07011248080352007070300000e0301a035668030200c0c03644034070034000c0080b980c800401035aa41d00c000d0030100c001d45000e0005580701d040614002820700c01403800758a08031800d80040034038960714402650003010003403007a81405208856000052220440a007803244203c50000e44066408000c00d003d0f1815005035170014603003014000c040350080c0010048400611b0501e0805460380b0b000e6003040395180c0c103418004004005d00c4602c4e840030650000400e0282d82d0340f4021f40e10746101405a403016280036405400410042c403061014800030714803903007d0550104484e96800000d400300010703600c09000500e000c00188038040c01841380c804000041400408154148400101901c402c0a0300600c00300d0481c0012800364001c0d002448403002d1031480070215956440c002d0a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 134121555 1250 134120305 134120309
    0xc2103010311030106050a0b031f120b01090903090e070e0303040303030203070f0207030305031909021003021c06143c031e03030c070c09020406051b06090d050a0e1306 74
    0x401502c070401c60b4940c1014400d113000c44000514141ea041d107421440900c50b803026200d00b10240c0020f04188040e40d00400d464014543e1400c100400c0f441800c1216600006811000340e1a00300300700100840e503c8000501a903045107480691501c03518002d550200400c800c580d01404041400410b058040e80690f00c40c0e06191203804001481d100126141e003c2400000c4c0031440a2000c25024101e0101d00c981c101811600001c0c03035000b64002522420301c155402000135000503810485200114852400000c0490107220060520480400000380720074000d002e10340150b000c56200740b08081d5844800308100001d0840d444000c1044c09140480541901034402c1c000c0c510b4030f2980b20307072050440c0d10286010b5411611180c40d600100d034050300c0f0582c0c03840d881704070110f1859502d00c0104010061511900e0352954040c031420f91044000441006030740110303080041d42c51020440c41149040d501d455503440003141c0050711244c400c0d81031980c00031003441410071481c41650100d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 134122805 1250 134121555 134121563
    0x4030503040c0b13090b010504090207121b1e1a04030201050702060108210304020f10050d1503030e041122090509030a02100207060902090a020d0509030910050c21030103 75
    0x290480e01c3c0c0b001c1108600c2070034801d10303408190b010304111104081c1d2040c0e226003014034049151035035429403503042c0c2c1c010800c1a1000054030140060241d0040989000000d2503c0000300390f40d055212a008000381d0302164002c0358480e00c0e120b0400c04100c000c11100303480b28070030b9001e6051a042c001c0c0200340844003140940320f03400021450050004c1c0300e000429000700841c524035084240074020350001341049810030030545041c01c495070b5404000c0951030142e41c4891302d4000a62200c0e044c0da0381c140740840c0c6807180c1401480401d0b07201d07002e0000240281c0f4007142c0c00c2c800c2c00082c0c03c244550f807401c540740f4145035101190641e15105c464219071f55184144426250b04407425101e06c90a07500d00c0c09a8007010340c41340c5410264014080715801400300081050b072980124800a10449052a4070740c0c0c0000d45403042e00035441481e401916000c021800c1c00d40c040049800700031444076280034030030302146540301800308002d00044030080501c50200c2d0440c450380d48240d0740081c0400c1b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 134124055 1250 134122805 134122823
    0xc020d0f12140d0905070b0309100506060a0906031814010e0c04050f0f040609060515190b03060103090c0803070807050601060e060418151403010c0206060901031b08060403050304 79
    0x180c40920600e5400603002544960301d241c03d150240340402404100011280c1d0702983e100001d507000c854000c0d600c41c00403200038200c0344004c0300701c11046403c000e001d41d206c1c5c1ca0038040b40038155401181a01944c80780d06002030080d5050f410080c0b00103c03481d00505405001c41c0c2030382c030b022040d041a80c06848450440c1c030012034610400c01907800c100d80240845d407220b400102c01c042c0d5402d01c1c0d501b003401800000b81c1074019454180640d107040700c3c101b02d103c450010f454000e0404030345c00b801c00a09aa15192664209001700300d45c1e21014240354101500c404400e800e012016541100070030b265011a07075245418600030449410000098849018040000800302d004806181c01c020008208030300e01030404601d4011000050b415001c510355030401145a001031039030000141c001000c8000032400100700300350955071103102040454004c0c0e0144282c80c1c458001c01419281e0004003025800d401c400742203c00704859014010f1403041a050005243d0400002c5000d28001c3c0c00d91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 134125305 1250 134124055 134124083
    0x414031903021c0e0d060b060c060a0b0a06030c140307030b0303030f0f130804050d0c03021206010503011b1d03011803050c01060504050c07020f0a080304081006081f0c0c020d0f 78
    0x10b4402c841030044c0c150700300b200544600b0000f0501c0c3c4c03240c2c03183d0a004001900b04041d15400d2072404508445201040da43c50444500510b00740640100800c0b26103801d00c1062010b081c020b203201402d00d40f90504980c08808601800d0107500400d00c00440038003145d0f103d00d094420500050015280c04000344100c80c08a662009191101d040c240d4006821600d000d280105100d4054400003094404034495900400180d4903443350f5604402860001e20305541005d04040c01c440c03400248804000c181c44509040d2a00845001030049001c00d525048414190200380901034458075041030700305240a030410103800070080c00c0200c200390002c000709a2214284811100c1c2690301c0794081c501844040010300c0c00c5069922050f2000c0c16002105695a4034280346070850b03041140382d6003000a50102c04100ca210701c1c0c008090140003001c0080c0d81d0303070b4100d8510301d4158162400355280c0041c181114000c0400180342503000d00502c1d07004109003094030184440c00c408032084802d1070b540b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 134126555 1250 134125305 134125307
    0xe0f19140607081608120c030405061f0302090402040f060b0307110a0b01050d02040f1e1a060f13050d1208070201060608010b0c1504030203040e0702030309030414031903021c 77
    0x107480c01980d000702494981815240e50509601d644d00040b2003426040040310000300350402daa5000b1200d004101d9100c0c00c0c186802410504001d05400000010a40710080710000c42241401c9036019254001141c881e80082000703032002c0089012400c0c00c0c60000140000c0450082d0700c10621a44d40d403800450522900b1b45601034001c024000d40000c800500245c0740c000100310071184000c2c80000c1c455030500203031040c2d0b01004440e1b800610705003040301c5690b8560082d0403103110f01c90b01500d03d071502800080c01d98000c4041c50040c8640100c1d960650440540502c00500002443c0e42000a2146841d41106181d000c1000c009041e200200e02194014007902041da0483d840741d01c51a03003000410b01c4640c0140304c548000340f01c0c4110000d88001c4d4005190300842c0644d01842e500e90078089071550808015020804650080040141c0c5240200954096946802503908903040110010b4601402070581c408000f504031b0911003050303000540301000c408201c0400c9228020408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 134127805 1250 134126555 134126557
    0x3041b0806010b0307050a050c060702071404050108060403030914010e2407120b03010609060e0a050105010203040b03061905190602070504200c01060323061503030a0e0f191406 78
    0x1040303e0341c041c02800440c0c3c0860040010f040015140d240490a04004110940c6000015617400e0003503088504280014180c4a4440c0505241070310301b48015454010038a03a42c000090010f800c140e40e41076a00d0800030742e003000d101c00d0078414009104064030681d1075900c44c411070303d40060768245511142d103c010352003100c91003003907141c45031440c01c01c07442c1c0c0c40d0026020b00000a80d05558540001c1062203080c81220003070206c00f20301e05694902504035004031401a0041815035200b07210070000148003e0441360b00200c152007800319603820f0b020410803100700d50400f0b51301c49842540c2101c02205421000101e6613640d003203a042a0365001440100c40b10b0b02c0e00c6104040c448000c05a495a5903402001003d070400000200144e494645546003800c0c21820744c1d05030100e810b84112502c00b0001e894004001821003101c00c0c0700f85001a650b4030400c145030052041d443c0d00d40324595250f00c00846950406032901c0d280900c9501c1d44164108140900420038a91800200301c90800070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 134129055 1250 134127805 134127809
    0x10b031f031e0501060f08030408010b0402040b07110402041a0a02060f09101a0409030234030f0203070b03182803110708011e0b09040203060a09030e0603041b080601 73
    0x1010880c030402a10031100c11140440003e40300340d1340300c010005216902d1002c010003098500c0182d43c595042c40412825200b06200e03480c41940107000500820020b01d01310340e101a4012903040415002a0128000c0e000d5940501f1041082068030b80007000c0c91402030000318825404d44109585a20609900e0035040d1380e46885a484401e000d80d000806502828802010342c02c80b40c900351011000800355414002c044006802528601e1540303c11420210362107881014000050640c5006480c0d1703811079448043c0c00304002980d518107540b014441c1c4805015945506656460302c4481e2408005840384401d019106611000324001c4410011491078500114403a80340c510381e8030100d642e0441201d20b903405020708280044c04820900c10b641d00c59075014141d030b045c40309000b80e000895400070401d0740102410800c201c016600428250340c070054108000a4044050504461074441c1c0c41449400c0a000024002030022a43c2c05c2100c020b1195203070407180d511040c3e890744808082c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 134130305 1250 134129055 134129063
    0x60509010e07142b030221160809030a0b0123030d08071b0b041109040f020105030a140a1505031504031b020d1a0703060f0909020117010b031f03 64
    0x4100501880c00043d84090082100800d659041d0301d400803411074008211001c94109640c600301c0303804042d014000e2008071142c44818448541d000c00c2a900305218051000b10445113100e8104100712500e0f05440002d04040d046981d52019450445441d039020700982c52418291011100c0c3e001c2d01d07140081c0c81070009406000d0029120342c0c140c41c0c0b044042c01620034410b407085055440442c0b028140c59050150083c2d84050600d03052410300b0104017080180500d02400400001c1080c0024a40d071030b0380e080c640a13903203540d601a0746000701071044205030304100b088103000110140382c01c0804090415420f400d4800d940d0b604240c5c4c0c450402d500d030306079480d01000050100340140450902810382c404000d600380d40319400147c004000d230204440050b442400c046405990200440d030009050408019036810200f180340215500d00c13988200c2500c5140900859108a507801d10f200082300303641106503116285480e030383d00111024030359102002c140200300c001c98040c0740c04903a04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 134131555 1250 134130305 134130313
    0x61e0a030911060c0a0b1b0307020c01031508150901020409020c1c020c1305090c0d050d0e0306010810200a0807030c030524030a021e090901020f030c0a210603060509010e 75
    0x1755036030b51080404020448a000340904032003039602d00d10303c0020b5200310660303800381002902d150300240480b1850840c0200440410b0780a001441c800240034075810024941e1224075a5201c000502a1140f0341204050074004a510707108010002142000b6102031030321150200061801240d45c2d02503800c40c1f43d44410b0208081c00545200d40c005600318002d41c055a2402d2007200101e9410340d0311403c2180e296012000d04054564000001944148220041d00c1c0c1c039450300713804a81d10340c0c04401440a483e1b940c041000000031684a0705038080b2405015500e8607150300c00500000b8041b28840c0103e410075420a4141d0710901c83c0038440c10110340440c215000403d04107010208500d41c0a4251080c4c00c0da01c03000d40d81c0e401414414400d0111810a4041c41d0b81c20f01c101028041d090662a032f0041c40a0102c0000d42801c0d03d911001d00904541c803011030b06d03000c503000000700404c40428003251801c1410604a0f421a60a80b80a01410f01c003586403081d1090807101704200c1c160241e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 134132805 1250 134131555 134131573
    0x14090703020613050a12050d0201050103050303071b0c0b121303020a080307180305031c09020d0b06060d0c2c010c020411070c151106040f02061e0a030911060c 70
    0x18000b406401e0030002c2900440115444001007124969982c2200104c2000c20b01107404010003005a100d00c65164070081c000c0354035599179107a803404043d00040c02e12030403000c416000040ca000c0d400c0a55042201c0703000c02c075951f000800c0103900c002c00b03090442d111040090000d001c1048820500e40d03041e0b0007014502881c1c0c03961030f002d400c013070200703403c00068003c0c04401604110a01003d0360140d00a1a6100302c18130741d82540c2c81c0c400d94164400383c05c110629000d03944807105d00203820381080009801e940c0e0030340026014482d9403080c1200c2c07841c2043d04640e2903031004c1801d4449402c960780a070303400d11401c0c41c0f9030305011100c00c4078001580c4400450050a240d04101c0d618503c13880f185041c0340465540700406070081c2c01560b21600d00c0e40c15200300551100240300e4105004d0701411480c2007907100e020040c130058102a018810000d0407002c6000c40703080c2501340e900300c00700450326141000002400f80c24070340300582d44e52140c484981110301c2d1003011a03c44600385802010301f14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 134134055 1250 134132805 134132809
    0x1209010c0c0c0b0a030b032515080c070f0b090c090f0606030412050d060e090606060f0a0e130501080d020c06040f091a0d05060a0f06050d060218100903061409070302 73
    0x203030002504a0405499042c6e80c483e90701d08005000801d0504101e1014074940b00c051003c0a40180e400118142d8000c0c40d828a041e03000250980c00038007683c1544da0741e210034284030101c082441d030010701e041c024a040203c000c402056201b01030f002251525520345074070398514002041504c0d09070f801401040410009400540c86000242c4030b0f0500b542840d0b6840d262034211091795022031b5000e008413041042428040c011154803902c1103e8690402c0c40943c0702845900400b1002424007910703413000d00084da030f01c11409800780000d203410f004135a181d00d0055103403900316460340c0142c403813501c8440d01480c0c65000d403805c1d0740c020b0003d0424185451080300240030448441c603440350f0b03242e0380c0341c2454a41c0121440ca40f4043c000034513003400c1240310441299142e410a000191810b801404190f54080110501c503400c9178000d600e03610b0700c1c0b139401414441c801e5800d90150458241c0c48915800900b50070403a0b0141c5010010441c2000100701c1c500c0f070840f40e142d4580c00540d4184018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 134135305 1250 134134055 134134057
    0x90908030601050c120313030201050c040b0403150216140f06060306060d0305040306241d04200a09060501031503210504080304060203070c090212060405060d081209010c0c0c0b 78
    0x440d43c00302220742d0200c1105c0c601080d9442610000c80980300801c10380e09143c1c090081c50707000200018441e24040c43c10200c0c649a001d01d01009100041c0340c8010042c0618940580e09140001e10742d40000c21030a1031300c949a0500911505214017810001c00c803009400b1a40364810b0102a028150300d603140f004025203282070550440c2403240034400071010030300f1841030f01100700c11040e01001c0040c0c00c2031842c0c0d0042050b4028251000c400300c1e02d2804403070300c21009401c6a404410760385081d4854014266075110400040c0e00140142e00010f00300f122604164100c07902a01c2c100f000d00c10382c45403184511a10300000c0e1483c00c0c104401c03808a141e0220030400c000841c5400c40c101601c5042003411540103070302681c0144e00c082400020b01860345000b800038004c0400451405a840012b041c0c00b2900a160710310840d501c000095854440c140032801c055404003c090340d84065140c1744280c0a400ea400f03141035844d025a036070030580900440341a050304410184000307440c2001c02c0580e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 134136555 1250 134135305 134135317
    0x3010513080a022b17091507050405030a050a0b100308120a020f030109140709031109060102100603081308070302090c030702070504060303020f0d03110d0f090516080709090803060105 81
    0x7184036065810020550005403400d01502d0821038485060044d60700601c6212034400301e00c0190303021814440340c0380c4c1c006020110710354035903070f2001da503600c404040c0c440d0300941d8049074141c000c017102d01080000120303841202c1481500c95480b01c1d00d4207104090210024040104080d600300a054620502c0d4039215501c019824409440d01e205000b10000d40d410aa202c02e06c91030f1110802e03820031150b001d40961046540c80c00346e40782451031311500009080840c0c40d602800e590008515640d02c24400280051030858003884190fa59160000c03d03503105c2502e0a0708044521004100007a010035903d04594004000c0c1070140c4135140900c0680d40040c02c40e0f0706511400300000307600c0c1c407a40266801140680c014000200305104a00e0800b00c80310264410075140150742030142d40c0d1942a80c102e28000403001541c1c00b101d02d1f40d170f401011b82c01009881c0e44a102a0034001c0d40100d002e00b415070b2550821f8400a66030303a0f4400c3c0645080d554020101441840020055440742d40030b844 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 134137805 1250 134136555 134136557
    0x9011a09042d0c0509060f0d1104020a05120a0c23090907030902030607030506031c02030c0304150908070305030901030504060b0d0605090705010801030b0a1d07080a06050603010513080a 82
    0x10290040c91801d025081008030140101084251010a0007042941c840040c0410394002c041032420380f0000c2d1403525908800c6102385c1e80604604140301414200340d0620384042e02c11035943d8000c80e409006908050041c0306008550b00004110240714007445205c18441d407100101c0701d4180c001c408032100e400d00d03502c0c02c80ba0244400001c1e555030101e0765000e401d16840002d451100c60040c1410030600410b40070605040005001044e1400144150b6601e000300740350300917100200c3d00328298440d02e80691400d00c800310f4041083c0c0b80c024508964034a560711140c02255030361110680701c210310f2001502681050210540319406604100d5001e40f141d00002041450640050340c407078000a0147e4480340d80d007007082050f62042100501810090800303103d6076155950301012914018012540fa60b1180010f000360448050a0728a54031003006407480e068507240c20640d81c3c044010192002c600f0075003c03542606044c803072035001c0e00c81e0980c0e0361410681902c6041d1294407005901c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 134139055 1250 134137805 134137823
    0x8030403061e0c03150b09031506043909030b010b0703050409020a0e0109050d02130e0c03060103031e05090f0409080c0709051603110703030b0a0f0e04060509011a0904 74
    0xc0919401c1c2c4521121040e443d14001180380d00c20319405640041c81c0c010000c40c2100701301c1f0402d01e54001030511020701c4001c405801565074640450040c0c1800d18074456000941030178403003607121800064080d1a9004c61180f04800b91010486086607a80320142045142c44d005210960b4840000d040d018080d00b4000e1070030342e4030030420040781d00c4489090000381d8812541400b41d81e21402003002060200c9440006254680000f030643e1807103c070031088907943d4500e46000c0b08007409a9454628010305030703801c079a03403400c0142c0f888858903039180329018894402c02aa0307002d02c09980904c48050b1000008000d01c40611000345180c1714251813001c800e210310703e016581080510064403162202042da800c1c1081140f8008140103003410606041c0303c94104401c2101060791200341e0180780c0854104507080c0030414281041d003001c2581c4803146000300f00001c019850b0340c01a841980108095a641003210f401c072079892420003040c411040c9600500d1a24900d0389400901400b81c10b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 134140305 1250 134139055 134139101
    0x10507021003020306030f070609061224090e16030206070f0b07020721020603072a060b030f12040605210703060f0e0103020604030803091e0f01150803040306 70
    0x50305160207034064100003900041081001d090500c08034881000301d100428216040c0741000e004040203024400c104044031848060f5485140c00c1644040c0b2301d40e02c112501061485040801d8142d8012034803840e04041c030f00f40002000091045840b00039842c07882030360341160700708003281d885447d00751440c0c003480b070303880c1e010601d415003440c090400c603001801e50a00d050416603550040c0403112465030780002000e00540c9400044a5200c001464041000b1844131849411240202c0305030503505031000244013008081e031700c50003a0303800031002c9070800d00020045c10f54503a2442c1103801c8005051004101070350042005d0400610345400001c00da40500030682404441190b07032400083d201d20b400c02910204804420103441d02081c1c2d02259811500419030510407031000501402e40000081c1708014144803003407011030b134000d10844261910500a50f14088140710410b15403138200c03241d08222580d842c87e01102c8c1200051801c02c1e1654540c60300402031460754010081140b109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 134141555 1250 134140305 134140309
    0x40c0507060f060807050901230315041a090c030a03030b060d0e03070201081b07260a0e09011d06040b01020703080a0f031d0a0f03050405040e010506041103130b040201050702 77
    0x2000c80280e002c0c080022601e207000c000501c1d0015551103240103850b40d00041c821030701030005038a0450803050503003440c5020305012a1401c400202e11002240090080c00704011901a00d0411301c1c409a20042ea540c44103404683c0303925410030003a03456804001c0c0400028040d0700423100d0071200418241c10116003c68850980d85185045078903904002039000840d03800124464000003406138248090b80100901000c42c8200b003005070180180403c070100010000400500f4400d43e29141500c52402d140094070400c41a46060700c90403a02c1c00104022060a08c0107000c02040003085481ea04d804c0c1c03d00c8002d01c40e804040f411401100404004203480c0f0f0004c2180f08030039039949444582e50701006048855101c003071035000c51100001700000500003100c0303905641041111740c0c414164641175889108a5211582150500e907046c0701d00071040d0700091003640103031824020000b0241d200401403000715562200c0c00001440d00e404070344140c00d40c81c0e01a1040c180586040b80c5900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 134142805 1250 134141555 134141561
    0x803070b0415090201143025020d0509030705030a1a24060a030b040f060303020f12041a040902130816290d0614090c0315040c050706 59
    0x21040d40c0000445040c8810880c03a006001c200d8030034418100503820055000a1032650b0400b000444080003094070f42c0007104a103404d000c00d090310b0302d40010040d454110650700b4081150002d81812800c0840c0c0c040c1040c0308801e8003c220305a02502801020354420b6690307800038121550948a9641c01060039202000f0050540f40154041c10700034400480c1c0c00d92400c4018034220800c40c009001d031070605100c018032050354030121001c0b921483e00760402c9009241d1742d034800754082d0400d2141c0303580d0340c5160f11003404d40b4005c5c0d0964283d4040307040b13034558864811464402144003001b00b04503681c002d2408041c80c05a00c2001854161344010170340c20790f04030f40821070302d65501080c01c10080c003042102200304040c544c0c035440c2103880c100992900c1103144190324078100e800180c003c41d09120b4001c440205c0c0c0c4d10f141c100000d81d140e201e20752803401842c040501440101000c50103241d00041520f103e101c49a00da034140405032810b210240005000301000c0c00300a1212900143c9180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 134144055 1250 134142805 134142817
    0x3021e0409050402190602060103060e10110408070b120105061c060902090f030d0e010302090102150a0e1e0c06070c030f050a060f090317090307120203090a090b0f190803 75
    0xc10080b0751818140100a6500107504c5581c80c100303a10b00e010050290082200b0741126048000094a6001c40300b281e41054580030704880b030a407900e40404000101400074009441c95034040b200c0050320340c41209024811510101d0030542e00030010411454601d0084c4140a920715059030002ca00e401d801c400d0701c205070000d149035a00412010b019040c10405d045605804800500d100d42001e04042c000c0030184400d1410141c00064442060b4020403104200e0308000d00715082c5c1c3d2414000307802c001d2009040004c41070145441d20080c0040002c0892081103400d4050881c82403034504000d025030107104122224246042d000011441f000040745081c0e0190300580106116458004201e5083d0180104581e2420201401107980705011502c950f50300030179205540c8901c80410710b18060018000c1c0815414170000d107440b40e02001410140c3c0301910180b0100340c13104900b0301964800e01440303402c0400350901403024a0610406901c803a0790f010050481da80306d0301d44504540c404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 134145305 1250 134144055 134144069
    0x1e07081b01030b01080c0a110c0303040617010504230405010605090a020d051b04050402030414030f1210061d0409140a05120c03040302090711030301060905030d030504030203090103021e04 83
    0x420391000195805024884009009281041a514040c01d0010460003003401e1f03007040210a1000c0c1c0e81c0d05204000c07540c1c289030010210f80e10346969960091800032074a01c4103001005420002030346003842c0c000c111182c140b0004842800002040c00c0390361801c0200140ca0030341d240c2800050548039080050700810b8141005a80d814461800340c0541c0e0001c2c1600c502440c400a007040d2002e0030105850580e442250056034030707202c80c02d09040d071a18400c0000458040002c410700070f102040c00805c85401c0742421110281d48265041039414064480c1102060740054550040343c902c00c0301d0300340c2140050001882c15000d480d8550501c911030003240f5650b0080400e0300038842c00708200c0541d2010324010360703e403818002c00280c03203005900c0024010700100c004140d002d80212000904100c005045a40b40d607982c40f0000c3c08a41248244e501900035841d0800c0c4080c440c0c02070510583d01030300210703d01480d0b100114020343c4076590005102c5070780314804c442e641e000d600500081102d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 134146555 1250 134145305 134145343
    0xa0f03050304020315010f060309111302030f0705030601050702060d1b03020d06090b0f06090a0306050a02090a05010c030e090c040504050a0507180e070507060b030109050f0c010c03021e0708 84
    0x148181341c50900100001c80c8503a00b40001006604c10903081c10003070782c07124580820304103043d240c29908002110a1a6404607841c0710646604845902451080c601100040710603168040c0a603042d20065604d14001071007007204002604151004162441d5041000100309100b01100000d000700d02120100103500003030388800c2202140180e1026140920f4200442c0100c440000c800340a503c01c0c0074010000807900724025500d40200b40010f540010042c802440c2400b041ca00030351000011b41d10480c500c10300404c840d4400c21100c0711060b41526828a02102d03507082004001004201e00b0f02001c2c03c00001c03440b17464a0080a004d140e80d0100490300741447c0c1d8018106400001d0102c2040720700030401c000e0320812802640c1c0100003418542d55680740c2c0e0801c40050108100b0990f0035600f003061120411100003901c41c0350030001d0040d20400e03101c41c4d00448190050303580260050b844682c000150300450480074501c030030414106c1b0500c80e5121031560030712000d01c04496410300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 134147805 1250 134146555 134146561
    0x312040302010605150d11040f06020309010f05040e180f011a03012f090102032104030e191a07060c020706020d080403350a0204170712140a0f030503 66
    0x1809008010142c0412242c17842110307a40b04c90307911503004080601240071b440d0f0420f034500c511a4004c0f00c000e407088403400d011a54840d000a592a406040494009500c0e40d03601c3ca000384c03040381941e05580d500120002551560b222500c0b031600801c07010f213400e00404074003840030002403194082c08078045030f060869141c0302e0704050031a05000741024600e1801102442e000c80ca400b1600c4666454009041c1c0764501070780100c0c40c5000d03034140a15207480f070507a107080046011420522680c030903596070540c0c1c3c441c4000e01c02c01981c3c440c08650315884c9281c09100e42c0c07403110300d040f0f20b00c1d00582d5800d04000c1036881e0b0000b0396080343c01610243c2c2000070305020342c0c0d9052011a280900070306160000d420180c7d4000c00c0d900d01d08400c08402c0004009c45403107208144210780210341c84854001c40e40c00c001c11080000e500c94807a0710311440e441d10b00b80344084c80c042030b00c4023258211401c084800d4441c0d1288590301059441d111947c0c0101c003250b000165090b004a0801806551032030340346d103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 134149055 1250 134147805 134147807
    0xf0613020a1d2403060a0f0507020a020604060c05010b041410060201090302060f0c1603020313090608030f13080109030903120219151e0e1c2a0503120403 68
    0x207a8214102d10500c107034150008060a154158000c0500740040000d40c9a1100c5004404124601213034103004200c140112002540c00c507400d9408070010810454030b40c0d001c141d9480003610700003504803000348020416a802031454072a1140110008104139603640c0010301120b942c2c00300d0040c4441010140b1907030344103048400002e050140020800280181c038040e40c0c9480c0102012103218440c070020b05403038000d20945803441840248003191980a1501030340b00d41182c026806400300150f800070300803865020340c2007141e0310400076524011190f00c6e41e0286510045882c00c005a4020000a01f8042440b407506054003e5881010742c5095103801515111680034507011940040d510700c0036600507402c3c81180c80c1e40261040450102d000b1410040e010116400013001d00101e1401c8003c0c10a800600c102040d040070340305106d41c9421020007000c0c580d0701c20000074030581d10b0611508a00081c0244c0003e031564051a149519030302c0c5071456024110083d080c421070b006020400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 134150305 1250 134149055 134149069
    0x405010902040f0812040e060d06021207081006090314030f040e09070b090306060108040302100c031e0501030c12020a050409060c090f060c0b0a02040e0c130603020301260f061302 79
    0x241c021315010b80841083d83d03250703815038000c500514000d0010107002c105556600011b1204055001000b50345031035001241104181c01115074801058040f030009522a03001d0040c0c2e000d8400326150110b0560458031040b480c044d00d112620007030710041045c0340d400c410003c080c00040c580322009050600c1d203c0581c5041c078420b60b000101c8507405001c46155960080751156000b202880d14510558550030102d2410110155078038203540b4020102d207405526130040c246046540440e4190140c0110301d607822100e0903c000b0740360b260481c4050042540580003032112174002400c03c840c42d0748400000c2c08a43e42200c0032100076548514105c42140c204501c0ca008281038598038603003500e00040501070300444200288858070240000d041c04d000f942c183d80152420390000c070310303500d000b04080085034020b4900002402100350b0018049201c0e0080724103070f980803103103104446908074440209101c1944242c0c0c0c40d0003590039448c013031132081150718070a21b5068100c01c0c03402c0a500501c400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 134151555 1250 134150305 134150309
    0x5071502010c0507020904050c090c18060a02072d060806040e1501120303020708040b040501110304050f0108090f011b030c09030f030e0303120405010207060b19090213050405010902040f 82
    0x10340e410034541035405a0490103a4425a4042d071300020150340d18a040d5052011030f0309a1a4840352450038480003110000c040c00050304207842c8200262603080c00c00513140160840c42d030060780002000d010070710a4855010000d00c900d03140b0084000c04408191f0070020a07045400014101000c000040c94580240c0d02ca222411028100c0d02c101c04c0d12415038807405000301440348400b001c886003098840e60413540101c1d040b9100300d8880e43c542c41c01d400c0315800b40c440c55001400e0458640d4800b80041304580885100601c045410072040c801540c6030540144001394a010f00020788200003401e020300c00603000000b26859141d2082c003005000c88006d041840c0070000800c5040c40000c0951440781e81503505030070300041500c0600c000928511504903045106120702051000304a015006080064403514040c441030102000f8401403c0d0a01c0f9510b401c1c901050041000c800198000d24681e5040c448200c2004e84401c0810290785080e400040700d95400102007124223306041c07480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 134152805 1250 134151555 134151557
    0x40b1e07060b0a0e06030601090c120e10050105090c19271503020a080c0d0b03030c07030c051e01080604180308010302031203090d0f09030c03030507051c02030f0c0a0f050715 77
    0x43c5c00d1500c0840d56500b07050260340c0610342d840d049040c040d401070b01e03542201c2c16203a5017480100195982c0a40f00c078a1003c2d50a50f00d8203100002c90203240c642d0002e403165032040d0aa60420424402220b40c0c2a0103108050034000109400c001d503540c0500201124002800640c103035918011000d450b080c0d080c8801020988140305449050b54003000a81e04001c24900817038545801d20410001841070410840e414071000602803459030000c9110000c81c0c0c09140002a0140c1d9081803019070111501745200c2c140c2e03c5900450158018544190004006000050951a101c403049203050816100360003040b140401002145810040c00c0c5450314401b0f54241141031141c425540c0740e00004170b91040c420070a00d100019449050382d03400958119039540c0b0115500e05002c2c080d980038103815529401150302c50010408444d000c0d401c070800703a03801585000300710b4207040025041050054000d0007901e16070000306a0b06411088400d00910250100d1840d0906c19124003551046003c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 134154055 1250 134152805 134152829
    0x71205040e0a021b2404020609060310090606050f040509070c060507050c0c0a050109060503040f0501050a06050316080c041e0504080a080906070c020d030e0301060311010e090c040b1e07060b0a 85
    0x41761035940c0f51006441c1700b09070281000e20b0300c5d548000f5885c0c5c02441e400c10340102c00401040908200041c40340100e0714800b01c01c01c1810348030001101e00e40329400d01d1001c1c1400410040016042200d0000d071b10003081c0c905554010b40d5581c411040d1541034851200040020440d486003120078841842c28280c21103820540501d40300001e407070300d003492144400b4000c0c0400001c0600c48044250007846034408020050340c0b812014280050500340600c40c004c4c410200e1140c038282e4094600c03400d9401240007040703c0184081008083c041803c4020340ae241001118646403496010b00c6010b13911412820b9200d51080c48000d01c6030000801d540e5082c2d000c4020300048542020002a002d0740603141480e41060500f420b44500000800560309580307050000410311650309011801d03c0d20903a65141403030b84030f008015001c3d80964880d00d012908100800484c1c01e60002040d0084185403540c440041c003820711006034200306401d4803031a44030182062989031021012000d0980300300c6078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 134155305 1250 134154055 134154073
    0x1030f18080f070503030106020a1406040c0b0903160e011a031006032a09030b070e033f0304020301050a02030708043c0512030903071205040e0a021b 66
    0x460a003840d030000360180d4000690300071100203510880f000f454010301160341d0307540c0d904030003580c07542100701c15603002c00300505170141d0000200f03c042c011908048081e040d6810120000050703031081400030b80c50f01c189050050303c2040c4450240050940c1c0824101c00e61510805180e280c204003a18002c192040040140021601e803040c003e468a920b00012004e040030340758502510704c3e11a49580c1c00c5070303000e05010b80d6030141c900b1050300d12036201c45545886090342900e5501140d649540c3c140c020042d0409500c0c1203a10790000401c401790b082060240c040c0d1083d40ea8181600b4440501500104000c107500742409959040244c0c0e44c800c62440c41d082200030124040074100a20200240b60310b10918024a40498940360050f501516000005a0009446c141302c03281113445010314101c2000142010040c0c1e4800e07090000030358079000391030740d928028004600c0480248001400081402400d842d40030703101e540351807401a81c81d0b0140e81c1e1528040b503d540c0b61480f0b580600b0103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 134156555 1250 134155305 134155331
    0x1062d11151005010e060f07080906030a230106020d23040b030a1104030f02060c0109060615080916120303110f0d050f0105010504140d08070303051f05030601030809010e120102040501030f 83
    0x312402107c5003d94144c071900a071038400d84610420340c01c50b500c0080170003400b588016640c011180400b24460f0368111901400115903440c1e424170550026800549099180c140650310070340b1500c0c6160140401018883d44240d07007604641c2092000307102c04420401011283d101c4c00c0032490814116a041030310f135540f001c030b58550340308000307024445c0440c002c0c240b07483c250403540c44554400000c2c8900c0344c580d1401036011040e240c041d000a00900e000c10f9134110b01096241d44803004960b20002c43e41010303050904a090200114101945e400c04880d03400d069002034429143c408a00c01d230340d03044040c00e00d410b81d58041c04c40708000e24400c004000580c0c000e0308030ba04079003100311181c103000d030303014001044c1d50603900700070b80021400a00c1500301980340d4040c0384180b860000c09409030120f9550060007003201d000e80313070701584202c0041c80803030340c00c60140c14180414542200324030102c00104800108441c07218086a40108045c0070301d42c1c05016101003ca140242040f420b910419 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 134157805 1250 134156555 134156557
    0xe030d0b03030c01060305010203061e09070503061804030903030f05092103070602070f02180c09010c020f060a0201060f06030b030a12020a0803160801062d11151005010e06 76
    0x212919a0351200350440e5038805000b65001c01803c40000c000480c0d990402601039401219500e216a2aa004650390008034940328141610302402c860a1070b61168410303502548040c00e1a548500d0b40300b83c081c54081780c000c0c610f200303611a986400640d0315604d40500710b401241c0d030b07083c14400d040c02540e000d40c5419580c1200d021202e1601c00013080d034111a5400c61007000e001030561400041c3c003005001002ca03200c0701c010300c203903040e0540900321450410b2104056408540c0341400b040700140d03940c810003601c0091800200042120b155002c001100b940c086815480540d464003410412041c17801040c500600250070140300c103000c02c1002907169850500e00034007404a50595010280c820850240700c580e000913080c0d40c80c01c2000502e880010404511000206504000f2410900c5041840b003000810b10038500080b0a10181d07951f000300c18840101000112035a040791494204030410140910071300030b07046802d08032180d02d81000150000b60500c528060300e2081034171404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 134159055 1250 134157805 134157817
    0xb09060306191b05090a0501020606130e01110304060902090a1b0c14030f1206040c05070f03020f030d06030302070e0426130b0d1419090f050307060e07090e03 70
    0xb503044110461140c04480200703803001004104002940e07184440b55000802041d290008841c071a0009541e0b500480e600e40003101d0301c64100416130140c0071074585c20341041c2c00381001600003190b00c914a0070710f1030203900200c034142c4001e91154409410360401c8840d40d60020381c0414240000b440700c80c0c20035140101012810b0400001c2ca50340c03001e01120f0074400e02150160800c3c2c0b55146049041340071f1603003282202207880703060b002c0416180d11740b62061318040d0380661592410040d581e2508407a0122824081c0c0550041400c12107491304180000c15942104110000321181542002454014140c00540c044107010003400302140019500c40e24032a1046200a404034400520038940c2c01071601040c81440340c0b00010541012410141c208100148820003200c0c0d40c0e0b040d00261000c06803110016220042014040605280c02000c0e40300d0048041454a80269a03218a90b51100d1402c0c0c0ea400d6480020035400300c0c080c0300003401401d02a10502101e82583c1400707417a48145 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 134160305 1250 134159055 134159071
    0x30e0105180a03050609060a050105130f0207020904060e0c03030301141011060103050604031713060506030115080102030709081c0c170a021b04020a080a0902010908160501030b09060306 82
    0x3080105180c10050070905803080054101840b5940d6440c00d5541c4900a54400496000c0c2000003800750540e0b100307940c104d980017000c403500c0415104160f00185180038589020580800883c03000d61030f40b541c007a0191380329800004003c1c007024103040c10a164109000d100f90010001040301d0703542d10000003074008089640200d186189503068521041c085c1c0001c0706030003500000400d11001140c2c030340c07241e80070b03440e807050000001005141d81c040803201480340110b4194000d01046050b40160b601c1903010780002224101010280d0120420f503001855681d000010884203a41c0174004100034504100104205655604038214620300496140c040020703034a507200501c041107072043d0074890000411135841704600030094942540d00355162480c54085281582e5051500c201d60180405641e071202a0300c4a000340700261118010503410842e41c0c80780825004824800081d04005d03041181000903e4440050140c400c00600b1a204d90540810009183c5020920741d6100c000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 134161555 1250 134160305 134160307
    0x3020609040f09120c120314040f0c0801060f080c01020309060409050402040f0507120605061306141e030f0609160507050a050102210f09190c090504230a030e0105 72
    0xc904200b802800a428094003010703c00601e5002070b07070840c041d030000354061004d520b640e842c140000c1d01038401000e1400f210b18508400500840c044d00c0c01b4041d803030f120303507850340c41d2695070101c090a403a603d4111480746d4801c200204016103080003264881c14081c0095424580401c0c00543c06000742d00c40c2101e505e444000040c21940c0701e510030340c100e1000e40020000c07030814800c0280443c0007d80f079500307510b241140c041450b241c104180c03071000a0110f5000c000d242041c6046944502107845621550340510610500280315042c810050710300307070325064503481c02c000750f0610448041c01c0b4034000c0010b082800105811141d12003d4a441c608091b030307580d409032500760720745200064007401a52011403400c04c0c000217520011100400c558070302c1040e4030b034400790300424001a622400300f98048170012006011007221104614001d0020141d400c0d07880300c06405841d012201111a40c4020315850101d4280182035507462610314010000c105581c0d9014000700884c1c111207061001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 134162805 1250 134161555 134161571
    0xf060c14010c1d0406210309030203071508010b0412200a0e070e01020f030d0504020105070b041b090e070905060613090203040204050c18010f050712270302060904 72
    0x151511400c0c2000c81080c00812044919a40c002c00c991204400d40c03241c1c43ca4924541c1c010710305401036a055582c0e20036488083c0ea0342002180e142c1c90140c0f4203c0510001850020150b030b411712906005041c0311000b6800001203080c02030500005800520fa94401440103120030f0b441680c4510800e548966480710780070380100f43e1402d87d9441c101c40f69000186420224448841c000729074024541500c1e2601e00e1109100103903110042c22840003c0c640c0144600c20804405070040c0b5085401810400d15184107038492001441c811241500c481349600a03a10316203024503072000040000c250104800d801d000040c6807100518400c0d05003d07511200030410b182d44400c21134041030201c40151092a555500d04000384d00300725020b078403d40c50f040c0050840304014003100c14042c10916007561a05100340152211918180354000f04a007d0103400c00280500f00003841605d40c41e251815411020301e00650304142c3c80407050300031140500108010b8881742c0a0783c0c184c210403503022030051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 134164055 1250 134162805 134162813
    0x20a02010315050405090c190506070f03093308010b07120e031b041a060a050a021e0f06010b0a0203091c0602040f06110307080f18030717010f060f060c 67
    0xd551500f0196105203414207104010078001072440b024402940c4020010b008020f5481c1d0101c001d110f00c540060081040c0070005050001203008141b103801e15900184d02c91035103141c0c0010680711072092980d480e4080344e8143e040e40419900b120145420603883d8182907500031140246c60f0002c0525802c002450422402414142008080a4200c6103401088055003a180e1031100b070380d5020301c0c940595802064040e2540d03651842010300100e144c020310a8003280c10f0342c0201108030031030143c1f20842100d1171f007802c01528070321070b8940104413000d1f010080e5418035006a000100480c0c1c10451a0300f056000301c107590121004032008007200842c140d4124060000e444000c0026200040200d2040c01140321003041e41c03060394070b00c0342120f42010070a64030710600001800e14001031140300f804400280c0241404121028804a0001103101103443c14809070004c206150382035090700342c000000d120741140101d03003d4041c0985072503c0c1003204800d045d0701803842081100f48000e002c0c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 134165305 1250 134164055 134164091
    0xe060309010b06191403010303090e0a230105010e09070219030c052e020708040b09130525020c1e06070c0f0611010e070501051b06010905060406060807020a020103 72
    0x7010007800b4641d48481202004d603082d41c203141d1400104c1c181c04141c680030800442542d06072a41038844000d06c40c140b801c50b2540840003061071580d02d460340480701001003010941d0f03009105c0a4801030055052030b0024100c1166651000e01a9100c0400c102041ba40020002e892210790394200c2040319890400316035448103400d0140562007620035100058201502c002807512520082a42006802c55440245e10901401805160f801d01050281000c013400400146030000c08003600a507003140300c1c0003510030803a60100d20f20b0300c03c4072a0441699440c200c0e0720000e00c5102610200c00c81c0c00c00030302c903100000750f209250803030b10400580940324101200d001c26049200a0803807660741500f130f20000033501400e00020f0480c100030640c0300050041d82000d1041001505d510717801c0c40c1c01100d80d90413090103005600a0b04030840c038540418845180a00003560010905103002c000b84025240542e0042040106180c100141558041804610f1507070910f000300c2d000024410708a98 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 134166555 1250 134165305 134165321
    0x605010f1d010e1f03180302031c0204120302010506010305010914040602090111030d06240215070302091e1c0305030f07020114010b03060907050a120b12010c111b010e06030901 78
    0x1000645140301c20660f142c2c160b088046400f543c042c001200011b00d2946250100c0710001d0140e031090000c4030b07085222401d010305e103c001400050078207130303200c40301c2645201c8a4415009030359141d0a110665903d4007030303140075002411b0240700190000302030310314020b002840980070b00d90104003089541e00c5000d00342c104685440880303031540a6424114010100c034429030344001c0300700b0040031041034081d40d840410010794000c2c00c802203006403220480c060050012041580c01c101c0800140d580001d0400102c082c04122442580c011040c05034008040c5941d0748400358499819000940c02000c40341c0c0401c951400840c3c6494040040e409042500c0706400c02030303030f94800461041c0540c8081c44c464141200d0b04101910b800c14281c3d03041c801c020b8110b00184040c4908d41080a0302d80011120301c1c0003602200070800240c082070b084440492154001407111008614241400c001100c0307084c00c00001610300744450000a04031581001d0614001c03880031000450400d820b61050340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 134167805 1250 134166555 134166559
    0x6110a0803040b010e06150301030b0402210d0306140303071e0609030c0b06010e0114091503070206011508090316080d06030302030a020106060e0d02010507080f19030605010f1d010e 80
    0x41c41c1c1c1403600c0c1050440109006074211444200002901880c01041e50800801c03003082c40c038656400c40c0c451660002005105981120b61044807100d020317101d050410f0180c01c80030140400d0307101460020181c903252307400591800c220680004440e50f02004039624598031181411201c2003800c614520452406c0000d8515842c0c11828010b0503040001100000c0c401c0313900200303640d100001500d4a14000e5102c50003c0c0140c2540c0d404001080028000c10300010310141c5a929000c110069550080b20050300603000000104460082034100803d007a14504161060340351889249990b800740050424002140148400070b0102d64411a40e07507881c1e006007440301944070f0034065641d40c401c0c84001c0040d843e00a000403510f11403c4800c10554008101c0314001159400464054129a000b0303100800700304030702400c10b090a001448a40e40803a80c1020038007031800040e04843d00384c1d0085050201c0c51042c540ea40d6070008002e0310f0014604403610761a9081c1004980080112900c25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 134169055 1250 134167805 134167807
    0xe060412271404060b03090d030c0212160203060c0f0913020702060a0810092f0405090403090305010c090b03041704090c080109060b0406140903011103010e190b0a06110a08 76
    0x10428507846485070001c2d10041d00c0a01456070f44030300c01400740c40700316401c003240d0300302c0344203841e1807480ba40118411a2452040b10f41b064004090703020700e0f030301a000c00352082424034007400841c201800400d90010f000e00c0f04505000403185400380c148100301d40d8510270029400c1d60581d0303002950546a00030780140c01d498403001c0d00000a032241a069078074282121b0715a20026041d80d0328014000c10280d81c08083d152600c110300ca40c0d0403012904107424403450107101c0414551104074101c0d02c00c6011365640c5000c1c41c5941002421a01c1c4103400604024409200f400fa200254045940103944150500c810700308604003005503006a40107200102e0902c0c240701010b5a2007050907050b140b610100300b11340c541d90340381c00e8060b1095106079400f0520090f03074120034003410b4000d000070601c060300103e03006034000308190311070340b09804c1401c1c00142503044c01000341c0707000a03150010051136410042808641e0004044204c2480703501e0030090100080311040009000302031020307034028480c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 134170305 1250 134169055 134169059
    0x90201090e040602030a0506060a05072003060702101a1e03011d0309040e0102070203070509040c08190311161806080304060215090c0105041403011b0e01030e06041227 74
    0x4102a50051b103c40c590242400085856803a20000300d0b03d4140043e2a402d141140300d0b954244401d0708155003001c021000030350380242c4d4030b090007641d10500703c80c1e000d01184030090320180c0884100d48401e00003841910100e05241e19020401d45083e203030f00750002d000101d210300007405401f0946480316180115898107140c07840c008080c01d89840c08031803c0c003590244612240c202c0c001c0584c0650326902c02d8034100903904100f800c003600240601c4852412544801240c1d03c0d1500881d8056945601d00d6a80800d01d03a1210a02c500600410060800704e40600341c030303085141d21801000308410b140031051603203910175031010009121200503207803201c3da21a4081c0d10b07038480b52031110b0500c2c042c4000504042c40400e4144c00c1800584a807402d0a04203504c20304201c00e119100740e0199aa56441840c4480517802c2070034003020f40da55140080361190005003560040200c0e04001d62102c2c0502c4006440008042c007003810700d1500300b8810116580b5160442810400f44d00625011140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 134171555 1250 134170305 134170313
    0x2091c06060501020d031a12120a0c21020c010302160b1008010e060709120309080102181918021608040f150503040302030d05191802030609030a080703090201090e04 73
    0x31070480e02e00b6000e54101e0103a090041c3c058600088000d04003680c0303462500d1043c5005011075029015500413100303a16050a12010680c3c007081c803000103e10546040d004001014131015002449502141202c01e00c0c1d2001035550074030403540134140741d008680300b605107003440e050074403a0342c1080294545052540b41551400e0b080d0242030069400c1071f8664007007a5001840d0384c0a001c0c96a200212140313800e001411143d02c181d0210200b210301000016451005d002500c5080d0000007098041d02580e0200250300038020b59196400103004000c01c01001601c0041500c0e0040c8030700035a40e901c046540c0c04142c03580d00001000c00308081400b02d11451181e01c48000e81703103060098bc0780070f016032205039a6800104d9000b401a070080000d21420000768105030381144d09448a4002020740d1030b0402c0035500300d54550039031140c00111820a5150400c005900300103c4009140f9040f182c1d80020000d030302c01040717103040c50b0716800c0400469100d41c3c404002040c041520012904092038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 134172661 1106 134171555 134171561
    0x1d06070b13080c15060405061f0e01180b22140103020d14010303020a05060105091303050c011d0a0506010506030124110109030c030f020c1e03030d0204090204060f1b0602091c06 78
    0x900860300150203181d00c005808982c2d410b030b80703e04c644010040c0b1023b2007148003003d10704203001000f0809501c0c1020a60440030300c0e0150b80c9000000c1c0f03034400b50040040c1800540b0810b4000018564041040401c0038442c7c800d030b4200381da0310420003101e940140d50401c00c0401c0c041701840001d01520041044101540011810a402180709151403c43c5200400b041c3c2000840c3d104000c07040c0802c0d070142404503945415541003890420035082440452000b580000c00c403119100d0041e140084001c80c108000e0014000514000b40200300010080300855440c1e286143d003a400031038100351210740606400d12400085010b0b40101150f40b210641500042047c0c814180f10741c0000d00262403403940c090703a103c0c5810801040103040b4002c0070200420b0901003052410580000b4220310340101005d611012010700055404c980c0d07800c1104000c007030b00c3e250000c00c02150 = true := by decide +kernel

theorem cover : BRFrame.Cov 133992805 134172661 := by
  have h0 := BRFrame.cov_init 133992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133992805 ≤ n) (h2 : n < 134172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
