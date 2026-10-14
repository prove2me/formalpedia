-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:42:58.094685+00:00
-- url     : https://prove2.me/submissions/ec0141fb-3bce-454a-a7e2-9f3730373bbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437769784 ≤ n < 437949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437771034 1250 437769784 437769791
    0x51005070203031509040f080417010b060903031204110303030c04140108100b1b010e0703031b03050a05031e040b06010f08040b01030204111306020d0e030303060f09100509100306 79
    0x5a440c1240c8038041a90100003a44244401140da483c14102c000e4210b0300401134010307061001c0d0713101d0310a98450b034403da1104008036440c0e03032065000c1c40b0f113010140c81662014602044040000d4907072061541c8541480b00710800300d420300c022540c04c0550144087d0071031342d4a0401107031800c8942c0043c45458a2100340d0100c0034401c0d4415104940070760004490b982c5c001e03041c0b42c4041e15070f8105d00082410010344286020640909005201800c5103800203040c405003541002800d00040c0d641808860103c2030000c000a9403182c03c60b0290388072842d0540e03c0351a044802101d000d4440c030306d00e91207142001031000f44010f40074007900030b4400340c8680c121002c0551b0b05545041c400c41d8041c043c1c070218401000542055003000d10b43c2c40420302d03042c0c9000c8401c2105c503480c154035084400140c0c080c00500d40030035000035000c407140b58100c1c010341c1146040f20006a4400d601d0003d28021001c020200d04501211060040540380c0141310740d03194500700240003c12503642c80142d840340c5c00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437772284 1250 437771034 437771041
    0x405040b0616030e060d0609060302090609010e06010507140d080708130b01140315070801080d031a010e010504120809090105010c0b0f070903080a02030705060a1503031b0b04051005 80
    0x42a0048071070a400c290111511122691000d40f83c0740c00030000c07035402c00b1782000740600d480f4003441a84083c02d41003900103850342c10350040c4901220000c0c641809808000c0060105600d1101c80c5903014009180c15651103e49190008520007180b09008451081c461001012074100f45180e00ca40e540369a4070070541d940d9200c140f2440b03080c84001d400a0140d4005214071002485440e503490000f8046803c446811045c0a0101e034003201c0c1c1c1400a0585801030140903c14400344d0094811481d003409040122a941070f14141ca0341021414803134024a52001c60f4020010740b0003e102180800d00795130b40c0b0b401c0641d9030340c4c400c7c04041e104104210010415600804c156003240c3d8101ca10010f45c1e60b118a108110040041c01220500644490000000b902c503002803002910581c00b0b1078850a0601c0c0041ca00400501462420ba051124151940700030565060441c1e0705460229000c0d00101c40c910a0f56038002da000c4d00c041580303c06c20045c8030300007621146001c03078050704102954 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437773534 1250 437772284 437772289
    0xe0328080a0b010507110a05030307080403050c04091106030403170c0406121401030b09070803041203030f0b010806150d0609021c020301050d0f050f0a050c211228050405040b 77
    0x4001401c514007244d014041d00c00800c44545415600c0748014201d40c459546540000b0301d180c2001008545107d0001014003c1186c14459901000300a5405100521055035600c040c294403541042c010100400042d050500c84c0f030300c00304401035900c6285101c0c1042500c20040e640719001c0c10000c40c2441d1050361442d80070344590103524840c3c1c100490641d09650700c6c0124010042c00407601c0748a01030002c1141e10b01840104002c000d400841c9070009240d190141c15922400f144021440c9400c68204213a60480143e5a000b00200c4955056445020001c0751074014609416000e41c60888045007902c0039030300805000c44000e1170f85050403076440540003030344002d0242030f802210140f5082c0000f240c0046c4400034a00ca5800e4440c9240600c906030318101c1d0010040d11190700030420f030f03440340c144110070b00050074680401034012006801282c0e6544200c41511800f00760005550b000a0182d5002540c4600d0000c00681c14400350b44004003650400c0c02102d00c10b616128140c4d07600e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437774784 1250 437773534 437773541
    0x703030b092a0705060a020304020a03050706032a0f08060a1a0903071a160309080a030806150f0316181d06040203041a040303201e0306130e0328080a 66
    0x104d60220003468103642d6882903101039000544201d0b001801a4808000180e007441408094203c50307400162000340451003102c00c016102e502c0b0000410303041e242a4160740200c0343ca00204039400e0406960b00d5a074042403d51500354400484820840c00e00081c003c40d5000038040c2450480880d4189501c50810300c0103182603c132690391540042001e590403844042c5190780260090815114065980b0a4241081c00c50141200001c006104028030f40c41c0c00303412103400c00d03480140c41341030400118201100b403201402c0c450315550744080b1017260314407d901c480098484203001240c090340e110341118000c80142c00d8000c0a54a400c00108241094426030748126041030801c003080c2d8541c01c040c9081d0324080c00030340800d1b8607035441e080d10340c419000b07040409944041c810b9071000103482e5880e50341c4c4081303c000081c0c0c60030811b100b101e80d12030400c090404e0380303000005144d8411105040c0340d40700b014289802c0b0f0740c0110840e40988c2402c2d103100304650f5685c03100321a41e612400c180d400c0303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437776034 1250 437774784 437774797
    0x10e01020d0f0c150b01022803050c01090215070b06030604030c1b0510021e01140f0c070b040c1401090303020304090b03032502030d140f0703030b092a 67
    0x580c419a50098028440c104500d000c0180f41000014440710b9120a03400740c10154480c10a5500c0d21141320407564100880b5a0ba078401800641c14600c02d005908800c10194001404100010400c0380388200207601a03000994000c04105201e245048219050780005200703035406142c14001944038100440d5441c80740c0e9261f5240c0d48249001d81d60443e003040910580e4410701110800400d4545545c2e1940340000000e80040044041aa20000c2d4841d810021078990307904044070700700c1604810a80e6500a01800c003400d00c03503514156044458040c661001d000800c2c0082400188060b8128000a8810841c0849420707080d490055807006600c2c0302c001c0c0140c0c0304000c00c01143c0300c141d100290a680c001c0c10b41e8503007401b5030807001c210741806100c4e04030030054a2a50007186020030401079040a0750422045000c540d40d850649402451412002c0030380002e000c6040500c40d46c0488405440201480303034030b00782098100d80d80c042c0100e4601c040b83d0030307482070804120214159804e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437777284 1250 437776034 437776037
    0x1401030c091e0303081b070213150b03181c0c0f0503030a05060f03010b1e030a02030703300903110109030206070507030308130b0112020f060a0e01030609091101031a03010e010b0f010e01 82
    0x70b08055a230034010000e00d64141c58186540e1540104d03104c91042010200034054540d040d52203060007030f5a0380146039169013040c5254004900e9011448020241c000701110500f440d1030319052904110116240703c550090850000008001080c0c03001e610003030080c6c405486420740400c0d84400e1500300d5103080d00160340b024401801482034009e085020703d0120024054a40d440110b0780460710f02004c60700102c805d071403103040f8604030680007401e121980000000700c4580c054140f40181210a007800060084110340c00c8069443c0d0141740c540e0000c50317015000564400031402c0268030351196010440015801c0004210741c4458400000455030b00058241056464842081c0c03201c000810220382125449040b6040c0355a44409442c45141ea91104030ba4110400f000404580450f0010743c407107454418903070040f91001114204503035080c00c001520030b1650050082c11080250902d61540c20600750b8141e03288190844000440c081e141d200c000d50a803801034503d00d150b030852a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437778534 1250 437777284 437777287
    0x2031005011d040b03120c1b01030b011403040606170c090106140f030405010609020c0d0809060709031b0305010c030b010306050603090d050a050f03042a1401030c091e0303081b 78
    0x320302d03c0c1c540c0c0000c203200d40080844108001c52014074400d07400a209405d000d81001c1075002c481c00c046440b40303170000c0007441c04010a529090000c0d028410030124030074600400310003d0104210303a44900094a42901d102d0b4004035003142060740c07802d49604050160f0b00d06000061218080e60201009441451055003003180d44840140150002002510990340b140e60000320683d6a1008004a100800203415006039045000d03040000c09020881039602c44000c2012066101c0081e2081da80d1104046411010050101f1081f0b2056000900554a8050340005a54140d404040048030a07241070112a5030f500400000b404215106455500092842040c152040004080304181414403605049a040c403400703a680080b10101c41b00c3d270505400350a5407620344d0f00703035080300c20038450340b416282001401045c11003140d011605044d15081a6101c50303000b014000b01501c45062010748925082143c0700a070a418882134000c03d140703002040d0082408a00c5003040301984520702d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437779784 1250 437778534 437778587
    0x24050102010c1409040c0509060d140106090515070317010602010c020705030a0c031707290f090c0f03070e04060b040c020f03030105010c0602040306090605070806030307031709010e030307030203100501 89
    0x301800300003912008009041108c841c899503804090a4211110100018103030480391601c0200541a0403150a202d19040b040143d951a902d002c100b914080709401e888504600d0251100800d000c08000e0300113000340041442a8150b02800d50580150b089982c0d031982d603018551a06810200a84040038544003400070071104104c0810103044580c4c3c8514001d40750700e131008410340c0d11000010b040120040d0040b20401c0400c65900800c4070803024107141001100160307220140c0c02c21038000d00300c03520090121b68040c80000020905200d4800040c82d081c50410014052030003010700c80c42c90101c5500300148000f5811070005600030045145900b41001910103143c0384e40c00701c46c100d400300004000a43c00b801966452403080c0004070b0b840c10310101c05410403200418240c040d520a00281c000701c0c0d07200b00d681c0000c148083c0c0c4240203031a03000d012809410105141d40c19848004140f000040d81580194420000410340082d81a21800119000c0840c486030076029581d00b40035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437781034 1250 437779784 437779789
    0x230408072307031b0501050318070503010e010203100605070b0f090a1a07021b10050304060f0617060a1103071b0c0f0306051803071524050102010c1409 67
    0x1082064050000226458101d900800e80040c04a58110454000c1402041045800b55021407009444004124a1400c04000900d1400000d00013600c160130004942804a000d01c82600a02400303002403103a90443e0b01090301075402610f484a03200c40c913000008005225a042d96070031944217405454548411000c262807010150543d107036401031034404e000046103180512000f20f00b070368001810b1b1800c82c0300a410558082c00207100d408080004240f99510000004c00b0801b080c28a9504e84d101d509140b80201100b41018050301c1c60000c5c00b04002800c0b03004d601000100ca42195240e5403200e07c2c00d400c1c1c82001d039640d108242d09101040d0428042c84903203091900300d001c01c52847c205516105070740580c590050902076981030060050210710300503140e00038162820600000910042d05540e446415409024400c2c19800d4981c82051608506004d400203a07503030030b45186506982c4100383c0c0c6403058501661a101000d5003090141c840c0241585e4000507103418035101109 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437782284 1250 437781034 437781037
    0x604050303030402282607060509040e190b060a0b0a0e040b2d1512040f14030301060512060f01091401110304090207051203040b0106031109030a110301230408 70
    0x4d0300c1d00444061184804000c030b100c00d020040900d41b4210148a44030341c0410b50955690b00481841d4000c1e4001340a150b030420704851201c07405540020310f0000c1014803d0401685081c2c83c510b00e4815182d1030107000e45002d04c14001c09044818040e06c540d500401c140900c1074038848008030700e9141196005141c69480360796901d40c050008020081001c200c04c4403d125004241000201d15490880c603040000c0200d410030707040702c0f40514000c80020340c1406100c0c01040280884071010828082142c400200c846244510003100c1e1696103925000d00381d034004242c01d1401c11b9003000091454501208410600403040c1c403040070450030200183e020300c0854100c903043c06510113a012202804000500003004c010400680b46c50040c54401d0400b0300c81310200c01221410b105000108032a402c00d603046451600f800190a80003008418407070140441080e41405401140014009103203403d00079080110000c0069901c100d0445c044880d03c15015014142440300040c0003841100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437783534 1250 437782284 437782309
    0xf020d02012601080105011208040e0a0209060706061a073f200106030308010603200a0305040b010b0f040302042714010c080105010c03031e1a09060604050303030402 73
    0x5404000540d4207150b882c010841480c60500c00c2c030040004010040d02071080a01601c911440402d20b600141c8035405a4083d60180b104039002c510007151100800c0c2e8102c0314404000340c0f01e151070b184036040c80c4004000521a04080e80410082c56009020510031150380540c03040b880480704044c640e500d0800c00509485820050b00305181c0340400405028131502880c06a03030700423030022101e02c151305032030001c500c807030260f0704000302400003130b40010340f00e41924958500062a0360000009440c01d403150904dca000c010300080d2110042c1d03068014602c500d015580f04019a40d07140a820094070480000d281000014002440180750903000441943d0840383d0300c10900c1040c904058427014200001c591500c0010700a110250081c012069010300e40d00b041aa40d61510340040c0004000c031400804050b03540403032540380405040e015520a417003003410401d00b000d1007001c4c10702d0010102601e00c200d0003040021100d15084040b5021348501501450031034440c1c0d401d210203540c554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437784784 1250 437783534 437783537
    0x708120a14010b0d0b03011109100c0f080a0e01020a0506150d05010e0d08070905010e0d03020a120e0f0306391603030501060201051015020c031b18040f020d0201 71
    0x1108528900110704045038040e001c8a000a59510718500c5a40110b8072042c600500903414079050208103201c034400e58451a00c25124143c0d5100310410440c1c502d054002c005001c82c0c03e61042c94144981d0300042d018101c401d4071100005000b680069907149581700c00100103a000d60000f4919500b8100c031811014405011081c0c846025650942520914009842250701007800490138a41c0080c140345c010300d147c00c00344640b906100000f400704c1400819540074242c2e22010340c3c1058401c20400302595000b4001401400811308010001010050054410b0344501c0c020201441c0c0403907018021402420341e0024211a60321450540ea07c68140c03228824500f1a407107004040080145554030840440440c80e400529003d812117806820643c2160304d050308000400d140002d841c400e5810500100100000d043c90803032515104500080d0140518420910801119108502411800c8031a0504070300c0144c92403000e804100d43c05801c2d5481c801021026080110202940c01e006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437786034 1250 437784784 437784791
    0xc0d15020d06170613050d05031b190e04150918050a050c150403080a1d10170117031c1b1701060f0e1e0306090319050708120a 56
    0x208004404444880e0302841c1c030f0f80240010920100c9050000a60011000a1007030b0030106945030140d0390351544403a50148440040881c06111550380840c0c0981c1100c4003980c0d4881e00e0241c43c00b00884140042400b20340740003080003080c5414010000301042046480210754074151322000944416080c110f0003c450038130072808142d050005085040c081c8009002d002140b030180202c07a1b00c050350312200c1d49418001400000d0b032003000c0341ca00150f5403400c0700340d103d000c403d144480d02c0099205644100e0101e0620506a000b180f41c0300317040c101060207081680d9500c1e22140c0b00400d21410145508100f00040d00b4034226900003040b080b800f10001010501d04039800c0400c05101050004100c0741134901c10f01c55038042c000c41c05407079a8034181003100381c0068050a61000c04082c6440ba20a120700385885208480c0382d51031007a0010106c42e101e00303080c00925204e900203250404140680705501da0001d002d00116126198094042407410110422140b009400600300c1d402c903646 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437787284 1250 437786034 437786047
    0x809030609060f010911040b0901030b03030307090302010e0f0d080a0302041d01090b0a0311040b060717031014100818010911030706031a0d032601090507020c0d1502 73
    0x181040854480d250480060166081c411449020303000d050b445a5505420710002d1000040c0d00420b8038111000b0109540e10750b905080180c01910b21040c8881d05807001004011895500182c008100c0303000381c07280f40c030b80f605510a1015a11038010302e103030401c8141c004000000c0c000402020400312514005090944554107074800464000314541e60030401c000502c03041c1d2845c80360ba04001802c6480b0408946907075a5030070047c09400c00309105035640c202c1e80c0e440d51500b2045603001580078690107484455886502c41c1354100381c445034510f05640c200850040003804031041c01050007849018100b00c550070480713650400401040c1ca4203800d0710031081680003400b620b0f001c0751007441382540c0e100c1d5400505141c41410343c0b101c4205400e052040003010b541c8008454001401d0352042140405828140c403d50084044201c5004208840b0070421025201d102d06903694070400340100c0d2030b6800304030b0740c82d820783c4c00180d840300c034203207800001070310700181c0c0c000c1d070300703040768090704100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437788534 1250 437787284 437787289
    0x20105120702010903090501020619051005060c030d0b0307030819030e010e0a03080c04050a1206020c150a060b040311040b0a080d090906050307081e0a02220605010206070c0b040809 80
    0x42510001e0160307440702c25110400da00040c68101410007031000781041c0c030340000c00d4018004c04440c1c4050036642d032404100410042e01c02d0001424000e0000ca603074500e00c9504e00d5880c1c0c405030b80b14014500d0148041d441d80380c0410590116900b2000742c03410034501c1040d40c07180408994071081030513a210b250195102d003c0c05404440300300c07a030280c01e4041c2d01d1700f4080c0012000421628412000300001d11071070303a8081c4500e0640b2044002c40e140c00c2c1d10b502d4100000d00ca0b4502442c00c61084490600c0c0d41008040c9992250310414018030050390303182c9601c1014090f5000003040108a40305042503400c25501400600c1d030000c0c0f203084c2c1540d90321920703410310484814484c00182c04403800d00065080b4051503004220a50050254600d041072243c2c8480440c0050b4801d03011240400701c60140402c02da40d007180d0020809880c0c0400e40441c0c40b02115501c0784501120308042001842d98004501148101159114001810341d26550351079403c800800880f0581c006000c602d600c0e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437789784 1250 437788534 437788567
    0x303052206050307021b03070b09180903030a060503010603080d020d150801140f150d060f0f0b030d0311090d05031c020c0f070b040b032a0307090918020904020105 72
    0x1441c00c1d84034165641482c440090400c400809401d06114030f41c5000034042d100019104122114021060b03190181d40000a460700402a10071448407501030503c0880e00000c4000c1d8010345210400308109a0f60300281401d0316002c0c4405000040144000b030481d4025800402403074259480c0020145400048200c61101c0c5800400040c3c0d9240c10000c5607242c0a4600c980250b0450680e52480c40c1500c584003040c1030841440c1d024010078140e0380b08112440c0c00c80c00703907045d81c0c180c1401500c0b5142c602d000185000c40040380704c0c0c803604100d026454021704c00d0a10174114000300b289030482c0e00d030500a84c0c0c64102c00840b4540700400c40c4241084640304c1d94004440200805079440801c1d80c1018545820789040d60a10b8001e41c85c2007128102120880341265045019030b500c903660691803e241c03003420490003e220500030007001d074101c42c2d580198450711064840d50305030703600c80303000d24212941e00741c5400b40d134428802408054580800c026511074814035100d450b000b03410824003440e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437791034 1250 437789784 437789789
    0x3010902030a03030b1e0a1715040f0b070e0d032007121202060910051b03180105070906090918080708070506011a0d09080c0d02070806060604030302060103030522 72
    0x81e50b92109002c0d81c50044405c07081d440c0050a841b1020702c0410009581488601c92240104204c2000c4e007900d080c1803104114400140050b5003c0b41b8190416121411032000202da000c658600082c1c1241c0c09049403505004002d07120080e07214041e81c0903101ea4481014803620a40c4114101c000f01804000030030140030703c1c030302100313515201c1d241608805200400e80403d640200301000300c0b000000079030100d43d5032100000f1030030f901d0b0380c0c100100e0310703181080150f0040b00000030411a5411151182090403140e4000c0003d5034854908864001c480c2c0640000522849410001c03521141c010420311101380c05c0c00b0480e4481643c814070598041c003002c13039082d0350202d500000e0200a028080c010010044170340c18140d1a40803004842c494035010900d5540d562024009015146c1c050750540c045000c02c46500d00010b00c0c0c00b80d40c9030b100b4441e07841d461041100064060418005950499601d07800405259003190707001d448540041000315000c0b000074820164010600c07000800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437792284 1250 437791034 437791037
    0xa0f06030b1e0d260307030504030f031a01110106051f020d0201110304080c0709020c0313081507110319050a02010f060e160c0b04061b0305010f090b03010902030a03 73
    0x20510100c0d01030002030700c107180181000344000740c81c05840c0d032203500150025940c421054001c600b0a0300e81c44e00c113504d2110070b80e140100d020042104445c2c01d640410b02a5000340c48402c410094100d046051341d240c58500041d01218400c03a00c140e5005110070002e4588283c00810282d032204082102280c410401c0c40344545e84010000001380c062001c0c0003a032220744001d0000d001e28480407001c500c00504010501900000c1400100e01e0600a041c09402c0851095654840b80d0050b950350780c01c01321640c0b003040b4031143c0008800380c00281e1010029020140601076664513103064560440084460110703010801148940b40007100700074848650725141c4680350091102c000b801c48000e031601405035072400c481840201c04084816034011404046029030001001040b83d00c08500381c1e00408540060051104008503900f140000a03003d44201050114903a811001e4032020700c41d0b9641140310150a1010030103d40105c4114000a0000305c0c01005981c0401d00d0000030300c40030780 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437793534 1250 437792284 437792291
    0xf0509010c141f0c02061b09030d0806040b030a0b06040228030609061202030a08030a0213080601171f090c08060f2a04050603040c0308030703050106120501030f030e0a0f0603 77
    0x2100d00072000c64200181c10400104070300140e520005e580c40030081c200f0102e000f0b502d01e40302c50b4000c9600071100e80780ca01405840404041c48030241442c3c0040e101c1e10702c03490926201010904000500e540015040b02200115440790b0007840b00a6001d891a1260350103003c03041401d1800c60700600c5c5428515607400a041480c200c0d81e402103621640100c851400414050030140c2ea0009800050030b400035811580ea03154280d07100300074400c070044500b80c00718005d00020782242c04a2407904279010307004802000048004102d8960b502143d9810b041030300403528030300c044920b500030620704d071041495181c0d2a448094041c0303008000c50f600d2420b032030716100300702503040c495005081c41c0c1d201c400081c0780c800c641200810f041c041c80c01507034042d00c0040001002d224007405504001c5401c488210340c0e03801c100f080200600b10900030b5501050300145000044100c40c8544d604807a0003980050b40512190344c211843c0344842c11817940719282d080080740d522001107618004100d5a140003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437794784 1250 437793534 437793553
    0x90911090d05030c074119090c020607050f0a0207050d150617070324060b04030b0705040506070204020c1c110c030303010e010608070c08030f22030f0509010c14 71
    0x1c0e03203080420382050041000c1c0380d0100c0c41d2042d1b26102d00c00816203040c0003404601d02c001c90f07402805c03c161007072940b000801600c280180d4048204ea000e07604180820701a500103042c050303a40f16000d440c0c1100040c001c01000d00c0e0b21840402a024182c0a40f05a8440035929800505511440d600c2a0790340d83d004105a40d07001440d00c52030700100384110381c100c20f4640340461261580040c0c031015111100c0c40294a55605075005028407480e600d00c0c0c2000b1150316a406403641d40c03c140001c81d01581c004000c900d20358080c1c42a00e040384c0f4020061840e0000f2030f824440039400c2101860020310551715045041c0c4c0608200c504010301c10355070a6039050314408120b1810441c5001c090183c4c00800051090854001e04103040d68060b00b0704080a8480c0103048031b4020400e24042e10f0340340040184101209003054060007403a0340d245651203e0f9216481c100e41d5003007000020013185c0b1132241484024001c40c05001c540c0b2050503c1607400d403440c0c0b15400c025180d0341284290b0741000301076 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437796034 1250 437794784 437794807
    0xf0303050f0f0906160c02061216180b07080d0e062215051308030c0301170321070e030318090903070507031719031e020901090911090d0503 62
    0x162640649000c0303103074a640c00d020403010340304c07600586600d00300b89110290340001406074406070700040d8040e0003181c0da0b109800e085030101038140e40003603000e0212030140300064803940c21180000d80151803860401d1901942100940c04003400b103e81e0305060094100a00c000e01c10000580302c80b0014103c0c5140a9100e07810401d0304103039549210b424010b1100100c0c9054151200e4401050000246070f02d80c6c04c4800b2154520020042c14000001700304030110307140c00007441c101d58044003611110364201d207606d5128051840c00104110000300074040c03500480c100f6a8001c1070905000e9080b0110707101007030441e8402280c020541e0140801d1901d20704110400380c0d80002d00c2d03005135040401a0751416100c40c1a4032014000c140b004a4036800380a01c44c0c200e070300b402c04c180304806004202c8a405400303000d86000444009405c18103030024000fa80c001c981c85014140e4440d0315250500002c1c1e001003550703050070004420144524801c6884c2e82d444c042245010b03000454640c4c040761f4a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437797284 1250 437796034 437796061
    0xb210411090901232503090204151508060f041d06180d080402061b0d0e0321030912030f0103330506120105010b0405130c0503130503070f030305 64
    0x510082e40c0c90314910003901c03a00340e004242c0b070366030075202540c940e120304041601d03001d0150803100c150700d11031556491194041d800203410900c00e8400f40240340c100100c4203c050400c1c802d82c0c4224600e1124412400d1142c82a140d005030000c00420303c1a54031000b10781215200000b2003896034507900611907008040141592081040040400410000c1182c98458810750030300f90034041c081c1c0205045503107010599140d1303007242c2c458a11010103e103c440da203000509458001c20030100d441d16250802044083c90002c24049003007038400381d031207207007401d910081c002442c80c00380c00078002264100d4402180070700070703680322405254154200380c0d94084c0034181d1750345c60707440305040c0446a180c255030012036020040000201555080089455100740364800060703540307008004100700a201313025001360345d02900e212100140310004039084851034101d4501241e000d0002138624050700d01c144280c0307407085003640d00f84030140c3c0d83c20f040d824030b800d0218040707134845040242da11500803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437798534 1250 437797284 437797291
    0x918050601020703150603060513120c11010c050313031a01060512011406070507090f0c0e0315040201050c060705091507031d0a121401051806010b21041109 69
    0x10040045050520002c2e55402c003034480208844540c0740a1030b481d81c9141e110300020340d044003003800b442c98195080c26900f5540541103c2c0c02c1401e80b14103288030301c1464040700441d4020302d01c4000c10000b0005541c401101c400440c0c01384400c00c81310154030b040c00e410304000c5221b460108003101c2c4100703c0c1c02d100348050b00150308010301070003008600f403107028103507044440b4080e403500c0d0b03140182c0c003103038661284010240581c8126900000e208003164010a036109801401f04010354101c00c01b15610300c02e42d40d01c154103038015000300001d410408040ba070000d205040091a2680c558602030a0400c1141c03480045031020914600d542068103071090041075409840b45070104a650141c0b23154005a550440007400111410075074690b0050040030b4079030304d606078400018900d00344038180915040314586500344804070f8604000b1455481c0320f00c9800020b80000ea08004803604160072605071001d01002c0c24003c0a690035807102000c0c003450199000707000b1026410700b40f10014a000c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437799784 1250 437798534 437798579
    0x3030105030d0519030b010c021e01020d090b03041401090c0602010504020a320f060f0d0b04060515030c0904090b09120313030e060409141608040b04060903020708060709 75
    0x402403004000010180030004c81030341d0400091210250004880803001502c00a4101500ca81c6a0580802d002000700e4211001d03800c65200601310041200c08a80601c103140e40d02c1da00344040380006802c039205104000d051000001c41e180c0700c1d01c5071048c002441c1d0004016035501d20901c010344c18074441400c0035040b990740400f0a001c10100d0444411400070130741d0003e1100501d0000e040e50b4111000000c2d060052405880c0c1d90715542101e0b042e40903000c0f52001528041e256506e60030540541c004070f80000b04101c3c80441c441030b030441d1036480240710700c14591007007000140700e907990710420014502405140504d0320340a0501e900d00460450855400d840610401c021010742112614006a151504000c400e09140120322507000e03a82000000302e00f007218403036100c03150201003032280d011607103008210b0406503003d596441d820b4801400da524004000b50200317550350446440e16200b07104580714175580c0c0d030185041c08025500c0c41c3c0001d805417410484107160003035a0001a005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437801034 1250 437799784 437799787
    0x1d16080105040b010c0b0109020d051506040b0d06180b01081015050c0319020607140301050604030f02031005010803090f300f07080705100f09090f09021203030105030d05 75
    0x410001621801051094500c155100e100b5081c1ca81d1081142545040d4416641c981550f16800070101a400c07002030307a43c90514080015600c09040d40315142464005090545090b080200004499102c3c4100c203910310b490f010000781491003203a008001c0c649080c00050580c0d620000104408400b800b50450031480500502001048042881c03c01d061420000c1c3e07512558104a400d601441c01450005502e0040d41003844e034011900764400c0c80a40c0d0f59003140140005441550301080c094160010814001800024030400514403094001000c8901c0060003d4862003550400d1b000300742c25800115005500741040c901084800c03204490820b034017061f07482c04512080760300c0500043ea1402080c1a9203156090141100718807101d01620600c80e101c184550f1358840a00c29680545007051255014034401e410203080c0c110a03507601405a4a040d50440241c00320007820750040342d5581d20900141d42c0c181d1001580300c00440556281d40c505010035041c032220884840c01d0250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437802284 1250 437801034 437801071
    0xc09010e04051002220f1403072403090212160522020a09080a0c081018060b01050f0d0608150f16090b0703050705010e010c021908090402041d 63
    0x4107091034614910640181c032842a400030070600030254507201e01c4290341000106500d007054030780c9402d1f04c031b140003100703030b401110b4050560701c01c043d2241d912100c1c0550044000030410720440a03003180301d071901003640880d50700040c00304003000701200c101c2c1c2e0100300d901d040114007c0001d03000b0310048400040e01e81400c00030088e4241e603010200ea401d03030b0005011b41643d005004500107052990100d0b0542c403044d240142c0208036a0107060b03103511a080039030128100c0ea004200300d07081c8a4841c0742d4101c042c2e56403800940164030405040c42400c2c000713a1510a055009085420007070352020603564503250545003054004200b0244041d64035080048400548505a130018802c10b0b000016141d1190202c1e10750606410480545600150070380516900c032000c0c1200301c5c0114020804001202c00203400c80d4a1302e561000581c2168030b40a01c0e11890480721300150b80110710b62841c01c5200710004041f607110b500040724100b03011401c0a824005000d4181d0f2103d130a801c00c0519a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437803534 1250 437802284 437802293
    0x6070912020f130c09031106040f0311120d031d010507050417010f0203161701030b0105040f141f08030301030201090b0c01021b06150609060a0503061c050c09010e04 73
    0x51200002900881154070501c0490b00c0c0da051901c82da501d00003040080d440c014030011701102d4144000e82d92505c00340d400c80120301e00441210301b00c902e41e50b0740e0386c0346620311354402c2005040b854003d588808502070404400a0520005010070003c0d500041d00314080c6c02c204292000003112740e041680740c0820000100d4100d003c440585100b80501d00d0440d004861003805461109001c078600341c00482441815140c036100084100303650b496140390540f120480013072062003448041c1000803803000410003400c1942c80620600304007030020490103801d030050380002030241c420074514001c11456560b0560710318189800350010401641c655403440d00001e003541004e00810785117030400180006140004d50440d022500c401d4210306840409001075600c401045800906511380c01030910858601402200e00801d001401c0908011507440115080d40005210780e0704110340400c400c0c801019510140c010700d00c160000c140e0000c02200388005001c040e8095034400c05c01c10305100005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437804784 1250 437803534 437803559
    0x807030c05060304080d18060501080d080708190e0307052506051308011d07060207030506040f021801090f18120305100b0c03030109050601020c03062215050603060709 74
    0x4540486040391681c85900700b0448a10a0951426032241f80050b10b48805480d0014000c15074001c50080105030b98640c081d64964561851110000380c104001a181078040c21040b0f40080101a030168410705101301c0c1812120301400082e043d83c8003141c0310007000b00401c0401c03000c2700c103424403445c000021003014241b144540507000900030080350350700242c411010321400402c10b8400034401d21000c02a45031103084203070700410960051032000f140c61030001031580102d0b03520400820055a6548500c420560788100c03c03684000c16445403015074640a41240c007070015440002400008544a1400c8510410046020b0940702e82204080350340c07102606003101c1142400b0429070741d101c9901c00742d5000340d004001c0c04000890044001c440000280d410f0741c070844010040c980311040103aa462000b200c109034950300580009010815000c0d4440d680c6440c0400c85400158590728101c95001c0c016218070074030341e1030003004507500d41080440d400210303074104030322200c0c01c00201035440b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437806034 1250 437804784 437804789
    0x30d05071704080901180e1602010c21020702031212011a0a180806151203070f02060d1116020108060f010504090b0d1a011811040612020706050f0108070807030c 71
    0x7a60b40410449050b90040051b5140d0442d01d610070030005850703816541c0a49000e031043c441e58458070711000011401489a800040e0341030b00d561208481b20004240e800c0420390f0414030440d02032240a00684042000d034451014a9040a841d134140d0143d40409030016444a11a003040e4141c85d05004565011982609028a0300340d00e5280004c030482e0341811103074055141480b5013401c02100e02c03651f0b0341c086255041113402400050f0a000090303624001c000001d007044a0b04500c04005240440040c051800550390100d40070340c0750700710f012040e04600340001218680d48030844c21580c0c40503d07654814070454500c440581120700082c06400303540200c407006580c440d02d00704580d5030740c0c0c22254003a81c0900410016000c540c0c1c1e02501c2e59080c81a10710140302000c0885000c9483e0142c1300004202c4d070001ca0901e45000750480e10f140d86524a80120341c0d007000000b010071924020380e441049248003e8250b540b40626081c03401401d0380c0040ea00d900281001e00000d404400010304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437807284 1250 437806034 437806043
    0x50a03030504181b270314070f050f060c07231008040320010b03030304150e030423151206030d02010b090103230d030c0e010507030e220c02030d05071704 68
    0x400502912403442248039010701724000c600c0c2e981e07000041007014000210030503040000c2c2c0c0c40082e40c480d0103141c10301c054042d1aa10450282c4040c00c030741480c2001e0320220300444203d9000720b58500d0114240c1e440e82c2c0c015182e0003040c10500e8841d0401c4042040c40001510707004500d454140c07070050060521079044a90100c2c0c014150340c1110f025000307135000610007015a80e5a04151078140b000e00b14458101041c1c90422510218109000c426201102e03010300f0b00d28050a40b1100328004c0821050069a102501c12502d0181c07040c40000b5010002c203100715138500e820443c0800d03260404001e03005003160305081c0b02c094543c0701c04900d541121360100c024140c00008903059210046004015541c92080c4010308249a60640003621268902d4540904c074541020044605208450f805008034140e40c51880042c02d255041001010b0341020f4502c01c0764600d6001c0c801d039150b80204400503480440c3c00b59444013148225078029241d400c18211011680c10000c15015004101030b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437808534 1250 437807284 437807297
    0x12031707050d0e0715082a07030c05010f0203041a0603030405010e0f03030909040b01061409150313021203180402040326070210030e0d020a05100b0307050a03030504181b 75
    0xc200304029a4003d0b00141c41c204005031499103009003c80800c842103140e80401d0811a561504603d03207600001420200347c1d03141000300e0f04c0503250200003040403259503503114540d5242c0262403000d140183d22940d0390034001c2e64003086801005901624103071103a0020001000701d6030300200f2000c43d1000948400c45a403034030b5000282540a1841c1c1e403a00850042d04100c10000741c50392140c10b0b104039131120b6000c031074036502c001410300900071002d41200f0a40186c6070420658406140d00900c1c2200040c9260040d9000c1040604c000c001688168004207001030202c0800410545600e4180d404600f070920715114000f03640007250107c0307452074007500308191813002042100d4040350041c100803105045003070700a004001c01e200c01e01107030181403a942c011510100d60524040c0d0001d005000c0b40c0010650540209441860305a1520500c440011507032148585480154002e0700c0d916200c81c03400c00307002c1001650071941242d051505070803003245250024100100810391801c071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437809784 1250 437808534 437808551
    0x70e011803020306180f01292413051509040e2107140321070e0d0605180a0507060305040212030706061403030408061302041512031707050d 62
    0x100031403940000c1d401d80200300801101d0100b209042000d000d102c0100c2d01440c126250082c202c0b04c1d030400e0250740100260085440035030032444400d071450300402840c440b98401100b5080c000c1902014107c040c00030074000c03003030400c10500c580102015203244034000e003119088103441c840c40314598882ca40d1454016110041000508841c1003500401c42c0728032203032108504a500f0804e003ca545240c2024034500791840801039031218030000c1c00c0c034121b420341994890341c2e60200404810030405c052220340c200d59246100e03a072680380200301c000ba80b424044d00d0f00d984d4035030b60b030f6180010707a0286414100041d00001c052044403039501e4005220385407440003d0be10650000854458440400d40105200f501d51012040794001c0d0796a0542c0540a030501d40c0302c1c0101d124400241d084440003441e081f891221030500c5034070091001400d01c04041c5d1000350031819400c241c02401107103503900c08040e046a8564407100c0f02e114113040701d1420b00b00c01400d078800c11400c1c103016078840e0001b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437811034 1250 437809784 437809817
    0x31c050f180603090c0319080306100302250b0106020609120a02030409060b0c1e0c01110c03060429010f140310050c09040b0607030c0f080903070e0105040c08070e01 73
    0x40428078800401c096540e080c0807502c555518580c803411440b9001e203000c511011900e00300e00461032940401c813a8256640c0008001c1c002210701500d00616808000c0d04040e06030040b1001209920000c200d02c031a00c0c541090347c483c0038160800d40c1075500c08802d008070403400080304c55082c50060005552842802003c900b1070085900c8204075a0a10401242038004007000e01501d1040c0000c03294207200e40c0c41310221402e50b095507660560000001c2601551150542000d00c0000f071085604814082c80440e04d88042128181c5031040341a01c0440f103c0d410100400f007994a0103440c4481e5410701c4d03d0701403405031380e100d901e25041402d00d4008480d00d05002d071562001c001c0c2410032a514010705020140d5000111040c412450203400d04420314100d400d4880d11074041e9680c0c1459440c0e0b0f41c484510054a441c1507920304e00600040c0300b00e41d41040a80007034641c00c8010000c55240c6030510042c1e8174040480e200b48080141005045640704402d01e2204109103020040609000c14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437812284 1250 437811034 437811067
    0x1209070e040c03060e01111c14010f030c08060c1917010609061b1a06400506010c0213061703030105032b0806060910020c031c050f 58
    0x3010300c266864040000380680700720910101c0e40640300a000050300214214200c0b4061040001c0c0d60a041c410b00300006101462211f81d03110821000078101075804503600210f80903403100c510100322032000e0007044407102c240f800504408000b0016401c02c0014016640034460600394120b510004407660740d841030000400c0032041e086608000d5840e981c000b40030602901800021401e840070030405c0704003161000d020250400c032010304814540c0c0c0140d140c0d100190840f680b1807040503d0001c0c5003d00d80003030311111030150044c8100503942c2601c40904000b016111040c610380410051141d07000103504c9070031a4101d402c801001c20984150000300003d070804444215400700b2003450000000c000c50680700304804841d007400010075a40704482481502d4260800001c192a1965004802c0c454100d00020300032810701000c6030224411b1440c0c2d990041c01a031000c41284841c2c1400e0102ea07660001416032030241070b0011001070100d1165650428801c000001c400c4404003c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437813534 1250 437812284 437812289
    0x507080a051c0504110a030312110f18090615090d080d14062107150302041805070908010b1806130c02160e01050a031212050106091a030705120907 65
    0x20440c0b404100e48090880180003c580c00c6a811480b400e0b030051030b10b0184054412641d16640d40301d04d1064445d40c000141c480704c004115442030610240e201d81c1401d2000c0d01c0c5040c02c00001c007480074285010010b0b844000b400690180d4486071799100324000030310441d02c40c41d030151100c007405061885c000b2102d203d0f40c00e000c120580307002002034103000c41c1c4850034000c2c002120221045200000c0c0e0f04554131200b0340e108842c1d809604c0801c00ca1030380e41407208120780c06050045c1070603039a041010124072521400c0428071380d5141044442034003e80c05801401400000300804105440881c8042a418100c032000355482000248941e0711185144c43d500d4609900b0700c0300310a07000c4080c2d43c070080304101000c03c0100301804201181882d4816040340d0303005210b080401c0c61929a024156121985401040401c0c0c9459440402c54020a03000741000d60310f041116141640001021144103194285040100107101015901c20107480d60717203085807052903481d1030b4403405500d0b15581c3da = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437814784 1250 437813534 437813557
    0x170d1404060f181e06031a1008150a030303020d1a01021b1210050702100c0f1101090506070207090c0806062a010626060603070e1008250b0403030507080a05 69
    0x21142c0b0554580104412401c840c0d850711b05110701111300305404200c080001600760021a0b0f4803181d821103103d0801c1640003000c480c5030b40d0b003484e82540483c003458031a400c00e42c0469000030744400521403034800d40070fa01121961100b503c680e817200003502c8001244680d022000030848950a40d5902001c007070240c0c0d1464100c594203070800162501030001240c0641c00750103551307080b52200c0158020040401c280b83e0310340c55a00921181550403118080c0b2140c000d640c0e400c2c0c2c0c180040e0003004468041e8007a41c00400e12946840c40c00015115100c1c1d104c000c114213501449601d403110029900030380c551a0041441c5071010030340401c8000781c10b0f0300500da58203000300044c100c05209403407803032141c44100706d007108000d900c40c465481d801943c200e905035102c0c82c02000106d1955410640040700c040003002007640d1030b60007030316041a51410207884800c0901016440968028800c018200350320b00c1800d0174036507180a8954000c614001e001620000344a0b51604e1141e0300300d8050120b01d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437816034 1250 437814784 437814809
    0x601022a030f100c140c0703080a1b0f120309110d14190c0e0601020c0933030d0809120a02100c08040627060f06170d1404060f18 57
    0x35034140c20007078210701103048041605d0202086000301c030481105c0d017030070554004040072881d640c1e80703001641c0559025401c01045c110848590080c0c08a0703084141c0c05800c003ca601003440c101143d140368500241d41c241441d220b180030006019046c808014541100d02d522064520300700b02d4140c0400700c00e0402d40e03025614004003541c0380c6400104d0110700412980d0715003501e80ba04a0355a0360241c407100c1c09a48050500400341c40c21000a0f54071409800c05c0400d40c0714000400c0c100003901d01094100050745c0da184010350b050400144c1008030907841c5c441c0c03090602c1240a41c031030350008116218040002604a2094001c110f90312503500c1001c2c04008511043c103000b000d16505445c2240c0c114140f203800c44ca602060159441c15201210401107200c13110b5440f81d00400050800e80c000c00e44441c0000351400d4101c2452118085190240c4042d402d12100180f2800e44400c08442d02003061009010300b030350040820600c85810305101100311104282c0303000e12912644a030204800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437817284 1250 437816034 437816053
    0x122915071a0106020307020a0b1602060f1c14060d0503071b0501121a0d0618050109020909011b050711190f08011a04050424140601022a030f 62
    0x400581e88004451000c512440703070b600d071401245c5a100e0aa0041e42c00111010b090241070080d030018001c5210303d10250601200701d9000c19000d41248031014a0b000e03000c210048030078442246005031846200041100341e0400c8034900c40d200001e440d103130143c42040c0d051810001c04104447e111074100d5507011107510800003400b03660740140101c0e80021140303a060765010710035000308512141e1140e000d000003112142400010b0b03010300019600c560701e4040202d00c280400c014007404038020000800e48409a00501c80424000ba00c0c3c1001a0b00d030040f0001c01d24032411003550408090700c0c000c0e9440c141d5051440c1064280021940e00c06204c1c0030346883d0550a11760320080320041d1004030780181c0e540311100c0c200d03107420303c25400042c1a0000040d1524282c1d000952080c0f14108a18803000b40003194860014030030502040c2d17950713407080040140c0d011250580d000030248014503c21921a01c040011080401803d074511483c005901c46680d0038084c900907108540d044070511031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437818534 1250 437817284 437817293
    0x10030602030714160201090803130510090905040b150a0e06090a1407020a021201110702060c010e1b030601050a03110f0406120b010f1203051e0d020c010203060112291507 75
    0x84c281100f20701060885000280c00312010055480c021080c801d40079602d480d00050100c0d0b4480050b020702040701155010400d5403d500ca2030703016034050b80c100d042c1f51030006403240350a40e21040c064840c88482e0400c001c81c001129540da402101a0390440d06a00c40240c000040c06003404032240e40091803040001d1660300094226001d4000c84240c803121503590502401c132041010039000c1c2001c100032000141c10084003c0040340700c044000101c900d840c1341810300307080b5988080c4641c29030000d100750b2940303020041d0700c5c09440200c6005000320700d113540309071844400c060220b0059034041201c00495445904c80c3c001000c6505500d20f0b2401c5a183c484600e01c42401000d131100c440d4240491030a6016501c002400d03899181e0078030304150305038a149454075903d80e020080b00c04210a010b05c0c541f40c0007901c411480d000015885e828060005031000080e003001b0714059160a880300c802d04265086041103000c5000c20f42c1c0d5405500d800300d05100e120500d0340f8840e1000251020820 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437819784 1250 437818534 437818567
    0x7031407020d0609051204050d141005070903050132061909090b09060c1204080405030106030f0b1303120e030f0a020703022b03050c01023c0310030602030714 70
    0x80c401d9040c2c41b012906800307040700c41e02941c011560415501070204000a51903107000741101821011520214810321050040e5081101c20600103980c1820420812109005450010301001d403107441c44001500c14101d41c803280b9240c481603d40840204032140c23a44404014940d644400194810f500c40c182a40640400030b004c441f032002c4800021400440403816a0180d114200700d50f18000c0120140d0003070b1000540244ca454208000000d010365091040780b00640c030485e00c0818004050803d0100c60b5401018013030f0031007821500c10002503021100f24011860048005050021410800d1440c01038200d104240400000c1e1752102b2500040c02c41e04880c401ca445443d504201000181100c41c080c905029081d088070324080040e010758003400072005410300050030724002407520001071030410a0115160707032960414541c1440041c900d0840d0254000451641c24a071207600350640040c0b0025101c0b6030b01001180c0c22500c25081f4282e294405403203640c90307110b05d03004000007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 437821034 1250 437819784 437819801
    0x1050a1b03080615090a031407091a0a080f0606100302070c030b0a0c1d06070f02061605070f180506192315070609031101060803040e071407031407020d06 68
    0x90f4113820402030000041c0802c95021207000342140c40f1081c91035488040c003d10541c80246113004001c004580249584174060050120900c0f01006446590501210b408250000da00c6504040c840310743c84400060510b401079410344c0c3e03000d001c2004901c114028001c200005001c0340202034000280040e99003e680640c0c1242002c201c506042c0b4400e86400604a84030786003005000402d01a43ca884804bc080085c0201030300a68040342d5400039001c0d034000060340c90001112b104010921a042152002070103e1560703400565080c00300b1100d5120f090021200300c00e44403030000e19640c551041d00f98051a10b0080c04500079102d11944071400913100082d120074451070329600b21481c041980e000d0750101c119205240041c1522250090700641c0025014040f0140c0d0010118609106c0d510050003c240919161400c041c8094249907028110504002e00c0b16101030386c00c1e01c5141220a4154141800313035111a1445022003d401400806588400c2c0c00307802c2d20500004d030700031612 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 437822284 1250 437821034 437821039
    0x10f110c1915051009060602030d0606020106060210020c03090a031a0601020102070c0311030a17090118050117090a200310060b0d02070303020c0321010e040302030901050a1b030806 80
    0x5160320901560881e01200003a05000455040590008941c0d10090300542a00710011916494001040a49602c0d51000005134000241e0710520758039481010050940c0784004d0002d6850840700956906182442c60441c607400101100f03005410022540860700241c02000495680d00f8071410518080500006500b680c82c000346c41d5610601c04c4441c400da200400412081c250340b039107083c00038400100754040c130401c80c0007404686d00004424041455640056507814128001084004003120182d0300828004080c880c5071703000320486c4954211000c07007503980e41d03c01c040d240ca01302c68070b1400707003458828410b0706203d007000604160316000141c04403110209000700714402c07508103101e12144140300740a81561030940703800a00030240a03150141c00c10508154150666003e0542c0326150b0b51481e08400300202440101801041070044201413441d19840c040c3d00c0344110214203041060004011030800c3c003030401d0100003144002c0c05801082c0780d180242c035a1600b83d0f031251 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 437823534 1250 437822284 437822293
    0x50a090924090b0904030f030209180a0605010314041b030b090715020309031c0e12070303020c0904030507290403030c0206010b0403050a120509060c0703020118051f02010f110c 78
    0x24050310140100c81c50f009014107810190b984a4400b190035200010000d020140c0030401c0c0702140e61507520300700d02c03d192044000c550f810101c4a1504941b03465010314181030809104483c0b14600e125200c0e0f0080d0000310799800c1030b09441c00c560030811103800c0100142101e42c18411540c02c000f89001c1520140d0407200c0415084840580c0e8900a400441c1d5055100c7d000020014200520845032100203040c031442482d00d640001e9815501141030070303440d42c0032074000c005141c0c0c1041155020501030711400018281074034001d2040c8100400586440b00d460301181c0c3d0b440101c041c40031103a08150b03506581d030502d868010094119198400014420b10001140c1010307840101e81c1141e034070400919000c0c1580d0f482c3c3d030716072090440100500600380486010f40d16044028541070040741c4c00392084904501c00902251400b1002c146039041611050080e03480349a1004904d0034040d50703440448002c500128058200c10a401d0b04e06400c10820040e40c1ca03491005d0010307105e43d08283c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 437824784 1250 437823534 437823539
    0x909080405211b13270311010c05030601080c1c092907052205030d020d09061d04050a0b0316030c05100e19050a0b070b06040b030706050a090924 64
    0x5182c1c1180181a06501c40d001030398034400c181e080e43c0103150300f0341a81000c050440405d4810030b56101d100c0e0017075000c15070540c421240b0312420f215041c0e00d1a11030418a00354140000001c00750440103141e5480d15100182c06528004a201392a41c2c5121300308040c00200510702d08130f140c0c0075004500c282006041003a0f848a40300d01e02e0501d2103480f4075a20701d400d082500380301d01142000e00305100800500d9610200d040c1d102480440d800e0300c1d45800502d12480111130082032a00540d0041c4c0c200300300c40303280c82080714001c000420281c2e002c0384c01203400e0726a0640d1134000d00c0b04070640b039458459132401c0e8140d0105c1c0b41c180401caa014030b480782c8a00b551107091040e0a1103440552001410035025400c0500d40000e402d8843c8490314950400e4079212004681601c075681c100040c07842001c558013080143d5155650317441035066800f03016500103c004a5521405802480123105011641c1e0074818402e02d0b860b0300134040f45205001c60001c441000003209920002010b0340803159601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 437826034 1250 437824784 437824813
    0x17060601090810180221060c07030c0f110d110f220c020a0f0501020315030c010c0213151502060c0c0a02130f020a0206090f011104090908040521 64
    0x281d1085800c00000340074034490603005100209001c02a00c403d0351407039032010b405070f180c80c090700984058011010310104001048070b490300000070070507548a4400c1081d80c00103544005401625a4400d0704448400807a10300403620b0b1002c8514180c015481c1207040f010701c42a00c00b9010812410384079550901b105038140403030400e10450340c403036492168510303401c50740b0140d102c10341c074903414070503114a071804da0348683c050301540f0301c1035400e6034010041c09040e0140c0c0b41003640c900e008400514007622188000b03844c072103034510060310502c1081000410340041c3d4020100000c103210900e84820744aa01c401b0016030352070701e03900c0141b09a000040302405450203d07000c0c0c86154008280c0d10f07100d0382c01c002c48181c000000c940e2150701e41c949104000418005024044609e40240c600d5142a80c400c0703290010030940900f0720780c108084018011483c000700e1b82a21050100400c42c600641040241d81c49580d22503030704580d0811401505421001c0000020880002a00d030340c2e401c070001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 437827284 1250 437826034 437826047
    0xc0201060b03060f030a05030a0c060b06191409031906050a230403140a200d090b090406030c03030c0614150405040201020a050d0c0b0c0414150f0417060601 69
    0xa014601c074002c02c0481c9a61610f009030711070307a04004080329841382c0b1654500e4150380010304143d0100b004081da020422500c0e008903014484242d80003401c26a07501c0c0041c00c0600344006240503c001b41003200c04a403001800c994420701c001d812030b080150b00c01c8206400904420043c1c0c0c91a02c0c100200700c11068500a500240010440c9100000b51900407480c2d14040504100c041c0003612400441004c0c07020040d01190b0703641d880345c41d80c5450360029286d0340131a04500c08119080540102c039800e410440c007606480e0099034458a68600c3e101180c010444e0381c1002e080403139a0342c1d00008040d44641d0003403116102c1e801c00c0c030851a034101c5c0c3c0303089683c041c0c6810007000d41c10306030340c002820507601440d0322500510451319207000c5612902c1c113204000c00c03064005011615100140990401c0e020b0304680300c51003140c030301868110225902c401e48541944110554941c8081184921094824511084c03844503900c1da91460401c600390341103540e04c0c51038012240025807543c0200d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 437828534 1250 437827284 437827289
    0xb0a1205010317030c0d0f2a020d110c1306150c0b132402190e030604080a051b071401030e0d05030901150b0c06100303020a020603041a09010f0c020106 67
    0x103c8441507102803952940050b0001062402102818010030140801501504007100940c082c0050b1410081140c8091090b45102503172880a04204887c1c0569000940c900903200918141404010a041d5603041c9816030b415503500001140b0241c108850780d90000c1d00701c804515000c8040c0b2944c1201703850714101c2500250001140070300107035209a95005195450340b02d0401e0509074804e0f00100760b002d0190108018101e98082001ea142040b00120b40b681c8004078140b449400e254500040d64408004000401404021662014190040d42a1038809070300217001c410000765520502d541d040140b00700114101c1501c40c01d003080d4080d100c3e201c4c01490590142c007100b0a4620180e546a00c00340c111401990f8444c007a9203000500c8550340058010390a00903518554641440c0c500f6102410490b135040b9121010800130303800041c50a00158140d480343c0e100d50b81c9040c0a003003a40718000c0710140700b0345041045030819040d030100c2c41ca415a82c0042107480040e001c120300b00e44150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 437829784 1250 437828534 437828543
    0x703021e04050f03070305150c040b0d09021903020d060c0e0907020c01120c08130215070b101707030f0f021008091204050102030702131104030b01150302091f0c05070b0a12050103 79
    0x43c3d904580180c0e000c1c840743d400989d409205142035590700e100005984543d41c00e0f22714a503100010303011843d00402400c1c0c0e80301d10030030a1340d6850540d000102d0122040d0f80080840f50703100d04580b0303218003c5d0800420303080000d00742d00107481d108502a44500c0391004841c00601071100d01c4c81c0f604424852410074200c680e0b0703807003c3c0343d40d03185a1040c140c0d8000300c260b9000301d400664014802144d030040c50540c0c401c1c100c4012a060003800c1003840001504007540b01003e1000c00c00c80790f540000c08008407500803900340100e04450a2142c0003100100004c0e40159074081503519140d0030029180c002da9001c001c1301d1b481011000c0c1200e0301d000d18080c50b070050300100818400b500c1c2c41407070b2071416211420001423600da52a03094616074030662044079036000e840c004000d40d41900002507021042424254034123803501e00001d840202c982c2580c0445408080302608540c8615070a0603001d03441011101e900e0380301d09203088030f03820024200000410480c000742548005005680c12241e01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 437831034 1250 437829784 437829793
    0x90403121a031f050c0a02030304081b01050112050d18050f0a09020d05010f0603050903040605030915071e171803250204180201090e0703021e04050f03070305 70
    0x501400340060489140000000101507000070700d00d5030207101c501004800059a0b40c40004403201d0780c0e050300c50040400100c804207020800d43c1640110032660f1280e44100c00c031340d450039418400c041800c541140f00a03250301e0080081903480c20f0711021f488a6003d90100c17602c02010300000c541800101c91850651821031000b04041e0611034a03002402000400c482000c90325440d229007260024891501030f03035180c00040084001d4245118054400b41c40d0501142ca0540100c82c0c2e688128840d0000b0800c3c00800594403400074040081480c4600111581070b0405500041ca040303a01d40b0701c0880c25018000d5006071500980d05e411071604c900c54943d6903a600c6240c40c03000c0641542804182d400f081001d450380c4041c074205c10a00f4102622580201c0d07885006110445031a822080e002d210840048030240c0c2e00038005a044900990707102a00d9a00c0310012000781c09100010309001ca0341140501e03c0502c1ca402900035150103442031600d40b0108402c242d03a41c1c1407440081c00c039811 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 437832284 1250 437831034 437831057
    0x20105030612030d1d0a0c0e190213050a09020a1407050313080d08010603052502010e0d03091b0506070f0201140304050d1101060b09132c0c090403 65
    0x6140510380c03045009100c0038241e85407641a5041d43d100c0c070054003942c1d940d0322400449034803110601d1803401492008110355625070743c0c2d000a44006001c0d8601e81c414010000f2041a40e80325040e0660040000c15901c6692002290001280b075024480c4102c041c0c41c4003084801c5580300b03607101500b00c4d990701c0f10340f58054038101a0b9507101304030503205400108038191100d00d00228820082c8100e00c018640c00d0350500008092410681000f410075003020706000ca000c540070303021030343d126040445c0c2c1c1d44505000000c0c0d0041c050b041001c28039000c5c00203284d101d240c25501800090b03005002d14070b404c04113540d01a5600b045030003400d500000522060000c034483d445c3c1071042c184117040400303940c0182c1d000b08549030811581166951702251380602c1d07544e07000065029907100400203002c95820401d200720507009005240e405694904201000c00b003003508404000f80032161a1040198881008400056024469421807080540c0303180d4a04080352401c0c8503c0e0143c1d00c2880708907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 437833534 1250 437832284 437832287
    0x100e010e04021c110c01050f070e0301090f0201180e0a09060608030307140f0903010f0504062a050c0c120c090106021515030309121b010c15020903070b040806040b0604090f0201 78
    0x3ca64018280d0350424010108181d40c00d21495000b01980328008c1d18500c3e056100800040305000d04600990404920000095015003034604881d424200203c4241c1d80c0038034010382d450140d001d00100355561040c00510350380380d4402402280190402d20015464080d00356507844240d4040001454094001855030380304800381030040e41001480b89084040030001b802d40d02c0140b21444120355400c184810050144030300400310154802d100441070b820350200b040e0420356a01c10382401400a4042c813088420f00800e120784070000c0500700202c880032880d5136254455520140214027000010400e03034000100c250311000d01544542c0d455903503810703101040b05080107041d0948014001400c082d9150400301800c03002840042c4030402100c2d0809000d0b0020358050750610a100380184040740c1c0f04000c07445481d01d00c0e100940e4820035500440c5c03601d021680185034840f0302117004200602c2c0030903414015405040420030945881d0200300455000d034900515031000d0b00c1c020001035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 437834784 1250 437833534 437833541
    0xd0c0506070c140109151406150a09080f061008030f03010501031a03030d1a04180b04030c0b190f06140f061b150c09010801140f100e010e04021c 64
    0x452142c0e03d8010a801407185141c00c4d10440c1d0011903400010f50003204064041c0c3c840c03640080c5c4420300c1000307542813074008a08500301140d65010000b90015886a2060107601c540004103100c00031900c0302e00044600035225441611004064600a03000042d40c800c000305994407046400c01d01451a40782c08010741c000d03e649801074501e400520006da00d0b940e000e0000d0f100e50301c104e400201d120400380c0c5c50804414225910541300b1861301c400d0300c101c031085000c040340c655030200c600009901e69080556400b80c804d00b008041c5000d040422841e68111004c4011422641c00207201042040084809480f03042c0510154200c02200ca1565490851095039000344081c0c070140c41d1862440300c03d081c4403d2041c13000a25808101c04c6801c0000394480b05500c0850700103080d003401d45800000b0714130f50f0107200305404080e100c9103040c0159522004d100411710010040c5040f00b09801000d0015224008100e01089200e212030441d07041034000c80e502c2d80c241a034507401404001103c00000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 437836034 1250 437834784 437834807
    0x2031009030819091e03030c05181c0507170622030309140303011d010509060f060a050409020703090602240c1c0c0206060910030215090607020d060e0d0c050607 71
    0x2250b140c40c030480c041400e417520000042094807001c0c41042480c14080c0545000e10f0001003000307010000003518810741805100d40c201c0840300500d001a04c2c2c9090440e810b0a081c0142140c020070710001081c09003440d0703007800d401181082e0741d002e5032044010f070100508103489040640800c4170400021b8802c1d40640e030b1241c4505480302e4039008000360070f803843d00300741c0110081c4590b00000a90f42103106100d1030040508546007901c2d85046004240519860b480702030080d54080340c103041d0300b401042942c000d80364140341151600c08605000305560400d1113108050b000750341d8488510000800005201c841441a491540d00e0b0340c0429901580801d030600b241801c1e12580d0740b04540706014500142c04658020131103410010208010048050700b800102c0022070810001600ca040d900e42c040e84044011503107801c90000402d580f40305800009600c614010295004c11841d540711200c000c2920003218030002c0000c1d015184103600300781c050b016902c1400090007051049030b00081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 437837284 1250 437836034 437836081
    0x102190201050c300c0a030302131d0609010b0703022517100608031306050702012001090605010515030411060c0d020105160306060531060c020310090308 68
    0x20f81109011141d007403004d441c00304240c649541c14807011035242204440305800541010a107040c2030019041d0f5118076008000301450740100300341103aa00d4845003080140000c4600c0400d03240b00726504c00c0075441c00c039440c038803909440d80042107a480317a105642e582507151300140001e668015400010602c04060780d890621200004600320814480d265000b0310004020200c6c0e000078900c24090381d28a8101100544c81407007032802494800743c00c4c1c1c040310054100305a4811250004803505480005032404000804400e0350060b00154441c2a5440c0141c2080007240d80f95010403010301c802107640a0000014004139020a010181400240000914045c603169060200900b08010000b0760809030355103a08000390003c201349421031700d0143d403a0800056040c504003400c60b01a016441d580d80341d1650403a200f0480c1c0345c10b0703201000020030407071036000e5545000910450791008200d0090043c03110280403c0003074005c0c8891541d1686a108440e40c0d40d480300351500001100c00603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 437838534 1250 437837284 437837287
    0xe010213050d0309170616260615040e1509090607030c0e1c0c0608010b0706180615210b04060c020c04020d021c06050d0201080a0902040903030504110d0b0705090a0e0a0c120209010219020105 84
    0xac2800c03504010b00060803450039014089ca4042c242c01030703401d01c0003145405000840100814004081115036018400b42000030380d104000f513080b1580e2101400742508040c0c0581000c0d0010104600c441200d4800d995112416480d5042103c00c0e079001e218201a0000611540f00082e038641c008904268505a02c1305c0e04a03940c4c0c0300e102c02c0d03945c007800301104070030500c400380b00c80105540035520011102d181c0e083c0396519690340c2106c956004101508240d074540b910f10302c0f04d109010911120100600541d201c4109071110701c02580000307020442d00700c500d0b6400c0b1400805005810031154014500ca041540c41d800540c0d00c648000d20600c0441d40d101c070900b005030358510440c0c6000d0700035600015649824a8510720540c5400c2d40d180c42428100341e481e000805154034613601c24280d15023103071546003900101c5c500781229009811001d24078020040c4a4810703600c1501804a0350b1b480c08060034141c8842c504a01c50100b00764016084010100c80703d8085a014801003441890480d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 437839784 1250 437838534 437838559
    0x110a0c050a0f0b27030a0509032d010c020f030703050307090f080a0b0f10031e0507090b090c071208060f180a0e010213050d03091706162606 62
    0x822680146108441041030b078014800d00c07030070a00700c488190401203004a00c0905181242c1e45d2030085103007950400000161070ba41c035842c03d010810b071045007828220000704000520b60718950390314002c035015618107200e0001180c40010f507290041e03000c00c00f07940790a445442c116565840140b0000030f00c48171060009074210000b086070000c01c10b040250289540c02d181918511001801c010a13109085041c0109000300000e48000c490344a030880210040400784002c4800341e00c1c1c0040d059010b1070f0381c00541c1c0a2035402183c5405c00c21100f040c0140d850102c5090503005031140500121445603204c1e80e11384c003808069400c51001010102d41c0c5501d6000145110020f8049465a586080030310080035030501509650b440424000d504090b2032158084000c0c11f64401c0a21070b1060005800034180a0140c080c0a45100c07000308240214505030303165651003d6803100b6017040f01180683c05180702d40225084c0a180d010500c0384c41c1c81401e0b1340c5078002000340c02c40da80400c846040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 437841034 1250 437839784 437839793
    0x607080a090e100f1d0a09170c010608010c0c0c1815060f0201060b04050d0201030b04020d151703070b010537090b04050705031605130621110a0c050a 66
    0x611803c44410f000070071034107090013254200c400e9407016a02e4204001c40c500702159801c16558400310005001500300c44509143e06014200c0d104444040d00c00520403000c0141900402c05440c0148005e00c001c0111410460b480b004040e4040c0c582c8800c044148000300c0c810010110b4070b14020320202e42c64148600281c914502d582c42880401c1401e00c41c1401d494080c004c00e802050000c2040d428246071402080040b400200e0081c10942c1d602c0e4420059903035036042d1480002003030030410529407440c2105440d0306c0c05000700c4041034903000c21903415040000c212202241d000c13054400591801080c4545940503890360341102855051500422421888000d070120081410071948c515040c010001c940711080080d00607406c0408101c042d58120307086a402c210003003100d26503590700760b0084900d8002c40904030440b110f616400070340d150380103080c003042c1030160075000c0c400e0a00d101c04c030048541d0313800c07210002c400c14000d1008440c0200820500180100282e41170799509907607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 437842284 1250 437841034 437841059
    0x1e020109170c06060a03170706180803010303020f0109030207210f03080a0f021204110a090212010501080a0506030d0e01020a08190201060b0c0a020409061d010903031a0607080a09 79
    0x703051006140031800c4803000500b0030201e50441d20540d071501400e0300310b4842c0d90484813070341c6540600309000240349007080b1146c4c3c810340da2a452540030040c02071641c0351032240d5501c02e2009600601c111166415031580605c91407126544c1500200310043c039040a003443c640b00300403c2a508900140c1ca41c0104181a4403000050710035a21101ea910307220b03030700d0f000b00d420b420142c4148138411300a00039020040c80300075030811b4100c109140207003840d000061148106802c0b50704500d00104090019501d0849440c0c1030354002d0300c9180d059550342c4010700440e06c007100c11760761640c000100c24581901803401440500c0061041e980d051003d5290001940d20441202400c2c0000507501181c0300c0c0d0a10421001e031403100c0000f454061804031440d41d916a50002a1080b42d076007034507004001c0980d00400c503904100c10a04922400e001c1e8250003040a0581940440e040503004c0c6000d003020803a50020040080c02d0700e003070440035110310b00c00780c00841c654410300c002100e01041c8a030013040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 437843534 1250 437842284 437842313
    0x10181802031504030f0c0503120c13030503070501050a1a130b190f0909120f09030b040b060111070501051b0f1516050307080103150b04110c1605011e020109 69
    0x7090302da10760a141c500240414030141c000002c00481465020002d40088200c0e0304644c0c1c4171603010015202d10303405800030300c1071030324613001594010360000c1000030100c0903100d914000c90007001903540700185402a41c3c2e281d5584440c80e1540c00c100c101910f4590501e032640c5130708480000d402e600c1d000100f070348122030344580c514460001d1009c000506004a51300b014003060201489607481c2d942d103454048114142500610002074601106a4490000e8a00440d00803010a4032401d0070301b0850074001040e11028001203201060780341e10100015080100c0344181e480b44d00c1c0c01d912054491030010460b03420070b4a40506800c138244108100664a00e040b03480036440c900b818841140c2000400c40c40e18403080c018180100202107812042c2281100c3e040114440c12240c3d07401003000401d609402964082d02c2d20316540007048910015059404496042703840160414030a00034041641c85881e0029030441030f07c40f840100541c021403044428000400d44000f82e03581c4c1080d120101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 437844784 1250 437843534 437843563
    0xa120f11040e09011401050904031e0f0e19060507020a030b100806070f020c0f18011413020c0a11030f0d0e0103051e0402010f14030c0a081018180203 66
    0x310381030108464900031250003c8004000300004000d001001c030503500d051084c43c3c451302002c1c000800741800b41e8001618160720280880000010f11000342400803a00c40000004120441d111181e041070700310a125281140780c408120351a00718201d45036801004206d8000f005000d0002c00252031002c1140a00d41c03091a00c90343c40d0400828518015004040700204180d40d81c90200302ea4001c54118003003602a00d04481010320b68020801940843da00210060031701400002c0015144217130701c0c10080105c40c1020f0007048204c0c844141d001c4e6000c2210a80c00c6101c45100044403800b001001e214068181d030b510307042c109165414092000f481001003004020010030a40c0d1512855511450300c1504000c048003d02100803d50303401440241840400b1030100101801200341542c17000321400040d0b924a421b4110b807502d030300051302503c0820034000c0801c00700726070b81904100751031030390114014542c501310749030000d4a02d0f0154004050308915004026031418840301e045609075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 437846034 1250 437844784 437844787
    0xc0a0b070215010b07080313150c080a1e1a1003050402010e0d230f07030503040e0c0307080c0f090405040807020906010807022a031f0e01110a120f11 66
    0x40501030308028510b0b41d42ea008900700360050040c5000d01060320344182c0c1100311640c403580c948030500c0f501514550042d0001c107820307a03100ca000700107070800740f942e407142c0e965001035456276030b030007401d80b6a24151404405000707041e00051400903449204840c2406002d0900008014082a0700d81c1c03240c683d0400003600c5004020540d40c12030240a800e8205641540b401403036601c0700240c24046903009002c8210880740503100d10b40400c041211411040c06558150b40d403840c20a03501d130701c64441c0b1b14000f107840c800102c103e200d62060700e11800b860345a88540c1c0e0b0f1906000d40740d0b80e02403180c400003100e041c403404540c2c0d100ca1284c60711452250f6001a503030190345c01004400b0b5030081c100c1d0b041041c90810408842e5012451019401041d03550950f0000d6495040600c8000a900d0f070350148985110143c400b00f0a0b078061200c650f04060030400c1e6070341c0d01e61701400e0700c60094000340018803c00440b1241c511407801788a8071a40e0003000100403910300800019103800c5030054181c07410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437847284 1250 437846034 437846041
    0x11061918020405013c150c12050d0b09091e100609060302013e01020d051f0f0b1207021507021c08060901120510020d06031109060306011401050c0a0b 66
    0x10a00e02402c1200c681041c002ea80340d105881e42445e04183c021001c202480c0000d40e00b9141c040e505aa1140f0b038054104240110440b9000b00f49030010040c80d00707511304117002070b007560030900b0301300c2d024600234405440c002188880100c4808443e1180c001548a090721182d081e0303940e8031617903018140b01d6002203521442c600004184454440c202036000001315801d0325003c1c070000c500b9040285800400c02041140c071040360081c0110658484810b0078501045a12003080703003c03c811095160b8800152a191031020062a00500418040c1c050801110354414000200c1551240c000d204542000c0f80050481c02211029a103006c09603102c160003050f403010905500449490a150907005460300c4800039510030010300c10001a801c401801605019081c459280254880d003001d6590303444100910f0000c007003a00c0151003050032000d10059a19025010700d01401005004002c240d00f0804001543c50103010740b00d06100301004031501c51402484802d800038004c8002c140c0700e10307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 437848534 1250 437847284 437847329
    0x5060f07052b05130e06010e0d05010c08011707230d051c020c01080a09032721030203071b0503100509010b0603090a0602090301110c030306011106191802040501 71
    0xb03011902d02c2060010030320422400070107800003001110b60900c103161690300c4181c0184d5030f1b14039400c0700941044440030041c0c14424150021151013540b5a84d003007441c0e90fa41e906400c41b600030b0560706100d4000039001c128820404100f10313000c0e4560211070031043d02d40b1000495400c48640201c03015040242d19001d00400d858540800025500203880420b40410000307080502c000c010003082580c0b11602028188901460200568000386d1003030b1503003184900355102c3d0014401c1480078401402b103214001c80b10a8100015640364000314102503003603441e1a900c01c00314400e00d8982081c8400000c0b00d40c0e00f081407451064250f0b1002509043c0a0129825610b0f50745c001d40c010801001401003200001a008200c190400380058554810000003400b420210f26047c1c0254800302c0e010b40304038804070045010b20000d8844042c0601c01950a41c1c413070204580a4080300001120b24000740f2007030700300c00c0c4a201502d08028104c201039000800300c803c07c0e013041401e070588074918407401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 437849784 1250 437848534 437848603
    0x506031204120206130b031906060c021503150402030a0c0207090606090302060a0912060219020115121a040b0609090f06071b240b1905060f0705 64
    0xc05800c00040e1400d4140307100108010003000c0028024000051491000388044459201070811454819981c3c146007068070b8046076002c00c0c2c1d1406030303d03001000a901c2d016140b101c5405a026291000710801490b8480d4207403c0201001702000300c850200d180350b41c03648011482014a2400000c041c01d070346000030f01d401e0540c0c00010034a0300d0554203220040d0003904910480b1b03412218282e56a5055078100c40a0b0308660014004030070380c000840030444c107500500904503900c08050b1041c0743d2040c0c1242a110740d00381090840103006010b01c030381410144103415079401500580f9a0301c070400000c140b048000c03101510450505401d10017146040000c5540101070fa4000708086003100900645403000a09138030f050010f01e25044000303515400d00314511a030480d00c010801c29141c1080c180030b062411400200350b1402000e51190301c0c0c140750b5107038500701c40007c50004c40c0c145020300101c0d610040c07540f100b800c428080000094001c025201101a600031945c480b80103011041209 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 437851034 1250 437849784 437849803
    0x15032505030609280b07171609030204020c0a0f0c031704030503090d020d0f141608030403020f1810030b0703020c030a08100b0c06100504060e040b0411060706050603 73
    0x1e80c111070180914504000380a061001c540d401c6a0921254001900d491610803200100707401d59040402800e00d40081c10454402421781e0391030020b54810385403e8000e610740c520000420020305e818005414194003600514800c101241e800408585481d032401203150012191009016401e00c10003020400c061307442600801c0c110704180c116611103469004889100d4056060003110700103540e19415250b520b141c2100100200c00507500705006040040038141050784034481503561102c1c0e801001d1002c0354200006141018116400c00c0b0030540e101e04080e40c417000c105c2d007084080c0840c1030b0300c134000c01d0303249180310f81240f440c505010800d20080005040c1481800007844502c000700c2220280515403a1100150740c07a4404a0010381260b00604800d00d00451801031982001602902810407100074468055030f640402050b11a1b5008003280e6422407404100003820b00703842550094403500c211001c1030004004144607801150f82070f034140d03484600303110007810b0a214a550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 437852284 1250 437851034 437851039
    0x411040507140f040906061d2205090312070507030f020a020a030f0507080d0c0204050906060a180905030a031b080609150f090f0601020d050a0e0915032505 69
    0x1481c40c05071030180402070b004070021110360300091005020000b100444010b0142c840e01045119181e81000f0f0404030800d019440ea984c2181c654082e0380b800d8699006022004180a0410b640070060300c0003502d005465010b8500c01480b85141d00010698241d00c04d01c41992000c1c0c8502082c100103214006401d800825504a6000c120160700c9240b042015a82c00c8103221240c0c03074003450103070320f810b180c0e503c0b9220700d00a141030000c50552003021030906a008860074007254031031032011500c0315030540319958040f2402074200802c441c00070191204164611002410310f616071110307800c1da88813607101d000107541c031141d100c0396500e644090052620145071512162034440c0100e20305a03005000c114010300314074100301255030b03000f03094444004080e0211038a81882601c62241c280d05551460160040000920107031b031143c000d6841045155a0f10340c0c0c111018010305c419014050301800c540010395405001d0b61b142004120b03001c07000745c0f2010f0204140039600031210700840d0481031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 437853534 1250 437852284 437852291
    0x150e150a0f06120c020a06060303270506070311070b04031203050109051b0d060b04030807060507081003020409030c1a06030d02210a03090c06020f0c040b0117191103041104 76
    0x49607600814000c1c4140c43c0e000c00143c0500400400d91403c000048001d043c1800c0000c00b10400d030b8440403190aa00685452504442c41140710380c140c0d02d40c0e03000742d40e000103040c01044003203481000c4004047d4070040582d060319807111403440e4660b016400581726580c880c000310000319414400c49006141c4414104040c1c01e000340e080c2001030560341a101c3c1d500b00032440b1070034010726511890062603c8200b0543d116668580010036820012007515428517000008030124000c0e8001c51091050080800700c0303504540c00c010003800740081c2902000080710035000008c0b083c0b00000505086400e5410807454140200b5140c03e54805206085400c600c1c9401c5455034440648045448940310311a119a03844008a00920301054042c12a403491140015502d402151107030048540c0c0094604000440b8184420364140030b406900281c06210b04140e51f440c1c00b000d1075000314030140040806242615544141e6211b42c951215000f0000140b00400110350104014030700300b40e4003407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 437854784 1250 437853534 437853539
    0x7080705070f0305250c0501050301050918031c0f0e0c301204080d091a031e010f14090903031902070206040b030619080d03150e150a0f 60
    0xd000740640c080c002c0c201c0c003400304500e04042c003c83c140e0f01d60060320001c50022118400c112185400c128400782c0e0554110000415254494030807a030503500080c244032241c2d2a14010f8505012540c400c1c162940024000b60921106074580d00c000c008502c0000303c0c030f0440c225402000c4511640f060501e070352203807072031907030589608003800c40d003d48002038031504a10150103c3390319002c5240b01d104600860001841440780000540305071860441113a140080d002d00a03516071400d40100f000122481f04803100c50070340340c401184d019110b8104044005003102c090701c0400e400703802c41d02e03804581d802e05101c580c401d1407040d001c0710400c540019042c00d010884e15100c4c8800303040440410751000c0c43c94040191a0115612264040d0005690310790340d051001c0582c02c250340292190740c100c080c410f44d491050044005682211000d0a0b0081551078140c005010031082522000040300d07000900280f840f074107038440c00320f50850220b01c43c0d034001000025403494016018110595005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 437856034 1250 437854784 437854787
    0xb1803060603060a09050111040807061112190507171905030f07082a03180f060619030212010606030b0616030f2106050a050102030f070b0c040302090f0f070807 71
    0x3680d0000c120460014044945d82401405400900d182c0011001d00080014844100042c4042150008d5642510b800a1040f1041c1c50341351003613040d0280a000e00120310480400c140c05ca151002c00e00341145840c0c200d60340d401c00c00300803000e504180540480c45640781104000c1491211040d454410320b90314000400d04000a001345c4201304000417000002c281241c003910905103142128400070703000042c0d900f031240503030003200c0590201c002d803c4d5801044e00e0003e50102000241e00140c00c6076519901800f10b2038451a00c800e1400001d400c0010150311b811140d000c0b50240d50b4004503455050030009002c0d03d28410f03126001d00f07003c100311010503102e44083c06d452945442c1c8507003000080340c0300f2110b181c08142403151051020980050000300c5620001c1100c009490300303001d0703e40d02c00069031640150300c88007640340380400040780080e000344082540140300041d0709050507180d80104000b908112416142d0100c000180038032007211900103a44199145000000c41c03901e031a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 437857284 1250 437856034 437856043
    0xc16030c140a150b03010612060507020c0904020105180109120c0305150907060f021005162309012006010b1201091503120c200a1d071b0b010b1803060603 68
    0x84001661130200440954080d00003000904412410396107518241c20400c005080c1942d103000903120300003a5020b10308100c0301c9688200e0b0142c6400c0d042200d00110400410b92171040a810071050020102c3d20000d50404445039602403141048010700f10318040d403902e550322008001d005000002c01c0241030f40043d5540694a030b501d40842c0008159100303915068510044000d1a800d15040000851482d4101b06040b8107a40d00d48029800c581207103074400d9041c805040c5003103c00c00842e142c55000d911010340d91680341a1002e5030140c00f050281c20440c080e040b001c0c8241002900600110b60742c22150b01421b10410100048144401030101c40482848001c1000e04c004030580b110078054401045816080f4054201c50f42102d40030109102020324044c1c4280785403040491245e00544550816410b0000703544450384070f002e416505c040c40d81c4040a403114841ca40403001a141034041d034001c2c0b081c00700d81c030303103030000759001095285891100030302980c400010445203560004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 437858534 1250 437857284 437857313
    0x30e0f0a020d030c03091802030601021c05041203110f0c0901060e030c10030212010312030f092003030f0d0b010906021b0f0a081f0b0909030f030c16030c140a 70
    0x10700f0206104c0d03038601074402d0300722940280b110758051400c0384c2040203550003c61013907000b64240c1e1a41015072821444400d50f07000d0020000e0004d100501070b03c083d4404903c2201e0284c03c0c0a020b40d041080110301e01603000d40c8414207600842c4a0f11211301b483c1c11240d003d00642d0518250001c01000440d03030300c4403480201842140c3d0a0760012140e8040e40c1250f9000d03081c2d08c0402d0081d038403030500d401d4400150202d040040d107040380d0481204c440340310f241d040b40d40c468516456a10300342c1d00544e00a00c0350400d0fa81c103010400106116201620007009a010010408281c0010715000903080103003981c0400d003550883d1074040144401140c2801030b24500b110100410700e8441c003c1000860140c10200d07071842103c0700e518040c01a80c03030b01100d0b070b030300400103000340d0300d120062248000c004d1715564101e5009210110a081d0a00007550b4800082561941440c0a4180000c41e5081204080d8041a210101802407005c2000c1c11048292950b000b80032402031695907100810519 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 437859784 1250 437858534 437858537
    0x9040b0d05060f0c0c030c0d12060b030606031503060a050115080121030509150d05060303070804061103160f0c090209030d030e01090804180507031e02090a08030a030e0f0a020d03 79
    0x90000390b0110a02017034540a501d00000c6a803160701055a0580e14485900f0b95004100c070240005c907020344502a0740d02b910141d215840c1503403034040511206800140020440d0500910030882a403000c100c1a4820a4001c1002c07410303514048503a9624481104450108540c1346c0c014000c89403410211420100170080c00003000005080446607401210b03501588140e000031032660510001001d0011440f00e81c41c1007000c0d4961404150340c901c65640300803c4108140820480140540c40e001240c09601040d43d01e80010301800c00743c2ca041c1c04000300c4a16080b10f8071001403041480060001d824243c2d400c500d01406c2c1000207564641040290007010b88854090021210a4100c150103551100c0c2c003c1d11191500d03111612130b81c580c0d0305d074051704d49080001014207200e07016a4100c051481c2c3c14090342c81100300090040d500c9084050342200142c2c50024020100308014071000304d4a0f54000b400c91003a4101c2414075043c41c521030103a0340000c21000150303482c1401c074084940c0c103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 437861034 1250 437859784 437859811
    0x913121d0108130204020d06240801180e0102120f0601020a0b180f0106170d0c02010f0305040f020a0b090a0f0305120723030d05330d0b040809040b0d0506 68
    0x11680c00803c0d0084101d00250040e0010031000d0300c2000d5504480d00f90b841a10040d80e440c141000c4020f4040007004441c07000441040042282000203031030103010003402500420030041d01e0031300a00760b0340104040b0403400304800c102f0510402003e4980c2d000002440039059030201754969441045000d0310104424104030524450035204024408a081c26030303000b0b21110b40d55141c40d000c11186061184414001c43c5900541148100410031090f41c1c143c444013406018001c0480050100800480310aa40d501c03c1070301690714158808020062003034180d40d6020800300707000d201c0320b241e8800b001c0c02240721001d00c00030f02d02140e00840c01041d0280ca584589407400c02c0c03002e40306034010703540c52010300388400441c810300880144209ca040640a12898a0740c00c254116101041001125040c10760501d000e0001c00003004040264010710308460030050340c880d440820345c1a01c0440d40a0800aa0030607981041d005480b11054111100b80b0005041d8560944030540104103c0d00c0c00c1e030f03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 437862284 1250 437861034 437861041
    0xf05031306020313051e242208070c031403040518090304051f03050f07021b13020f0306090901181122020a03060801050c070602090f0913121d0108 65
    0x3446540c4c400a5003200449881e1440202d505407403980500024800d4029940503e030044085400d4401400c01f100d64502d4991b13800000c107000c0006c2e8090881c01c1c1100840768000b0661020180200501827055038045510f940b52610402070f17075008418603500144020465544c42002c011b500c0340c0c07420505a0540c3d1008400c50a611480c1c1087d42e02944070f04c802d0685410092000528244030b44040100f601c0d101200f0050321412140d91b80142d002c58030030091040040d842e10441c4002030501e8414803005440c54041e6045091141c0d0f0384c0e070001c420041070f0f281513040e194000340303107900070071080183c022040ea08000d0084007601c0002d60800300f00315600e83c1c900c0c111030303804070784000004860354004410103135020324103100005c2d06142e404200a4410320401c1d00680410a41d2490000181c2c1c40f0f5020f500500318103940008030300d500400039124841c0c0d45206031062426100307100c01c00e140c90703003e8034042c100003410041c42c000c0d202031280c40c01d580f800c600ca200f400e103042c40e40da = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 437863534 1250 437862284 437862301
    0x1031104091121430216060c0302070b0a0c08070f0507090902091008302d030112060b1f050a030b030604080406050a0923010f050313060203 62
    0x49032503070810202510b800180d031140608550280603d00d15000c03440c410249401e503850420f090710300d1495075803584c54140f0001103c0c80304036100c0490307070042d141210310711000b450700c0c07a4040d03001a01041954624500b010b0341030240102400d40e008425042c001040002407541086080052410340e002504205010182000d0011182c0c4441110b45c00d03910381003a4130217010001c100300d010f0000c002c0425010380044c4032640556030400010716844002c1520003247c0e0440301c8211072403402005003161710100c86002421700c0e02148031802040c9081102811100a5014603400b5483e024401480111900915048407a40007070b40480d903e40b1030000101a038200a00151501d000c011035000019000409801414402d4404120b900109814941c03513401c22507005100010030072041c0200360103a0302401003001d0500d01041035a84801001c100c204a95900f500e00c50f4551000700b2166a220302034071188261480c1003400c43c203010351004d03060102d4440042500d60080005810741 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 437864784 1250 437863534 437863537
    0x3010b030c13030c030204050a0b0f060f0702042a09060c02040b01031103040c031103010b01080606160503030c040905060607030e0d15091a07020d051b0715170105010311040911 78
    0xd41c2c51900c042c006039941d181000b00c0e0005848102d02450030000011854095481890031550000e051400305c0c2e1400820440107510404480041110a00c00d003005030700d6034442d11500c2040c010f440001301d45c8035500d20b20015503003100c0d80c042003038200080c4401584120149a001c1e41502d01207030201c00d0500503400342030425100f810380c0c036001c000c01c41481601242c0388100c1c1d0080c801600e40c000700304181402c0e42e039414052070204080034040782003410090000d00b42900840d103103104140003a44c8043c1580c0c0300362110380b0f186501040c01c1c01303645414811144c0148007110110b14000f52585d001d03255196429070144141d42c0d605411050003030010444484114008003001401030034600042d50b10090100e403503010700d061000650690000131004d0405a142e1201c038200b15003009240302a000805282c28540200744000818003401c03802c125087c011a240c0d901d42d00707950100b130000a001640700f1810181080c000b40c016a621100712030590b5000903000c2400094001e545006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 437866034 1250 437864784 437864797
    0x30204030b09030a11120f0306040603050a150606300f0501090e0c030706140f0405060a0509030105090718020c030c12120c1201270f1506031103010b030c 68
    0x40700109081109442001c4000c125442154403075882002e081c215055840b41e81d45000c4028680401809009014040240d40d02c080010f2021a14903181c4d0707100d80c1041810740085552070440500c01aa0741058001c0c0700181c151490200f0700700e02d1f0151316484c80b134441181240310745203201411590000c01d40102840c0444614103029a517500c0001ca001800700b050101e80038019000b85055625002c02c5c054101c0d40a9500c00c0841c1c00b01d5081c0d0301c076507800006400303c00300c81000f00194617220070307000e00001041a00c0e5070340c803070600005042c03d644000304000c8032074000e0102444a5080460881c4e000e80084000580f01c2c5903012100340345126105d040907107881900f04850140213518018014146510200a0180c6469900da00705001d08809200d407204520014814410541c0081c00800420148408001c0701d241c04003045401c134070203200166032203044005001c02e151109200412052a0070046001d00c80b0804100780410301800400110020105201103040401c2c0d595 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 437867284 1250 437866034 437866043
    0x30316030b100203032d01050609010c0b0f060a05060c25050910060f0507111509060304060c0806030f1b21010f0b01030b0f010e0418030215130507060e0103020403 72
    0x1c0301c00202e04040c0d5039820840b96070402980f00c46500380300099806101c0c0c070000c085810a0003603420001000700507000f002c809410420001741c1d02011554840c0c0f183c0c0070b10745100516038242004818032003501415041f0901442040040380d0360b6980c00a003502507550401110750031070401d8003030403030b00c02d0640c2e00c0341e6880000d50091000038000b06210300102c8400c1d8948100c0751031024803e80305801226009000c1d205180c00343d030078500700b244100c20550161050203151114071000500550400d550039a891a46c07062040034558112400700c0d00211b04500a001c4024903100d0256615040c0c0700164072180401d1b03610a0640b41c481803189840070215141d00b20840c2c00d02a24020700402c200d44040c9800d101800300c85501034401e4000105000c1c101e1070105030302c00015203903201940c01c040e80240e80c0c0c0904641203490741409804892280e4094801d080700449442d8400c940035080d40c04810350308070b410000490018410003201c2c6641000c200c442040f08c0164000d0045030300180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 437868534 1250 437867284 437867299
    0x5090a15170c03010b01030908030f090c09010b070308220f06110c0a11010507020d0b071206122003070e0c0f03040321051504090f0c0f061b0302030316030b 69
    0x201500425030204600b42a0002c003e07403107030800110700303480c40140302400a0b007080010400f0703e0700101440350b100400004031500c8280800125841500980c0400700c41c2030b0100c0c51740c0405034404145900104100c1c502d00c400e0b14099021780c1030b8040883c3c020000e805940c215410014030303030410310309030f50315400306230310340594098035902c90080a46c2155001c207000c5c0c0300310943d070203403040d540700a4010f4030060304e81669030f07100d20101c00041c040c10240b003107041002c600d8a10070f0081e080a0700038501c0b01c0d151844545096074211160301c0c14a62201003038921740b0110348000404000310703485612110f0071911032090a80440c0f00b4003601d218034400c008104003d06070041135941c07064580d48941b0fa544410401c60b0001c550041d1800c124210310302d2480d494a00d025084110a00c1c0200c00c45548d400c43d40d078a60540d01c4103584200c03000780301e0070310400015401c0070220000028645102c0d03965826564001d481c0c1c840102806130b580d14011034000002d01c02e9005005c659409000907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 437869784 1250 437868534 437868569
    0xf0606130c021207060209150c0d120902092404060b191808010c17090601170309040609060609150e060d0216030c06050c0c12030604020705030f03040501060f05090a15 74
    0x1947c44501c480340a01c030703500c3c0041202200482110716030392580000c0c1c100c55041000454020150240c02101c050702d400442d80980e4483c1c68050007806c00c0000c85c445684a02c0040d078400340e084918510991400f002003105218840c1200c04d64460601c17240b6a032809003034151108000e43c02e80740401d502090002c40c40910541c41010034007961345880b051003450302d1160030321040841b0042459040800100014048002c00c0008071051006484c141074600b004102298a6035101c500300a89610b001c010054000703031108013400010b2800c25640703440f948003600c00c242e8000303054000d150004044000307902c1e55041d58441086000003550118180c24014016150404150740c002d20345000700c0c03100d0b44030104a030006040c941c05002002c414044110440d04002d200c290000d4080180600254060004094143d007816405480303041a00303003a42151065088541c0032002d4860078042da6a58046990340504142004a18214000c0b10f040841e2034960010f400c00340454800c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 437871034 1250 437869784 437869793
    0xd020c0717070b0a051b01060504140f07080108070e0714071b050613050402030c120403020d0e04050705030c0a0e030f0309010e0a03120f09031a04050f0606130c021207 74
    0x1c0d600c0700600e004860b61541c9590346442d07207104405403480801c03402c1180692400742c1c0f568000c0d002c1c03880740c000100940c1d9180450b055405072807070038160442000c10400017202500346039400c00d81b10300e002e02503503040c00c44e42c070303910320071400ba010701070300b1b07a00001c3c00052203441c80c80d03280c2010901e483d881d0403071791074403079032844e5940d51070324101400800200321414070780180e440002920300c081c4001d9103414203000c001d500107000c194038141e0401c00581151050070966004030320a5005008034035182078010210351504000c1032007603003084107100c0282c1d03000064a4010180c046910740c0d43c180560181c0b03e84c1c051941c03076a0580502510306d1145071010015005846003030300e0380c00311780c0416420841d8185d860302005000e03a9544841161051190240c0b00305003001341032007400e6079141c2d2a5080800500705142400444800801003001428807180d020040b40d580140580d042080c00200411007002c418100940d0719031010652910800c20305958003081d40d41c0940e1f54079182403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 437872284 1250 437871034 437871059
    0x12071b0e0609151804031b020a090b03010207022e1d100509121f02120705031f081b03031201060f0c140703020a050315040f0f06020c0105040b060d0503030c0d020c07 73
    0x801b034010900ca42c00b9105004075030509220b0720f69000f00a40042d40c1000d20400c000c20103092102c1d00741d9400c0c400000107880310164401c01107140400b00c2045803110308210300c84802c88100300304206d4003c081c12603803000405c04280c105401c80340304810300c072204c50803100c034051114800c0d4021003820314803000c10000700303100a40e0028441f440301c5410046199005910034000c89a92017480d410026442c1440342001c0e41d004101c4185940d0340004828a1004c0c00d0101d030041d00d80c54019400d55401280508030700b2200c4d040950245042080f1140c00e05081d040501c1100207200380d004400915520454400388616400345208101a030f9840c080ca54070f21080c0001ca0150252080c0483c6510300080c3c510440068810995003d80d40ea03aa081d0413608810002c41e0030501498030034000405a0001d011001c88002c000a12131030f1a0510200620300038100314042e59008080202180002c030469071700603100500d1a58480168441c00003d2280310745440c0c95001d450700c0811416031040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 437873534 1250 437872284 437872291
    0x2061806121f030302030301150c0f05010209011d03060406201803060109270602070b07081b180108060616080c060702070f06030e0f12071b0e06091518 67
    0xa98020300780b00070014080008050101038056841440100180d0404603104800001d0f1444c0820300c4461035900c0304085440c41200300c1d0340b40d401007000390840d640480c607100c407558000303d05020040c11b00c011030303120a0007a101818640c0c4904043d507007080c030b8040542d401c03812114a86d41d9411030340035140103005c41414091003802048000a001c00950140c451451800c004403034004150040d48908488480c000b181c440741c0901c141008111103561151107560395031100b40007807410000b105802002c0400103505148117002420b000032600c020319140b01400c1c2011440c0740c40d1800040d03290300814001c4c2201109000c840c600300030824018124001600c421078209458513102070761511800c1c0540202d04144e6241005814440c3d00f00c03030181d070711900c02d803100c0707081054100b410710541c04241014039a000940c281040076a000414011000b016410f000600b000c003800c005920190000e40702d500c00d6400b244650346c0200360b2a0002d40e008182070550380c09550034076920401103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 437874784 1250 437873534 437873551
    0x70e011d09010f140906010f0f14030709150c0503030c090111060c0a020f07080a0b04020103140c1804020708040501081b0301030f0210020609060a1e022802031201030206180612 78
    0xd40280703c29003400380fa5140146c2c0141c6074503014200041d4100d0354a942c2d440b11070f0803c0f00c8050340c0c0c02480251001140101e00d40d40e503082d051400c2824411103040c40c019200e040000030941d03500490b40100070b59401c82c909a1550356183c0700d80004031a21440400382400901801040c0070320f1012400003041c96105580070b6030b50007006a8442901c0300114032803181c4a4000212140010b405000700781d0307100e0300c141400100045030384a0b6502d0508115418071510400280d0840b5100e180c3c40000a10482110b0540c44c0548541d40d110541c0540d2048a0500c07007041c001ca8400c1420f41341018101403802800e648039070390380c2003840302c6e101d22880c140e00841c600c49404640d20320200340140304403203c00084c00d880d1a56504e00004103c1100440c0c86002040c1005203440d5640c00200701c50a000903d051030b2100324000f044154500d8010700c81558810000329140200c00e0311000e0450790119685e82e161182d000001d544042140080b503032000700000c1280c500c0c0c030000e450034080c041c039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 437876034 1250 437874784 437874809
    0x304030209011220010c0f0b04020108090a0c0509180d02150a09051905160b040806071b08090402040e0103080d050105030118020f0a150c1a070e011d09010f 69
    0xc400301e03007034142296070014003500da00b0302000c58031080e40341380c004914a040c54111211403072500d44401d800500074048442c04600c070306110966170300807840e81c1c001458a02410355610160b507900254941c41c451759001e520000c001516500082901480307d035618000c0d14000c0801d040c00075120035408112800c446a030f2804100c06103040c0c0700b80c250040e4000c00412011031000d1403840081c0c242981260144607040c848221085c1140018009113070720703a0b102d5205c904000044d8201000180403c080052244c040303150034804038440307042981c110407455981c0a0f140301040c00f920590300068a9804540c000000f08104000201010940c3d14400c10403640c03140f00701400e94045034050490b0022208000d405860403c0541656120042002204a9480307500d244c000419219920224250608010501866030034090000b5104203185c15146070408014102c00c1151011604200e402580d40f0b80003d222561136041d090014004400340da51840c080c4585150750190741c002c00300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 437877284 1250 437876034 437876039
    0xa030e120c10051005010507020402280309030201111204020d0305040e0c030118050f07110a0204050109090c0618091d0609010e0d0e090f04291b3117030403020901 72
    0x80e07184c891050340e0059503140d203042c00b1502004044d40148040020001d413400c0b80e81c00004c00c03406034580340c0c02e95132408144150b80e4100079084400d4180c0300045a0307400c100409040b9680c402041d8040d50459903208142031504048440d4003c6410801c3e101001406100c403440c845405035040b16003d0003030a1b183c2c0b1000d02440103407601176a41c8090b5194142c042400c0f24010030b08512400014070803102c1051031900018140e403020f0788010241c0b9516030103401484503c1150038050480c0c0d0411640c151007075550b51070000c007079106c5c003909035035104030f40c1882c41800c102010b00300d03ca1200701c60581c01d0007900c070360003844001d44020081c803031420f032900218000c9410000d00c0600a01040041d80c955120207000800204100ca20802e06051444994030030101c00800c101303850101e44a40c64030840e908400c800040d100b0100341d505000c0907031020150b02d00c04080a07001c0704240107499403c500d60900030b4007071b08404429a81c070018610107400010213441140d0080301c4204160741e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 437878534 1250 437877284 437877301
    0x4061e06081606020a030e0f06090901090f0605100504030b04020d0b070206010806010f0e13020a080a0809040609111812030a030e07060306030528020603041b080609030a030e120c1005 81
    0x44071844021b000c6007050f00300b03c0b0246061251a000c00f80013900003403618034000001040120f09070090051103690303020076800c0302d456108040240806407007100c1c0540006038003a029005910005203003050040c002011500d41208208546500901075160360408443c080d4803140b0034000c2c03100c548542000011030300380c2a4440d00c1110002c0000b0300b5a900d0b039412056000600d00000e0340c120240c4480000c20340010011600c5190150280307541ba1200041000142c03103956004004103420b004800b040c5001d92021100760080c4020a20600c407a01404200c1604184414441c2030102007125a030182c0c2681190f950002d280c0207540e5007644030002035048400600010300300394440f40d00c400c184021003040986005101c503980070340b0301381d0b580095103544c801c803021144040341c0342030080c1249980d81c4890240140001a054504e4410800b40d501d003e008095003c05840d50181003465100744401890340703201000300ca41d02e54640c102296120450318840d01150700c0d1400240020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 437879784 1250 437878534 437878543
    0x40b060102070f05010507061d06070905030a0b06060306040e07060315050a0e07050319060f1706071b0c030b07020f0d021f05060f0409151d0604061e0608160602 71
    0x1c801a007030003c0b11509100044800360130622003115825030710003901da40c683c501c0d000c0180f0400c01c180209041d1620310030007000c1d0072140e4400e030b000ea0700c41d206e280d000a0241031501d40c0024140c0b1600e8580d42c81c0760001d006801c10910282c12030240980c089000c130b90580040c009020076100b002000d544c2c070f00a00c11900d022380700b2290800c000c2808034000e580b00d8001503410420703030000b490001801500d0303038080325603980c04909408400c42040040c4451000c0c0002000842c3c0017a206601d030443c4082c007000c400560080703001050844640801c04003640c1d030005560020340aa58514160002a42d103044400d10600640708244101034802d100143c11450412910091099400e18843c0c0601421001d40881c0d0710510707082d4020b1141c0c4807886107162032030188114264202d170104100048070070820b030314035080054282110200da000103110b03801a60210000424480c04c3c0d000075029071582300304810f4503040900010b4082e0b0300190310303c00000140740311191aa55441d083e60788 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 437881034 1250 437879784 437879789
    0x506071d030303060411040905010e0109050708070905100302040803030f0103060506100f080421120c03090807170702060c07080c0f1e030705210607050a0206011823040b06010207 79
    0x9a801000024040c1c282500a0315440e500384a146c1e05042e1503000e0081911400d8000c01c107008102c400420280031203005150b0840103a003420a56802c042c5c01c0241070414500641c0d004908512440715002c0c840d50440d801041c20900b540d03224103001a01011012003803000380d8032903041501055107890b2015081ca000c40320343d21110382190161406503100c08000b0401e0381c0204104405000b0003104120303403184080181c2e18a010000903143c41d0088810120303980040614100c1340000144000088803481604011007a915110051465801e80b00d01e440003501b010001c1500740030003100064150580310010f068036807026080060100302c3d27044240a0350f12042009030310580004c01a800c40d6441d0000e419582040c0e1200080b6882d9140801e010038070132250410011101c0c818415650082d065141062500a0684000b592a101801204103000c3d4034000050a114180e00c500070fa0b0030318050000240500c00226800e8040c200d400782c5071440c0d07a1000035100e600c0132542505 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 437882284 1250 437881034 437881039
    0x13090b1f0906031503082b0506060a140f0a02030d0c030902090103062a050c0f0c280f0605120601030e2802040f060302011404080d0c1b030506071d 65
    0x2054a40b41c0e00300d001c1c0003d12800342c4c0ca100c41240100109031140010035105486500c0a0629241001c4107495110b0042c00c01600728605024007106070340f440110b9074420800d10784881a09000c0c011450392344244003a401d5440030000b100800990040003500840080090401c0346c440088010340c165940780c0402035101d0207001c01400096071075131201c45801c411008001502c03803984440c4110b014211050004a42d004c500c40340710b60400c0000c5c000038940003001c0c2045214940c0810401c03021600d4015a800315500110f1503858103404a00081080403002a2419503448029000c3d070700c0b540d004c4103412210740c0040c58550080c09010440f00303090b0024210b95404c5211908511041c5040c0d0316801c0c841810b60f40582e40318040c10314440c0b149035001820514510001d03081890801c16000c400100340020410714034085010042c1402e542000390700001145800c8107803c0d216042001c000401c95000302c10310038001401c2d84180d0090b201c407001c0105074000070200705000c5008a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 437883534 1250 437882284 437882297
    0x13111e180c070303090f0605010e1009180b06240711011d01051606050901021305030d09060e130c03050109050a02040b0403060b06070b01080109050d050a080601110313090b1f 77
    0x74800c0c0d220414086c0551400b9450301328a0740c4420a4071020fa00c0b10505511040c00d000a24003401040c00091052510800220200c0c02140c0a00400140042c0c0030044110014442d51241754141d9542100040d01d402e80706080c05001846810003403064035003800715495542c0d90350082400140c001c0d008140914541c0311440112802c4c5d12480a003221294013408840004900d030042a003d20542400075803100d002c42c400341b200019992215100b50710201c1a841100c0e00030401d00159541446e01c5420300d0b01c1c0c40301003102025140052004103150034484460984c1c1540840e040c1c90080c0750034405926042c0202c030030f90145010744034002001304401c000040c2564405140301783d020b0020303401c0a03026282c21040d014241d124400c00e075100d900402c00c01c42c0910408108074128140b0300d0070241c0800009080f680000d1455040c488400134010a00354200241c40011140c402d502807501e490b0162a009030010352405406207803104080d022854505078000250b00043c4d8540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 437884784 1250 437883534 437883547
    0x152a0406110d030e061303020304092901030921030209180a0b0604062f010212010602070504181509020402030907031a0903120414010f0626030313111e180c 69
    0x7003046d9403400040302944400c0100040c0d441045c05400500400d00c030420107015140d1032000314070041203144034100351915002800103100202c101410400c24015505c01d916400401d60003440fa40c00c00d103900514203c03206061440c5241040c0c421011480240328002c183e2081c02140d0207580104404181404540707030050301040a801c03c5501d46000002079142124000b45c00c90f449072001c140c0f5400880c0050001c42d40400003980200806d440422198005282003110034850f9640200485003004174a2042c810b81d40040c051540c000b4411540c1c1d04000e0040eaa982c40203100c00c807008805941300403000000c0d20b400501c141045000f0310700c0c0c0030035134100e0840e12800420894012007251000ca488900034410710032140a212400030f082d42c186400e1042c2c50040203502070310940c000324a81c20855002c4143e9420140d1340b2103450750282285001d001c8414030120454110f1001561403d05100318107086a0548090741c003814440102204580c844030b08880024002070108001d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 437886034 1250 437884784 437884801
    0x608151513111303050613020a0b0a050d060801060513050603100504030c0609030306090605060903120f07020415050910030b01031101090e0a0e070503152a0406110d030e06 76
    0x640c4200a400c00001044240b80368000c556030407240308500150000c4506104201082240d40e4000c00b01e040200c400c14901d50018120320010f00464220203004070301c006859000c4c1090740c80c2091401e40a004990f210304100d8001e04c039038414148165071065200c00c10107901d04c291805500b0240280802ca6040362804000c0d05015004408010308210040301140d0380c0c4c4a00100d280c4650340c0410b405152109000030f0780e0103500428403410041082c0501d07950006043c802940d54110380325160424850841090302480002a41007414030788400e11210100c003411056a50450b042c450649980000755281070980c080101200101c10040c000702d501c0c1c3d035243d04559014588003104c59220480303c2c1040070140c0d619003a040c1c460101c41010b41d02403001c5805014281d0082481c02ca24105c070f902402005020900c02c0d211401684244100c034180540c0e44560400019a450340e5a01c401044249000c20040c450702802030326110041c460b018841c8100300c0c0710000e1140b51540364a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 437887284 1250 437886034 437886049
    0x1092c060a05090405070e010b03070819060527010923190218030d230705010b0d08030109050c03150118080f070302011211030c0c1f06081515 63
    0x8903560154101c0c00004840e511030780346520851181d4080d100703042c6030107505100305d00187c120002c440e00500401c40240d92001c00190b01415030407420724072600c020000e00007130800e50049131304844a610400c042c0d891035003c0c40d0700340181003904280f40c2c0c1d03501600d4088585458500448103108054200d5020b4140310351500319417401c244902400450071180f0480c2d00c951706091844803401c001d000c0c0d80c07400784600b40708a0281d0a0180701c20600c0d88400b203141034202c100122841d00030900c1d0050020950101c4c00c82c407405000380c8240c03549402d190300c458209100b100c40082c04c20307000031080f4611505480c003e8101342e003001d50100b001c03001074810080d4020050414010048001a515400c00155800c000448040c20f9503c7c210300005000050300c400d025a01c03400d020003040e5000e003a00850b5440003101d8092a02d034400f0000d0241454403000a03c20070a10f0f01012a0140b01071358403101c1107414050482d0500038140310402c244400807545020160b03c0b103416000706040001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 437888534 1250 437887284 437887291
    0x80f031c0b130509010c1806030903090e0408130f0302010806040f090c0324021317030c030a0201020a0e03010e0c040e0f0318180f0105010f030f0e0c01092c 69
    0x240120318100c00c003000ca8100d82c10008000041c0e030b250418041c250500f803203102007291280c5440501c02001089158a04c42d0901c514420036036030b05030300c0781450720618040c000b400c040c4685550750305213400d20700010703004001c000312071071070402d000a842e000c0c882e941d1b021a641070b11040c900c1e035030b00c008000082c41141007505203151900302460002e2080ca080c50051440b6660b40c881c450b0700d90b0101551035805002d0402c1e51481040b800e8513401c0b0390b84925040391072a0302a200103802d109030702810341c001c10628141520001c108100740d1501074024100411056403947c0f2000950810035090740c0c4201c01c0341000ba00000480c07002800d194001c20901c04030001220444681240c200f840c1d40c1c02a400542039108584400000340b42c4010b24016031444540740d20814144200603001e0b1800604c101c5061080f01c010380b161107802600103506004958008000c1c1e00c4003101c04580b0790b10400e84142c000745500c036010485070f0314204000d9010303640c50080707400c00701d864034442c1e880781018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 437889784 1250 437888534 437888587
    0xc0f0603040c031b03062901030e0c240a030603030206070309030f110f0a11190806151801080f100213060c020f0303030c120109060b091908071e080f03 67
    0x600048049046801042d0000d0010391703041c40300c0c2400ca0387c0d00d980e24501c1c0541604060401200d07010402c2c0024401c100c5000858240300c00041788942421214500280010700e007401042070002c03190181e21210440b030081e025101641c0d50700b1303811021503140890041c0423480d025035603042c0912460a90614485180468006612208100e850032101503022a10a038510a20b0f40e064101139001d584d03100b4246014124ac281810251904d0310402003141c8041c0400c0f030300741d90460780c81841d1907002d59002c1e406a4900d58480c0c42c52610b410350119218003500c25294882e10000192003110890704100c210000024100401107810b5000c00d00e06903072000c4000a0b0320940d59090000350b02034a40424915139a12208000d410f000034141c1c094010f5500d07019041010041580845201d6a0120391128407411400e001a221503609d401c01d0003a482a02c802041e01d00341194a0a0500c0030f20201c00c040720f9541c1507031584d4184050880c01250410b121040c000d1500e5040d0307840d4000079 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 437891034 1250 437889784 437889833
    0x206100e091f0209130204050105040614190c050c100905010c0201031506030507200a290106020303070e0f0a0506030702282d110402070609050c0f0603040c03 70
    0x950800301440b915180b4010b64907680010321843e01d1030031501034046800c500001354241032401002070202d00691060b102800744204016140001003402c6030003200e11500e000b90000743d10007005281c031715016421a000d100e0020101d59524041031009a401c02c50342d036501c0d00700d041c8001111290b0050030200d05040e1030315100d60b1440d52002c162000740072a80e82c00502c1d4a03107107034001c2030180c25180040a8a0307021040300008031021440008490b040009a210b40c102e140d8440f42c203500401c3c20444a803142c80010590b10b50200040d4080c2c0e040c1d40d2042d11854015080003090907001c14601e5004a05010402240c00d244010315446042401545c5c1c0e000302e41d414142801c070080e00030160504a902e014001c115144600d045503502040d140e0080c41880031540030303842201c03880906452035011f000300340380d0390b00d03011500c540b43e2280003402040303030503c0c0090f59100c40d2030a06100f000b80707040c856042d0501e481624412a04941d40f00d41c0c0600d1510b032300d800110118403540d440c82d00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 437892284 1250 437891034 437891053
    0xa03031b05010501140a1a16020a05030a150608070b030a181a010603050f01080619060f0b0417030702030d0e19061106180c0f0d020909060a0b010206100e09 69
    0x7002c1c801c035402840c00b1141d04441c03114100411507480030f507400001c48401d07498200c03c0304070103200a98201c01003000b000131089803c1d00005000e510158080755140c41030004550030800c5001c0079000c5800c0c803e00a0108944924035181c8400ca58003481058140034800621a03d050760801c416183c00c2c0721585901001765240c81210104a880340080c0c06002c40c010803c656240c070800358850030918003601c25504002c4c503283c40398400340c505820a040c1c1d8008040c6035089502c05001001201d944440c0c00380e0710902900950403a00c10181e0004401c01031000303140e001300441e00d91355402406040038401c090003c0ea40e015400310080e403c1203100c0c0c1e15140103004010107c000d000c1580740c807488141081400c40c9090402460b009130030b0a60520001080030010b102c20344186d007210ba150303074102c1030008a85850306511020394019150024050700703035070104503103008204046040c040d020412005aa40f034100750b642c0345600034030300c2040216002e400213103070700b041c80030054a50204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 437893534 1250 437892284 437892293
    0xc0c020607140a030914040207030804080c07171f0e03041206020f120a05090a0209190e03031003020102070909020d020f12060408030603010b0d120807050c0f010507090b07020a03031b 81
    0x807108502240490f64900b0f09005030352451946ca01a54812602545000031994004020600140000700b03824004584091003200c1403051001910b4202c8251401700d40003100d550782d90480c03207184235008003002d0500300c000d00540140d001c0c80d04104021071919207403101c4041d110407141c1f01522126070910107066200d103102c0042800010540005039a410041d61400450308050010001c940c41504224016110703600c04640c4003078030ba20003040300c02081e01c0071405061407028242c0240000000c00c896203040440c84c0050301d000f80d080300c6086031030b0007100701101c601c40c20196110f8640d48200307005242542c02044039005c060001c03800503483d01c00e030328a003a40a407011514000c0c0402088140d04003441440e94002084801e060071a0030740d250801c1b58146100b0704070030400107000007113141e8050f0040301d2035008a07808841072682402e07440c90081c0800d4074034000040c05440000b6000060105842c000303500140555029481d5076070566002114110824200302110b2003240441d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 437894784 1250 437893534 437893543
    0x40b030a0b09280c030b04111b0d05041208040510031d010c050702040e0c0d030503070905010f021005060a0906030f0501061e0e0c09040e030901030608010c0c02060714 74
    0x115a000c2022500ea03511004011101c6001029124803c100c00c1640a000c0100f119681000701d600b00001030104040d4801c4026003148100e4a411608111001245428800040403c0800717179180b078104640301d650300354403140407980170400030304180014001c0c0500001600c407501d1192000503c5c013591000401c03104806401203e0200c0d07a141030640043e10788030742890aa035130000007000700b6000204007510300d004002004e406039a588400700c0b0004030030480d8420707003e4010b0490036100694900209540c1c4120b46403000950b80000005665008841e4404142c2c25a0041c0002213050b80c040c030004d180007001035901ca003480d2000030706207106100c6d070000b46004140040c50110319080443c00d45143c1c2c0c1c0708103030380e400c5504286042c0c454401c1c0e101c02e585c0d5003040420982c030780d192030041600402c2c030041e522521f07005408601340d00c000f00803e64004280c80c280b040980d126022402ca41150041d4000b040c8030008840052500c1030043c0708451148a10781c014001305d90046281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 437896034 1250 437894784 437894791
    0xd0507021006090c0207060c050c0622050307030b04020915090a020a0e09040206041e030203190203010b010903210309062d0509030a0c0f1515060c08090f06040b03 72
    0x581c004010940080845019030030141c0a85481406405034103900207648000d130340304803810844602064000c00000788410021284002c0410340c59155094042101401c4a5403500c400040c8110004140c00d001c42e000781202d80001110b1029a2981c00f44001a00d0003059000000700380020f90a040c0e5070008400c2c0101450200183c4444248002400c500d9903803c0c0581f08103008010000160798003c119801e90708201e80010542078245075100d104005a040250300d4080c039045141005851060a00300900880092103081e41850040d901c001e040d000103498804003d008004140c1d5030b001c0c00c5100a854a4009081035540d1144800c48190046008181409010b0403d85500f0400d40c403808094a80c010030090408111040d900d10035840803006001080b43c00e102805410910001d00a802c40c83c2d00e46175400001c4c0640080140c0300c1c5052072442d040102141aa00c40c030300e500103807940500080d240c0360b420002c010210f034030644150f138001c404201c040b480c9090480034500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 437897284 1250 437896034 437896037
    0x9030a05070b09010207090b1e1203040303120612200f0d0501051e090d080a0f05040501052502100b0307030c0816210201030b0f0d0b1603020903071a0d0507 69
    0x1103403030f150710009050001c00e5014403c072509000c10001c1e282c1d5404194031030003851114a41c00882907402060300d41d5108a01111030380800b0600209040c2c03c5080400f00c09844107007008041d484001002040c2d40303240024040d49260b000c4502060f064010032509650020310010001d1001c000240100d0003030101210181d45680c00d00c504e4603800541119048240c003c08245d0b8500048003076175414041000d02c0400541c1408a12440d066a001e4010b40d060444140103078501402c0c068003910041d200c5114640c45a003c400003080c49044c0207040b10341c5640035004029a0b0040b20001d0030100b46000d8cc103000394040000040d03081d11001004140b100c003c0c055880403c0103c2034100400d9100074251814120601e4001d0488600410a180d0900780000c0c600c910a0201d1182c61030400a20b8100204407140b4051201c48003030240313781d056404480c0303019601e5100300c05030f0040d40541605940704500c144610310840d40e07a00181010700c4005804c008800c0d860106803901618100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 437898534 1250 437897284 437897287
    0x50304170f0c0a0e0f0a020904180210080606090405090106170a0c050f18090f1b0a090b0609060d0e0d09060f0c0c061103040504052e1a09030a05070b 66
    0x81501080c00740c822480c2c0100c0391480710601d860710444445000501c0101c10343e1030400010b20048044e030588802c04c2c0064810000402055100700740c10400690036072241d01c440c64600308040c8105400d61082d00058906400c0590a106001c0a401c001d44408000e54840f2404210748810f401e0071102200c0350301c000d00d5010b8803030030f100440d04460703080710b8043c0c1c5400c59042c1c1191203401120f190b42c0941600711805580b00001541058209800070819008844041c4084500311060f0203000f0800c481010855a40e0b03071101b0100c034003000402c0d03001642440002032901e420300150000c2003481c01d0108114a85441680c03d02201074070007404612110018090740342d01c500c02c4503140d00c01d07041869681d04640c403062314503c0a03201e0481040903600e0b003007050301818000d880040a0261042c40182400540990342c5100034103884400e0511000e075100d42c40e04145003504862020354000c6c4403c001580015807035100c0781a9a42501c940f6001d803001400030000e01c0f004012542015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437899784 1250 437898534 437898553
    0x17090f07150c051005160c0f0f141002040f12050703020d0c0308031e0f060f09130f14010b01020d2307140c100903170a02010905061510030203091905030417 69
    0x60681c400140d031580104801f0312008000914607000d0402000d400c4a05401c04695601d403028409403881c0307586240d4003c0d42c0400345c00354481d4003e0300c207664003134500ca031101d911080040e25101c0840009410382e40880410405424010101000a40aaa503400c0b242d5242e0b200e8948980c401c0e1010030065200c017507900c600e42a5080b5440e00200e104030349070264103004000400c0640084640c40c850840d22002c01c405640078800700c96081d43c4a40c8240f001007550516603450b405103480c101855080c482d6000080d84081245091160740352103606803451103481d16100301d2005c01007800c00403c2002064089a203c8110401c504a00c1c0010001000b1290a10a04034035050070801403114001c01400056491004551000340e0b050f072550f1036544143c003c902628100c1c0c0080d006020703d1080c0510480e070003030414500507083e600300301c0d00326010004400700e1000701d0b48004680c002c0020704030b4807103035042e4a08a950007101283d0070030352248012410180ba003480d000181c3d11403280c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437901034 1250 437899784 437899801
    0xf030a0f030e19081507170606160807020414100e0c1624060b09040b03150906040b0f190203060a0e011e0b070201051b030c0601030317090f07150c051005 68
    0x1980d250400c5409a6002c2d4244450040c05140c21207a1003401110001d0004410b82c59040c01d681040f48410603100c240081c07810f0010103a40910cd0607030089062100b43c076241d440c0e0109642c0201102d075810142245003602c200d0b0a0316010300f00d440d050404001e0140409004400e0f180c01c42e0042c05000c803c580d00b244800100801103400c0510a0700b0000c00700000f00d05d04040d04d20011050f140410154041c0c80007900b852140c010050384401c610301800640540000c14034440c51081031001702d20b4841045014120030101e44070030070f900c5000c0c3e2801034900d4507000f55400ca00e0103404070550301e40391710032843c8401090300700d040888480c408801450b005450700c40020030f59186902c0c41c1210f99000206244200584c2014000c5511250803030408200708481c051243d2070207460840d40c49140042646031502d072220070300820f000c00304804040224880c43c601c2d0700640282502e03868004100210005002c43c82c013070258441b480804280c040c4500c00d45100b00c90030014007407400004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437902284 1250 437901034 437901043
    0xc1906020d140c0a03090f1415150603010512031605100f060e0a1d0a030f030b090f0f0c070b16020d050a090311061c0f0501050f030a0f030e1908 64
    0xc1116101e0100307020b0080482e0284101c83c4c80100d64900400c0c14181c60900a140c0c48031100d0080402014038094500c00303102140880b104010418460b000d0b84418a4084c94540103242d95036020104000420403031404081c081d40d851140d0003500d0911400102003940a54816010381e881d0700b0080e8017841c9021030744202010305201101c20000c42d81802c8425544180003003000c41c40703540c0c2d52544059140d0716501e060800c50302008407801e664540c074000304a1682c0c4607404011a041501c588181d151022817940300700491032003100d04e940e400540d400011405007811110002c02c01031900403540c00c1407000e00c0f8404071600080c0e204000103009181074030083c030400410205002d004020b030b900c81411022070b50448410a030b01009d0300006085845080a0350b500203015002c0c131150850b032904003180280034082d0030407040e80da4405100b0001d03111100c45070b0541014445a00148010921000660181c5884501a00d00340089524522000b50041e12500d0001d001c0180500802 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437903534 1250 437902284 437902301
    0x40b0603070f03080d0b010306030210030b04060905190f110c0c09090d09060c030306050901060305040b0603070605070b0a0b040c112104060f02010f0524090f0402060c1906020d 78
    0x40c2954960b80c6981c940c070b00d050280c29981c0c01115101c442c2c00006a1080c0c001c00040c2d50000c001121156110318054002e0501c8820f035401141403034400581c205e0035110742441034142e203c4210030703002400b080760000e244c030000e450010780c0c1d80c802d41d030701c015070396406050006200c00050503400080e50402007540b00040c101d1009502c40000880a030b03038031805100880c0c0035400c0c6402c0c0c10525207002d501402d15900704030740180400e0f00000300640c0c03503044140218000d4000300d610792285020300d41c031a0342c18060744001c00c00c10050707140026500d40e421503002d000d0190005500705500d0005040d07502001c0c511000034244400102d40388014440c80b120810048112642c0f42034032502d4490a0003140f141406000f81400440307100c1d4002e40200e1001000004104620328000c44e5409d44010841c1c00c80c0e010b002400c407501c00c18101190441c0c010101c240701d40320155107541c03c01c42168048811403403503002e0003003424980f840c10f543c200b603024418030000da124030340201032034115043c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437904784 1250 437903534 437903549
    0xc0f0302030615060406081e0c040e100f050d0602070605010b0903100204030b010506030603030c0f07140d08070807021f020a120f09051e06040b0703031b1202030a060806040b060307 80
    0x9140c502441d81c8004c201d0b0102d03112814810110b5071003200b0182c45010011a45c01a42c1b004000c01c0320080101006105544d0101c80c400c481e40c0301c4001d90007160310907004170f003850300d5401020301030761034012008501c29104903c058640581c0d542d07075500341c80080e48403103a504008121098103180501101d500d15100000442c14203295449110340e83c901842a81d00401000011a10588041c801c44010480300c50841da8122a240d02c450b0f60f42401340b2840a0a0a9030301d04141c075450928007002c0c40e6500260342604241540e1162500d66120441c1203900401d0190b140216040500f0030146c1c084480d001360178160304038180f04e0002c0f1002005642040307040b02415501c80e8003c50844140c1c0e03015588030400348180d01541925501c00c02210790b0005000c6030004032000d00301c00500c0000c0c4696004c0c04070702c09407a90b404044003018149000f00b9609071141d0b4100304207030b019562044901002088481c2d5804020b401c066090320f080d03502c1d0036040100b01c801d040c03c200700c42c001c0985 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437906034 1250 437904784 437904811
    0xd060506030f070309083c07080d0e01090507060807030506040b0907030510081222120609031e0512060303040b0f0c150117120f09090a090c0f03020306 67
    0x102106003802c070740003002034003071599801e201000e022105040e9048030590581c1c10305481700162404c1c0c200c0312403101c100b0312621200135041802180c082512060f6901c90340d0f02e030034460384043c3c81c1c01030400501c0c015083e650350b42429000c90010807100c0c0c01003005445031800c0c1d09000c0f4000742070307503001880c090180b030074a1b0301040c0d10b884407103007250310520500c0c000030079464061071100170071001c0d4002403182c4220b43c042c0410449000050010380c0815005000503032101016034104038840c820303081e035a9010010fa001094075600984040c4c0d10a00d41800800d24905680041103400c0310314000007800810409660185601c21982120040b40110b080605e050005485c5105403c50aa00c400307011411685843d030400080d0b42200b01d0441c5088650b85400c07402c1d4081d403d04c24828240c0c07064580504d0201d0f00b560450320340c07680300009289030030680c5007845204900544010702c8103903200c1c4850041480090480c014101107003400740b8143c07560041500d0302c0c1001d064070171180e4a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437907284 1250 437906034 437906041
    0x30f04182901261005010215040b16030f18050d03060b0f0d1103011d071e1d030106090f06050117060420070b04031d031e0a05010905030d06050603 65
    0x1040305524904110910340010a000600401c4a2490361211403d460100d243c0600039000180490035003501c5c8281d0071160300c2c0c81403c001030149a020364020300500000d1021401e280810304403150a40d40310306000c2405040e00360541c0890f04000c400004548108400804021041c000c10f0104403092409200c05270802d0020400ea200c0c0e80711038840700c0000502c00c0300302c0c092500404282903456102544940c1d60305c44907450124180c0d6040f9102c0418800110380b04d000f0280461aa4059422004540000101615982d1300d44446005044001c1000d0403955824029000030b040300381c8001c2144192030840c0021380c3d842d074003d0350521652050315010301404003101c541c080002c0342c0200b640c807008440d400001d0421490f04103030b2100041da00d414805034181d0305005512032b40d80c01d4050360180541a403900303480c000060b0706402140c0011400301201084413440101071095600b400008d0b0364182c02c4804801c802c442a82000c07d02d401a0007203481800000c1000352030702440c1d450f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437908534 1250 437907284 437907341
    0xf0b070302150601020a02130b1807120507050c06040309030209070509031b190308071703060d060906110a0201090c0603020301030c0902030423030d05070513030311030f0418 77
    0x24000b28803040d800c80000000d0762583c401c001550b002900945030b20780c0c1824036010380c0c0142944c403181034080c03460440c185040c45108401e0511504440d078030303201107031203c03812800a003601400940402c5400d020604550001b40125401540b283e100c980d100c070b107035105101003040c0c003e0417001405001c1c00300d500c0a88011994084080d4800f002c010803084640014180c400024404a0780c01c3c406480401040501c10003410100d0040010070640082801e46407000d01c421901c40d500281e22181072700006203d500242d00c040c1c421140030840021720f030440d551035000300f100b0200503911012a8018081e0022200e0f0241c0840d1a09515641c115203402d00ca1604611034980c000d40c1c0000014207202c5100c02c0400180280c1c00c82e03032586031000f1800c90b50f81c0c000c01d056404042c0351401080003075000d001200c000b0780d000c448559000303146460603514030f0030300d11020005010400824010145400003013001d0003021403442e00442c0340e101024100c0d50b0f000740301410080d141c0e0081d408103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437909784 1250 437908534 437908543
    0x3031104052803080c0609011104030f0f06060509150109050306010e0112110a1d0604150504090501060503060f011508040f061109030d09052b0b04050321010f0b070302 74
    0x3019002150407940e840b1500308401c140e01c07a40301070000d080224000c000c243d0049a01400344030140000d01c800040d040b50301a092143c4e00c0010b101d00c09107102d1a00180d24501c04140030b034000d8100155559441001c204032402c00c4400c42241e800d04201b05580e50b0300220a04050182500141515814aa80c007a0303201c50600604410821809903075040090680007000041405000d4990640d96582d40c054480d1030154407250028606000405908140c4100807902910310340ca2045146007000744001000ba0440c180e8030342d5200d5801160b0354404004450103000406012940c2f5890450354240058000034081e08000c0301d0002c0c0000b040032007840c00d40541d08203c00082c880c109145210103845400703c015018007a0701402803d4039000940f220460780300b036030103500700c03032480b1000c829a0500c14501c00c0000324800780c0e14003140104204a601500c600100c03480c19414214030040a40e02018940c81c00360340200521100b8500070070200100410b81c1d9603400c103182075034065140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437911034 1250 437909784 437909809
    0x170903031803161104060918021504080327100f0509010c0f0b0a061a0d050705040f08010c0f030c0c0b040201140a08090115031515150c0303110405 65
    0x240c007201100c00d03100c0c000c2402100d0480508034030803011203105103807101324801031005540c401c51800c0c0700002c290f0741c0f50240c458030800360000c0006840d070b030740d08000a464800c600e03001081410702c000300701c00000f000188660300301d44034800c2c640f0000e0b40100d88112581b55030a07003d02c0341c120b07880840c07580103104d200802004d070424982785c1628034012a91100054005030101d10a40408000e1003400d1180c2401120b41d401c0a10200c1c0d00c42014142c010301c0040d040404140802048003000c076160301058018095162561605030b075810b8502401100c0e80000032280d6644030f5181440790454440c103544041400d041c0320b082c1f000f280c040c0c0502602d40d4060310300f04101000034110383c819102082201c3c803012120b501c510082c40c0060a08604503034030007440d8a0004c03d030a61649081c94902181da00070381200c45014503004071005815000b82c50340c0e401100010104031040110311010340480c6980e0750300110300e0700d802d0003001d9442440d25400c007407104100920860f2031b1200c08000c0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437912284 1250 437911034 437911051
    0x101505060307080603030906120f07030b1011030f0a050c010606141602010e100302071a0421020c030a0f0303140609060f01180e0717011d070c060504080a17090303 72
    0x41c0d0f50704c60200b82984102c2030081c0e80a200092008204580d800b40e060080d402c50900103120354030088160112116426900d070320030304010103070f23810a1180302d410b2540c4c1001e00c05d881c1821603a5000ca60a070b08888a80c20100f4004680106000424440e42000340f48618010081204441004d0040e100b1681482c010712404000e580569028003c80c0c450704001400005030078200f042c0040080d086500d0460380080c101c030f0401103808d5010400c2c0c1c0216000702100d0440c640445110030480d805040c010154040c01c80202d050f80d0f01840300008c1e042c01107014a140e20030528005040b0b5107044160031000300740806000d940d0710317004a1540d00c5103064032510000740a503401660304200300240d01c10380b1104581c01180c0740fa2110380301801100b454542400e4004024282c0c0084d42c000d0142c2000c2d01c0c40750380f05201c406480c20401d60003604500b0031175650300040d2240e9040c0c80d411a0180d4400700001082c80c103a55004401c8481d1b4400e0801001c464108254030680380e2002411201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437913534 1250 437912284 437912297
    0x41404020901030e1e0f0307020303030a021b0d0f140717090102030d05090a0303141918020301020d0e0607020a0302070e04060e0303040c05100c0b07200708101505060307 75
    0x2082d900076442680c1c1c1c0e04e0b81004031403520095800c48801501c0b03603034160410340220b0030445242c400000580e5060b6500a0182d4215074400210744001d403c84203000c640b40c00c201c100b06103142400c1c4421088410a17a403807840718800014040c0c411004c1442c00699100c04000e001d0125141c140010b41e444c1280071216a1100e203000102e1540c05140074a0000f1850310301401100800000c000400313900c0ba4405004a07a00c07604d0942003a44104c0c1c02e0005140d8440310585905141d034007034400100044c1d009840c1415640200c1c2c2240c000a0070081c1103075a0b00b4040c580060100951540328250380b0040c6070400e50750398001e40f11440e5202e00f25183d040d4901040030840e0743d80103410010303003240c101e0b51070b840c086c00c0040340c02d03007244211400b58140b115025001442201c2c000f00d4075811070811015030302c820004880004100d00855458280100c000d0f0300401c05021a900400d010ba009004a1a41c40c401e803041b00c0b00d40140c404518512030003081103807142d0054a520045a0502c0b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437914784 1250 437913534 437913547
    0xf032a12070e03010617010c03020708040909290414030f0406050c010f0c0c1506051503060409140c03102d0609050c040905090105040203070b0901350c04140402 71
    0x5442c00320385a800741e6499400d140d4081b95441d03203c0b8052254a548400a1080390042103043e0101e10685802401c2034400300024071000d1003a400c101c44552195400c01076024060100740c0490100420321801001e600342480113101c0000f60310310486000700b01035850000b10b1a1145450720440c4100001d020010810300030840081d4040440104019014000500304403402409489440d008884020701c549a400045901d84180300c2525000f600782c0b40070020307070b0240d04104d400080144c0e510a0715220345000282e54103d242c0742d40d01ca640010101e60752080109824150710600e000c00d21842c000100a0641c00c414120300c10943d01250001d00001140da000003a01d500d801001040d4208400e10085004c41001030045501d25503042041e5213030718002609034ae2050728044c3d8142c0c010340e414841c03100c040d0020001d80905051080b40d054940c061005880801c8515000300f07001c903804c078140c4080c0070010030390018030307100100e180ca410b01a0041032070050b6803000d03022300c1c9c1c0403451 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437916034 1250 437914784 437914787
    0x307030e0703080a021c0212040e2205061008060408040317070813170c030703150b0405150315040f03050708070b09010b03011104030c050904020a05060f032a1207 72
    0x20005990043d02c8166240520900a5030f900384080360010718150908040346a28404100c8080410540a003540340c10301e803112981031b00314090200070b03a03003803d0341001400d0100b08256050407882800a004a480d01020a4040303004991010b41e20341c008008000010f0007110803a810f99500a9220901800c0103400a200e4016a00000e00c0284001b4942c2c150000b400e80c00411100000c01426018144080c11a00c071140b20440c560107034442c08080c00040c441003203d0300e1910407404000750380c44008000800b035410546070103004950300018038070079080a110303150340310542c40045400d909059a0b04020012804009030801030003041070004c004031036044620940d04681d5a100754149000c0c81e500030207041d03108501c25032030010402d40d42d0081c0005d030f41c00c82c1c0d0084480c0b41407914140602a103010014000c0b039004030070042c007007401c0e41c0700782c041c1890a00f070b05e401c103480349801c90070503020f84140550ba40b1004a044080c00759614500d04481c801031002045d8644c0d905c42490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437917284 1250 437916034 437916043
    0x20c010c0b180d020109170c030316030b0a0608010f090207081204150501060e090708010617060a080601302310060602030c1507092102190513060b0307030e 69
    0x6080b0024010f140c20b1042c82c6a05411400d0568010b00000700444a100c04407003c6101e0041c1850181d001400040c00c0c0303062801c035420702d034940d50401060826140c40005d40c1460f4980200c40800c8000d00103000e4052804d0340d50300070300404d20046240142c4c0762034a1880f40140610f20036105103020000d02004002d562021001229400c103000e156141c000240144a0350b80c1c9a41c09100c11000107100c1c107104050b41c604070317001610b0740302590180c1880354542c844000e000a4012080103400207078080100a1940240a42c0b14030a1f25860420140d000c80019880e40380455000c5541c610003050030700355941004a00700310040a034006001036207050000c507203841b007482d6150541c0000d0f00f9801000030220740400ca41564200380500351440c001900c280c0d010b200041802c0b0045c000344203401c0d0b20380880b00c0c5801c00580740d5070040d4006440c03000b040041f0b8410020341d51007081075080800d034448840358004c03402d01c0200d04084079542d407070100a091904050300c0d0141c40e4040c140520 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437918534 1250 437917284 437917321
    0x606150d09020d06090303051f0909051507020d110714010c230303070e062703160b0414030a15051003060e030306091612020d0b030d031b020c010c0b 66
    0xf840c02c0010003072401c19000800500c3e07010741c0880d06180010307448120f981c400c3c5100b01c2002c441b8103031042c2003010090003452444411240c0e80b040241c000c0c81105c030700c07020910505072540100304c0c140403200010044420502402c000d580001c0082c00151f05041004462280c01e1a040206181c01c2c00c101c00d801100300001644e02800d0080c0400070403001c4000d600c200780e107490310704030b005c03420701840110700c82c407000f00014100131410134480c05071061160030318940c020704075031041c000c5014030048070440e60700900300352000007400c000c0241c21801109940313038202c02410102600351143d404402e0448214048070341d44000141c4800350030b0160030082c68000f481000040c01e800701103580c80c2e2081e584213114840603000541e62803800b034800d103c0c44042c1c3d80c407a103114001c0080080a2b401000c1020541500d98002c0300064a0800101e040c2e2100e039074000c2041149000003c0102141d50f1002017103401280104001380d81018800a06950001e483c240e030740e079103029804100c03103076a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437919784 1250 437918534 437918539
    0x12060d0206120403030b0114030f04050c030f0a0210051216091503050414121b0114041a01060f050a1805041404060b030304050f04020901031e0f05090606150d0902 72
    0x4140b51003081d1001107064403e40c42500c2c2001409400c0b030054034640c1204050300b00e0032500f00006419403c0c6160f000703400c644500215000030f0003d20001c1c4c2020b00c03c2e01107441562203640303050706500d0012110b0602a5850403c9460003916001640f0350b034074018040800c40044904c0c1c01d2380244610150401842c81030029276018120707001c010301a05090340c060b500381000e024005811a008201e40000400c1c1c1c0768a28680345808040c1c441c07041e8034510b450420755840442003041c01c0b012540502c2a40300348402c80e10415050f910300510401a0003020802c1705504194a01a801100701c9000790310900344071aa051035416030034098441c50304640d4101d414014038119000116a040340103078402c100902403848924280b654078000c9104550f480120607452829904042c0c2c000c25903c0c0b0b040c500810740c0704214460f42d0038148a50480780800341e4401c0c00c3c42421b122407180310707001035040c0054451402e003100080c00d842014000122a444001581d0841c1004c541c1701c1000950301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437921034 1250 437919784 437919787
    0x90a200409020a08151c060e010908031f060815041d07061101090201051e090a230103060b0702102007030308060402120406150e0a0603140d0512060d0206 68
    0x200e12022019400050f261404030b200800403400d205006140c42e0f15115000e0710343c034803500c3c0c1c40c210382c190141741c0a41618640d030784040300d030a202c1003030042010250003410040c2c3c1c0d81c00c00401a01d190000080c008010b0211170005004855122140703e40020929421503a981c0500c0d00290080c100310060403080002e103840a1404007010543d0f0003154119211b01113020024048070b802c0e111241002800280200010020300d00c6203000c2ca0765104614400b941825103c201040140e0394030381025008a103059411003c00c8000b8090400341c10081c42c0c240708891400d15400301c030f402071100007807192028502c2e140005108040405121070407400300780400c40c1078810103444071128081500051400340002e00c01381001c1c000c4031209042d5052800c0c003681c1d292117090062140c007603000c4422945140015019440452407406402d1034500007482c0c0d4594906181c203a602c84802c0c03201900048242c10110f034001e001d6501c000c00582403407500e80e40c1d11000032140207074910000c0d8410310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437922284 1250 437921034 437921039
    0x50c041d0a11190e0a090c18090c0f0b0d020a110a11090a02160f020a05180f0601030c080403080714030a020c071e060e03070f032f090a2004 62
    0x300c8a654034240b440c207803158031142d0754040340a028111140602c2c507a03507411001054408401e031b4409019107000b0f480329000706484154400a5003000308100c0000b40d168221801406889440700000b041055440d0041d540391020240c1180902140f00075001d85c04604616520b009140040c01030740540b0594207540d0f99803401085241d0242c803454040c54cc5400050342c1812140f0898158221400614820341c00d180e54a0145610700b040c2240c0100d029040054691103103220096240001442c03c8114907055600b001c00d0400200090704141c20590044013172174000818681054043c0742c104a2581e4014040d500034600120501c1042070010401030300d48010fa001d000c17200e900c581521001e0b0343e80ea84400c18926004180310340c044454504000e0140210301c0d203001c100016040ea12032503074030000e10701c0119041e801034400b0660580c054201004a00362030703c83c0300e0304e07041481120264601040c05414010000b15074241d407412001034080b080031030b2406e0f8000c508440d40c1c2c0c03030740c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437923534 1250 437922284 437922293
    0x9270c0e16030b1801031e06050c0408011a0f060c0705100e011101060605030744092b030b130b01030e030903030706020306010917030301060e0607050c041d0a 70
    0x404101c4101d000030b14082c1c1002c05454482110001140c1c00411000300e85d0a41d107800d0003242d20115541c045098040944000404900400303109041c900c1e9070540b2207141c00c0b0340c24203451a507035850035003e00c812081c20f15596100e0484644102c180c6600f512008080c9403076250091380c0d040f003940030072101e0b01e803e01d9907400000860000e4081c2d13962801d10726680782250030782e04540681c1c00490801d1002a14051041400d81d2481c0500c201c02400c405854060000b84003900614074030039500b01c45048004031841e15206e80201c102070051502c1d010100c801e40c41d140100c00000200d25070b01e44000766492081e00450000c9070002d0800001080d0040d1140050600080090119040a440c1d040180d07010054071801e9002501035403034500300e40e940700000d5100400ba141803007803485010401003102038918a002d203801008660703d506059001c3e1131071103c0081d0701c0c401d6804220303003c0011404920106a840103a5005c82d402952103003800c04011070304411030300d074880c0359054820300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437924784 1250 437923534 437923561
    0x1401180909020a090903080606161407090c020f0c011d0915030c060403030503060d140601090606172205010b062101171513140c01030609270c0e 64
    0x1240300300c4560303200f80c4d40e450100d02079889005001c0d011500c1c000005100f41007150042c141610803600f4000e40802c1661901c8056900c100721450a510803002804104060b00c01d0039071000c1140001e0089007070800d85540e485030654030032410840700d03000810700100320050380f40c43c3d140018000806494000405000e081540c001c091280c42406000714031400c002c0102c5060f80c0c0c0681c0c82c603256503600d4092010101c41c00f0000c54140032000080c4801803421b024141c00ba005e040d40200d1400d02d0004020000c6d42e900c41c3e20a1000d01c03030f000f0700180316000d0404010396103d0302600450340e012800c0260041000034601d580080f4000b071244076a01400c40c401c9440c2a08505150840e41c80303450341401441c65418200d050342c49003102e1149013405084460344243e0035220421122001e0b40c3d0070448500070040070380603601ca0100c3c010035607050b01860000c0d004c002c004100410b01c2045150f1845000501103200350110700059003400200e42c2050050029010914051309040344a41c00f41c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437926034 1250 437924784 437924801
    0xd0c03090929010e010c030c051002070308090f070f1206060b0415030e010203070e0d050321070318051002090d0c0303091e050901090b01030e010903020105090c0102011514011809 79
    0x400001c102d0040c2c9540c003075581241c00d91410303034400c42c01ca0b200d80d0301a101c2c0211440241e50314482d602140d58100c81e42c0c0001e2103900d01c02d0b6500e011901304401101d10308003000350000615008040c050204804e0400d5a000f01d07800c41c410060380741d0640c203004008020035081142605000200400e0250442188030b407450b815650030000e200c1d512081500300d000a807807080000c0c007180c0d41081d66140c0584d204012501450540e854084503041079084d400840000c4d0001c64400f00c00c100c00d96070136104010000c6201212503030400ca00b90f8840340c41c3d405080d0030000d465800721b5000400d4580c1241c40066942c429806c80c1e07010345034280a2300c00004e40c0b08401c0d8400b00e0303112800704a861151500d08943c00600044140d07401e240b01f0321b024103522200907042580d42c810859a4032030034080d84048a003e0380002072681000500c050600c035104907030030306583c10141402d02c0400161410022202880c159038007541034100101c9018600f591018080f6101a0f0003083d011885c1e8042082d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437927284 1250 437926034 437926091
    0x10806010c470a1104090204060810091814013801111b0f0607060605040b011704110d050303040501141501020a15020d0c1d120d0c030909 61
    0x10000e00115203a255014845820300b0528070580400c2000e8110f80140b18400c0c40e1511560425843d08121800ca801c2680808001182103050102ca07402c0c1c150b800c400307005c840c0b5040c40750320315455100d4034810115a00601c601321b400302c0040b91034402e601502034401c40c0d03000130042110360745211001122210002c40d040d081e119080310598041c503030464580343e0003405000c25401a007130f120f51030007005170340581200082d8070102580e0f5a8400400040b44200d0001407113606200c2800101c0c2e40180700039040c0041186000390140f032604502b940700394007403500c501130b481020114011517110346009006100100c240010080c041d003108607002005250710495555244081c01010000300079a07016030024220300010646c0311400684c3e030020020003601c0c0441c1c0b0340d600301c21140b0020080c0e000880d980d0540300550031071030500030304810441d09007404800b0340c03040b50b0311407a150451100b0b00c25515a030008050044090f0001443c204100700400018000c90040d6086005030040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437928534 1250 437927284 437927363
    0x7060e0d02071809060209120f070906060504050402160215030915040308041e15090b01050d051c0c0c06032708040611010e0307030c030801090207050606010806010c 73
    0x61610000c0c14030225407040e15940880f40304038598000405218106649083c1c08000c011590348865080d104c01e020064000d00303282c20008481400c2070f0483d0001010326040c90340070080c0b242e1000c2560140d0340100e400598860034072810380d800e5403000b4002500300e152800304507207124851000e54814401c81c01a1241000850041d01c030003501214002c02151004004c0b40109201341d00022203a014800c4030743c0c190410740c444080e18445000c0c80c028907a100ca03c40f20410145650729801404180c401f440c504c6442d41d105602d421031242220107030310440d034210700e0302807250768040c11498010400c1d03441c5a40b56003008003c0c0440400111001c500c8a0004020b0000240c0c5205001d801c0750307045c0c1c2070905124044800b2044114144034a6495002c61049040203100074500940f1940302c28640303801c2464040c10410701603011081039881030144d200458801309d03107140e103c80c0900c0e04070341c1ea94505005130b50990600718094554060042d550b00c2e0003045501c2031091810000d8400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437929784 1250 437928534 437928553
    0x1b010501270c1205041e1202010c051606020c1011030a0614090403080c07081804060f030506070e06280e0402090f09042301060501030c09051e030f0307060e 69
    0x20068a00c402c0c1a00d0000300100c2e002000c4070041e0340b101c1d0300079100e05030701030501d900664142c2c014403541c401a2000c029007002111300e150240b00d2088181200e08000e070406000d200c6150a001c0003c501809207500000e2906c070440c0b0512503c20000c564840070030034980c00c05c038601c0ba26042203608858032441c0c60390200b04000080c8020000c1f0400403d50710481e502c6131740807101d00300302400f00c0e8103000c0305101c03400008a543c0064100c810034104003280744401d95003004141c80d50755024608141c401c0c602071002c20030105580341d10a600c0e0400c000380504550201c2d90500c80d0300300000b01e19500e980d9040040d0b650b4400681242d01994515244a0154040004922901d6aa2580b00c2038000312010381d800c00500c41030b4001d0203001000d04080c07449480c1d41c200d440426407203550380d540d10801d000a40c0c061244d40481100b0b40b800c0ca01c1a03050401194012280c00486202c0685030140c2500c182d8040107980b01024801c400d0300c3c0c65a14038a864006403424041500880c082c51018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437931034 1250 437929784 437929859
    0xc03020d09030f12030b03010207150c0e010903060b0f0a080d1701050f0103050604091208220809090402040e030a020d031409070b16021c060507180b1b010501 70
    0x30942038940080d00f00c036400f2015560300f00d40c2e82c001c0e0160380074192100c0d0070383c0c0c45580c00e1014140c01406062000d40e092800000702d000c03100c0210380141170044101d020034580c0d9200042c0710941c0c1e800680090101d06000000d9224203560404590050034907102148034030300441d284846002e1616518001212aa01103031103503003d0141c56080b012600c8034801c29071198026903003002000d0000109400b0300d48030f021005c107804852001180000c8240000031586403001d10100840a141c112200c1840d80c0f0600c662250107602c6108251180104040d5510760344401e00901d040d03400c695403580ca5600183d282c805400761800400d00d0031120340f5441c034041d28064898030604000e4141c450601044103802d03007050401a01c500c0c60802080d0058071032030109004213002c81000180031080d841c0810503a5030084c40141002403010b000300c01c03852040c2d07145080d100f00401023a124003a81c4525010b40b5030101c940c0c1e10719030912000007840403550828000c02d5440d0040301c105100600798 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437932284 1250 437931034 437931047
    0x9030403050c0d240c230d0c030f0501090203060a060e01020601091a03010504111c1101140f070803010e0901091703070c0503030c07020319080904150e07080702070504140c03041a01060c03020d 85
    0x9604100c02e00f00031104054887e0361016403000c00c6800d00013444101d0340c1b2440101c4a0981111100c140d00100b07100d540e29081790400300404640c41d0070301c008040c3c3d50000b511030784188a40d041d500d8a440e03c200000303c012a40a80c2c943c4050000c20041ca81402d1485c904481c1c079005034040c280c982c051101c0c0031803403107801c2c9071141c002c102020204100c0004460701815612100741c080030500c860f80c0c090800388020034a0600604c1c1c038645075410200c031480240b6000e0100030213a0b150450385c02c002000100c0910010602d100d1203516a80c5228050303a01c00c050340c8006006000c00800c1226000100d0045c00b90140260100c0e140c040c81c90b12072404a009040020300380d541c051004103640d16280c0c2083d0005440e1255001c80c0a03603410081c98071500580d07001e0b000c200e0132010421040c1e41000740d80021b003403c030303001e00c04012040000384100c50064508a004c6c00000005404c0c0030282c8500030350100c0c0888003120300e42e0f41d1071008240c1c00d181c100c218014080e94540085c414407491 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437933534 1250 437932284 437932337
    0x1b01080630010b1503091615030b0118060207080f031309020d020f04260607090905100518040c08060c0306040902010c06050a0902030609030403050c0d240c 69
    0x541c2003a5400e0440141070400d0305101c1500055922210350700f1094032030307008016040c005885900d480c2d00f0300007805400d0851600400b900740052210030400c20316a000400784e0712983e4180000c09804400c0125120540c4a01d42108812050030000d122079000450b40112107243c4207448a071400503014686a00c82d854000681e24150300b030520030304106074001c20380e02d40c00d0000140303001031000c3e00340f0064019a00c084040707441481903052101a59002041906082010303240d50b07c2d081e20007404a070000d00514900c6035481e8000b61071840b5641c40c01000e0807005102090040340c0c1c00d8401070f011000c42e030456803188507103800101c1103000168240180c1403c506275046940c1c013002c0c8001845050002e90400603280d60510208100d032140901607600004085801c04e542d0040c5843d26070080c11400d92070307100b00b0080020810106100c012030307000b151445140f11352828040045460001924161980444149200350440e40a15031003840c5c1c2e00c6064040c5070184441580ca0040c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437934784 1250 437933534 437933569
    0xf15030510090c0509100f0f050f0d03020319050705030c030a14070b0403210f0204090b0f030303010302010c0f12050904050609040c0312120203010f05180c0409020711031b010806 79
    0xc3c070040c001441c01503043d541c410544c461354900d0a90700c0c0d0b05180540456070003203c110703d000c6018400e90908454201c07a0050990b1901c01402250360000e507640f0400040079501c0141003440d1462510400484101c160004101e0b600ca601d4200c0b01c80e180e50000915074003207511442e008411410349416104500c0c0c2015007143e1584d00d0341c80958441841c1426001d05d000ca00b1414400c1c2c00103817280102000f10642c006807164101070601c011540c5000d401ca00c102806481d02c815550004112410745e0341c28645801c0c1c003002e07031801065802032040000c00604889181e0310b405a0b0020103001d20f1101103a042c0301c0e685410050100b25501074502415079503100c4002e00c04a074003900b1092409510b494072001140e81006440100d0b04203070031800306c061910104100038642401c1d00c0c84107040094410303c480c01c0c202c0c03101c0460f11451080c003401c541c001c24400c2c05e02424000014000382c1c0a8151103141c0c010300b00b0816170741c4442c4101400700d11444085200e07030170b00d416054400300d0302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437936034 1250 437934784 437934803
    0x210f080411010507020f041a0a061719020f0304050303150a080c040507020705150c100b0904030c0501110d0b0307060f0e0d0c0312080411040504030e130f1503051009 73
    0x4040110f41e26480640d09a8001070454102074035601e49100b83d2000003090322142031500310b41c008001c0010700036409001004040d411007440451450020398006a100301240c91060a280000019018201c04140102808820070043c40000701c001c500c1425006881076907412800301304841c41c1d013980190840c1e680840480409070500f80d00c8190094201c0c0109da52240e1350b68005041c4180d1000f005215100c0404c0c400e440e00e00c10007030407020f100759142c03c3c03142c0c14100700130901c0640f00130006420003e0b00764a8606014007036203c0d140c401c2c200c0d90030f1982d441d240145580a0300c025001c4c41d00a11400c4800a14544603419010040355150380710350042e28450308010410007003080a0320884110340f0000006250300c0038a419940803500c0c0c03565285840d0500c00c1c00c0900e2809a079000b40c0c200800c100c0040e0340303c3d0041d109948100da1a491000d0100280401024070304030303000200c1c0c41d08841061208a14003440d044910501c1124241480113110200f90784400b1001815400e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437937284 1250 437936034 437936063
    0x150406050a18060f081314010603022d100908010c0302031e0c161b0e040b18064c0f1802070f0510090c0e070816020703210f0804 57
    0xc242c0604c1e4100144444465105c82c0c41e441c0c047c00c4a101c485920003983d5a10300400450600c0c0310114601c01d5454146003d0400442150030284807507880705205041e4107090800305806030f1565000345c85018003c101000c685003020380254010765502d22410001504a4a801d102c1500d403072054451030005401c100f0414910781441508000440300360004c00024540c000c0480495801418000b0601c06113041c6410074001418002d0494800e000f00b01d4000e45000f0700000315150090419500000b007400e41c160041c01c0d050280d00380810340c1c0c940c00c071680303600ea0402d41007140201c015811076038100c0e514103541034011502d1248c0d0750244004080d0b40c1810143c2d0f40034180c018001c00c000c1510f00c0407660341d00d0a11200e90b0038113806c0c82c0e6444c0f00c101440144010a8003421804420100c9800c00d03000c06001580002c06400446c160300d245030104030310070300040d03004551150107486815031003440940e18186803241c3c040040d121b9201085032600c030b0403010b030040e074020300710428052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437938534 1250 437937284 437937287
    0x50c1503091c0306030206070501050a1508070e0a2307020708191506051503040b010b0403020108151f080412020601061b0201020a1502030a0506092202150406050a18060f 75
    0xb40819110ba040c10b5540b1000805a2542070040041e14850030001415107006601401203030110f80c0182c40d8200d000d1014000e04000107000416a4106408909a980e0720440b190192003414400520200d0704101ca4264100c201a441d004240b00e409981841b511a406c4958481c4240c1d00307107124141050898000c1341c0824050000301300314000c00304129172a600070a000350210b000a2454070701c00800c0006200c0e00c28102805405000c1200303280c40c0c659000244440805080c4c650048505e050200e030750381d01c1844644040307103882924038070340b0b50700000608503031340890781030710014558007072820a94408140541a12915280c2030186204100301160032013804808030b05520411020101280c604585100030711021760340580d4915110703030800255040685114000c1030300e81e080c00071240d145080112b1940e1134414840c00649513000180d1031140060382d04041000c00940803804542c4000201844606501d4901590f94807100c500140e400c40c0c8690700008a6541c0f0011b03006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437939784 1250 437938534 437938573
    0x607021b03030c010501260307030e0402210c090306091603230105160e03060601050d02070503093601030c03082a010615230309100603050c150309 65
    0x10000350480b4100400c0d0f801e69402c4500a0b000b400c29640e14a032250b49880c0c040303d4070002d50f00040c001d14102599994040c100301550001c4510941d00410110001480e8410300549001d882040c21880e05201350000702030b5000c40c80781070003401004009900508001010580301d40d040881a50451940e01d8001c0400500100c18100c2011040c401c1c010700024060b00307006201070b10340f447c404401480050b00c00c0740307203038281390090f04030004010f000e1380c01a0541c0d4140c0003204015a6541051400030304511030480b640353f11043c40c81c2402940860070304608010703c0c044070041c484006003403100304092000d200007080f0701c0c0039640c00e00c0094a81c0015141c076400c8003104042c00801c11054000e02880749a0030403e503136550600b0041030410520323226446206050404070007100301e041c500707803106106e85050410000000f244888008200150910511500402a2035101d20302980c0303e104124245110b0b24400d081e040c659441d80d4101e90054503203000600c0108800395054652 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437941034 1250 437939784 437939833
    0xd03050d060305100501090e060c0901030209030718140f070309060b03240a0b030c194e0609020609030304030503091306030f0303050a09120c0203010b0102060702 72
    0x4029050295045203803081c020600618490000740c00307141e80040b150000c44205070b10404c941401c2601000c00d2600126a040e00103241c00e2400c0e42d13820305400140c0c06032056240310707901072040c0c3e030b40001d54038089118441c5c01210220244403080034121009003a001c00c0d038150641d1610000442c0f27803280268884050103100300e40101f0220070b030300c0010703037008030034a88a000300230880c0ca0400410043d28100740d202c00080000c2190000b0f00340400d42d1812a1400103004030300b1508030010890f0f003180c880000f0000700341c040040b0a1440100300000b03c403020f91041b091400700c2d0349400506203e0701d440c40d0701041e500d401c0c0310003460344503c00a000c80e50410398000c002007141021585041c0010301c041e42c000c40c01959a200500b003400441c40c103038540b80107818981034003400011003280794032800e5501803602180d96142c41360354030020328400700c2c0204504020003088407001d42017130354140c505008a000700060340c40003005a0300d03a50121070990040e08800041d10046840d41a09100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437942284 1250 437941034 437941037
    0x601020d0e04091502030907050307210c0e09030c0706030902090a0f14091501050603012625060e09011503091109010f08071203020303181005040c061206050a050d03 73
    0x1920f0074191610b140c10704881c1c0c02c40c61000c1d00001040421076003000340324010b002c194024055940741581c0141c1c203486401a8581010108201c03005000b05a80080082c2900007200d56440c10010b0362a55650b010400000e0a07006100000408034028031501911680161402c1c1d81076403180c07031017002003038440300700703034142c2c0d07030341800f0390403940e10741d00300b62141003100010001904c1c0460f000080c0031059001d58443d400030001809522540840000300391003401d05a07044450006d8a01d0806400603070024645641700750811100c02045800d42c00c440040c2c40d41d00000e5580810300c42c10340c200740141040c7d0355403120750200162195010100f45405041c000d00085d0f800c1e400540445000c1c2d1082600098811061115400500c40b60008019603c00d030300c0e10314010b6901035168000204103090842d11645840e1740c00b0018805459003105403081004940342034500125076080b0790082c4130000d501c0790045c0781c2d00226880351105070f40005041d081c1207840c00c010071540d12400c4800700e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437943534 1250 437942284 437942291
    0x512011b030209030c040501151b0510050708090a0f0305030c070f060b040b030a0f020f0a080a03090e01060e030705090a1e0501031104020414090604020f0f1b060601020d0e04 77
    0x1003141208104900c80aa590143e66500704408040c50203141d607030028452450080104046020804600001039203070501400c805558042011a4414048090214010003002406172050f83e80168450710080d16a03225a03210060126543c00c1c0300c00300104000004000440820300400185074070036684008145865010b903560504d007400791004035013594030f0740b9000a01f8035040c012021203103003d80c0100b84407a09912981404141c0590107030040060600b0700c4010740790741d08284058142002141c454130110b02d40280340c0c8816101c0c15251100d00000032400901c146d4112140d100002d0040001d03504040400185041c061300605406641d40580c4514403603a407101d51412651000000c0d071507156017040c02298400305502d62090303104100600c1160f015810950105030250752540302d42d42c59001050003807245c0c044402e290540810740f80181c90141c4020051001c01150180030b00981c40c0c41d296841c0021b03079026000da04880181751075184101d0585a01707103002000413 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437944784 1250 437943534 437943551
    0x6010e041a030d0e09012907030302040302090411030705190b0c01090525061707031d01022b0e03040b0708190306030303230127061d090102040e01051201 68
    0x103890400a950080e0101d68064601c41c130301d25000f84040e0041090612500092501c0540e01142842402031a010800e01154260515100358161006154040c0141100f401c0505080d80810a4440a0b41c4240f06a03000407070030303050158003440f00510080e01c030090306061140da140680c110f061040040d66a91540a0105100f080301c250300b6505840460130100100040100003110358005c83c052021100d16540c0c4140c0007a1034640c4070540f03213070008260f200c160340441100403950000c0740c00e60001c2003031402c00d00344803050000403800101c01e81c0307c1c802c01100142a02c803002420b401542050104000380c060803001061000d2240010300c0c54180416130301504036101980b80e00001381c0c0d4000a008043c0c0520400c00c0e807421070091840790076150102d117078807504140284508808407640110b00f001046402c0c1603c1651b41000b0b003e12a01c6031041c02840003007009210340a43d03901b000ca400004113200303c4081c0c2e150081c500c1043c3c2c0c28802400030503a02201a4562596101c259 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437946034 1250 437944784 437944789
    0x608061212030a020a0f0e060909090a0606150e0429060706090b15030a0203070504021303081803062a030408071a10140604180b0312030a0c0806010e041a 68
    0x1140f10307805070703d00183c445010b280300901035400e1346040814018003a00981c120394640701660528101250420000d907503244495050542c02c9900408927414030b180071600407040d140c030141280240d5101152030303540b0420041914103084125030f10131407942c1d00c500d00b04504040001817840c064021482d001d02036489504840c0c0326401907900c500705006014644800c60f14800e071420007100246510001c0340c001a48448092103607034400d0703a000401c85100301d02c445042c0300558211300d0042e01d459401003194003040c1c084401d00c0c428024000021000c02e105062140214405041c0d40548013102000c04000e90002e41700341c0d081da1040c003420740002c05503556980300c0003904007044180c3c14440c40c2c059090440307411612000c0c5044203c0c500303d0701d070308094074120350b202100b66401503001c1d800f02c0010440718100d40c1c2c16000d618030007001c142030304000f540103038402c2c1c408100c0c6803554142101c81010550301c250000d41c0d03402140500b0300d00341e000403640c000740940500c59100242c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437947284 1250 437946034 437946037
    0x90a0b011a0f0f1809041505070212070507030b010902030103051905101a18070f0e0609040c020a0b060303271207061709060105030307080a020309031608010c090608061212 76
    0x150041400041013034082480108101d41c02c1801c0d00c1000807800c01b50750707a0b40350300083d5240584040d59480050303903070b070b00c2000140448440035528075650f4403076040690304c81c1c1003408150381044000b40005003244152085038100c0b5081009403c26010100c1034a08030032104402341c0ea20720078040075040d40c0000f80304075403a1607a01c4200c460559140000d2080c051510b018112410b606042000340c00da401101090001711a0714205ca8681c1c01030740060054051031342044d4211703181c82c03609096035800140e45240f0078050141d4044554078441019528417420884030f00341c40c040600c40030f03010301d203810341004100020051764448003068020b0345001d8082d4840030000d0304501810810380000a501c981180002c0040d010740c0d0b04020210f83e5a20843c00c0040c5920000544000320718400d105841600ea002030a9130f03103070640c039800c00d0800d52a90260700344035403803e1611110b0501032844030701240c060740c452010503522502041001040e0980d000420301546c004054042103980 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437948534 1250 437947284 437947297
    0x9100c0206040b07050f0a02010e0409030c200108010b090d030e06070b0403051c020301050a030311070e1312020109120e030102160b04061404050a02060f16050f06090a0b011a0f 78
    0x1c406507121134280c10120710b0484902040d80483c0c010300048000350364440c00d6000804416100407a01114600d42190300b0f0004c08009000296860b0b83c0c00760711480c0d50001484034100b66220101643c031751034084001e00c20500722941c03001c404c3c0701600c0003d018050807103040a00510b200d007401803030749800704186800c98007100042c000113005850305070a0645039408114400085046605140c00300e000e00b00c01c0d0001909000c10098020010201040320740c001d40040082d003a04c6082088164800b4109141c0c12202c244903403d41c03200440c8144510b059007038116400070441c8461210507a682c0d00020340082d055502005404040c5065907801c90750f00344a03a0400b903c0b8501410b00c40210b90020b0303054880c04481c50240008034070005940d00c0802d40442d8000e544110007101a0001d1003a071103000780390810b4041c148107004001c220811804030300c4042d6072403550b03008080344c3c691408040081c100001e000045c41031034a000100c8042d035094200161a00ca05408687c44c1c1c0d0700001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437949640 1106 437948534 437948549
    0x1c1a0a0b0c0118140d03020a17040309050301092307052803140c0111012d02040b0301030c0311040513030c061d01060314030301060509100c020604 65
    0x83d403200c50301d035408080304080a109450a43d0181085003000300c1e0600405170401410344c040c0c000c5071b40d810aa07540f00f00130b9094060b12090007420140003581007080c104000b04494409200d100c030f209016690841131001106000c00300f09022511b2018150400c400c05c00c03040c1c564800c0d01101c4003541c00d48a0070103250b072070320403e00c2d1440c1e800902807400e03045090b401000007085455800d10280e988502044000d0301c61801e032089103c008000e281c95010721814034100e4540c00001c090040310261401340d1380c42c3c580c2c2d00c5070002e81040e81c8000406504104000c48141054a8082d007075134144964500b003408009a0b000c00070001d400e000205101d242045001c4c0d203c1300e154050035121f00ca000b0000c030680c034001c003081d0000311003400c0c4050003c0340c040000030540b03040715159500c142c500200c903020700c80b040194003000c90a004040c0c0c401e8005944800240001c2c00c4c41d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 437769784 437949640 := by
  have h0 := BRFrame.cov_init 437769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437769784 ≤ n) (h2 : n < 437949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
