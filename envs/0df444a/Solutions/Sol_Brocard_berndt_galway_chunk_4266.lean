-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:03:25.279913+00:00
-- url     : https://prove2.me/submissions/9e6fb029-29b9-4509-bbe3-fe8c713d6181

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767086330 ≤ n < 767266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767087580 1250 767086330 767086339
    0xe011e090b091f1a030609010e010f030f05030f0706020a1701050d20031e210304060e010f021603090e0c0304020105070302190c15180504021608030c0405 68
    0x180020210128058400103440080010040796121640c00d00d0342100c512881c8001c10440c41e0008040700500711800e114001c000c003036992464130a0a001c00c102c8180d02440600c211100100304000301046048162a80321540b441081c0c000d007401c9195024001d4183e4907100c0003e841c0e01040f140b540203200d112807584030070400c4c510003808100305440910070320744c1152110701c0f2400000d402002803011214004038110313046950801291410200c1110004460b014201f0201001c0007045501021600c500305800c01c0d010600d040c640c2c0e4000584001e0100383c445a5080442c42c0030b403c80080c00151907000c54586820307076500992201b0b2a0800c0e0081035001c0004038aa05800004611405401c450703e8a5a1110344c0116002c4c0d108002c140d0460284640c08800299105080c20300d582c0103844c968002801c21101a500345800a400d8092154020340a00704003443c10540c0d017159011500140c03150884140303140c1e20100260010451b410000130024402c01d01005881a40e00584 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767088830 1250 767087580 767087639
    0xb1003020906150712080a0c0315150507061a1f1d0127091d0d05210c0a0905040207051b060909090d0212180603061c03020a0203010509072d0e01 64
    0x6400e400703c64808550008ac0e1248407c1403110020100400d400f516541c5400da103042201e484580440e6017401040c0001000d64507000702a143c078200428580090302d241f039000700c03940c5001421002a1911003000840400c8030321002c2d038007e40e4a40c228100480c54050202c0151214034601e100500901c1803d9140500c12a034000140b03181107031106100005200c5501115410364a03504005080c0020300b00d56561300c000e0700703074401840e4020200030240d0740c1c4541c001c88020704807010700e07000103010300d20603c4132102003074001401c454510740b4020030105199070382c00425800c0c850744101c190000001401d225035040b00142c00075185c4000d50a50b00000c20aa481c80a00e2140101c034100d81060000100b40501e071441c01950090002828070f504848200d0703480d0b0300c0031401075003900503800c0750311b40005505081c0503040c2c0c8694000c014040326405c10156000c04800c00c0880c1c0d145401c40d11103000826028804280601106044840f4940e51049040d40702c40100c80b4460806404a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767090080 1250 767088830 767088851
    0xc1d130213090f05061605040b0c0c0a0603020408060105150d050a06080d080405210a14070210050d0518070909050c0301050127140c0304020109030206160b1003020906150712080a 79
    0x10790546501580c1b41e80c50f145850b1800d060403c180d00300c041d14a125001321060040c03e5907890640500030600c0b51070243e2034924140f881ca08008059211a005000340e44a038500d444940d000c84541c0312000c9400605c0b91100f00d4420000e00701500003040a201c0c4650300e03400b81d0740185400784918444c408030345050343ea4440e0007444003106113079004a94802d00c9003103200703030040003241030420b5018405401c1444640010364003095058603e0701054001070101c01c804024007420340d2003094401122211078074140099076440991040070325090b1340b52105d00c10000c0500c1315000c2120014000e005c5540c640b45899030120010004c601d060b0706003a41882619520301500c08250040280d826070f40c0e0f6001403e00d081c3d80002c000300d04000c200c50022005aa46c28040c080c00c01c90500c0c10702106119141840300c44001401091445104000409c01a0703110802030380d10900555108851000c82c4211010600441c4001088100e990300b4080c24a580301d40c000340325202d10380c0c0c1032110350b280 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767091330 1250 767090080 767090101
    0x705090f040c05030f07110313080c040e0c01270f170f0a0f0819080703060506040315201c291005070c120c1d130213090f0506 56
    0x302c4901d8404101d09100040042c120503e0031790748400d4038140058185540c041ca075040d507010160140c120106140103005440c2c0c10000f00b078040005840822001c031142c900b040c2c0e20032400904604200c0b0852498030701c0c150121004415021840950700c2c00c41c2c44d82e0b03144210001c1340c001c04001007010228003030710303000006500103038945183c0900600c0c2c402c0c0e118501444101307441031f1100c178001c20130303a6425148c05409841d52801580e940301c041c00c02050050a440c2c0347d5010a21038030081c07200b4004142c0480245824648a5400040ca40e00f0103005000d00c006081e0204200d1001084840416103400010101944244010080c900074850300c0780700c1c1000c0c0300340c0e4444403240c080f9528803030030400394201d2040c1741c3e0301b80716040520654820b07990020a070404480fa0400c0c2c40c05c5010000d02411100141610200c00249002e207403910154480b0700510b25110202e941030804103540b600c6441c04646840c0143c14032190410742400c100b01443d01204440c948155030000b40300008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767092580 1250 767091330 767091341
    0xf0206032215240b090418030801030204060b2113020a0b09090f04080901030f020904060816090c0f0f0509040608010c14163206090105010b040b1c0605090705090f04 73
    0x4240742040f030f055003001d400d003429030010502c05070420350700d21191000003074503815110018800d41d03900c03506604620510082c2c2e080d43e4041006d0010038480b04903804154103e52100441c6a07206408079a207a4240480c207a20010000e50040301d00d4002007000750306000100030041060350306412586a41b0310320110080122000307040c1034414005020558480c0e00540101a0591409424100b0b9030300014111030b2640d2040c0c001d41e021400c0c01c00d56041c10600d0200901480c0e0b01080210031881b005004500c25403c01c90410548081d210b0020b40100d040e2112400082c0c000c010303460b152034885000f00a00d050010124010700341000002151404460301c0003c0c0d142c050805900795690041da040440b20185568010440d070010b200d10324500b96074070354540e00014141c6082c00c006241c2191300c10303081030b24211810001031040002d144220b9034060b2120300941c125282d18801070b801410a40c01c0260300403140414061925071140181203624811544803007684170400410003102d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767093830 1250 767092580 767092631
    0xc01180803160815060901021f0605130e030a0c150203040602040806240f21061f0501021903030f050906160305130f02030304120326040f0206032215 66
    0x12182441348185041c0340c40a81248201030040760094080d0801c5424259955603a105c0060380c0c4520805c9240ba200c00054115407122a041000c0e26040c807145132a885071f0b4540106000b03440003240c0c00c010623030703103502d544900706101103450f4209171034030380e0107988644035441e040d115803400324100b0b2900040030202080320840081c6050f002c1820b00500c420201c403034907401402c0f040028003841d5280701429100c01400007034901c0d8503120400106201c001c016041c10010302c1c080a0041e40d03000600440e402c6034000d241c0c02d0a1602c0e02c1c04501410b01e00c403050703500324141400c2c00792140e800268240526111608003c0604c0609011811503c00710303007407101e040340c55071607a0100301601c065100c0e40d800a81501e19280e101c21800d250001c000c1c0040380001c051036001850f90b00030032010000310110f40206e040318200358441100d140b040d0071010f48075102c000041000c0e01c8040040501c0c1d80c49607d03856013460b0760390901091100c50460703038440b15414817896040c040c0c4003889000d03148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767095080 1250 767093830 767093851
    0xb070908150414070503010905030d060e091b2b110d03140d02070c0e01050415050d150615080a05010e07021009030c0f0605090c0303031302060c011808031608 70
    0x503551602c80b00d4000c00720720f0840401d4042d194001c210794400b806001d03203450240c0020341e49e070440700d400c8000b1610664805014403c9404c14020301c0d03032010910719240714409600d03004451001002405a440c0402c21240400c1d031000102880312501000c0003240d8014800c012401c8003400510806a1010b80000d000030820601100744820300c4020b00088401010010b0900c00e21750b540d40001802d83d00030210109864004208918241c0100755018001d00c01d041c10a501e400c1c081140c54051850041020f404540440c41c514107a40c8004001c0200c1c0e460b802c2c04c40c0e4402d0003d032540c402030b540010924200000070440000300420350f4001c854a41c0201003902c000c4903201d00074202a02d04508228540d661b14020890305054211801c0c000d540c00a40c50504404180c40c084034075000c0d40c0260011300030840015442d4003803081c0c1e550166506540c42c60b0305c0810724010240850121114003003c60240144042d0101852060300108144154031103401e106940b00d1000325182d1074038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767096330 1250 767095080 767095123
    0xe0406050937050f01020703120f06030809060912010204060306030303110702090f19060b0406120e0d0509040f020711090a090507050409110a080115090b060d090507120b070908 78
    0x2400340a6000c4030302d003c2d030207841000045100d0300b03081e43e00c851010380000c1c608140d201c1e07010089204400fa580d413403800c1008841d2135656410610300807180064030070b1002181c500015104c88410342510030352400210364450704c0d040041c0082c45640000d400203860600407d0000743e280080300d5116800501e94240d40e590f001040c0e44604001304044a1203140c50204003081c48540101c0300607100c00d406064496007040402080c20490a0002c1100c0c3e003003a0041c0b051040229144942159a203030241d550301c0c401c004500502032558114031210f20014480040c0f049200b08002c28030005caa810880d6201d2901c5041500d42c41100035203150031035081001030b880c00781c0c00b0f034910500c2420540b51562001001031550707151a840101360341d440e101181c81888540c9480b1000e400994410007045010380c001c02c07010700032407250a245a98541c0220180803040010324014241d07840309000c844000d00c3c0c0003c6e034440c240e8020021a0100b000451a4400400c800c01188404143d2200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767097580 1250 767096330 767096413
    0x50a091806021306080903030708070e030f100605040b090705040b030a0605190614180621130b0f01030203100f110406050301080d09030c090504020a0e04060509 71
    0x104005400012006040d0040304001141400904905110600e41581051030700002078030307951005000840380d0b0400c0040101d2142c010b2071460700032816290450407203520342c0109140650034040c804061103020103400181c901c0780c016800f900c4040d141400001c1080e0148040110103503104008100306110511100f000b00000c1d65200c01e18800105e45c0c42e039144085151000f042d85141d100502c0110705000854101c01c40440b200d60340b001151415859080060751196652501445002c0005419a088291001040d0f48a0401001071403d0414901a146081034804101c079044100c10018101d90b41158105041740d401a010b031074100c844106c031400400303808101e0b50300e8642e6192800c114680c0c2c0340103000a02150348a0329641d50600c8060b030b10308402c14042004100078000d05000040e020b10a0108a0b140700700082480e80b981c2c4001002c820712a00728515904c3c800d000c0000b8400d0070741102c2d004161500550304250003c0004406815080304411f10303d0303190011022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767098830 1250 767097580 767097599
    0x30e0307030807030908030903120c0c071a070804060903060b0103060b040b0d14131a060609011112070c211112150901061a03040312020a0e0d03080106030b0a050a 72
    0x1d030700c2000c504d80000c070720742150340c0c9503141e810a0300c0c0c1c40704940c0003040104015007402001c9409c0408200850b08120481a40d2580c6107824004c400014000c0101e110050645c007042d1401c60b54015803590f20b9580381c40c0018000b0340c03244400e41303e03541420b0600341194042d214150aa0751031218603031400b81820440c0c10691b01c0010700301d50103980c0b03030744507802444010721080c0070303980101c0c511022200038181143c64160300f4003034100821002040c1300c13aa0b40c0d054200c401071103080c240061010000302803181031942000c4004190746001030100e042000700700010069038000c9010303e507030903102e0351041046480c41100030144400300e6500402e5141c00d207640614151103e00300c40411070b081f4828440407005a03a140126074442d90144024421030080140481280c460745085103071a4500070000b030700c800d02003000c00307600040c1c42400078810034955030385603005040b03070325201a01e2800807c0d565003442540006890000b10804601d48000c0740340c1107600003801812914203144040e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767100080 1250 767098830 767098847
    0x31060e0f12010603030306090608061e06180903070204051530030d0b1c150207140f3007020906010e090a0603020a0510051602030708010e030409060501030e030703 72
    0x554480300e80220008020381c24054640954841d50303000c6071051620f540281a10010380003c2c00c41d821440800c4004400b55803c0d0303a0110400140c09056111100400c606050340319094051180f004200101100000010403a8500c2901d0410840ea188200201d04c5c0c04098495580b004000b107501d1075401007241c1040d4281744800c00900700000310b04403d840c581c829041004400d807107c0700c560a07440c241d00b012a401103958100410f0500c1950f901c000c03440c1d81341844003a20ba0205140b010b00c0807058243c01d0081c0041c1c200da44641000c02132a0341c801000742619107203102c083c0c00540d55031210f4010340d04166019045030410a0079070800c520041c0042c046410000320482c15003080e622401c02900400c0b001038005102821401842030032403003508694044c4601861108805a110007260209094041803112aa1103880020705101d0b41da4009034a660824007031142c2e400e0044020022a4211a001c1150035035030001034050701c0c03110005054075041440f4100101c0c1c001c8500c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 767101330 1250 767100080 767100109
    0x1003050c01081f090614030601060c0609060609020706050402032b0305041401050c07061a010801051c02120c0108060d03020a030f09030503070f030e090c0412080d0231060e 76
    0x801c3e44190543c8040040b850748007044843e25900200302441c0c1070f4221034641d2a0a50280040750b0600c80058540b00c26800c0051040350340e0400c500501c0801d61080b00540108ac00031366452000b8142003002d00002c4da0140e204c3c4c002c2da415101c0841140a50115500b62207101042c0403483e494241c2c01400014810340b1003020800035a00205004e114076441217062440c440d84aa541d13080290889181155035803d81c0c40004483c05141c0c2c000900f0b9044401c22075484800c10340c04a07400112034190100290010100381c040d400031080411200c05004080e0f0321055643c2d2804100f00880440701e4000d40903811412080d00843d10900800070b0109850401040003980ca0395039070310310352007000c059850782051295a4101607201031400300d0504220340d02c8000f400c09580704c41851080d40300320b00340c9804122808040103400015600390140d00c030021901e81c0e106881498101d6a0010104604186030f0221030ba0440584608000d417a8241e68000100880d07078144000780885104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 767102580 1250 767101330 767101351
    0x7121a04090f05060f070207060e0a0909030e03060c0c010b040603080a0e0a0b030703021902010507140a14031f0b0c0703172b0c02010b0105072a060201050108061003050c0108 77
    0x1a00702c041803041100c140220114552480c01d864003120003420a61150041c0e401c02c1400c2d0702c1c0c00d442d07968112030013040d900c03040800207120225150a440c1002e00007050354040c09081d0400c14000041805000019036103002030005050610030802110003a000003004803078180114a41544207039180003030000040c2003007840c1500d441308200e1039007084443c0c4000940024001007030211030601990300f000d403400240601d06010101030300c440201c10380450139500118a041c48035100d480718007001c0c100c244c22203a50b800c03c00d0620856080e2411660a01c65480c030000800401940484403101c03501000781c00420b056550340e880d8045040c0c8803050045081c02a80e40004805000c241000340d900140036441d800311400c1301c1560f8104c00c1c001c0c19a403405800030340b1660132000725482c255015103901c1e003911040580d905110007003090107102400645011034030075015402107041c0c55018080381c0c0f05586481c403112900000d030200804a07000310750743c21995401030f07003074a820840521 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 767103830 1250 767102580 767102603
    0x605060d021e0423070c060f020f0c300705071508040507050a0f03110a1e1e031703090a2a0e0108151801110307121a0409 54
    0xc000400d514a00e0b825444020b00c0010112058a4a845024503074403661620b8412900855040c802c01040200b140050200004030340c01007081c50342c030402c1180702c407107000c5459113000104511b554000780c800c155944111040700020040c0d024a2801480990800407034500790086076190680111508591030b100e1700302d0100724001034001314000a001035851400516290800e01c0c6045155407000e4024600c0700002e001e550083c0000005513070300315400100201030440404e01043c1c16901280d144c22030100c909418460110707541013114045000c000aa0bd074003850550454624400100584000c0c03e220301360075142c0380070316440141c540980d01d40c20b190786c44030b80c0c03c03c041400e880072030b8402c0c01d0960082410015582c0141011820002d42581441c400c9550794884c0c1d5519a040354400303001414541022481e109a185298000e2207058883e9070402d0098109070350b40e9011a118681c06810f0142d580b090400610590b034800c00c0c0038015005220041c60f1548055a4102c03044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 767105080 1250 767103830 767103833
    0x30c0510020706020304060c0f0e0d0f050706050717090d02100c0f05010204090e06040519151401061413061412040f060509030a02071401050d14070e0d02030303040605060d 76
    0x1e1000e088854000c000142c2d803032805142100459161078580401d020814040014042d17016104030440e04064a4180006155007801030384000042001041c3c0d101d00e000129000354040b015000345d40c45100751a032803d0601c101c000082c050f40388125005003221031000003620b04208000c503448084d04140040601a84a5030441d8444003000d031401c1e034001808001e0030145203d0318659000000151800307007800c1e80c405840e25800800324501100810f0800c00340008128040c0c0041c0030500b04102001c4445100501c0100912810011949908030401d1600809046401081480762554070381c41c2041c1c3c007507a00c030480c0348010300800414040c14174001019203481b4041c0e401020002e16501281c41c0000903108000c00300700380c680003400048282ca4001501409852800d605d142c001255000101e420b4001c003001e8081440c10301c1012215250710214150090ba560f54801000d40041c4085c042c01e10b01c001402074055108200050218409920246d0420030090030300c0c1484006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 767106330 1250 767105080 767105113
    0xa0204091b120b060715020f0307020105071e0221091003020d1a0d060b040207060204060c030206060103020406140903160305060a060e0714130503070b0405240403030c05 75
    0xd2068600404541c01c0c11101070907004100340030040361101c030600a00f2903020100d80705009018000b07094050300390440c54103519603016140181d9600710410b80f24034212000034040c0005a4542002c0b810240d082d00c88a08980b945100d071644e40d800500c0000400440f1801060001034005440345043c08880c0c09a5a6820f00c56040c84160340d01680ba428004000f00031640032000102040c18200060070864450f45042a00d42e5000903001030529100408200a4030a0750300003464144006404509170790440d000719800b6000ea402c95074280d66001c015001c0344142e000c1e0b0070100704120440500340c2003000c0180145071000d01540c2003003405240c0100061f2064108031440d0300540d04010801d0034512a190050032a168290030303a04000c040600a00203540c24208132150015040e01c2e500b02c0340c00e000c00200350203002c079441c460303a4400503407641c0c005001d4035211301c0c007416440302d0560102180c50901c0600d4810f45140c1443c41c2d90940c0c4103105114120341500440380c120000e10300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 767107580 1250 767106330 767106341
    0x906040e030f0a09050f1f0903020904061a0915040b1f02010c08091b010507020f0a180c0e0901120f0b07081e040507052404120201080106090b120a020409 68
    0x802d010101c2e11100c81c0c200280040400740c000a000c1c0c1c86404403505c041c3d42d04140e140303003d110000da121814900103000c4401000940010350021001c000b0701c420089581d0041c032092060603402084046402c0401c40200c0007a540c0f01c10165401104204902d42030303100d1981e80500400000c0c0750f500c60312602c181d002c02c01c407540004d40d40d641e001803401ca40040e05154041034030009045154409000c4546007908002114100800441c40c1e60441d100e4181c464005c82c0014500780135281d03101c4800c0816501e6560440500d802c140e01404d00c50b010300f807002d0503584000c22400e0280e09004c4411020303480d0402c2618030800c83c0d041000404c05500040d0b000b0b60081c0d4035403000f441d10f01076207000f06054150a0f08480d40d8441000042500410380c0f100365001101d800c030b0700c030031040001141ca42c20640424103021000800056010f500791080030210f200303072280c3c2d0316603a9481062340e1078025803045442c0030400f04010301000042060745548010800b500605064450326883c080750b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 767108830 1250 767107580 767107597
    0x5041d01050a172d0109120e0a0e0c03070203070b16080f0c0318030c070f180c09090209131407021c0212070f02041509150308090906040e03 62
    0x10114401800141040529040640182c2c0c02003c8021036508250b50390320041d82d1800010000409013118180040203141d4619081c4002401000c1043c00c000191402c03880c00d003808a203c55040401d02d0a190300c0fa0801c0b525004226405030791025403011407640300600760f804500041003e000010b0880c2c000d24040c1d070107600340002903984c85001809080b00a000380792942c001208000d900300242080f2a80541e0241c80000d00c0f03c0d1909c2d102c3d02e1802107080844240c02140004100320080301003540403503511b03101050074111080010b008440d200c544003800203191031014880703000280c00406502e08080c1800b07040040000c440f00484c1c1181110b482c1e40f1074000103020308a941003081c410300883c00b00361004204d1001d00042c0d682d0b55291520714030b400000c60301c8070501c090010500011900074000b0701a05528a001541e40030040c0185000c40c2d04c0c0a101c807400445014901e8141c0380c2c00003c040c07038440e8050811013000d800400c110f0340300e80c80b071008400940c024030241103002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 767110080 1250 767108830 767108879
    0x2040e03070b090a121805030609010f05010b0c0d200312070f0e0307051201091505011a0408030409110c0a031d1207150215150103061202090103120504 67
    0x1c001d2441d14901071a406044888039500038030008002c40c2001411200300c00c16410502036859150240142c1402d51754045981030040c0f500700510343ea030640050382c02240d820000c1209030f80b01d00e0280c6039405840300d06885540054180c035122030107900c1c550350a9a440603c4010f40c1d10003c2c526245030b20950080b06090f00703c105120302c0030b400100000d035041c190306003400402a0040441e0340c8200c107220303c0f4440d03030210b03480c521451000c0d8410010190003500000300c00d044a035600c000340c0400c0c810040908080340308090543c2c4900c0550341520300ca000070f1072801e460100540041c3c5040151045541820443c4c21103411041003038a410714825220001040d440d02c0000e4081d031181c4281e24060480c5408548503000042404400d550340b40380d04603030704c0150319000c83c6044190f05611400e981d1000501c03003162b240401000e60034000741d0301809a030fa1525440c4042d00e02d0f022000b9003007694038006100003580310345224100020303898002c0c00c00d9640c85264050072849444c809a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 767111330 1250 767110080 767110087
    0x603031c0f060b070f02040b04020f131e030302070e0402150d06031106070203060a0515030a030905130204080a150e0d030902040b0a03021f030902150a020c10020d0c080702040e03 79
    0x361000c901641008150f50780b10320b81880801c0d21000000c00f0a4100248900c1d0b403022a1001a51540d05468924502115446d151903885002c03002c080d8050043c41d040d01d0100342e0031401c21074842450029a54140e0250000514014075410780c4440a803007240d11034402504503c0c0140120064412005641800705a40e461424904032054518070041d0041808210403809600c00082c3c2c59000440c4183c0010740341d0f507465035034140a040c1d07110198103014014010040c550711007030102c02d4030011194440702c5c000c3d1030a03131400c82c801c0e40300b0401d076500040c1c40e02001c100c40841c4841043c410902c0421100c5460032224184200300400d00e01081d52000d158041d81030034402e0003011b000c19200c3d882a1030540e00001c201101c44050211007401d5001070014080c8242c00c46104a80d016001d68044010740c500c01150703800c10424407005210f00c40305030b002ca11f8030401d07215041a242d0064400c68044003421104001781d9041a500394100300000030058a1310301c22100d2844013840035544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 767112580 1250 767111330 767111351
    0x40b2b021e041a030c060315032a0102010b010c12121506031503050c120f0303010314011b08060d060b030d17070903081204021c1412040315050603031c 67
    0x85503601c07400280c40f0202c03526803016030780300001d054084800841e4515200d0340d5000c41200440b026050968050060700e03046184842c00c0051401d0054000e0100e4a000441c0c80c0124200ca5025508600013400c0c0c2c612803001c502c00c80a0341940b41c403645020220b540c3c1ea4620b01c4107540142e003084040603400380003000415414400c0a040805984082c04c1403031464980554400c16910940e00c80c1c400200c101c401c0c85410004100810100030540303480c0d40e0350341040e90059007110742a100315420302000581204040e10f0f15900401691142030090300c40e6014012905090b0004482040e9076500109a0307a03410842c5818620807655510558040c211100b00000b4020b0907510074072065003400e10016404c0801d5544180d03448224410700da865000040c03c0f200813003d001c28100b94240002e00b032001d0113440c1c20041c2d08038000c48180402030849420248258803001d4209003180f080c10800d0300041d00469003002c0010102d0b42840c4102e142444510001c8840a400c00d43d2400e0145 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 767113830 1250 767112580 767112589
    0x702190314150103170309100e1e06040b0a0506030a0b091c020316080d06031509050c03030405030c0f0102010e060702030301031e050a030e0310020423040b2b021e 72
    0x1142c0c04200d0220a1a035140d9955020944001012400301c0b8001000140c0d80620800c0f00103020b204482045c0f082c0000e404010f6200d0007111004040d04120443e00c0e0b0611500198650166510145040c0150307215147c03c0c00802e0050012a418003072126500c0c080b542d048025030058a488018001c5c2ca502c0004418800c400300c42030740103540003444010018031000040d1140c29410001e001d66560502050f00000d200d03031b0708010070005201c0561940e19010b6031145d10780f54230035411110130504038400c02d50740380243c0c86040d5065010162020075820300071070403001480180004074400e040c5100c102d013040400c80300300005910200040080c8400ea0380b4007240d44004d200140c035140c001c0d4a560340c580b894480050284008150490702584082090205c1c00c0d407075900464544e61076040e000800c1c403480300084081404129103404c50720b041e2041e1910a0001001491450068845036100156905070300b030b590b50081e2044000b507180d4204441c04100304900e1048940315100401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 767115080 1250 767113830 767113843
    0x6220c031a0d020a0303111c05091e0a06141e03040318050108010e040c080d050408011512020904050c150405010215010e0c0c16030b040b0c16080702190314 69
    0x480c4a42c0380b4442110160b15412025026203805142641280000600c06442e24402d0f42c90304905040110195104a620201070052081d00310765101c0100100f180c40810401b01500281e40161080c0342000018000d01d480402d2a026003890b030305044c8101c20600802c1030021504064400000800080542c041e2128480c1070354a418a02d2460038000028014030050140320964640400404c0a00001d05641c10080c003402d0708407515407002e000001d006800521454560303601344002c00c0500300326801c801058541e01c0009603800a1180c080282004003c0d1050380ca5004403030301140c10b0b44130305000e003d01e620740500d080d982d54030b814002850040325511082c05492250014003031504034900440d00914210800c2c2d440d8469059950b0410320f0380d4012201d06407240c40c002041060000440b441607010759140c800ea9510b039500200244a017a4480c41203421240e018030004100a000e000790a0029001c09140a450b10000700302c00e41c1a0401d42e503030b5000034860005400104900f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 767116330 1250 767115080 767115131
    0x50109090204080a140312090c041a1c031e0305040c090902010210020a030e070e09060c0315060f07021c0606080a0b01090b01020307050a0b160f0806220c03 69
    0x440c03030705141100c0c0c3c5455080d0310f00d00a0040300c070f0241812028a00700191703008104040700c3c603086800c0c840d90150f0f48150781040c0c1400341d400c0c030606940120f030403140520116001341c03e00520350601c406060700c0411180f802c8041c03000070106290fa140c4aa00c0207180e514130350301e0008803804d2900704414200c1c041e6000061a0381407005100050740d004c500c030004008105005a1507013a41e450640107089107040c1a001c034803070703104006a803440704011180a0ba40c007600b614000e40b50005541d10510040f1000c584207003c10780702c03481e2030901e24002d09480c0d00c05041c090400c0300f5a80001c411030b4101402980ea0610420228184240c9204401c0203054010040130000e03040d9503104d007641014030900049507a81e6a1160141c0d0080c800c0382c5145a1200640e00302800720b241104103000c00b40e41c010914280c041018900358007030b0084240b4043e0340d03110750f02582d079006c0400c913600034500300ca540600001f00001003c40003602500f00780780d200d500c2c081582c41340700030b444000cac90303e8000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 767117580 1250 767116330 767116349
    0x926030409051e0103020f0405150301020703020307120e010f18050a030f060e0303060d080d0b03030c0a06050f0408071203090507171510050d030e03150603060f010e07050706110310050109 83
    0x1040186c1d0340740007c0303948400aa0f00030506035100c039139404070000d504580d190194000a051000c050340403009004262044ca0160044032110701c0480741714107501110b034040b90009000c0e400c95801003102401041c2c28404e0a00f15640b100003103804500e956200320b418020540700042000114040c81000206c8003006606610740365000681d1840703590380c0900341b948005016103200c44070f40c00c503250004016080b25500c1c1c4560f0102a951911007405031075107803901c00494031420a5041c25800340c0e030401000c0781440c200380c40e44070480c513540345800c040c1540c9055050024500340400c01c001d140001c00c448951038a21001030400b040303086406040005030741000080c000c1c40c60b945090312401e85040301c2007a03c45c03a081d40e62040000120768940f01707201d140c500d030608400360140305900a50684925032a030391a0b00a0301d24080c010049080303400000074aa0900c0b4201a0514500075100070410341d2003141c0e00da602c0c1d0304c11350702c041c100020310360140255604407460b80001d1401c2c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 767118830 1250 767117580 767117641
    0xe03100c0206070e060d05070804170403030203120a1407030e0d0201022d0f030c18031504030e0307030204020403050f06011e0302010c060906050a05190b01092603040905 75
    0xc00940728107008020b0010301610043e41103e0f500c0d0301058801c100c1440c0020001c5040115010340015011a000c03244d081150480b9500c1c1200b81d0240c1b41184d905800442c1014174440c2c07440c581c05030060000c145169103403448480401c0c0702500e00d0040f0861b890008503d1000344842d81130900c004c00c21029680100a45110143c0040d443c01ca01500d00c4e61041c2d5040e00401e0103d040c1c0f0451110442c440f0000c003d10684c41c00071001060700108406544030001c1000d002e01d82c690041011000307040c030f00d220000b000710340200440d1070050030040c192102c0750744a1b40041c04a8100d41c04c25152036110300340c3c0071007105042003154098219601040d800060100c07003124411540c0c00300a04000b00a21502d0401040380c02100c0e4507a8050003c0c4503500d44070528500902040b11140c01c0c003414030351b070320340300350500e05c00d17034044d010180c1d02c001070241042110170003403011540141070801c0181000c124444280083c0000d843d000710017040c07070b061490a0172910f40c40030705850507081152 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 767120080 1250 767118830 767118851
    0x25260f0d0e0615030319020c030304060e040506150d0b061603200606030d0f031112040201081b0d020f090907020a0b0606190c110324010803031b070c0305010c0e0310 73
    0x10a0703c4803242186c0d001c07042004512070803410215960601c83c0c01d4840401d0200f04581c003c20726601504003a1820002036032880c040050f02c024002010030820020044120b034031119800544071504044c065a182c008000142c0e6201040c410082c0c00140080c242d65a206084d9218040c950480a000f0009800c02400003a00d07a02c201c00c0407010f000f0544581c1280500a4100420151030000156200c80c00303041c10408452040b03408a002a9442c00024090312800c03070290110310f4060781440c14400c4442c840b100940c070404003005000001c1c41700040b40d9940e0192a440340032117a0181c49030703007802e180c4001413080140030540b150405102150002580c0c00900c8000e85252918400c4005d035030401c05402a001c1c500560140203041d07005540c00451490100c07412400c050f07090172680c1e102c071004e80700d02003960303040100001c50751100465910400a4210580550546140a0b6030382c2d51f018215800d50f500784010500a00c545941c602e0140441024090440e00520150340c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 767121330 1250 767120080 767120083
    0x1b070b0403080a080702070e010605031806100b070f020d0821074103060a0602190605060a080109061409010506030703021002030f03010b25260f0d0e061503 69
    0x4000012013040309034400201c0091003002204002c4c0300011154005503100e2000828036441260480200582d00301403841d98400090000d2180d4100d81c2641c400030300307080c500902644520030503102d1407098004000540d07111a1015905c0d4030400c1c07881d5403446101e22070300d504066004005104c14001041004035600844450b5505900c1482c00882080813046070383e40c66102904c100c00800455140c40303000340082d00540c0505400c98070b40f4052540c1d85d40c00c80e0f444a800d5800400c11f5085655400001e11030781216802c010020b00c41c03402c0706e84410383c545c00c5881c0d414040c0e0f43c0940f10420ba51422020001e2290070090300c1c0001d0044d890708001080d41c5000ca440002d0048082100c130b040d9042c801e0042e03c0d6408200c0c807819559503529140546141c02001c41c46031311701c03004500c81400707690f0140d9403040d595004184000d00d03074101d401014030b00c20364003110b544941d007044200440b078800e800801c1414031079000000c02082d104215450100028140e104030b40400c05030540d1a42d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 767122580 1250 767121330 767121337
    0x309090c03090f03030b0a0f1a0f040314060f07081e0415151403070806150402040f1d060906130b06040312020a1203061212030905031b070b040308 65
    0x806440105840c9026041203005000d0800060400c00c8031650040415038150041900172601301c3d0340c2491643c032521200350074282481151302c0012400241d4419944170000707000c6041c038002569082641e81d031107004c58400f41040994407504208208850000d460b501e668001e00141b034002c905241c0104924442100c801030301c112a520f910004040001005d0710b80d040d03c032081e1041c044070648150040e00d6000601a0700e03040f26240103685213a05001904c50101ca15100003403080f0f46845035040310109a0140d0b140d04941c00304004608103620b010301c4030040c001110001008083c44000880540000d884607106600201c2441a107035144c1c40327800c0340e14400a070001040002100001c4082c801d40c0e1006080106641c60311001c42e8000c40c0c90340516003e11500e04095403030382011021182e541c000d448180c1b40050740b1101140b405000e2000940440c140000d02034110303103c02c3c0c91074000d500504000d01b050007030806071590502044e0002c0030402d0980c2d080c1030035076403000c41070300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 767123830 1250 767122580 767122589
    0x30c0406080106020d0c0f0f06150501030609050609040b07050c07031211010b0a1505090d051f140c0307020a17090f0d0213091703010303020a020a060c0b070809030904020c1501050a030309 83
    0x103095012407c01e1002900c071380300c0c00940c0123000300000640788690f80303040c030000e10800d8007182c64030f90001840d80300780c020f891203444010808201d40d55031f9600c040030400003401070001c001d014018080100302c10031208001d54000c041054241c40d010f2001406c9a4032180400c400b039042c500c6070105900d80ca5a50002e5070f262103110491010a0b01d0b0031280740c090300c40c00e6036200d04804112020310a01140d4100d0340100c500c498410040500d13840f0f02510000c100304204c1454604c0001e80b01109000035580200541c4103130707048404240ca413004030204c80740c17184081081c000381c0b0324140d1419070001c4508100c152180395614500c1d03000101516103001c2102c0c0c2d240d4031201d0610820901051004070b8200780c080d900e0b26540c482c1002503440d07042c3c9008900529903c0c40c0403e0f060b001c0c1c1808040c1c6d503409010200a5030f01d51000b1940514040e0150103248014000030019554500284c001c84c0881d070020b1a55440c4001e140c144070700b069000074090300303c246082c00820741c050810800c2d00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 767125080 1250 767123830 767123843
    0x270403030b03121209011d0c0607030c20010912030813060e0d0f031409100c180e0f010e0603030d0b060d060e04060f05190917030c0406080106020d0c 66
    0x281c5500803a003030101501c0000c200307500001d40f049000411800c5280a12000802004056084164404009040740000c0f61680c454041002c40345030003001011014840d241815030b60003a41d0724074129183e4600c603003d50001142c1101541e50340280c121004003288a082c690445940c0c401808000018007143d115840e9008054240301c1035030010308090160904a0340d14041d2120020603034980805403800180c1085c1d0382c208181490b141490051a0101c0035000c000000043c0b80c4c002c01d4481030341001e11030700404a05145503501100c8000740f014000340b070b8043c60322aa0b90007940d02c0503000308131403444140900000307071800800d0f1110481c00078000554400c1100c00580103000c1c1e49000000c05040950201d055001c0d821170703c8c040c0c0d12070b0307206100c0394005620803020348201321104158408003444c02e01d400170407a00b29007400c50140c3e40d00009107400d00b142c850142d0003213a11080e11100080c0400c29168051a02401440c8900c007412403a0954a8001c1100d444040040d241 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 767126330 1250 767125080 767125091
    0x50405070b0301142b110303070813060305010f0b0a05131e0e0609130311210d0b1f14090a091b02070e0106030e010e071e050d08040506031b0a02030927040303 70
    0x29607c1c204100c80b1341d190006411621071903d1004200d000302c0b68020000042e08000c000181c100c09400c0d480d0030740d10101583c9007020400d03a0200c5250b04010004401610b503d60006080007140c160190742d5140e1102c0815480e041c03070740b0b8100b000070140800b801a40c1600810200d140503034640c0f100d032545407030040d01c004454100300b032805207074102810301181d400c1c0040b02c00103605802403c0340441f000051010908110400c45402031010b4800c1c03003a070881520020f580e129000483e48044e41d00c080604120b207800100780305654581060004a540d4180c42c1d120400d81da07540c9180c0d07089403004042107403c00c00c0700c10320000180729a0091589500d09402d11000130740106181030301200458540f550364010601c00004100107500c01c1e4400400003103200c0c206414034000503a000303080649454644801d1107074541c0300030840d80241c0ca2240c15180200320840c001e101742040d03a4003e6845004600c10810802402003000140e004401541c0f895055a80c064980c81901030400103030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 767127580 1250 767126330 767126363
    0x605010f0806150a121b09050d03171e04060203040c23010f030b0415030c0801060e0103110307150c230d030506010e0613030b06031f050405070b0301142b 68
    0x10940803104408150301d08101d4044003006614006d440400c07510380c0d0b9413008580d81e400740203958440300c1c000f8000480456901d50101824103160750032200006910a00c814081800d040740001039404644a41d000420300c000e0106803481c8102800c0c0c803801a80752004039000300c034000b0940303400c45c6061220700702d0510031030303030103a4030603503041c0c00141080c088951207000260311081c503030108480240100d079020030100d01c14070840040e50384841366141c1e1079007140c450380724481e040380055034035110700c06000c98880c0742d00d42040c01d5a5601d49a905680410b81f030303c81c5100311b1400012500d050140000f0608090004001000c0074144c200020240c40d403100480e030b4042d040e18810b80002d400115a903d9841510103801228000c40b03105140352103c40800d80c031181802e02c50001240400300754401c0424030352005e90030502c20000c5038007599940b416034180350001d034442000c5c0074070140f00c0070048c100541e03541c210703002e80c08000c40e1040c41c209001d4120b50200d40e025041440c0c07070f072617001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 767128830 1250 767127580 767127587
    0x70314011202040603170d15050f240415090b0921101a01030501090b01050f03071101110d0e07052101140906011a031e0703090609060605010f0806150a 67
    0x117160481a9075882e607000c0c1207468035a42c07000b0038100020f4513041c0d1442d181001c1c060420b0039110010011544d92080c1010000b51045880902c40c0f030b000b850003006004420f02004000600320001003c050100752600a440701215a201c800300d954100000442c5a4034070040754010760b81c240c0310014007c984150146809504544288050706e850710030030144003126990120b080b0241c1c4c00b13108030ba880d400c0308810740740d50080803404500e089c00726544402c1030320003542e440381c43c6240030311110015034134490a442541002200030207001544e49104841c5004c1d003015503068500402c551450b05021031611803070300d84000030f00100c2c14070018482000703410500845240d8602d203111410000e251f10307203501080c8510b0f442207181210144411b15424113491090240e01d81900600c02c1c010711000711040010842c81c10035681d0980f450004102c5c0c03180412041c040c2c00001001410280094401c4242c1a4200244907441040080658030704040400840c060040c9a40701d40e41140d0a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 767130080 1250 767128830 767128841
    0x8011d0403180b1803070e011a0705150105041a01090915050402070b010503160b0a0503040c080f0f0d020c0f04150f082a09071815030b0907031401120204 68
    0xd454500310340007514070302210203041c5001d640c10120107544d030581c003015614a498070818420b22950401007005e101d19014511442c0307807000c01c80e4135190050782c40a00f4110028104040510104014051814188124501000d9000b1680c2e044401c0c1c2001800250151280000194690081030700b4010b0031038800c0b0003010040c201303641340c100602d861111080240a001c0c040d10840102080a000c030b00c00540407180c0d194a010310304203441c0401c42c2c07580c2c4010000c0c2c0f15006c1003000090440000c200c580126044078001e8004c03020651501030a01400f000c0c12001c5503c801c01800d5940c1e2941108000d08104641c00240302030320305e0300d03601303003074600d47c0b090400008000000801070710200d4861814003681d001000030046403a0441d00b886a4015910380104041000641850003a40e418820750207040c4c50303501e00360351040034040310079100828400180d240c3c503100485051603240d20360000c03840c7c10203201d02d1251907514074680f001403003480c0580d001071001c90290346071503001c1e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 767131330 1250 767130080 767130107
    0x306270712170901050a120209060406050324130e10020f0a0801062f0c04050705040e0f0105220b0604150e092403011407081608011d0403 61
    0x203444056580741803038054500c207000140c94003500004504100300e403250440d208050705071510fa0402000b40d4048994456004042a4403982000780d20842d23500d070f2020740000c00f41962103c2e501d1802e06903030000e004c0354030000d001004e000c000300291591480c4100c01c00c000c0a40300000e2000c07110451502d8081070301c041c90401440000d5004800002c0e0303004003140245615002d241ea40d88540c115804210b00902d80c0c41140381640c1041a0300101c1192080c110000d4119100c511040002500b10b44043d11188081400002c080003402c401802d8540c3c0411000c058a201c2d614280216904200381500100c034030307456811804000806a003c1841604090b1600361a251501e180081d440002d10304c80c1c010130044002401e85c0d03e448103103940304460150104c5003003520580c2c01c480001035807090079450354803200d40b183c400c40c6861245105585540d01c05040381000c0b007103940c000c07034012008030811204e10010f01c0352400c40b00307059050000c030700d051690780d555904048070304080030f951 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 767132580 1250 767131330 767131333
    0xf06130b040602070806242d1512070503040f0f06051b0a0c1514090102120702060f011e050909060a1104030b1f1a03091209030627 58
    0x204641803814050800d490303090f000c0b60000c0b43c68958480d075401085a15039241c0304d552284010b40003100ca801d0000f80000303800c0080145092003000d10040808410508070400004160101d180c024038103900480300702c500341d1501c40700328070b004110300c0c1c01054007091001c004003003020000e0400c020000e01d508500203404030006031030f00c240645000d9403501450000248103c150040200444910300280e48072448090400da0321403d07640c403415100304010360350b15030b80070503403040058951080034000c0c00141d0715000400b818620792805443d000c21940b01004000881c14141c008906695140b075411007030801a101114001815030050754001080d20144004035400044440c000ca0150305c0600c01c0217000c1807500d006010314403002d0800104500803404a508001c20000c604c10009030104440d91150444100d24243c0c4400c950180000401c10050301c2c001e205e51242c1000b1400b40e6854922000002555400c010300134045403110481d40346a11112082e00c207261041210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 767133830 1250 767132580 767132617
    0xc090408040308030f0603010606031a01030e0327041401061b06020d020d231e0901060302060f0301140108100b0a0c1509031407121101090803040b0402010e100207050f06 75
    0x191002c00c1700c181961450701075801c003c4003040c5140680240c0c00390a07611447c1c14a82100c02c001140901444090042c1c0303070204001111034208150070070ba8008600b40c1108041c198080140421a0210500c0e403060703036081130050008a46c400141e2410200c00c0d090004810000c0c1020300003881240c407a1000c103440000c0039035128490781c0161102c039505039005401070402051800c10074030215005554030000b61070200443c40002d05d155000200c140000801c0c0f610703503000c01c1c000da01405180c400003601200401140c040008607000051003840c001f451400c200275901e4036460140248495081c021415001081c480c0718000281d60b000000c20b4502008840340398014806080f013a4005041d050700e190969a4010840340400c3c0e12a58800f02018050b2007201c1345244840504110f54a0302400310203d58880d000e18061401075024501d035040c144000b4000072091403066006000026242c42d460340c011401c5000c41c0c03000e840b40f5107202e0310740c0e0004001d84100d4810041c02948170 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 767135080 1250 767133830 767133841
    0x2506050d0b030610140d030f05070c08060901020415110a0201141c0f06060309080904050c1e04141f05030613061d250f091508070e040c020c09040804030803 69
    0x800b83e21003200d171840081041c41182106004070201c2c164400740105011a8601e9007030380c071030002004074501481203101d64136103c004060500c1400c0d640a0410382d004201400f0002d04100381845610b0b49040000d8050003071384030703a03031036510060019050000b1f106002c041400d801c070840309075000443c070100e106038001d680c0c1e500401200d0800190246043c0022035028042d11500031484d07000301405007085030003010031020f0305000780085500c0000748031043c4500342c0070902041c1c2e254905149919141419854541040d00c07554051003003040318503c20481c46900d5071042a00050300e0181da4035654a804a02c0107644041c1511203189441070000d01004440e01000c90b04107030742080165901d50341c170088854074219285e804030321114099058032038065500b0f90301c0c0304020308022009640d00da90020b80000c2c2400700c00e001c40e85482c200700d40564004001903442804540030400c40300b03c003400956481c019803840d03000752040c5d00424244030112081e140215030011021390361b403030070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 767136330 1250 767135080 767135101
    0x81005060a09090b03030403080301090e0a050312090c0d08072d050102040e1302130b010e06030f0906010807080c0105030901110c0a0309050a03020915131d2506050d0b0306 76
    0x19441243c1c0403d2508501d0745a500c0c004c004c650481b60400004c50031a4200042d280051445104040d22031084280c484002030090015014001403413540d000103181076680b4034180840700c940544988030745074400c00010391f184155044c580e0469403061000c0702c011001b00ca5510141d02400484034030381410410080150010400e46100780740000d170548840c481d000d08000e060380025400810403846000e00e0180341d21442140b14145880342e281500780021420179030040c2d4040000f8120300040041c01c600c20000076004100d148018a00c01c3e140684440d100d0100d0484d840c108140000401d071552004d4201c640c0719110500d0095542c3c52110b50b0a41c4d910300748104038080750192600041914040881c2c0c42100d80280418001d0360325000c1428811402ca0007050303120aa03000031200703d82052103481c00751080c0c405444409502465820710307003900c07900308000c1a9160b50b58842007100031403488003103507480d090032038580c171243d8081d4011b406414602c60f0188074010421140020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 767137580 1250 767136330 767136347
    0x30a06081009020105040501050a050f0415030515010203092107170717060a0902040e0a0302030405042a111c02061006030e060c03060a05031b100c0b0601081005060a 73
    0xc84100e41d0000d900c01611010b40d080104003a000c558284010406540a40010180300c2001e15146242c41c41c0000011019000b80c3c000e1840328907403c0082003503a07098441c95030401c4d007560300074003a145242d0001b90350380318021803640502d4040b4000044001c013003143d05003091001c000d40b0041501c0f45000e041d00c0d002c46c10801024410540009034208074801c002911503154dc015010a070ba50040460180511907002c0b42c0003a81c46284910005091003002400c0c1d201c0c1e40074546e10746c40c2c80304100075911540008451000280305640c2003880c42a40b000850351035040080f01001504400c501301002c000e00411855101c0c05150402035000c600d0300d100351440500300c01d90940b5250100c0450300301d50310b41d2aa951141c00403c00115822025640c0000c0081680c1425600c1d41c01003401d01c0c140304580f881c825500800059a4074140142003c05021403070102d181c04a82c0d140c61500d1a00505594140300c00300e40442c455940029525002c2d16004d0540c0d50b6900c84803400604010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 767138830 1250 767137580 767137589
    0x21b0f010222030305190507050d08040c06050f1605120d0902010807140a0c0227010e060904050d1119030e030601080601080d12020405030610030b15011d0a0803030a06 74
    0x1d40b055020b1076020b240700d4182d42902d130560744003414126204490301100b68290310180920805000040010300104003000602245580724952400c0070301e029050194250030003024490240002c0c6581c0d541541230f91841401081d140c1c2c012200c908141d0b040c401e0701d03a5a00c0018000040f002c0e50030700c5a0b007040e00118403e1361600b50581d04c50000300d80c60b100802c0708442c80d80c405c00c04040814803522100034124001410300031010340c000e52801d04440c0410241c041150714200401071001003102450f80003070b080d598030300e080c6420307a140e41d00d8406001240301401203100c030310141500200440c5080103520103074249105242c2c280909082840314241e1300c82d02c00e6000104980740c0c0070542034100d43c811030040c00403088085013500d41c00c0c3c4050704101180d40c203100008450383d042249a0046000c40c216541c510300b181010803146100801e81c0c2040010010145010399005000011140e01c1031100785071081c1c0980000c1031140903a009100b43d100100c2070201141403640544101c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 767140080 1250 767138830 767138857
    0x90405070602121204110a0504050a0f06150f0f050d0204060905090a0608120a140f130b0405030c040908091003150614070f050f01050405031903020715021b0f0102 72
    0x218a6100300003c0c600c664130103040200325100c041030005182a030155a00310300207240c010140e482d00d0104086601c1110f07402000383c1ca8031803012200c1200c4c42898054003041c075418240303003000c240c058141d0b00d0060114007009208031450303050310712801c00d0390a02c09029000759507a66480000514410060165620450b64440450100e0303c05218901c100e803030b100081c0445022404002d08507400142403401402840c0c0108805a110a4020a40d1a44130769003191680c40400c0c5209044d1003d802c5114541c00c200010300c00c171381d0006211103044008903408601040300346401d0040740100c4c000140c01200107a24018201c2d09a00b280803101e23640100f040320305646072012500c402602e01c280c42c0c4850304000d1800410f509025804600e4011400c68408035041103103e42180d0040303500fa1850780010a83d4500441c108002200b1250b440c60190700300909074a078540c800c44a1082a10300e540e000403100203508440f070200d00c070402c948098500c28001d030030030280130f03511065001c03100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 767141330 1250 767140080 767140093
    0xa260f0703110f0d060e0a05030c01090c23040f0605090703061a090a0e07170c070b1608151f050c06160f0503060a030210050a090801060612020f09090405070602 71
    0x107007003058199861602c01800c802c04000e01c0c2d25845d004000a55144003140210812180031940400c014221b0344101800005c521a960a00c580c0b002107641101d02c4241c4412100585244c940300c00300240c5804035400103800c40214060002000c0c207503c51500945030000304110107405a0014080301e19030544889402d0a440500703520b0701c24403803419400001b00c2000d005811380b00255542c08015818894000d01940d41c40121a480803200c0003d510400240102080414815241c10415001010b00b48200d503207000741508100801c0460341d201c1c4600f400c20306a80b510792500100b881c030001030701c0b5419102c20081881e480324412040510a00010070228a0743c100600c01f078030356503501e2400b281180349046540e035001a01a0340d00072403102c40400540d6442c0325454030b040c2c1d1503c80390f640c1d4a4880c8041c0040085622104160340350580c20001c0c1500700e44052200e0503092801a95866003d400c002e2a001d118120f903045100c000c1000104000014404240e81103074084426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 767142580 1250 767141330 767141363
    0x40603051b03030f0d021305090f0a0e060f0112031710050a050f010c0305030c0d1803110105040507060f11030c030403150209060904050705370c020a260f0703 70
    0x10380c0d01c9810700c03030000b10314204200c001c54120782d406040b2020310b0162510750596940001201c9400030740c0c0b00c14560015508bc8401c9527454404c00c030034244d00c00090041441c144a924114a40c144108090b006405003c0e80030184100c541c0d43c00f40c50485001d0905040840c0d01c00000140c9020380750003000444004286450022807602e00c05405944401c0341100594049a07540c0001e0042c2110b01c100f402002c510350b2260040d90345200d408072168104c64461705004000c0c80e03038800200c2c1141d01d044144400701d03102098107001e4408c14242444c41c0d031054801101e204200c4030701c0000c203010200f6000200ea802000030002c40340245c095014028801086104078814014403d52201d400c100910040c24581c00c181d80c443e09070f08119090450203124901100002e40411215031142c60440c080002c0340a250911480c281c039040d02c9201c000d030f0100e410304620340034012590581006100c0c50302d804a8481002e222040191550540360000040d0307140c07280e0200b100ea08075503849260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 767143830 1250 767142580 767142583
    0x23150603150415080d0c0b0a0905150c0706060b0307200c0415080a11090702010b0f0d050a12020f0d050705300714070b0f03010303110a02040603051b03 67
    0x280201403441031050410a41d504010081c0024005645510001000003a02100c04d000c1e10200c0e294545500b94480c4182c0350107070700c206000305a0b050291a2480c420041ba60000301d4400141543c1c0020b405c0e5180c0c4448040740d401540c6000303148034140000400c1001400c3c0c00b45010301c2d19603da509941805050a824014244401c3d4145031710120014601d460b058015a81000b04000c00342025922000b0751800c4c03080809060b0342001c241480030005051a40c1038a91101c0981f00810a8901c40000100f42c01080d4580c14444d400c89461003050000600c609503406501811820841e4101c62019480e101c410f00c006030030780074000c10540340900a01c1111180b513031000291840c001c600301c0e40444010207540c12000d041c2030200140c0b420346582d0040040c1400350441090894410914910b0300001f038110b81c0c42c1020500484a401d100030341aa41541c3d4141070024108120042c10380c81d1504c1c045003c5c0d4010300b0602c000041c80800715010340c3c815030900448120040340010715 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 767145080 1250 767143830 767143837
    0x5040b07210e310203130228060809240906072d02160b0c0f010605010c0b0c0c0a0f02010305090723030c0a060905011803110d06231506 60
    0xda030010070000403805034210903443caa2045051103100100714001c0000c101c2240c008452110381082c100f582071040d072820040070030031a62511031208000c920481c4000d51405140316600c10701c03681c03001254071034a003400400408c079100e4105207002240d101c00c0b08045042034911608070f00071803001c0303065a480380300d41e080b04900603401d03490400c1d6010088800c040143c07413241e0440c060500c1c140300185840c14010000e05070399a02c180c0702e500d4003041e2801d00380d20000a00451b0f00d803910800c07080c0d0700042e2540042e5040424070310269243e10154046104039503020409004140029003000701e400c4080030954001e980c101f040d6500d03142c00b40d584411602680e145402c98103072880d0304440311240d60400d90000b90548680720b4081020810985403600040d0205007030714828080741d40d100e19503500703d14440742650030355861500c614000c44410b1590fa03014000070640c0c442402456008a403408510701ca552801003c0e4803074041184034242c03151f03c041c6800c090041468500301c0281d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 767146330 1250 767145080 767145107
    0x90903300f06011205070e120105061e13050c190807210605090f04050c01090b1207051b070905130510090c0503060a0213170c1005040b0721 62
    0x241400762038050801c58068030041039141048100031003546444000c1c0105405010aa160800449412010042051084000b0b800e503a8034040070080b290ba5500220b80f251000601c254110010314800b02c0d80d0714101c0d1030100d5840d400d2000344800ca20680006000702c10440e4078903210b031401c1d0042101d03507040a031180c10001d00005144155072800d01e40368a00703006504400900c00f966000440c54051040b03172041041842c6008100070320a007030010395841d0409182030704a0506080e24100b05001d4660303000080b0020344000740d01c580c010000c40f42490042070601600c0501441c1c4556a510b4502408031514200002308050903510004401900c0d808005403196180e14600d2200800a074002554440b0303041c40c0020351a14284a0039006460040c800350340c4030780c1e86164000700031080e031001c070412540071858600b924021840203000d0b4401c03181403a1005426070211910b000e181c00c40f090040c4002491810024a202c285200305007a5100249070b0350b03031203015070b0480000c141 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 767147580 1250 767146330 767146417
    0x8070807051e1501120204050a0f0e010209030f15010618050a0305100e0607050702190504020c07030c080706080a0b04091203091b03020315180610051f021c030b090903 74
    0x3502c05c014580741d0016507003c01d11080006154080c519140103440242034440c459960002e108030480c1402c2c0181039990200c03000920344000300c1015050b03603200c1489003a080000c85101243c1c05181400140000c040040070098030795100c1c00d06503181e280c2d581120586a00d89010000c4003540803070101d20505070390300c0301c9082800907001d01106541d1307854030071000c0315041c0c0041010350710343c4050300b0403401c2c3d6402810194214a07110980d020590000b41d82075000702400c1210540c002e035100d5014810007030125888600300301103800750840744c0c401400e480c012041d1035152549507100260560081101152001010b1804005445a80030203074041e04078800101c0800fa094170003030341200005076a0492104030012650801c0015502100c00705989141008036142070f84900c9000000030825501032102c0001c040e680301d0490403440c2c070004500803103207620350103036100c15002040a08400c40c240f03080749445071641c0c0140100302940c04000c1e0340c0d049000700c2240803030001c0721040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 767148830 1250 767147580 767147609
    0xc060a06180c021207032001020f0d0b010c0f060c020c010305011508100e01030605070f180303080c0d02120f1f18180303060501110a02090408070807051e1501 70
    0x4030603000303007004001c0c2e10300754860501c400ca000400e000c01048a00e02a41d1010925103045202c0d01480652420030040e40c0e00500c1105e91030350110702110190401c91200140c1c41161300010317103007201d41c200c015140510051b00042841515040050354070786550a990000320303500019001c4641c28010804011000d13115000f6a90040d1062a048000455549416560f508c0750700c64100c000d030000c075141500e0310b041c02012504101180000307010750824441c55074000006074004031a622014040101a00c042810070340f00c0e208980316050b0042040d5900d0480c4050500b980105445c00700303160300e040e000a074a0800a507440078100140c60700d0310b4491454961007060700415a201540d03002e603140188102400700500c0459111310948010490520340000588140407080c0350300300301e4211403541001682c0b905a5103a00a0340644003a40352009410011118090440c1c020030511a02140d00d11001c04003421041000c018030441d07514400740c0305220014070007032061015500303c81c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 767150080 1250 767148830 767148869
    0xc020a060906022206090e150904020f060c0c090718150306120f050c04050c0a1101020c06070206092b030c14042c010803091306030203120c060a06 65
    0x1e40104000ea0b008001c05402c0412100780308001d0041c0c1c91404900d400c926404120080e001041c000085c40910b031500308a10744034050280e205190020f10380701d40382e54000581150323a20b0030405aa036101402c650b40312117010384c0f4969103140d4a030240d482111303440000f4250070300c036102a4820505403141e21240f1780c40c080140c910b481218807040d045c192038140101e8042d1010350b45440181c00351061048200305030030480d06004000e02c900703003c1d909140400004a9994086810040345440d014229035400c800890080c02020031108103801882c082c800003640c005002030080711900252903400840036100c034561071660b002d100071040c1c000b10740c42985009500a001c43c43c4281420010345080750300c4600d4a61098010410b4a004030006154050043c8049442010b07901280801035040120b40c0303689001d0740d0205407107900340c0c00501c450220300e50801402985e010303040742d103001c0789030540141c56003207c01981914490030000503001d21403402801c0450300c92003001802c0c00b809 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 767151330 1250 767150080 767150093
    0x1050a060509060625030e130507080603120a0507060f110306090106020307030909230129070c140d0c0308090f0f010918090b010801020912070b0a0302031b0a020a05010f0c020a 78
    0x217034681a024441950006101360300c4d5040d80440c1d50a207410001228504180007410445000c0c01c40744c025030003001c0c041e03680ca042c501207860341010360520313507154005817a028000d41100345d12a6501d5041425030000b00820300003860054008075190410341c0c1c3c843c45c00300d07a01c1c0694000a40081c4280c9030802c14485950301c40d050614903200160160860301001040b602000c0e4062400024190003034140d24125032039400c0020f00c000070003454403440751100e00700406a8043c00000e00d140040c01c543c0e941c0e44185058a03154049862040d641e0b82e07080c1b100e540d4004819550150040188072010b074507081c5020000e030320050315011080d030300781185044001c045094a40c51079030b6840507000400c83c3d00751424002c7c01004000342c1d0380d00302c850511884091100c0600c1c2e6682c001d40c0e061001629a5098614440741031800603280d40e60020002c403101c0310480c3d50502000001203911002c1c1d0b01140256440340030307100034440c41c00c00303c1001049a10501c181401600081540d00010b201d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 767152580 1250 767151330 767151397
    0x9020702010c0633062106080a03030e06070e030a0f05030c0a060b030705040501060207060507081309051e090a0f02062215051306051b01050a0605090606 68
    0x10324040040403201c3e075500c82180d040b0902d1405189218aa5661050302d41441e03030b03c441c2c02c0403c071002091820030301400000c020010510001c420061480000c2a954001c100600b1041c0443d440d082c207509001c0c00402c504020f030342d00380c002c103400551001c0c0074811220b1000300140040410342c003252540150004040021502400100103810482c0d0f030030001d00303045134042d000c005200c8004000701460301e07503694000e170b00440c10b1900422499401141d0081118994104103944403924070748906c3c903100301004000f510506070408074001c00c140d88214408c2e40c11918004d09055100f622003200f41c2c00715600350a13a03001da8280d0f0b00003200030b251070522510141802d41000400410003c1c00003440d001c013214064101001c01c06001407046142c080720031801c1683c40d0051030f0351100700b040710034020041031180014401d4603a20742c903610130744071742280ba00070001d508220081030041d08181c41114410808032010485a241100880703484c2003404140a03041c00c90b0058241d40000e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 767153830 1250 767152580 767152583
    0x9050a03030504231e040b040525090305010519051003121b0602070501091e0308040b06010c21090501080903040504181e0201030515031005310309061701090207 71
    0x2607900d00014945170203510a02901070b0b518550400051442480211100003084a11890404041c003440721841c20034880706d099042403903500c1003d100000d5841d80295400244150b18100400403211a0313007850f94a0840310800500c2551940940c010000c845070001408501c40140403c00c440c0c01100c0130413120840302c03e00c20b41c980140d22940c0490b0400c940a0302d161b515280d810040040640044d440064100114410007006880080124400500060425080030041601a0301401d403a01d0001c0e80305160303503080940403941b83ca9031310a1680034400300302c21040100e1658000c40b8501d20841c0c1e07400046040a01d45020000904400ca004100824100811034081003014041142c0c140c440d21042c2310405c490302c001400c4510040c044850404464141a144daa000c1034842c02c1c03500d00d542c0410a5160601d40002041344000c803075001c2d029880000c242c40105a0407031003094003079101c0c100b110b0741c3e400041d03810250210340d41d044480458010f12481d05181d02400006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 767155080 1250 767153830 767153879
    0x120c0507120f031d011a09090607030506040f020307020f0f07031e02010311040b03010617040506163f061217070213090c06020f030f0309160f0609050a03030504 71
    0x14011041311000c101000c14000d00381d44402c08511054032181c00c400c840081030b202603200703107081d40307204e40ca5901c0600200708164450700828031641da60b0f0001e95019400000440d50f0b401d0584010799504c0f07180e0b95080060144d07032010102d1450110301c10080780c0d041241e8860120742500c504044a68150081381490303550030749104d40d04800d201400c0030b44100c5010a0b9203504100010340300d40c4080b849003002c07109aa08000000302e0100e0700d40d8100903091901c0040c210000400e07101c051810041d240c00c0c11201e9422134848035402100c09513900c42030f10320b81c00501e1704031040065076030360300400e83c1c002c40c0303003084200150120300c0140102d0443d01c4840d0801455500280b80020300896404480740c440c0700b00014000b42210850040c400e5000419803460200c0c0035170b440b030151000d4402005000310005100300400d000413100c0009405e04528840c1c0c07240100c441002e410b025000c0012603154001c5024101103654100352501a222a4281841d01c034540781104200a000181c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 767156330 1250 767155080 767155091
    0x4090203030409021908090a0c09150b0a0c0308060609010207060c08040b120105130b2808012301080c0105070609030219050c030f010b0f0d02180403120c0507120f03 73
    0x407404d101426803081c82c1c0d80c488480c60103003840104403a40142018650307402039121000040d44813601079003225220039001c1120b0085907009010704405900074911000005649050250b120f0540c400942c0b00340ca0760342d03254403110b0a00005008450082d0f02581c0644400d104690056850010712031003022542e15007511808070264035045100a00311480041006100c5894038585080d015000e42c401003060b80d0440d00007850b074032030169451100390f05e1003041040740504070b1403100c00b40010200900800c2140160060381e203421a1581c41c00e85d0001c400859024000f10784a00982c105940d0380742024040e49840004200035031049040d0f01c10100142c08010b0410505145c5500500c0078140c40c124820a0504000c0c5000c04102107924010b021003060f5200c030031138040c480d03081d41c821108a86034408108180c2000042c0d8038001355501c00c2000305035200c41051000c102d0340405001d940c1c124101542e95015204000f000b181c0c5200f42c08a903140304406015008415280104d403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 767157580 1250 767156330 767156339
    0xc030c010f0b0f180109020904060e0c0706050c0c070312050403050d0809011a010912030e031009150207021807200a060e030c120d0b042a02010218040902030304 71
    0x84600c546110030031140ca03041034200c6481c1001040540743e9058920444044240d00d11080f49081401409019a03021400d00070035191940002c000e0a560030640b107003403c0948000c001c603002800300307c65207410b007000221242804030564070301381c807a0700050031018195540c003d0410110f803001000c0103814030002021131030070440071419080355240d146881c10206000303401e4624614860b42038078104d0242900780e9a00030700f4141144c0c21b00e9040d5200b0035140c582204d0542c0e60207451a414815070700900c41513000c5900000ca0144100d28141c0b102214411038000c0c1d01480f04040d500c51a0303100321040c41055213908552101680c84c1c505581c401201811803a200d01541c8500b59900203110302c030401c103080c803d02c4054040b031401542000310440200d40e6420501c841103210880124420042003002c1c1c10000480000134070510100b000c00c01d00c840c1001e03012250f0760b511440e4401038210140103100310b81101c101e45041000b0031980354180805031030703540c100701d0b09031000700030015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 767158830 1250 767157580 767157583
    0xc12090f061a01030b040204060e01080612070602340e04060b10030f0609051003020d32242212031b051603080c160b060301110408070302060c030c 65
    0x9002e0301106201c01c2c0022903035000504460044003840e01480c410001440a582c2040c1c604d02100000d03c0e02c99030070742d55400440c4400d10700d80b4240b24103104032103001c520fa17a00403421820039a459881a04c81d442e8401401d46d00e01e000c1140c06000540801c000c0c0f000a01460409a205001e841b001c1783c404c40500100754408929813141000070786c0c4450340340b03408820380103450050424080c14401424800c81281e441d101c83e2000030310851203242001c0422400c0221340c5411074000c02607050305004219081d81c4408030074142d0b480c600401ca65080001103012100c01540c1c41001f259000e50380e4035403140d007181001c00341740c50425604030692000490000000f0701d48a01564041002d0b0021008400c159070315503d904140035040c4040c1801c09400283d20302c440350540b400401300e071105515040703d40b1503900f441d02420a030308450410300c01e031042c200b4040c0d0800d500030040703405100d034410418000d901444e11a5000103800b08090314011001c0c1100c80e1101041d64030f046049410207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 767160080 1250 767158830 767158841
    0x5010b0a032a090f240e0a0909210305070816090905011d010602030c1b04060506031e0108030c10022b0c0f140d2d06080c040c12090f06 60
    0x40043e03002c201c140000300441c80000020104c48507132a4401c042d003c010310308070400d1004502001142820000c2a0795404071070030042403109010401007400f4185012554084103140191421303540340c4a15051103882440c1c800e070182e90b46d14100b51600300403001d5003815a480a410044881d40c081a07002c1c661007114000c1494100da080741e00103a101c030700c035480340580c460800d6400c1484200e900150200e050b05840c2c1074120003032000c0300507900050080c00c00307810541e0040070110400c98207000400b0f42ca245903e5444c04e402d00d5030307030328000a40e07248500c00c0803056640084000700031285070798000d04030010010007a404c0c0c4040c40c2004443c690311103202a51515151140c081507550400e00003240001a031920325400c4070704024030580d5200300200e401d8080e0b6200840c0c0d110b92190412003102c81d44070340440500a034283c607000c003e45175a02507107109000345d404c0f00718145054400c49801c3c0c003880c1c03141083d0b00d602d144582e0052020440a98214150003507410002d410761080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 767161330 1250 767160080 767160161
    0x501020d06080f07060509091812040e1e07120e0106080f03120c040b03040b0711030a0e0405010e0402031c0c02181f03021c080c0105010905040210020105010b0a03 72
    0x288101809941c03c41d241c02082c2c0e101c24140034041055440d1500c2d26001984c1c044041c8031090322604007840c050745030a003185a0300500100219000c00c01c8800b03403944134003c1741c83d070080354009100b100c080300c04003000741c4440000c1800e80034508590502904039200300011304d800050142c1d41c4891403400e00ca0480e50001050b080060460b0040100031482070f04051000a26400e00703040184025607440003600142c42c0503400030000d41c81520641000d0311b4400300d50192031302c60b1990b06000d001660820b400f2441385040500100ea40e86e59014081c0c410780c0c0003001004e10070b01e42c641040d18003403a590454100082c00c1c1d680300140c2c88105c0c01c41149820700b900e100b001d10b0840d948002d50700c00e020041d04455141c034000c00141c1d030380840c018000c0004036a0000003040c00d2030140000d1050f01070006080d400c090000500c0d4030039074040da200d01c0c025602c00481d5446408100e00f00d810074051804c00c400d040c020010030714400c0d403082800c1604058903680c2245584d5000f0322004e0081503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 767162580 1250 767161330 767161333
    0x3070218042006040909110a0e01080106060e150304031103040e0115020a0f031407020901030b1803070308130f02040906050108010b030a0f1e020d060b030c09060f0d0501020d0608 79
    0x7440104400111602d0b400602d509109005400c2500052828492445629030b03240e1100c10940510840000001c500840144080c0320903130b0760103008180300d00074420120954a400d1700000d04502400402c11031400041403072401e11004c2500700901e800203002a0308208c404240d10380000410002030014090019881c943d540c541140c43d203a03079411070010402c6400041d642c90000d038040046102c2290725040480302c0d2000100c84807154001d40f4006980b213000c1100001c1880480c103061030003000c2c60101010120034155806a49104584004001403520400290b545405000c410409403090142484904082e000a41503c001030b8080e20b1440e5900700400006000740b10740032002d04283c01a042c00169034460100c1444e440c00040e1454103458220345140c2c0c5c030703502983e50941d40106003c00b60032150034413000031720380c0b4040d840c041d00c51080c02d4815032030281542480386a00504207040910650203200e0804650a0304442564091015010f408001e00801014001400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 767163830 1250 767162580 767162629
    0x206061f05072d03050c0c01110d1413120c0b040b0f0c030f07050d18050a06110a1a0912090627040f140604021e16050a0609110a26030702 61
    0x1640e1b40d0418140d00c144034180110340d21015803080740402e0801410101d0700301403c020311800115070851244215559440c1c404000200380312005040d0308074030b58025584007000b1620f40003d19101d1081b8000d4480d80c810503c103111010707103500c0040028140b18410790381000d5680c2c1c0c5003c840d400c000c00440b80c0c0d80250780640040365100002e03820ba82000004031100030b1910005c5a818529401140100712420514081107941000355031040c0d1390000740c9884190440c2840642004251085807242c01820303107110210032180c0590b040c10000034005842c0004c0c0d1803100b01c8240092492002d0820100410146030392540703c0c1061200341c981e008504140140f2480f2803540c00200700d50310652040c80300642c04044030092200300300142025a5075501480160180c2d000c28450080061041100c50002c1000c5504002d91052048507862814442c600400071103000da03012301000400d41d0f14038070644030b40484070384000303064a5066130f1a040440e00400c0300207400082d498031801242 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 767165080 1250 767163830 767163847
    0x30708162a150501150e18070201020408120405150a0309171b06250c060204030602040906050607020f0402030a0603020d0b1b04060813020a090c0206061f05072d0305 73
    0x204580d0907903000b01500704020740c10b0a148590031181030710310300c0c01c02025400d91511a03c030300220118160059110440324a800034000313000c1e5005014042940c0105021485605280e100b41c505645008180801d0099150800352240c0c004908120401d52104250004102003a09100c1c2d82e4004440c00e40d542e000761000880141501c005401e442d50040e42040303146200b405840d0307280310b01e003056819004802c1e00c2c219a03035a519500075050702d100180010400046900400c2100c1142c24180303c81980c2e0b20402215001703e0b0806900405540c40e0b01400e0300c1c00340e0055503c00c0c00301d01d000a03042e8880d008200c08a072013010403504031044805000c0201c4079400800700481c0048113040c41d090400200825403040030301240d40d4180b1000040e000c540e1540324a0020302101c0b83c0400c20803c804400941c0c0328420344c1e00c540500c0b450044101140480d04800c102c10045d40c8400b49016002e03510300008081c1c07600840c103204811440200c903440c4c3c05a00324041c038040e80d9510780f1600b0f039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 767166330 1250 767165080 767165093
    0x11191e050301061a121b0a02060406050f060612060112060308070b0109090f030804020f04020d1d070635090709050c0304030f0c03030e0d0210050c030708162a 70
    0xa034011400104c0d880719a900282c18120440c1d602c180621080c11064840400400d001c0140d0400100300b0b180201e21040c060340d0004072075101d0341c0039040070b010310b07164009040044241030300d455070031030010469028091119121250880418540304140800c506a058204c4021740c00444035810000392040620205041a83c09041208000c000b003081d15910407628980e0120010280aa28000101950384180004d402540080e0054ad9546510342400000307129501c4102c00001c00402c040c181500c00141090903645940c4800400041c1c06110340000c075014502030311804492850b80880304002c43e007490203800210b0041c0036140c1010152400c0d285c1c010007103010090180104804207a00900f510081c1c015810102d54084880c10200c1c0a85840c0001c0d1586114842e41261020740c00500c040c1e07680c5c1820f904010300e40300c04240c08814801601d840300003951240c0403500320012880004042a958181000c019403e007006244203404000390780d506212080031034090200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 767167580 1250 767166330 767166341
    0x30c0b0a0206180718090f0b0103021011030301091805011103180c060306090a0b031b13020306090c0906040f06120c0206071706030a02041109180411191e050301 71
    0xc4200d01142400d82c0f038480c2c0c1d80d510726502c500d10034010303d068116004181c3c0e038003200a85400201c2d00c81031396803900305140c0c01a42031008038001d03030000f00c084101d94810401e015004411102541c034507440c1c01c0c805406001c001e5003140900d00c01e1101ca00000301d09104202c5162980c0c001c0c00d8507031a00110400021502e64034103881d41c0c00540380b51010359900c10440b035115004683e506050748034031003818001c0030b0759200e15405d80b04500355400d083c4160540c0d801d012504840d40290f0003018810002a0b010942d0443d8015150401180d00320a15170060451614040c1c5020300305a40ca070011182c0c83c0c5540c3c4040045004003c0031000e01200c1d0152614000b500c1c0000d040038181740100403c10542d0080410503940341202040b102c0e5800d0010241c550380003003061140e0f40c5000480c01c001c1d40071030700360f41c0308842c40c40e03004181c80202048148a650000a0708840c0200c042c01e01078105003580d001d003c0400c1118010400030010400c00000c1c09459403101d0505d410072041c1800c651 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 767168830 1250 767167580 767167591
    0x1b14010b09010602030406031806230a0605031504020402130f080d090320150a051210060804060b1309151505030c04020702060f0304031806050306090c070309030c0b0a0206 76
    0x94070720040c0310041d0000304440071a07006140000e50402011550080100c49240040c8801d003007140044d5510007c106120721440d020400d400252241c540c45412141107100e41d0b505504030740b40204034012900003140c0d01c980080d0000d0b192122a0f01010040c9030660840c02990001820911601c2c800300901070104085c2e00b0400d22709411510350f24500e03110ba002018000591401190058580c1031401c505000805c011a481c1c1406042c06032058000c0c00c18042090b003400002102401200d0030007046809584544103d0703101d81c0c44200140c03500a42e4a9080444a80021800b510781d10468154602490400f00f4016a038a0364034103940383c0c3d82ea81c1c046410300c1c850a000b10355010a030707551039890860b80107030348103840c0c808105a8094103003801c00103000401013200741600502003648030b1045002c90710000d502d4020503240360006540c080c1d040300780400000c510051803401408140d01034180a0001a941d0365a00001511501700c49050b01c0f01140140c0b5542d0100101034010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 767170080 1250 767168830 767168839
    0x2041a120601031a040218070212040b0a230f0a050c07090603020907080423070f06030504021002160b0c100504050d0905011d0907050d020703051c18060b011b14010b 73
    0x28107144e000a42c03842082c7e42900110010b00f00403c584034020024440c0b1801d489000b55142c0b0354070301c003101c1c03150400a021800304002d401400e075800344000e100d10000081c080901e0408040b110014460f80000702c641050100c208100c60b90780c0420000e000003001440300105440e0700b580705000c1250805401401842b0491040c40700007a620b40151080480d140d08414040621500e01840c040d4960700901900700d103c0300200e4425895041030340319030b009991300508001d4025040ba13036482d80104010a11074580c2060140381542d10041c05001d803140301301c0e01000840c6109400f11501542d007141d0380e84c007401e140c458480c2c000110100508003400e000c0306251180d4044641040300818041c4512001400151130380c1c094000d0b684c0b070002145086481e01941c0c5005019a0301500c04015450b9a01003030220300c4880380105e0340c0110041e40300d0201060f0ba80d0360300d0094107102c0d44036414480d06808035040001c000c0c441c036400c14099246800444d0425500d5421503402c844000d000c0d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 767171330 1250 767170080 767170133
    0xc0306150408010b0a1e0b0d140a0902090601170a020714010c0306050f1918090c03080702090114130f0e03070602040906080307051921020d090509100302041a12060103 74
    0x4586c0301007410308803041103c602d030382d801451759000014046071843c945070002a00512115010550010303200c24403d4565008a0f200c110054074020400301c04010148998400207101c3c0780d01c1e80140175024402c07408046e1115000401d14291074207900000000780e0b40760360410641c40d02c07584c809401c070340c1924030180300149696509801000c5004294856030040250142d050b500e80c003480385541c001c0c0c191401e1603101d05d1f1000103607004503000d03403103404c030780b000071810312a40c03296500500801400044076510114000000c1c00d079002c1310381c900c1c40e914850030540560074001004124410301e00141c0e501c0c00c00429a00711031054200d148645d00a0150a00240f00000d9898101e00b0181540c2080c024a241200c1c0040d6440407220100039402c802000e040e8000031051064000c0f40c80d02c4284d50703215000c1c44141e41048038503021040700c0c840d0800160a20b5071128048114040040004110610100c1d81c4500003991807492070b40820010000d00847d08880946202c1c0c03608603900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 767172580 1250 767171330 767171369
    0x80f0a1d2407021c0b070210051005010f09210201021203060d0308040c0f0303050c010b04090b070f1b03020a21080f220303051f0e0c0306150408010b0a 67
    0x19540164164007810200c001000710955503144082d01d802d912080c20707022541e009141200c10004280c3d007407001b51240030a01d41c9115054096240310b101c1076031041c26031a14100044a10320f255030f1409041c000c81480c0401d00750364030141950b0107400400300f01c4034455548002446c1810200c00f0984520013481070104590310540320150050b0507240c0581a900c540c14104034035462a07006000c4070410076400800c041c0c00801034038080c01503a000704041d50300304080c030060b203500000c003c4c42d0103001800504124004c4580c03550258035860700b684014042841074001c494080c02c02da016174490200a0300708650800c040d20220070008240f001c0d1880c1d00405812442e000d0421081041e00ca0b000501c0c100642e0910070680c0540d22080e44040402d05000d4010304003611a4066011200110110400203035001004c0310301c202003c000070356658900e000950805020141d00c008079180c1d80c442c2182d1440540f02510910000194030300302e01003046404101d0307610505c08000106802036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 767173830 1250 767172580 767172619
    0x51603050f15010203040b0a122405040e0a1e05160b0301060c0212060a060807080c0f060a02070e040b0a1a060702090402010e0d0501091707020319080f0a1d 69
    0xb030300142090010905400d61900603400c0d03000307503003000c801e24002148817140b40d80e1020511107003a0720040100300c0440c143c07069042d0840305400c40d000e03c40301c0340700030419801e00d9804150039031842e00030384912035029561015415991074101d842000800c6105051040600034011690400051155064940014010240814412041800101d8071807006544035103d500c505c404001c000d4640d20301e45008040000c200701c4c05146034510a00401045803840007501e0305e040d0340010724110700c80d0030306401c00c4402d6000c51007200443c00390b034500140c14014040c0c128000d030301c41c00038540c03d45402360009045882d140c81110441d021003c200066498a2080781c0540750160741000d081da80350f0006903010703141c0b2458140c00c11420410070082c48010f51000903601d1042d44400e80c6403621225400c1c050194500180d415002900385400105150214000883c400c41c502c1c1c0c204000c8402c624010b4010001d85c0c404600181d868004214495100942010301200c4c420745c40000c4d2588038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 767175080 1250 767173830 767173861
    0x2c070c0c0e070c08030106050a02100b180901090c1211010327060b060f0a0323010b0c071a0301060e1f1202070510290609011d040501080105160305 65
    0x842481d9210041114144918045202e298110300c6117076072540d4a0100034010b038802441d400042c0107450062072410114010004a1280109040d0554010940d44114224060440d00e5150360b507161400008034070103a070b0fa00a0159a02047c10400e40d41000043d0941609441d4101850481c0380e40c0c184528500f0101102c0420f1010303200720b841d51416500620b01100304940c400350100e100941030b104c1c40d0060142c2c0e56a81d80c01e0000010080e0f20042888165100e1701e0003007d42c00050040111020241c11004100301c02c96180700d035030703041321505800ae11a080c040c02100000602120340c00000134503002605403050498581c8009962400e440060201000c004030400305a11450b4581c042d5084250400240c699241b0042500001490307245001c08620342c12898004070241407091810584202a110b9860409500011101603507400d41080303031540034540d544110345a038841c0e54040c11f4200000681800c00329405a41698032000b048205824501000391000720440031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 767176330 1250 767175080 767175089
    0x170601091401030e010618152d0f030b0a060e040b07110c0909060108190c05060304020a1212110c030a170403050f03040f05010f05030708102c070c0c 66
    0x707032422040c0c89004030060000741c2d405101035030900c0000306d01c01141a01500e00900700781b1003040b0a08a10394082c034000381e1440385014a080d540014103c50302d50748802c03908000c000403002079180c3c4031502c450646c42d10360010b0340c003149484104220b881542c860396016101081c0900c12034602955860b000900042c510700410010103024103450000308040151540300400b06090361403c00c0c48580c0d079120900c51403034a07210364001030300900003540d002045141c00c01540c8007054102014001241d00140c800c0380c02000c181d00001e02480140741c1c1c0740b0790703a01c1250b58508038a00120010074890381d284602100d5003000d120521503981c0065404e03080da42c04034268044890b0340380004098000c581c005002c82c052805203090740c1070080002c00030350721541c40b40d84e2003680b0307100112001941060214041401003004c982240d0290750207580c800d00715090489180e80b84c0c0f41c0319220010a1450044144006424168030a0200c802c264403084a1900c2101c6c07201a48800b8000d0703206118 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 767177580 1250 767176330 767176349
    0x10030509031b0f07170607170103170904090f110a05061602043b0c1005181012060b030c04032306010f0503060601030504150c030e0f010b0117060109 66
    0x15030150307100300740310841c0c900f05401c0980e03807480c0e541c0c1c41544c2000c03090305480c0240d0281a001030050307401004941e0001c2c0e26505564110703804c0d5540c0c2041002d280e41920380250f814006801f0396550f074043c2480082c0710794001701c0c0d10481c41c41c0900344006e0b8015024440c19240000b4045900c51000f5944119401403050b000b602070340c000301e8001d094803141c00603580000080d411403150b4400b90b42e54000c810002d507a407002c0c002030450ba254003400c055141d200800006450009210b2005010f00d42c0110700070100307481d0700c100022800884204150081748540300301c1d651030902c40c4241c02c024034083d02d004d8030b1443e001101c401e0794170840c04014201c40c0584000606685034900108070300d2100001c031126941c482090007a82c0015101c2d00707100c2c2c4942c030009002940719004e260b020f00e500a202000700b00e5000001c034090802003000004142d41d40f07001460b5908200030001d40b4030440000003500a107a4030004151956a0511040040d940400d02070284d07440038200302250701241 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 767178830 1250 767177580 767177617
    0x1501050f010c0f1b0e01090501061d040b120618060402030304051002120c0a02040c05070203060f06010e0303040f1e08060a0504060605090906160c03020a0807020103060807080703021003050903 85
    0xe000283d2001c0444041c100404124014040008807040d0b44141c45aa0080203d10fa90702d01111066803001d000703000001d000d5101000c040c40a0791402c0a08850042010035502c1011000c03d074592403501d20304180750301000a02100c0b12902d41e0b40c25045c0c2051001d85031030303e032a4010070ba07248541e11070325004144e050007494080b403080c8160200f00d59484007181da07034215080140d07941e040c3e100c0300b60312a038036284205c107601d030041d007c407503185030f0180281c9095130f51000e400b8100e4000501950501c004d0403850030031a0f40a20040015210020030800428241071000d6945c1d041111021010b02e41c094007802503001c0094a035a01c5001c0100100b141d54443c50b1810107000e290b40055080400b04080c80500480440e4040c858810307541388040141c05484201c8044040701c00145c0036801c02342200c404115208d00525210f4018140811429554044640f0b082c407254840252508040f0f820720451038038824540f440c8040780b400b03104c90308009238035540360712a4180b15070706580441c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767180080 1250 767178830 767178833
    0x5070e0301060b0412080f0d0207050c06031909031e05030906150901090b0f040603080c1501180e19050d0f090e071107051c0201090b2b02040f060509031501050f010c 73
    0xc000f150b8070049081c0382c52361584416075550020350011841120349004020a9409905120302900d20400109203680301134002c050700100100003981084d803c00070240c01a50751803810001940000e05143d54540d6603181000c200d9041c242c0c041c0008503030300d5002140400076a02d5016550544104060028180340354000050f4101003003602250014200740c1c00000b44580f05002e0103540e0588401d0741d0081002d03c412130b24224090103401c1c0c12611014244012080703640c41007402c80f0000c8100ea504461705a10381c03003140d00500045416621903403050314600c1e0700015516070b010190070030700c011a0030018100c101d440003d0a003010001d4806850200c0c4c0c008105070703001010064411400e81c400c201144444007508030080c2c0c0030842c18075001030a1683ca2085402d90040100d00703a01001d81024540d00701942c0c00d20088800b40c0a00011a8440944c154000100031a440b00f5507100350680905040c0f808860380c2251000c03400f0010002510342c0c0c8010034640000346007071044116075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767181330 1250 767180080 767180093
    0x50d03110c03060a050109050610121e02040b030907082d0c04090b01140f060d0b190b04030209090610260f010b12030a09060302130902030a05070e0301060b0412 71
    0x241c40440d458442d8034148520550350740e11142c141d400d50381d810b00c07013940c0e000f09100e0169108940f00c0002094250342c03103030050080e4407000b407100305008030b607480d02001010902030ba086074210b41c0c54008000180180000200814401850018040c203d200c15810244e84501c0003d55071003a5103000e02c080b040500700c1448002509600140308100b4090f0b40d05003008025024020740c0032440d1358000d5400c003440c04111605101000a01d1907141c0300c2601e0030500070300740b944034464001c5550140340e03c072607078011040b0700074103160640c0540340d9255004008400d913001d800501c060300003200388602041d44221b00020344030031a51091442c00d50070801204009030304422445801501010400f880c8190000c0c01c49030821640c0c814a00c1c0340001c1180c0b02c0c810b0410a00c007045c40c0400400440b400b940140c16511f1580142e20f040581e5040d0f44803c3e603108442040d90966910104050741d07400200000da07071542a0001c001d01e03428054541d089208500584009d640c414440c1003c0045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767182580 1250 767181330 767181343
    0x4021903061e0e072c010917060c0a031805150709141012020c011b14120403030b0a09020901080901020c030f031003051207050d051c021b07060e04050a06050d0311 72
    0x894000521018540115560a41c0a000c1c40c2d00107407d48800196440d0340050805a122204c0040c0c1040d4403500641052680002c0f0703040141615202c6032400e401b68038884000060080001c0d01044e1000100c51104210040c0f120b0188940b107081801059aa51102070769030781c0c103660361761401112042c2902ca58081e4a41881c04500004600040d440306400081c664900345541c0c281d8480e5420080d18148070b0882c2d0140d41030001c0c059698508014882c080e002070090900050002c00711022401100030341d00070f1980183c00264507043d07943e2103a5581c0e8007815100007103081480226519450f03108449030b02142560200204100401c5d00003183c1c001d60780103003101d80c0100c00c080607001e540c02c201004c0e100c0b4003c1c4c01040300101d0050341110304000c48050b03141040c03210710001800a40080480702881c50301004600c0700100d08028441c060700c8683c0311020010881c2003040207440009007400107080c00c01d0420411078075105408010203505007020134180030507080440c903111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767183830 1250 767182580 767182607
    0xf06020c030a110d1109130b09060702031e0d0f02042310050a0513080d11070e01150507050106090e0c1f0c1b030303020324030d050d020904021903061e0e07 69
    0x1100700c1840810059070408282c55031048c00d0040181e0340707044500e41c0700c0d0000c58900c00540c20400002149454030001890300031004050142400f0341c0b03080403000c5441100c510142144d00280501c81f1105540080c04095200a0140d464264840104e01020510300d0b51006015000c0762a54a41d401503040e6400e0f0f80c0004100500c89540701106c0e81c2c2d80495030320308030125082a940b0309081c4800324483c021f43c0c0d00781b00d210034581d19091050180f0380910343c8281c01c100040c000180001c42c2070103080c00400c4505c00204028200909407410454601c10040c031401c072003074030140800b40b441d641552980355400e0218089419082800714074452045190700d1341344801c0003204154240d40a103008036680b84106840c4003918482062000c0340c0d40181740d141d40007078640b00285110f4401081d45000740e140150820003018042010380e081002d46d16081c100c03068541e400c0582c144602401410424913000300e008540c2e23003005501510340620b001072400f0380006215140660717014403070923 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767185080 1250 767183830 767183839
    0x11060a140a27140105190c020f061201030201080105010f140a03231905010602063105070816150e01020109411005060d020a0f06020c030a110d11 64
    0x7002100d680e0b80c082c1c01d4014408414805840f080440d44102c056605407000610880514481c9410980e902e2141d54401c9038040d184a0f0f11150a440300310280007004500c03441c0c44081e50561002506d030b900140c02c028100620078102d500c1056200b4891210405407940d2259101615542180500440e80c6200d446290f502040d0201d100304207a09031161a00951581c4035190103c202c0060700d0003072140c403006071301080100d0b888079042d0a0313040119520b000210761441c0d11440e00d1421100c40c07601519903400500c410003e03400709200780d810b6101d5070541c003800507050034110080e031080610943c00300300c40d448030141c2a90007584403540c45600156402c84002181e0b042ca035040c01c60f551691091201d0700c062805a10285282198807407081c4c010305400d001044003800204030052080e035010244a043c900581c45411134140645003003880740701100c5c1000d501900d0592955036684c000d034007600c1c2c0c0801081000344160813500c0c086482c0080480541400c0c038100300030504040e0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767186330 1250 767185080 767185127
    0x1e0106020f010609020708030f06181003110d0b070f050409180203011401060e060d0f0207030203191b0b0a0b10020d030f060e0a110d020f0711060a140a 67
    0x11a03800080c48620601074800900c5042d86440303508041c0d00031000c008264070014004518a466004202a80000064040f0b030440c00745040c40b00038180c050320019643c07070300c5507000d00c28001c0b5010040080c00045d256007458280c281d480d03843c007820040c4a00108482140d10100803031240d000c440041c04800302c207005d11075820b80940310076030b036084049202c0c0d031070220400405010f210040b07040b103215468100d107000805041c44800da001c3c0004500703050b5a8a481003030412203202a0101c0d9003e079000b5602d038141d1000602006162a004a003840448001446282a00e1103003200c010340c171803503481903502d600ea42d010241054074601940a000c1402040385e0550003d0a4103200301c1c0c41e9014449105403240700b00c1100e025018884501300d01c040000e1058005802811070302105401c054680b040f22020a000c03a00001c0c42c030f228038040000c0c030b1410b000042c00058940d4104a1340c80303180905142024041c401d1011003200308140200d42001b005005500480201010740309658a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767187580 1250 767186330 767186339
    0x1404121a0405010b10020105090c090c040f031a010807032042090f04110c160806060603070e04150f060c0c0f03030203120c07150c08060603090706081e01 68
    0x303013401e010300d00d0241c644000000300043c0305008150148620f0780142141d03d40f100709001d9103203401030400f400d038407080000080c01c08138501042c0c019400381064180c03810581c00c661310148411307172102d20b4a87c0a5181807000c51807034242000d81c01480d403803140d034501d5500003094201003150b20b0010352168820704141d40641d206070117140c842111002400c038094480311000c40e40521004070750019003034881d5403802d042540c006030b00d003040300300140e0030405030160152400c016041c449607a1107013020204908501000380d1a000542140c00300e0a51810100082c905007402c00d03900d21454550003601c1e5460004401034000d442c0050300c040080351242c4000d000d070b0760f20703860071a01c950310700000284030595940200c00f030381d9160340991301e00546503e00d070107507802c09444881036010400003c0002803161052070080c0b441c3d110041340c09071310901c0117412130340020100c9003c0e400030400c01480020128800007610204e040c06215a221110846101c1d2603c920041c861a171400010a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767188830 1250 767187580 767187583
    0x31203150d0f11010f03060f1a0c03130303020c0306040206090f0a0b0415080a060303020706050d06181d0a020901170a0807060b030f07080706050d0216060b101404121a0405 76
    0x42025000b170301c0d031400d4102540d104400711401d500c2000d40c101d031400c030b0500100c0005007004c00c04d501284200c80c2480760240895007140d00040400003000c0e240039040080540600c8100304404048025200c9481c05030003140d0188950041c6030700c10f0100b89240300c07440c2d0380e101031180542010702041d6161034980040c4030107080721402a4010410050004208038891700030380c41903a901d540030304551851300701705641d540c20400c0b59110150b142e0202085001d000c15908030791044050300804d1410400181d40b9904826001c022100d80000c2000c00160310381000490455525101664821140420300d50400645410003040800e00068460038003010740c010440081c002c03815680d044003055180c43d629038651159010a810013a0100302ea1170186026108529234000098a04034070b2160001c0e1561040c030040701c10a50711a0b910b48036060640c003410300c0c0200c5042ca42c44500040c2207905850059220b504a1025800c104e00100400404450a5041d110007224118100752070b02a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767190080 1250 767188830 767188853
    0x6030c120f0501170a020d0201080606040e070c151418030705011505030601061b020f120613050111090310050702070f090c1d280f030b060f031203150d0f 68
    0xe0744020b140024000c01c2034004a45c041c04550f0003020945010481d5006540907000100312b50343c043c0c018000003960080c0720424520502c0d044d500c29040502528003180030f42800c2c1046281d0030b240180c102d890088815059170804041510000d81200c081c0700a03140d4400d10038000d1195007020690821000403440d01c0040c0c500407010f40b0041c4c2c0c0c990208a0b602000c2400300c004449540d040d01001d42031508900b4144a0040c0000008010383e900040c60701805403084030201a0180011007403003c01e00c20841c40704840c00d00b4601e00419100004e41c1c0c5c49440c0c64440303000703603030701d010400c0e66008001d0b940050141e0340e50060070742d540303010700d0009081242c4a6008610800c2440818a0380bc40c40700520503001040000c800d9100c84411801c00b400404c904001192500c02007a040003003015034004500c60254000c162030250700b40b010301c604031010326000344d010002c1e01e401c00102d10140d0344d102d044807200c0406040b01074000303500307000c6c01c200150140903e10348007424012515180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767191330 1250 767190080 767190089
    0x1707030c0603020903100504050312010e04050d020615040f060918051002070f140709110a020111210a0f0c050409051302060f0703050c0712050613050706030c120f0501 74
    0x2024540c641ea800706500303a100d00301c00594960040d00c09140b60b000b00b54025034000d40560210383c1030a1a4a11003d00c0e07072020303009075044105090400c1f0411000704980c041d00703041c41c800b1700320504007030100d4600600c81c2e81007030744100c0d00c4032440c4d800c000b107a911000003410803030410300c0781b00d010301c10100503601d4140e010f84040c00344401c1d0600f42d00c1207000b2038042650020220040c5206138441d6483e42622003c1c8202d28040c0c040000f5881240340100c00701c403154042440c1d51885000400381c01c480c0700d03000c6801401c806100101440726010106440356201c1e4481e254981d403048810401860020000d80080d4a04030301150055070000103001540c940342c0041102e40c0b0b4031088003d142117655802940460200502410000c1d03a0016064103403080c05c0040c103202005406c0307420f000840c1c000d01003882414500e103040c048204503040d00581d500c0e01004140f080d54850035107820050184d0030500d41c5410308102d825210b280c4c0c0742d060034048801088015005410308010706000c0c401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767192580 1250 767191330 767191343
    0xf120a09062a020d050a0b150409210c082101051f110304090212040218040c05041509021207020d14040e1005060a0507050111040e06130204170703 65
    0x340070541d94001c0814042c0369601100040c00b56090301c0c0c01078040401000d0880c0c200c0d40000203100019000c11103401c0240c46914241414a004090b401c9031200310f84880f446075080c1031084012407400d074120054480059030700000400d200c04182e0300c0030744481c00142803600008108104940f150340d800d504d00d4a0302128242ca90f41c07001045100900e40721500f04000080f901c12004a00660505901d0240c2005076400c19170381d1001c0f076040341c01002d0100884281c0342c080000314502030300c106c5a0700da00445028864203064a0340c040b8101c40d07010345802207a8445c0134a00c142041c1c0100380040c181100e00b03540d50804110041c03c3c0040a1798024054418405c020329001c3c000d0350410441071303031092400c4c2002d1508846421000700500701c502c0c008031054000c544e689800c00200f00450140d1541ca541e072016203082801c6034102c01e056051085c044c001880342502c61000941c0045007100c00508103480c02c14401c00034462030784121041c0c46c1051685140007404101d03d030032a4022a0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767193830 1250 767192580 767192597
    0xc0b031005011106060d051006120611071703310303050c090310050a11070f0b06010e0f13141302151e03070c080a03020d150509010b0a020f120a 64
    0x43d100030854220340011a081500026242c1c20304010440c1c4c80350062085407136569500501c40201c4043e41c010a98a40d9000d0044090140724001c02c815001c7c03502c0050f01d052501d440b49031418814080004042c4c0001010941d040d09a03e0104d48400155007800d490060751511001e80f100946c0003107001c2400d040001d1908040401036a45d11080075001d002c0c10320702c0341001d40c014031005000025465a031580c018440340341801800050748100c154804011032804c0c131020b41130f00107106e00e04018580c5806122a00d0340030001030900800d41310f00411162614107200500034a04c00140101c084904204640e80a00030030100e0798003e0758403400458140702100348501c541600f403000c40d5100d038a0168200c1c40e100c000c5500110501d0034090000c001d541d0044030383e0103101d0900000c1c0e0041851f01d20460030384142c40d8410300b0b1a08100c21145410046103070800c0502c02c000c260400460300001ca0740c000e100e40a08a0740241c00d0324500d640d40102180c99810410403a0000303135811 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767195080 1250 767193830 767193839
    0xf380a06201207020f240703170412110c061c091b050f0904020a1a070b011d010630020f0301030c090b01090821120709030201030f0c1202090402070c0b0310 69
    0x8448a209425906100e02c0016109201b800f40707a03400141c00f1030402106800000d6603070303040c1c3d101d10b02842c890240410b43d115004d0004140098000c102d0103940c1200d01d0200060b0360717100440d400495140c1010b00c2e43c14842c44440010701e000b0101400850a10030080a0f2030b90708050031040d00c0c0101da900500118020500400103400c44000350403112252050181111150550464a0a41401c545008141e43d1007403850b01081e0700c00340720440d180845200d0a030417545070310301528240c54002c400c240c603a01542590a20820303512003550024940d400044640e4048a401c514103510140d5256500c1c9881010240213104044042d803400000d00d642e9131003203240808503070023003008000761031501002800709605d5400141c0c0c400301c00c02c14801e030500b207a540144142801c1c1c6410108602e580005400c4da000c00001d8248e4510304241c40c460f803030f00f000304039844c10689900140c9510b9280003140003840b03852130281c0403111180000820095840003103109882040f02d002e840c0340d55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767196330 1250 767195080 767195089
    0x8010509010234080703050a030b0607031707121a031504150c171501020d083903010b04061106040b070507020102010f380a06201207020f 61
    0x800714142d41c448a003202e581c5100001d0f03640c2c580001e1800c81145815501c0b40d8034002580c0c02044120301045010410410482d01803007140c4655405a41c1146020161354008019001031014820b0b000c0390039010440b02440f95929161030409500100002c3d54840c0044404038039003842188644211030744c14101005407120580200e40c05101d040c10031000c00130b07501c09051120b0342d80302002003d00080f40942504002c8a01520a049042c00030b140d41130300090500c030100c04030b071082c011400248400c5c0030040740c0c00d039403807001d40300980e4040984441000100c2081d24100717010900110010480000200052045500c03c0c0c17180301c0000300c542112340d10b40204030707030140420221900040c1043d0080340204152403051000040c242d101e10585d5044172016250030045401c100100c404100415100c100c00300f0900110250340d40c111070001780828483c0c01810304210040d603021380784106070b0a4000580404100382d43c0c0310604151a909550041041070348120301d90307000c401080c00c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767197580 1250 767196330 767196337
    0x60908100c090b0c010b130509010b120616050712031b0c030c0201120b0901230319081b19021f020c190e040f020406050a0f03021005091009080105090102 68
    0x10540382d0501d8140781000c035543c42e4000141c291899502c078441e0420940d224001801e0f800c5040e400000c1600700601107508462180c42094011403410645605d502d0000403025400a480380651800451030f80d421070f141e0140e40c0c00100003611400d0f40d0060180c260308180c49012490492409400601d5001c44400c0003503080a000318460340a01805544035032103030043c5900480c004260380c415000410041d0780264081c80c100c2c0515a1a5038182880d092401c0d06420201c0040c64a0955160030880b0a8031001e0006e000358800528102c005244a85206007400f014044c1c80c0764801d0400d08114040060100324401e0240000c0285600c14840c494842c2c0c1c0d9050780201f5002604d03205010b81c4007801e150003018807118100c0014548042c02030948a68800c5c1904100c568840c0705201c11350720544c00c07980c4a221058400d0212240341c0c510705045980489071446154901ca40a4030300340704c0d5905241e048070114a2035095a13402220080445107a0300080110f030382c03512041401c070701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767198830 1250 767197580 767197601
    0x2030117070b030a0534030501060e130b030a1b060801240804060b130605090a05090d030902040b041a090a0b0d02040207050c090403120b011b0807050f060106090810 73
    0x30062020032100c41d855401103500c0394410240301204038602a000c4010901d180f680c0000e07030302411001594a5140c003e00d40184500d02f0300c50320440d20a400500c1c2d42d14400401c1d00000d80d80c0c98082040d07a010041e164199410a07010608030b4004e00d880ca400300003901420002c00d0075040001401240383e1386844010803260018409800f84140c210b440c110702030000d40f002900c4075081481d940d21800c00b04100d00c2d80c3c101c001580c0b480d040c2841440d13900244481c407503900c2d02e010802d05160200303640b040c242c514030700020792108910004004290141c40301f0b400034a441d40202e83c0c43d070030314011905040d084074000d085030b0b20722608106840841002c2a0840030704000d00c030060810750081d0449902c20015903200720504008200b95120469003903001404881c0b200300c2c8100c91b0710800d11703001028640102004105001107000840d00003006145010005105003031020500c0b1050040d82214243c3d021540d581311f0040a0b500c25011720072843c015144403c213101414840c4070003d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767200080 1250 767198830 767198849
    0xb0c070b090916020a050d020102091908061f09110c1c0e06090105040803030f040309080309031f09200a0f050f192111100c021002010f020d0203011707 67
    0x998a801243d62000c080d404a0300c00e5201d14000c03940043c6043c451418802c000342d00040c1c50340000802c009800030101d15035504204400d40c240002070b004940c0b168442009018040c0e4001031000852030621680c0c4162000c80ca0f20742030100700d283c1403000741010505d05d0112003603c0780078130202010489410351540802d405860b280d07a40d08020b4003501d10914141002ea0034980e42c0c1c0c0e0b41c1400c562040340c8603845802500100400c04d504101d01c04003905426004604040620001c40e23510b0058140c00c091a1840050311159040c0c0754204038203081e4480c0c1902101800411a0300001070032010381c030301c03e242078900800d81803041c4440c001100c40c001c03d02c050300f03103c1005010140c500301254492400d500400420100701030303080e01d5948503011603609500403a5003849030060b411b645800f0f200b01c0010300d03800e00e10741d8481c12200615030100c50320003d04441140c26801022503a01c2e030b00300d5600102d076851a000c8076601075130496003407802d000712609080e00c410f0748613082d90056500d070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767201330 1250 767200080 767200099
    0x6010f0516060f090209130b010f06050a0311070203150105040e010e1506011b0309032d0201271403061501050322080705011d01060503100e03040504060b0c070b09 72
    0x4a4401e42080801110f00e030b6000070844420703000705000c4030b812100380308a01d1411664204110708007001500500502c0001e1b1451401c1400082980c801c03400c0d21001c244d102c81450300300c40c460304100c4200590007011280449000d41c1c011000c03200900c1254032417071030300304001c03031500041c020400e1442401c40980815803980450b1200c04202906e558100400a100a0801d0b00c5441c0941111406615200203107450741c03a02803241c0e80f01c0d0032107a03aa81500f4070445150b04140c0090009180e090815400302100d81d4044100c0a8903000030510341411854000b0b00e200040c00c04400c1e4200507001d50b48990307100244181c0e11040c4a9605000410401c00108984441c030318803544246082d83c1e07030031030840c0c41d00c0340c0000740c11220042c2ea15940d03805a08070b510502d5001e200342800220004e001d5145031000003500c0e0700b40150050070030313511111001708030030341481110040c084c014810031440d6100d111018107074118405200d094481d02e44049102c2c030300030050710080103004104029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767202580 1250 767201330 767201333
    0x219030c020d0c320a0b0916030308280e070e150904060b130b09070906080c0a0201020f130303021011030c0c030903100b10050309030a0302090307170606010f0516 72
    0x50003254200002e03041250010a403032480030304d12810701d0410701c00101001ca0b46810314140000300942400216802424100300c0060054982c0040701d405080003115540c4030554440d101c406940c81d803003078010544d49212000138580c402000c0c0c842500460302c1c480c3c2c0750004600b02c0d80c1c0c10b40310f8607401b00c4451407400d13083c9000140c1036070040c800c000210b0b03403c0724400804c1c05482845500e101c2c490f2220313100402030500300d000720752000007442c021008501c1d00f00042e06085018140903601c00e00083e0404c0017900035012507648030303000c0340c58031f9440d0006030a488100460b40003c6006028035038001e03042032824002c801c240000c00349031501e585c90b42a1001160341c0030035a401110b00080c400071078166414440403010800300346004c02c801100d0410030042c541561890300070722205109100c1d070b85500105030b502c1102a8200144c2d9021103400183c43c003840b81d40300f034501001d1003d2141e403100d80810345d07600900081c0c0b522004018150416141d40c02003081541158005907040c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767203830 1250 767202580 767202593
    0x1080c090421021011040e2406160506040503040518070813031b11030706030204060e040b0409050709020c2b030903051312150b090718090219030c020d0c 68
    0x951401c2c2e5401164004d880c219001420b03030b40c2040b81411707040303408501004a034410309980d603807000d494055681c0d103981c40b03001c201412000e441064015840420340c2003010f0242c0c0380c1c1550072034001c0111415403605291195032507001d4090a80110303000d0350505024041e043c01240107908544030780c10655500805071660f50000d10003a0200300b0412840d1010900c1d032400804a9800f90703c0c0b829030484410185441c1c5811a1710003403c1510401040201c00ea00c10004002c0e050300f2200811500d161400003000f0340000b910182842c041c0708000664103806178001e21030302d02c03101e00307943e04040881c0c0400d41d031507031804500000c004100442e00c0c039144241e00c2a05418440c2c01c1441c20301241d109100d4802000d90070013020641c00704400810300c8082c17110320081051444081c000e060000c400724404010141013201886400081c034601d08581c807014001602c0441d101315190400c1128252980d4801e000345000720b841c10003e44080d500c041440018588140ca82594050b01540d800c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767205080 1250 767203830 767203883
    0xc030c030712060f05010e0405071e0b1e0a020303040b01050d0b010306090c080304080c0306010801020a0915050c0d0801060e0d0c170705040213030b070306030f030e2701080c0904 79
    0x203d03501039883c805038016641500c070341c5006e000020850704641c6003a1512030b01e08032a5810010780b41200160640003040b100d9250030036030706420f8039aa114400742c00042000c00f0f4141d00d03032060074004a003c1c1007041e4004040e510807070142010b084242d0f82e5006200c16843c0c048406410f940300f0300d00600200d40c240d081040c00d28442c201040b034507a601c444450071034010340c00a450b2600100c0c5044a24541080854050003820008610b412030901001d03005190500c1881e0121029a400900340350044040d1807a104001003510b040f810b01d95001080c2150901606002c601d580035803800030f00b4950402003000e603020b61403880031810600081170701d20900c00f840c5484e01c540786010495449600141180810080849a005003141380181088900410f51801c0516001d4200040f44030000441d451a406013000106101041c000c80d50030f01c4004031000c40040c004824040d00a50100660f04a0300035500340c031108503030007007000b034640030541e000360101500713142603050914902d041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767206330 1250 767205080 767205083
    0x403200a0830060103060b040b090d03021f020d05070f020a03031a1210110313030c0f020405330d060b03150108010e120f0a0e0f0a030807050c030c030712 68
    0x100c41040c802c07081031514580c20094030110100d4030009101d01e039601400780300302500c180340030315007000d040600c0b16072035005030070400340b140b14000b6507042410700910146104480d00300351f443d10350039188100c0010758001c1030415a01c500d0100040d41c1280319040e580004403896000d008050881e0b1422030180c035400c8801c141d95031050040072880e584501021140d007032628003400b01000040680000c8402d2100607003070540341007040140441658400d018410f50500b0902315403034881c10b0024046c8400a03000f50094130741414001d1485a01e900f264040941800200314200c0c80900c01c04a06408034a1a400c2210403078180e0010b072581d04103d010003006011a10355164012040541000a901002c520395581100c2420041c051140011107071038458064946400e1a210a485101c1c0048010800003200b4403408a507a81d50260384110700300078110400c1a86a0030b1021296005074401c50749032280700c20052640c20041285007000700001c3c041d0100b035203030995020240000000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767207580 1250 767206330 767206357
    0x60714041701091b030f03030507090911090906060406141b150906010e070f0809010605060a26010302031906110304030f110604050601050d0302030904050903030403200a08 76
    0x200c0c808a080c80c0101c800c0307140100100d104a21410118030007010355107040945880b5800c04e0011031240e25103001d4142c0d04d813400040a9803464400c4030400f1b2550890742c10b480c03c05000009007802c0401500c2608801c0700c25101d01c1d140da030304000e0a8811071003210041103c0d07811180e0003490520251925000740100d44c1030001c500ca81c410300f800300303240160905022900c00e000701c20004210181c007408008903840010b0500010141c078680c01c01d00140108102140011030854082d085540240030140c001c43d1101c00c1d450014004c88818000445110048a1801c0030248a41080c0b030482c0e40280207041c06100e05603503400b448941d04030a44110751503807080c1004002010045105500a5655800c61002220010042e44490221841c158890028030002c90310128406045402c00c80e245500340356186070581c2103000d50040e141c1d105107001e042102004020001b1842035101c0d558a016607201010706401102c0c4541d1080d00316441100c038000065040c40c01080032010200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767208830 1250 767207580 767207587
    0x12010e0d1d0301050f0108100e0c0609031905030d0c0c0f020402090121050601030e0d08070305131b0806060613060c0f06050a060911070f080d1118010207050d0203060714 75
    0x820f080d944252000420315032008010044900c081c0005484c131010f07200c0034011103a40800b000d40d900c914554007481401d00041d07907021980c5c104500110310382c690700c201582d94511708215403241c11601561440c0e5041642e06800144134542d031128555014a03008800c035516000d0000940060144e0703414000c01c483c00146400c1196103207074091410300302c0400d81e850712400060036184038696007481a071003826121440d94111525550006e00341c034000030710382e0359201042c404100c20b00d405080c3d00445d003c0203641c01521803820b0165441007040303400340c0d107558050000500c1480542103295542030700078004284a0f06007464028010015440000655102c6000b120b00a40d171401915950700001c0180420758000d480b00808110140da090001544507012982c4000100a045940c00508088050915807083c0107132007181c6070f03068841501b0002600c0310a50810038902601c42ca03000000e407841d14142c5510302650280150440c0d44803c01c00313840154095542c40d06140091 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767210080 1250 767208830 767208887
    0x1a04030201110f1c0902010e0f030106050d0c15020d0c15020403080409050906060a0b0901030b040f050f180303010b09010c020a0801020c0d140906040e07020c0306130212010e0d 78
    0x4003a01081c0030f1001070a07595a403036409988600350116a040099050049050141c3c0c1c114483c032400c698192501c8000035207400c0003030300612654000c140c0c04921514904181310f10700c24200195500c1c0381504810407515041613940700103140007200041c80048803100010b0600b0303909408c1045080d005800d142d00c903524090340e908142c00036240030350b0300c0007000940042049550341045051703840901c29030070001440c2c164814004158181502c03420244001d4440361700c18108901c90032420000341c141901c201d40c0c00141502c0408448840211076003005c04080b045074100c46a900d141468162400015105c0010000040ea8882d114100008141c4001e000511440b04560042c05107110007041c0078100006640c01181019824041d69540e038442c001120152014040101000c1e034481400328a0700c10700382d0300c8507094000c14040c080400091042544c00c0d0348204c41280307010383d0319840d0500b210722079584801030b50321441d510b0504a0042020442036100c1041a40c8155102d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767211330 1250 767210080 767210111
    0x30105311e080322080a11070918050d03110702100215092107020d030c0c09020706021b0d0f1b0c080d030b3f1f15031a04030201 57
    0x14101c2a03401180c0041000440b241013500003684041061000500110701e40701c41c501405002c280009008401441108880003040240c005102c4981c0134084c21050aa1a1000544402c01200c4620500c800c0580e598000e000d0f0101d422000c4042d1820801d00b5000c0002c3d52614000780015801801c61150745504c403003405501c034022030300040c50640844c54488114542d401c40745c509042c001e000c032a0041ea11ba14451080540600d0415010714041c24206124625503020710402d40c400282c250400140c3e4028202049440c2e00d0300b05481d10020b0401c2d11070401c0e2420702c7c001200f00d90004030150084804407507503c0d40710300c1030052550036500c0c41c6040000b500401280d5200c4841910b030160702d80201c40c4440c0040d100f14103804018055061080114848026051360042110f0baa00c002c4440702245c181c0d00d813040320080320520010100346048903201c500d9181c200051002041c2c0c0018055080741e52000000000d105502d603113801c5508003038022801c5540b83d10302003400111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767212580 1250 767211330 767211383
    0x6170c090604031a01140312040902030a0e030406030c030b041e0c141b0f1c0509010e040c0503070e03120901030209030c28080d09090915051503010531 67
    0x4144191001039410403410405000781d1b08440c912942c850605064502c41001c151400c40d0181840035840b0b448280c1e164001d0a4446503041ea1880080760024404e5490741183c007094000b51070400c031102f0080180020f8800c41e03100c02044403c0e0301e05075003104c1c2e5164801402610240b80262080076008185d00b003d50004600802086243e00200504041809207503d4004003500a007640301149048981480020300320000f4042c000c10718144c00d9025040c0140203090092080001c1080c10744064850b40040d11084002211400d0380640707402c0c00102c5030b04810f10305246a05101891004502943c803044031b05815000b00c1c030b9400349540764018040d40c1c064900c0d41d00180e440070415820980902d41e80000307191380c05030002185407504400800240d421a04010900c00c01a04042d910800c2490b400b4451500e02010881421094080b2450b0024100c0007800311340c0b90600e800728a40810048000c84610a50030040e40da800000103c280324801c542c035141080d4041c06543e0203a9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767213830 1250 767212580 767212613
    0x15090d081602010207080a03090e0408040e0c0d05070c02030c0f06040e09011e0b1e030f06190e06010302100309020a170303040c05030f060612070b07060902030706170c09060403 78
    0xe0501c0d503100d085603014055800a4203030b420080c08126890b4800410117103c0384999016050100c01180621040b40e0840300540058803802059052010344902980d00c0b07808000161032918001c5400b40d4800d00210b2840742d002402410311412070410404080c0e0310041d0150310690403c00010416098452a032064050500004101e1019091203486094102c0706605a17450040d0507106565030313008026a0a10b00300c558603070b0350b140d080842e2406401522000d8944503103070800c2602034030003106181c0108205410300c00b020900020170380d04c82080c0002940720086c1003140c180c02d442035000503007060000b00294002076075601c0700c1201d00119000c000300780c1c000000b0007081c000a8a0002c008040070340c020f100b0255031000441d100d100c003a00182c414078527260010303044102080500c01400c42ca110715680c41c8010b1030407000900c051035049000b802110313000506140500d0480303484030b8a60f00144015510141001c4040e80050803032544640d09000c080040b031043d20051241c0d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767215080 1250 767213830 767213857
    0x71a1807080c15030415050402150d051b0f03220c03030302091c02011d0102100c020304150f050403080a0216090e01060801020c031204051c0203180108010515090d08 73
    0x16616905204071030720302202941443e1020801d02000a052480c50800300752000e000243c01d80381c42c1f0004460560340c0003003244504000c2412101c6c68010b0380014004c00d0050041d0350190075504120495002c0d500c1e604107001e2042c00000d5620701c81910300e01a254000003079040d041c001e0f0380d48603500140b0b50015400a41e010030403020328103065204218403490a50103501c20340196000034000760b08204890794482c0c8800c48154a40d000b0800c020001a484600344006000850000e5594110f8801c0035614400d00c43c8404010f80180d0b000c212000d19070383d0340c600c1c1c9415900c80e01c66a50014100d1000c522035080c0620707a01101103240000b400203058080b400191007a005429103180da0480f900f01c1c2d104015288854070000f003201c6240a5140240311250f4440c2001814a8010700050500103000f5840310845ca6022000700841c8c510407040001c4020460011501044240200c0d81c1151a1a0211030410031240140645400051081c0c0107a2100c0e0380b1030185821542424506 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767216330 1250 767215080 767215093
    0x4090219020610211403030114041107020a03170d020a05071104060b0a030b04110d0e0715020a1502130305071d040f02040507091a0717071a180708 65
    0x40d19414880c0642104161000c4045142420078651241034241c01ca281c070480c41c015548104403580094110104000d01940e441e5a0b580c0c5441c51000da40c00d0105224916010080c4084401c1100360fa034160b4000e414905d080c2e0031941e500a9403050f1140f0071400a006108001d14003995000078142241107560741c035154001441e00000c0060ba580703138580b107103003019000d11440400f03034251440f01c0ba09180c0030403038400c0d40c40800e0041c45c034841502c100101c00604e0103a20030b45a0031070080807000108998400e9541c2c460004104013034280040140c1154200f840424103c43c9440041918120014500584200c480f90300c81c0084e0300c1100c26420183c0200600c0c1c2c41002042c480e802402035100c0309151035500e0000c90103000f03c000348250756a078041550588246980d1001d040300083c03058900406a6085101d504900402c82d448030b020303506000d20140780c2c1e041d1185e03140d22201ca81003015200080c040f843e5002424046901401c000866900d482000b00d00700030040d81c40500742 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767217580 1250 767216330 767216377
    0x161703010306150b1c020a11010509012703090e0a0f0507020d08101217070b010902070c050103060501020a02360103050d0c05030a03090203120c0c030606121e03040902 74
    0x1001e10480d808040302200500044021142015501911500341c0d500180e486131140425145401d007428011917560ac1d040c100300c0c0140c015400740d1407038100301100d84001c000c80c42409801d040f02c2c04000707002407010b1404100949411607940c0c0c00071a20107000c16404001c0101400b2a1401c0b5560340c0143c0c002490701c42040e07001094650071a05030750025054a0400320110a200d403115401032004100348144850809101e003030343c500c1c07580100f00030440e507500c3e1500742c041e400081c419508825000000195580203129020403600c041e00945007250040d000c02c642e6001c103e000d40c40c141409050002c05190b0394014101001d0340980041065055041407440c01a00c0c091000c14000c888810901194002040d0b0340300c500c0b18500441d8107040c910104e400c0013010061103442d0b04022070305502d0b10360042548040f01d442a403c82c0c45079a159000c0200008004c00c0c2945250084614111100e01001000d4885c1c0e100300c1c2200e00e016610101c2400720391000c408428000060540c081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767218830 1250 767217580 767217611
    0x20a030c0e09070f0e030703240c0c020a0e25052502092a0403140607140d09061b0503061801080303151c0602090109060503010b161703010306 63
    0x180784070151045074142c907107148050f00ca07080c40d0341140144130b4004121a840d640c1004240003540d0312804881c3c1c1030b048841003001c0c860340030f80d0f1118101d08210120312203512034085440030a8005001000007454140422103000000e056600f1008008601a00341c01c0c81010840300300c038256840703c0c0c0c1d440d9070b5142c000e000d803c404002502e428040c1100d401603a40c40c00c00680190705000303008007c8210149000c11041e554162b194084004180002404041d004800c90303034211205580b11aa10940d00b2685031701c82c100703000e500540030b0045500311300990b441300c0c507d03e203d518006270310000b10600000059140080f2000036100004205e490b0403c000d4000d103140c0e80d20b003141803c1d4103040d501c6449010003414120190300e0300c00458501e41d9512100040c04603403204160814843d814100040e44c40341004e6408500c0340c160020ba49071140c1c0444e07048850300c06800782803000a925040200040350800d9507540b800c0c0310303150348000f05000214003c41c4a010006052a982100c09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767220080 1250 767218830 767218847
    0x1406040e01060b04060e01020f070b04180e0706030b06090319020f090903030609101d070816020a080901210c0318050616200120041a031504020a030c 66
    0x5031550741099800c0000a000d42d041d142658080e0508107108104c9a00403072a00042d1074071441188514880003411700030800c0100159111100e00034042540a00c548055071002842d45159078001d140c1001003e2195001c045000700041ca098649581c1c98006468106085080c00c3e41c084100d110390110b203802ca40305402210262950049407074500c42003512404000e01190080700e6080000d01d0503503282d86c0c2d250180040c0344500d1018205001001e1040380110f07484000704041d680418410703c40303c0c105580e4000c103580201807952441e030728200e49400800070181444824652160f80a124500190782c0c0110008005602c00600d000202655450403001c5000200d000c013030340220304045480c0e41e0000d078100c1d0348000b044581c40101c5219002c101c200c1841125411000421801908654030b42ea640c40920791116682460001c980e10076071061107120740440d60700c003082c101d00c88090344c0c2c401860308110301c1c0c2d0003d01000c142a80c0c00552010300080d0b50349650f904080c0c000d0300a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767221330 1250 767220080 767220101
    0x20d0b1002190f0f06110a080f061c14060c0c0d0806010509060319180303050c0906120916030c091401050a09020c0a0c06230c0c0d0204090501140604 66
    0x1007086160b02e00254031841c18000010f08400229182d103c20f00208400750354a0640c4500104403840c0b00e070348148015004024400005220380020503c0184044600f50240b44001d103490240f41c0343c81c140d20380c103400648044844c0c2c00c100312103220f10402489000d100d454003c0c0e04980e11240387ca6460f081c40074924042041c0708222052001e5a40e1040c04d5802c044026103c05689480315001e41c00782041c004040801e003800d03c01e40544240d2411130003e1258440d4400f80000e446940c0200410300030307440d106d40c01000601890181c00d42075041c00c2d4020701745509a030100464080300420380788894000b52188890180100301c044800c0c030921001c580c1c00c0e0038400c055410900054000c1d00d0303a04c1062a001c0e008243c0b4025180140b210400c0c950348480e501903200c0d40c0300130141079000215280078180f207080001a1500c42d8080890f0164850500500040f5a02c2030030000b500703504007070580e000399030f8050100c0040c9003481107100819806146c40554030308001080b0990b4024a003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767222580 1250 767221330 767221333
    0x27050d210e150f090103090201050904060f0f06050c06070323040b0f0a050603071403010b040e0a030e010c050c011b061410080a030509060a03020f0720040b011e0210020d0b1002 78
    0x40146420460f0083e600440c009203408505607080380012105402955091980140f500a00040202c2c10040c4e1104031107040f80c00380c4590340e840c40d007a143da02441411400540100000600d050b1217030340a40d10f0454903910b1040100210003070024400d1086404a4101000d2002c0c04015000968610b80c0700711303c0c2c6003d000c246003c0000c41d031149134034800c101c2a506031034414a8035035029003001032841800703041085022082114580e441710043d10030b0b4003052902401120035440f40d103104210716000f60080c4010303255003004541c003000c00c0c5840080040b0350000c0c1d0380042c110b400740b01490801103449040a0400c1b2403400e030349031602c2d8402c0d00d031130340403140941c0000d0b041000d41d08113074000c032401c0d6290000d980c03003600a07109480c058020200700160100401c40b8000e080b000185a1900022040d1180d0341404100c03001c0e004114080380c02c00c40c915031110040280c00b41409102c0c81900c0d2a036000329045426030b00040c400400c02502d40c000003081d424140660000c0400d03910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767223830 1250 767222580 767222587
    0x801090603150906020c031c0e210f0f0f0702010314010828020303070b0f060114030a1a1e0f060708041205070b120727050d210e15 58
    0x40e03032001c5149640061210b62030321034480800b0b006a40d8107442d120b0411005032591f03040e15805000d04c07006481d0102101034075000001d9409440000c3c2800d001c4070440983c22740d1002e000490303900d500b10020600c2d82010400c90402d9900d501c40c040c22016480811f0b00741c44080d58400503050714001200c611060707400340010070821800054a03900061210f84544000304203524102e401851914065010301c0000b075118108028441921300c5200681032703428981d1138010044404041851854241c04000d2000c1804820b0b581d0001452140001a06444003d008040384c4608080701d8411208103c0c040c4020090806144292035294225042c40c40c11900795128100350040c0d00400800ca8170202c01c540130814104070803030150402c0742e20f8580318644040141e070030540803110980000c010710039042694400486091241694400c01990b032403c0005000d105c8a41000503130301d0104150408807981c0c01c0411041d192591035541c40c1d0007601401c140b100300301082241d09038816080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767225080 1250 767223830 767223833
    0xb0c19140d111b030f1c090806010b0a080901140411030c090613110c030408060105120307020108010b0a0c0828020a0302060f0a0e030d05190902060d02160503190801090603 76
    0x22800c3d2400f42160303696000c0007000040440d18044031511001000d20a03000050414482c4000305108804540c1c0c642d540d803911040c0030754a0b10400c0c840c070070101509000000d142801440c0a5074041c820f5400060f50001010900059140580b030a40b15000361061418407030030140003100f2449015140703580c582c00c000003c94900c0407180342000001d6941e500c410085001e9100311003e41d8500e200b241c1c5c0741c0d074950020a484510038461188507941d0100d511007100c002206440382150161a01d4046a20700031000c09a035100c1ea4000c8100120580c140c40000c0f031840c00350030500c0040001001c03c8141c0341c9124030158000c12501c0c10341d8000c0d98035000180c0e0004030241c1c001c081041008151300c4010200c0080c0110710500b00c1c0702d000129512102144540c4030f01c0c81084000300131050140f02c4060307003046600440019410400c1003155070050303c1c0640050190070100f5401251044441e103807142542c1000001c4007800d070a080c0103090183d0300140300380c050030f065402000720f1444e5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767226330 1250 767225080 767225083
    0x30313030807030c0b0708150a030b0a0b0f13061806120305090619020a050616020d05070206040527010803040609030b0702100c02070503250b0c19140d11 68
    0x403440014600340000650408040c03103200d1120420f640a0b010301801c0c24202c030040d000d004101c450080c0f071011307110440d40c2481c0007800da4045030f4003c00034600e07545544a03440050031036200900d4014064540c1107520f038070b0311580050000c50440002610390700304a40204071b034100409a07400d00e07040000c180040083c10200e030128030f0f45811300990341d0072100c0116040d4004d03038510300310006504c440501907640200350545550f1107501640e80d01d41d980b800d403080200e8080b861310010b83c0402e0321401154091030041c245a0700051000c0d09040c0c4e40d80c0014594103070003a691001c02188122041e051010864003805442c860010b0b5041c0b44c101040140110070364440034000503554030101350f400e8002c0c44071003040702e214001804090420080070b5601d500742c0c07003450b01074401d0b07500003d0300710320002c14894403100d40755050100900c0c0c607221000c1900082d07240d040500601070400b007018102202e40c618148680e00414055000e5214641072180c40403258041c07007a801072445d02d6010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767227580 1250 767226330 767226367
    0x130303031d1f060e0c040e0a0c0905010f0e0d080a020f240403110d11122a070f080615011b0219080106120507081b01210203040c140303 60
    0xc0c2c0000000d4685a0360b1074640070308402c2d80b12511503001001485000781c02c940c001c0c8103841c0006220152611040c0d507000850740d0742908a000201c4586c024000c0d03620800703010038515194a010790b9440704500024805014644044a0245000542c0496150140071134181c078425030010b040b05184142c100304103005800012161009480e00103002c040c000c1803082c0d8030b150311501b1200403200d1240007030064070000302c248021340b06014103c0720413009981125803d5866015100e210b195a49901c1c0b80300f01d000d00001c696002e84180480c030400c0003c0740400424084005201c61304200c1581e1840b000c0da000c156042200d4032080304203e0101c00b2a060140c0e0f815a00040c100043c0703a0400517440007500444101d5007014000254007203000c962880c0742d0f0040703041d99261960f41c0d410702d594001c40201c445010b42080340c4141c1560180740d61004014110310700b08840003400003000204da1044600321810985680c0500c486982d114444161120541c0114078042c142c2c40300079172405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767228830 1250 767227580 767227603
    0x10f0504060e01030f090c05040518030d1107080705060f10031119121b0b040501020a0f212d120e0a02040c09090b060703051605010e03130303031d 65
    0x481e1505040b8a912a42c0444100d003104c50041111030010714064106003540d02c40c2ca40300d5402c1a001c5002d41c1004030350082d4011007840118902b003026081030010304005040100035110502c02003000c208400028284a48038402900b12481c01e02610340a0320405004020018008081400002c41d94081c1c004000e0b0112001c3d404030b031f12681c0807c040c21981d084240d40c030b100800c0303030000c00c6202c1e0300d2100030110040c40c1d44015900d810b00340e54280290300c62140103a210001d00004a95107000452610b4001c08041e41d10341c02e840d402034624001708041200003040b0000181c200b124121141000d0000c0100301c00c4c148c02d00c000000c00058030f4286814100d81d5500a10380f10b03040801034020380d564042c20611804000c1f0300d01130710110442c07151003034050418242e0403951814000b16224158142c83c1c45052102d90a0007950178210910105c170355640e140d4140c0c210132030400260000c64030211948214900318034004040c0c50f82c1d14647e4080109901c01c0c420800c001158804c10320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767230080 1250 767228830 767228837
    0x204120b160813060509070f1e1401080f040303182910060f09090c030209120303040f110d0c030605180a050d0503101517061e0f0a08030c0d020c010f050406 69
    0x60b06c2d400200360404040f544076041c0c1400082001400842c002e00341c3c2da070084100d1080c0407803a60b900b43c18280c8040501c1d094002200c00d030010350b0075181103543c01d4020f4060710700000c11054030400c205050382081e006039090100c0d28400c40e446c0b0381040003240006a400b41503501c070300700140c500c04c01504a0040780709105442d14880c0041c1c0c07140403030200502c4030390028082041c01d0500900207522111055015125030344440390086030001c2101c0c082d550001c10300d600d006c16500c401c001000b00090041e40302900342500d902064840d80c1080c06180104000240d5052a50b2076080d071241310407138000325811400784034001c02d60200b1100710140d00c0b07041a603034a54801c138613034104d903150390040717000c091003140d1501c2007950280c0f200c01c0a502e130440c82201d646400e410802072520203004101d000a000416182070300f44240218103640c00640007000082e15495428255041624081c031550701407040c071000701d6810400d442614000b0709220404204940300144144554040c80051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767231330 1250 767230080 767230091
    0x71101030b060d0207260a0918090209310206190306030b07022a090a0f1b0e030601090203010b072006070b041103010213050d05010204120b16081306 66
    0x39500d0b254112500620008400c541d503e601e07150280341282d05805185690b2001401001c611800500b10350580103079440d070394482407070310b1381c1c0040c422200d2205105a03501e4005640050300c07132201280c01344060411a80d000c200140c02d0a4162164181e8004a0101d80641c0000358888804480c8440e019640c400142d5031900400d80180681c0d5000038007550f803142c00c00080b0799011a0403c9401d030742001c0310501b0407110040411145128440e15481088800800c401c0c14a40d80000740b00e0344110001b14031000444003d80c60380e040702002401003080c0e510101d0061805101d04d078090650094210b04650405807010001c2c00351030783c028505000840281030b5141020162104108028a43c581c3d4940f14035213280c0300c480a450407101c60004611070201840c0600940e500740c1b076144005843c1d01d00d003c08022001c141708109542c40d5508000125512000c201c071075644c0c50180d42d5031142814a41080d810301000c06003150b0410482905010356100c1028034001001c0e0801d901040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767232580 1250 767231330 767231351
    0x9090606090d15020c060108030417071a030402030a14030d0f05010311221b030e010e0303070f180306090302070b070206030a1a040507020115120209011505070501020a02061b07110103 81
    0x24440c0d40c0091145d4450300700001800d00c0b0000c024030640f5509203410314181059608103603100306030301510070042d4524180d8408090b1060207981d00034002411100c2817400b03910b4140864800821102d440d802c00240302c004004240941c6e041d000c50a0010021580746072504440e903082c00a0311403044003100a00712841f050380607180302068411138108065034200305070030840d480b1120b410001c0703406c005500f4001d2006101d03884a000d980e1020f035296580348001241c0500360301600e401884144002072032460303d002011400b85101d0340c000140c0d01007070b003000391030315030307141c0c417000402804100c0c540060b100c14090b25007000c40030f60046000314040b031206030a01400d0315040e80182c50502005122581500101450310f00c000602c0d440c0c503115080c002c600c410080011f0f401445d400010858114000349802a200d42c6103056414100195100e90999105560400041c0d000c04184400200300801200215000300150f907d882840d9a542c0807640704034203030303d05042e03440c946d10a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767233830 1250 767232580 767232623
    0x6110a05030307030e070b030114040b06070c1518120c15140a110a0c0e090a02010503040b040507050303210705031608060604050409050303091510030b15060d0209090606090d 77
    0x40103407031001f2010380c903981c460815462403003400284502c22403e03d001015036060440403280c00d00c0d00813200c498034a0402003c000e68808024a250801201c807002c03a0749259540d40380405005c02030f0180144492905000c0104600350b00200d45107000215079080003034101b090403061280e079481445c0c441d06650740270380d1401c40d03035840c0c400309014201c2c650301000201c028003400d0307071071940c541c254540b00ca1035015030320301c030404c1c0c000d000c103500b08042004240040105d5500902c600308542100303489001180c19034001401e01d100381d00d1103408200aa590001c042540980c4518000b42140b80041082140f8105004450306000740000801c185440d02401c480c040c0c6005001404055800d01c1d02558030b6004503469603140c02003060407d160311006001034095031072000501c42032811034842405000c3c0c0581085209480d506030001252280c0c1c0181201d540d181d840140c039014250705200c111800106580c0c411001000b080c4070982d160b0910080840c0c000304c0f06259146512104c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767235080 1250 767233830 767233843
    0xa0807061214090f010f1a04050603030903012a02010903090902180a0b04030c09050103020d121e1d090f0106050c0703050a080a170f0103030f0e10080106110a05030307030e 76
    0x1140070310782200b0410380300030016800303038400024402008000109071205003180e04008040c00b084030135400304002440c141d04032700d4100b02c0003010f41f840c240d1410300103801c40e101d20340c1a00c1a01c07140d04040314140b046011074a452000c90000380f00300412640d004001210f107009543c041380d801f14110300c1c01014260800c440307401c003604c00340020f43c81c1c01c420800b40d00720303100450b0080710642e80804d00200034010941260340c094020300300000c13669990403c030b10f4100c00e21000c000c01c22050814264142000c0040080c080c2c480321305411291803040070b017401d000d030014010304007401031055240d41c0d42c0055044480518000c0d84400003007680c0c5052a000d507002500311310800403007c050156010007401043c18035116807100c0740001b0781c0381c4584001220b00341a501911001003010030700a0310400070381034a901d80703005492ba69030006000310501507100c2001818001c010301110b90048061889160f0480c01031100c0a81a51440d581e4400245040101070b03e4804100f1050f1003003282c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767236330 1250 767235080 767235101
    0x105091302120303060a091406011b0b0a0204030c050924180903130f08030919180f0f0908070f020d020907020d120606020a060506061c0b040b0a08070612 68
    0x44000b845001148140d0707030703001a91032510401500e030001990605602c1030900942901005422a84da01d40056800f410810b0154032085c0b4010500e800099a107681d4a108070345107080180c847d0308504001e4240201d642001d80148049000c1c8030040c121802188400e0001540300f840c4c0c030650b030300810b50880350741e44031a60107145041888042d12010000c0c01c42c20310103a2150f8160380d5a1960700050742094880c01c241a0001c2001062130300345941840c04091840006050540d500d4042c00b1007400d0400c4002000c554604102001036908c1c002c0303025454002c10180008141d030b48524040d4800c00c0380091600b000d01c1c851100719100c4102001000390018005034035403030001d10184d100c0da5000104000035400005075114800d82d445200c0564005500501d601d6030155a40002810003070b14030340d440b010500c0040400940341c021040700d107003c0c103008075040c015903041c0410788501d5009a0301c66850314409200c400360008030b03076041740d10b54941303005202e080d1072414004201241c0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767237580 1250 767236330 767236339
    0x61d030304172b0b0d0213020c0102090d0f020f010203040b1204050c0306040c091b0807050a20010603030212090d030804031407030f0807082e08010603051515090105091302 76
    0x114000d501d040381c1c401c10882100f150501880310041c082294101e02a03500950202035058652029a816806400c4074180000014944071100703000581c0c03130003074001c220b0f041c1082195010071803e02c1c0740030003851602070004505060400c140c000b014082c000d200203252103094001403c1c05010081c505100300c015003a11800e00700790821540c5440c0b1401001041070421500e14000e000e0380400c440d103c1c0256688540326194102c0c11940c41e400804924100610580041e10303038800b91070b039080c007490110000510b6500d50316002e414600c02d11606900c0f42400e02519413a61030341c0100682196061602100566071490260380320151140d140032420340c0414440201904080ca030381091110b034035044416134400b201210035840445201c2c2402803284680c20758080c650110724412154040c0e40721060391504080350071240da5507c25207465026404e140959a60209125081800c03614030400c50004c0e000820034045041c0b00d0315001c0e843c0e01c40020410400c10100f040d4a550051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767238830 1250 767237580 767237617
    0x2063d0603021908010815150307081606210c0c0602030c04170115210b0916061b0209070e09090a1b0e06090402061201080703061d03030417 62
    0x44001c00030b4210442d6044018503c074460741c11540030314103403412070315210000d0a0180d00d070318040030003400190880c603480c1803106417000b06d540c0621061000d03011400052441000504902d4451102c5500c95400c4c04510003980c034400e14002c0110381124420000400c07100c084940807200800300040c00350420b4804024003d00d1940100140200c50500f2640b0f14018114000c4600701d81c6404180510004c0c1c1280406c880c5a000c002e507020451983c0c050091840581c0742d400009600300c840350641d8210303421900d44000d91b10b02400282500f484c040403a042001c1d903807203e440c4074a1000e88900a2200041d2480d031056106080705480074002c0c6103241088040640d503864404412603a1040d41c00b1440c0d900c01d0112598000c80f518945c008070136032110028000790480280c410b90704014108008020f00482240d118000c14941c4002c0605074078600307103032080b61701d1015490031440040301a2600d0080000a0302d420981100c2a500710300400c40311317080303144901111000341c0388030300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767240080 1250 767238830 767238839
    0x100515030d090501031a28090e0a0209090a02010207031103160303030203101e0b0f09030f0a050d03050f01050405070215010b040e012c04060e070e041202063d 70
    0x401010200c0f10300b0317207041c800100780d0b4506200030003402003580d4108940920448442d42084100c4501c80940144007070a02c1c4c0b00c21400086d1041412400350b50703400302d01e00900b18208650101da01c40007031341c040c0c01800600e5000035110300c0780d4800070300401640d0440403466a8140042d0350390500c80506422420754918014001c0d408c116170303030803920036010b20020b940510481a0740781c10b2410686040c0d420b040007d0700c20070342c0020900e040249014040080c0648040041810545040c00101505007851900510300441651482e040604040030b014030131410010007070540703104450100b1716070344200b0202d240c200030240c0c95110001200c00000c107007035000c0090091ba00d03e501400c049030380383c43c000146204041502040402e401944155041a43c03440a030481d1052101052030342c000100c20380f074a8001d41060744416002000e2204201204020810101c1c1e540094a8286045420a8040c807501035600c1855040e0344055000d403200d00d4041c80e82e40304003610f1350f040fa6895 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767241330 1250 767240080 767240087
    0x1101080a11040f170105070504120c0e010e1803090109090b1309061a0111030904020a09120501020a0305061c0209060102160b1e160f140a14010f060305100515030d 72
    0x1380300e14041c90180081d100114001030007420301c18401604d5840c509031810410380481001188107543c00b40c81c0a01c045201039440075902d000f081a60400901c038246000d00030007040040d034800059600c104150541c1e0f90304008100b007181c1d00642e002407004a4800481c07444050a40c1034020b0510341030f035070740820003c1d901854606604251884103a0800710042d5940e9042100c60015a40305114002d494074240c0c000701068040e078905090960355458540f0303640c0c0c00d0710104580c183d40110750008404cae414030030242d01c92011a00c2d0030044241405c2104084140710000e4003c0780d500c000111564001c10124850001620792844901d0317813150005026000350743d044400400310203000c1c00c4c02e500b00d002ea920020203130640b2158a58160744110a482c01c04504980c211441c400c014400802030001400e150300990840c08800c48141e00c80307007110558000d402d2528904001440403500000e12111900804a000501c940380c000385071400d10045a036041d41449400080381202d0350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767242580 1250 767241330 767241359
    0x1119050d050a030914010206190e070b0304060b060301050f0904082a0709090b0f04030c0804080d200c280f030312060b090d17030c091306031101080a1104 68
    0x2d079a49982e55407244004140c2121720040c070340c011390001c80030440e4046400e45110004013461030000308600e0b90003443c4d007015500e60004a1201001c0f04001c1446568014280074400c100ca416146604020004083e00307001000710f40a8042c203c00101040b56810840c2c2e048200d0044030b61801040c0720342c20401c001d03a03102e2035100c1e003c1c048c000980e01210f8010f8034100c40e8003011050050352400000090324900410580070000c10030510000309203800c005002400962014002d090300d0b03000302510360303c2043e2110301030404802c0c120b08040b8000c5022160914100c4111540660700d4459440c80d07448000500720030207034924009a204c80c0d06104c24100d03442900c540145411030110601122107911800310842d008100c10981d03490912004820144211421001026040344010284d00300719800702c0c2012001450310402d203494580186041c00e441818000b41e0700315600c0b900382000b20485c803410b2001d01d00100d2403848490700300c07000e400d10a880007525990340303401d9040d20b00b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767243830 1250 767242580 767242583
    0x20010e060c010204081005101e050406060908010c020f1207060f020a051903090b07081806010e19091e0503041a030a060e040c15140c0c0306010b0301031119050d050a 73
    0x6c80c071000c00e0120f0003e0f0180701e114043d080316003003071a032525410b42d984880b00c40446003a51815a0040350030384d40c510819020306055603c813007100b41040308840c212640d200315a029540302d280304d41500c0e0300008044d190319070509210380d1654030f140f6014000e0302010507170030101e40c004030721240119408400351038142c9800c11814580480001c0a80445070640c0c40a804c1c0210f410000b10382e54018011950403120b0100790032002420b41101600380b01082c0c106861803c0d100050119625203400c04424014110b20304004a9000d556141c0443c41501040480260400d803010180242030094500502c0c91003400048030010b190a80401c0e4012501c8003a2300d4901000404d655042048446c400d644c4512010a901d0500759880c601510084445041103109541120713034444800103030441c03203c0c90000b0100030041c41c0805090035016041b00d00c444505200404c0490004078034030328074074410745210000d440d08007039410008040d5040700340c03c8240c207401c80342041000195660070380d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767245080 1250 767243830 767243833
    0xb03010605041d070506120f04030c0503070f0c0501020d050313113a080a0c0203010e070b0d0609051909051024141005030a1407120b04020720010e060c01020408 71
    0x5d0703e540410401d40581c80d005110b0210800010300e00c50400c810701c540090203810310080344c0d00c2681e03550340385502004c2d08440b0f944d2041441800c1000803407911018100900240189004e60320005055000c001c1082c005a00003000000034040d001010104c00800a04203042c80c107411003000c07014038480c030711107080f050041405a00004020803080c81d11680000e1880c905000d10390200c0e510600c1040980e81035580f00780742a4181b1040204c40000c1034600300d4943c031607500864100071074080e5406600e0080c01c00007007100030044400189a02084900d001070a9200303400e1882c03a203445207001141c00c500d00121000c0d0460f95802c0c1010742030503101c00c250035a0300c808011112110801466030014101c28035660340d00c2c021006980d1002588600107060034142e004a8407d008c01d5138104046080a00c0c0562510b04600030001d24007402d603000d51030001c0d1903880004101a0312004130402e158107200d110302d40e103d03054442e00907000400043d00c4006050416000758414420003005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767246330 1250 767245080 767245093
    0x90f060201020403020f011d120f011508061603060333060302241303031106090712030c03030e0109080405120703080f09060d0e0604060b0303120a0b03010605041d 72
    0x54038814000c0303409407a8041d0413111503840c03030001036a03101c11500c0c006402110905140b80942c0b603250340c8200d203050030700003020000c04548045085411602a0030381c0b003164038600340084040050243d8001c00c4800240034400741c84803044004204503040180f80241d01c2d074a4202800902d01400320115085201c001200c1028488104481301c6120094000701c813401c0b0712800040d5040040304c0b00030202000c500d0091000848101c48445800c200c1c04aa00004907172100c503020407807a40c2c8441404010801c1c1030400480142044414200904001e910070360002051300c04d80205c800702c0303400b00003407000d0b80f1286052544e0b0b8000c1d0061501455903e40302520000d0000b03150000c80f034010b001249170048150343c1e180130380d0200f10061740202c007c002c0e1884411030b03840f60410000000001d002241028078215040c1d03151a409188203600138802580c84070700e01050036400040c6180002401138200c008a070241c101c41c0c7c05203900a284c10180c4c4c807015004680080014440f9080d03406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767247580 1250 767246330 767246339
    0x603051b031c0e0a0b07050709180302030405060f0c15011811090402090303071a0f0109020901210608030706090c0609030528020616050d0f021513060507090f 70
    0x540e01a00c440c16048002e00415002650740240e60742900b0303102c080d1200103d80e4450710000100c2d80001c0302103c203944140020000400188140d1600d070401d00c0a614540110b91002981c9000b0790040701d110380310000c1c40f046003003003080c02c550f0f150790403c050b189015421003014052400c00d20035206199501412031189404500c41c4410000e048903205040c03c03220400e03c4000d40100c403116403d0b02c010494075000c030705a00c00103a4404044040d645407460121403540f641c0006074414a01d9900510480c807540ea00103e86182e00c0800964000c400c0e8001403003140509550f90001150b8040080c0d1300081c80302640112035200d000302101c000ca140e54590840f2501010b210140183d0010f0324a50b111074014401510207140c1c100212107000c0d16900020140d601000c004503540b61f00c60881c0003080710502c0090807041c8641803a035000c0400c000301a44541d082201003031480c074424002074007140d0a01203e1121030b0013410030030040c58003d50150001d40d1601070561302c8a0040b40006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767248830 1250 767247580 767247583
    0x7031e110c0f030a0207030b06031e0604050d030b0a0302090a15080307020301060f060203040314030c0d0306140f012f0a0303060501020f0303010b0f0901020c100302091c2001050d0603051b03 84
    0x80213605180d0080c111907296803100844a400a07001c90751502030803000600d5107090440d140c1083c0d02040150040b4107141c07504502d0325641d0b044150600d828070032003515581d1150800c1c01120b406458400303448d5152403036180100b541800407085415048404240e86070000081d00006100741c3c000c0240c0b54035501100c8000b81180302e6a0010b9004000a06c001f401005801c00102c41d81000c0b6810064000d040c582003c102c05200700c00255525070800c85038160f6110a946000e0a071180041c0301d051a00080c0220b0060940b800b0300c41004000400c800300c1203c03405200c107510760903202c5403000380c80c1c02005051540301d8140140f0414a50802c40703480441107074100c40403854070506d80032000f00780280302e070404401141036004649400e10300703440c1c4101400b0616856500141d4890041f8200070341c0c403a800c2445225190300d00007400001d0708103510544004500a006000c891145004035614405c0302c00e101c482d10705002e40041001400500413050111035000811284230407004d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767250080 1250 767248830 767248837
    0x30121020603070f0507060507020313150c08090a0506180a08060705120a06121b090902010e090a09080c0705031218090709050d081201140907031e110c0f03 69
    0x60752018040012030542c60042807400c5012045080503414070340d890312900201d0380100d480c20056000040d000342540f200c00f0360300000d000280c0d040c410441d980c2400038004234000c01e004291a50000d00d8400c180d0300c0d1314a0300000c1030000c18050f902d6508240c1401c0081c4500354540c06401480008500e030140412040d100714420b540700b40c14a42d0258143d44000e101070101c00140d41c0c0c40d600442c611410b50007a141160007000c9526048000110010702048681c0c008041545046c8a040040c2c1e4000d03810600c1c110210b501524a481c1d00b02140000d01080c03400030300d52400001d040408080100320801210b608034159003090803104012403081c2b2038060311040c0030900414009507031411409183c1c0107221850b08080094440d0042171440b661b892040d14103210100b900301e144e2103940005405043d202c0b03840c0f100100c2c85004205540c030060701481c2071640700d0070316001c0b03d0601203120303079890b411030005d1222a1160080f40d0555114480c039484900403110891034101001085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767251330 1250 767250080 767250083
    0xa0e0a1203021309150803040501080f15041b090f06120f0b0307080d020706081312020c031002091f0212160c060c0201030b0a05240706050403030b0907112817030121 73
    0x55400e00c1d0b40b400f00c5440765110041c003d4014a950401340202074483f44140b454040860342041c008440152010f8011403040d840850074000c00b03c000d100c4594040c400c007a000c2030750700000c5404002600484050200b00030b40e950503100d054000148070b84000f0345130b45c642826400f85c0700c450ba00c0d01400c950441003100c00d9030329043d50400e107000049007494465140040e500c1a40d0460300d554002a04001d40c900d401d0980c076030089504d50b183d15001000c00703601040e40500500d12001c540e0003940320b102409401004540114400210003c480e0240201320360092040c3d45041d102e101c0074207100f462075800e84c0000d14110a4207602e040c00416902540e5000b045009440c8401922131008141c801c180904950240030300743c00221b480c041e05010300d00c40d403008a0565008000d100f000c5400038010390800009002041203010041743c0100040da01d55003000b458018401a60007003070307154800a0854002c8610a03541d01e080078091412380e4002500920340d078084140004100c0002d000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767252580 1250 767251330 767251337
    0xb0a0b01051603030f0507051b030c0c040b032e1404051e0a0c0f090b01020319180302060a110601090b011b0212030f040302090a0e0a1203021309150803040501 70
    0x100b585000340d40a040c200d903512900d0081001c00301094103005540701034442001280000c41c140c840404054034034820480000c0046060039900c03a0083e56404d84480a103020300c3d6112444862610203000d0003045074011320a0440400020a9071004640f041c04641301c4c00385450400b503100d150a403c000e001e180c2000041401c41d0b103108544600781460080d21001d44985003401c8001460054200d008142048542c00003d180000841c25a55180c0c015070441d00100904000c40c1d40744030042210242503c4c005203c0c1100c0e07482c00c06c0d440d5840d04003030352050011900303c07442940006000c54000a080a81d200d99076141b1203c01605e20f200c0f58580842e01032900010303100d88103d8002550303400180054002410b004015085034400030002181001c000340900550820f0001300307410400031001006a050180c14481d203d41d40100000c001b80d0b54800140306c66407113a0190303110402c00180c4011525550b0f8810780052800c1c06411704101240d00c0c0000754044080240e5003103800684 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767253830 1250 767252580 767252587
    0x803070815100c020130020c0c0109030818010201180803160905150c01090804030b2a0306130b091305120a0e0112111206120d0f11071d01030b0a0b0105 67
    0x50054a4103080004506031b10b8100307403800102602c3c0f900710724403d07903044100145e4664150745c000381071402601d4087d050080c06002080010002000c070307050b41105034861440506003400407805080c0c024801725044d03046d9240302043c042840c0c000c6000b10075288504070705292000c029102520f503885801d6000b4446900f2644c68024400101108408174000050281e83d82d540e001c400d8100d07410584c1c51800700c1c001c000c007003ca84507040004490000781016880303e6035107207803c6440b0003810a03001740b03183c65008140c04900d80004600c8440242841c1691500303620500d82e9400c0c2420940e00e0348a9500e02110000c0d00300229141c2d29100d58034100300001000042d140e4204441008140980c0c2d2944c00c81030310b04c020f000e0081c400f04c1d0480d0464a042c8001048400322543e03500d401c0310b400401c00d140e00d454002040030440c513124286074a01d5000c411032542804081d50080c5a41044038044140901d00200700354142c80c450149a00a9100d140711041140c45081c019408100c040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767255080 1250 767253830 767253833
    0x2010e030d1a030a080703081323101a0f150403020108041e1a0a0c0c030e0105160b0703180b0118110d050a1d120306030102070803070815100c 63
    0x190002e044180c040c245070948010300e007011900d084002007081d40d040502190f1101010703481207003190851726a101061103100241c4842c0e144000c03891800d030740700c42940b0810405881c00c2c0722200003074005c0c500c20481d041000b101e050000c296841c0d003900c1046407030021402480d049240c560302c1540307144e206040074210340c010343c0c194801078400d440c0c040794100040d008002c40c200c90301304644a404400302c0c0c01c44050302c0742c11000005e0300300c406507030070303e180701803619803051030952104d0f0940740641c5449a001c006032f507144070740042c4402c140c031003040040034081c4049140340110250b0b41c04001001c6007251940002c01c04c15002402003031028010000c1c0c7c2120020300c0d05c40704120724009450401400354000c00d030700c075045243d001030b04d45082000c0b484003803080d80c4010482a170319a124000c5020255181c400c6480304100c003101c00300c081070294074254103135500d413039110404642e241805c41c0c000d0014007040300c0c10000d80181d0300f81c17034005090603c03541d0034408080e1900c80104025 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767256330 1250 767255080 767255107
    0xa05030c09030118060f0b010504084201030c050d020618010e04050a0b13150b07061803230a05030c0304020d0c0f030c2102010f0c0803011d0702010e03 67
    0x1d01c00381e030564941c07102c1024030101e4100c04001c5440345000040401c00000349000384c40d45454598140001400304105107180428008141038041d4490494a54001138840c22000350515550185d88155084045410100040c5040e00d010350044a03406503a0010042d5802075008002d40000e000e0100495403105203600c14480750050501e01408100c51020800311042128201341258a40643c482039080c110f003090b8000407034100500c0301220a4088245001c11813040c1c4040791000181902800b049500150b03082c202d0035503114149071039007401000c00c5450440801d59042d41e80a0600000c2400d0860f00b0f45143c0380c5800e420341d65803078101540c0340c000030810381e00710010103980030010b06070b0003291001d00b0030030a80c031411030708604010001448a170802803404c85040f40c0040c51020038140c10342000d60918084201000c50141214084c4041900516076140403001080c03100556480c0652007280011851090303035040c400720f0a81d2452030003181240c00801607107003684003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767257580 1250 767256330 767256337
    0x106170a080a030f0207060204051c02010e010f020309060d050f0c090a0506030a0f0908030109141b0a2a02151c0518060a09020f0a0e1303031103070f03060603020a05030c 75
    0x300b50030001000352450081c001680c0c4591011030b95903a0011782441107140c6070340041014610035482c20303610b00743e690010b0100b0b0604070205060152001c12001114401c10807184400400740440780c4501c0c1c2001146c0c00b818080d242d445d051540b0b100002c5000f000142a81c10613076004115920140c039000030b0003500d90001e05503100503912642042812003542c001c0034001031050401c10741d03d6141200c03000c100c400d254410307020003100d10144103070200101c001d003940c004481f5241da501c1d4400d000c03d0703074100d8402401c00500034010801820764a030551161032828000d450b10403244c5400c41c10fa0455204055849421240c222100241300940c0d03030189034070400640b202e242280000c5021450150304a0329a88141c2d2130350085011424401c0c1000420341c01617410b42449800c00da11400d41d0a40201648002009454000140351084c0c00c2080010208a0003540c0ea00704500014001c0490380c410001107410644002400c0f8843d10894000a150341d81d1030f0304540342c0101e00c1c40c0311b50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767258830 1250 767257580 767257597
    0xb0a02091203071407050d050c2b141221090f0f0a0c09110a0c051c05030402030105010614180d1a1602060403080f090a0c170106170a08 60
    0xd00e2407100384a2418104000c2200a02410300c0c80181001450483e1a0038407035003000d03000c2d0300240d80c2c1e031001444c0007600600c84603044884001d183d42c07001070f11020600d80740c0350f091220704402107001070102000781ca4141d601319a050350500c030728141e141d541a2281c1e00c81c1c070340140105105941e540c0e4a0700142c6410089102c26561584c05d1914203e103401d25044180800d030304820074001c03c00100054a074020070711344400388040d408002c1141090300a003030606041c404130501440030860144030801d01148200e820b26080f030801400245582c0088400328025882d040002c01e201d40504c8000071102032203280585004440503480601c1c2101c615907541000c0000d80f1000090182101c0c0c50f2030000e544440f541c80d1410100508240c45484400401d54003c1c60600000c80e51101d149a80201c8404070b0b01c4d40c1d510380310212840c01500301e00152031a09444804035880724058880c020400002e0000c1c4005900d803e6000155000c00482d0b0240e9480303070740440b00040700347c4094035000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767260080 1250 767258830 767258839
    0x907080907030606270b0d030f05070204020f040504050f06030606060c12040b070c0b0c1911040c0503060102070f150c140613020109142107170a0b0c070b0a0209 71
    0xb039403030f901e0b0000d0f50403d42005c001c03507281c41c1481d0000314120800010b5000707503400030310868018001040d41000300702d0b00941000300ca800c4000341180103808176030b15158007610441d50340c02a4400440242c205000c1d282c4958148008030f00c44074082901b5601520000740a0002a19030308100001c3d6840b00b4081200f44c00b98120030880000e04c080648010044000c030341c5da884a00d40f6107030320748a0198208903102c0b41d050019502204001030b0f4440d05600d8400e1303c4c03030400b000703040c02d01d05200d68000e41581306040040700185d07a54000c01450054000b80c003111034450f240d40d603124500349140600847c0c00e13041c41e040440613214046c0012020701a412008a010320b100015042c58004c40780180700c0c0107014600400c40d40d00810a000a0010040c511000111480041da850304000c1100701c074002d04800070a4605018800c41d00203150b92802503c1440300040030507180e058840040c1c0340e4001c0000011006119142181c4001d84c1c040100c00c1c56580d05402040290011416190031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767261330 1250 767260080 767260093
    0x8060f0406030b0103020907140415030905060a0c0e0f060706050a02090d050c0a090605010815120a0303050a1a030a0803040317040312110f1219151503020909070809 73
    0x880d1203a10400020714090705103800f5941c114018054002e40142c4441d0407c1880051882c100590b00165403d807a01038001d519515041401100078246090f07002d4643c1c0602000c0c0200815991b201444260440d100c0c10112400e02003040450100300240d5a0022020040d04c1c00140540c0d2116500c000c04040c010305004209000c40c20012042c141204c10f44c1c0540103080151409010f548001d01030300c00b0074084542084002006018003600e0705c002546039980c036007096601c0410700d11004200780304a91490007242401805414151108041140360203815200c0c0300c03a404080c8901d12001d001405c03035900f65510f44000707a20040c070a4080058040c1454070342a150303032000d0b000b140030750f035810a0716040352440f00455020b04070300380e00c1220400052145545002c10341e000d85000301e52009607580c805012500e4108e012200c0868286030188112480c000c1c021003405450980b0400741c0042840703c070a4040784502c1c10030f580d0181c80000001d280c02e00c94503144c2e070b0040403202907031301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767262580 1250 767261330 767261359
    0x3021b07030c0602060f0402011b0203101a01110309060f0f040b041202011d0913170a02031308010c0806040b03031614011808030c0a050705070602060a0c03050411010806 75
    0x40c8106a041101d034258220350810010340d0400c0580d400c0380c003080012140c0d0600e980040d10441406c241c40704d96154100b081c4040d598140400d001580203504288030700074000000c2ca204038040c0490a01140015004034200d000000603210340780400b4003101e00d400750440024000f40c016600d84207841c41c0410000c550901c000014000421a00380000143c0034144009041803402c015030740d140b079140407141e181558600f0141a04403481c001000d4144146003070446080c071450823038401032080010340354480d560000c02024099080e000403079886460340440f50036182c50500030400145840040340c1d0a15055202c100e0701800141100d28201030480d0100044449a0064078114a42c01c00417680c1d040a002d00c86104c2c48820440b8506011591402024000a00040115003000c41c65a140ca405401202c1c251a0001d08071080250f50300300080d902d41044824020301414010400001806405403501a13540082007102c100c5020700112100d4800070245544100008458032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767263830 1250 767262580 767262583
    0x20f0a3311030403120c0807051305030a140f1f15030f0c0f06051608070507050613140d0521040518041205030c030a09050709060b0901110111040603021b 68
    0x2403119030070380da660703100e180600f406040900c0e105610041c00d401d218200040c1580002c01e00c0e405103003070130407549400e4205003180801d04681c00480d0140309030001102403000390801450802c900401b04e40c6e0070401181c49646070020558014444c01ca0b119041b07a0125040d0007a01c2029401006100000d82d652201c5840114280050700e400301e140c00140040b5410303080340301c003416081c18030901e40942c400444152103030500d8050120400440d4a2040107400c1c08568010b2200514140d00c0e00700ca1941c06d640400315115500c401014600d8100050070090b098501003a0002c02078100500d1580e4400240c1804144102e6048810040426036a441c0e0300031403084517a0048414040c80c00749000c5501940c1c100c41d400500000b4403c1261ba40300c03c2d4100ca07842140a10040b403810b0a515141c2d14000c4d69030071030354026041c44408031f402070724140940b42144c07090341c03030b0300c005601201c5850888014080c048464181000240b10b5140680c008000c40c4044600c2c0180e000c4042103030343d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767265080 1250 767263830 767263841
    0x111201060e1f050c0d080114010507020303040b030103050f012301030212100e0d1d09011e030503070b04291f0b07060c1d0901031101030902040516020f0a33 69
    0x2c0041031011400104012080103840d0400802c0d003418401541001300c3d41d010341050942541c10481b0016050003152001e109480061203011641903c07943c49203041c640f222881506a0610340c604418504511070114041e441c00d940c420035200e0310707402d5409002d590301101030b01c0a0a4401c0c840000d030708001a00c02c00d80a403000101074035400702070003001044070401062507a0040c51251008850b40c0c2c5d01440c1c1750440e2030380300035034080f000780c002d4043c4060941e50000d0964000410001d080c001d600204d5403007175204000700048900e0745448c041200c41e44110303d0b401a803840b00080c41c0c00c000280022078401810b003c0400d0507940f100030001d5503103c110704840c1c4907202e15614200d2a041440e805c07a00d42c90000c50140d4a21010110314901d05c148405030000205140c891400e174026030095064a40140050003203260440300a0a081e010f5950900148601d0700207941458001c107114401c1d44d40000a00201d00050081c0d028016818140840280d05101c2c1d10842030100c0c0b090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767266187 1107 767265080 767265139
    0x2d070b040b0a110d090509060103090f030e0d0206030a0e0c0109060e060703090e040501052d011214060901050108010506060906090103050a0b0a090609111201060e 72
    0x48400e00e210910f041c0d42c90140c05504043d203607009810b00c0680b0300645601d404c503200c1034011002c944a949010701503611600c241170000c2d00c40e0940d02c44102c002403403800200350f83e0700021550b50050300c4107072040341c0c2c650540052880174004040d5160007401c0c10342c41585070a0014110100640c4118401c2000185200400d80606900b4002d00300c1003507110355503e007501d0000d00030041036501c1082c0307101c01c42030f040071400403076580c8900031102c1032079144503440c00030080031200003000c0440d504801000d1200500c0700410541e80703d10590000491194500f0140c607084074030140c6141d010303140c100005a0f00d9140c60045034140c8000780307400145039407070f00050801803040c008890707171209020034005203011841e084071058a09920042015240b9900440c0d540e00c01d0f150f00c0515840001c004015031400b4003007281d07240f0006004102801001001415035401d481c3c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 767086330 767266187 := by
  have h0 := BRFrame.cov_init 767086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767086330 ≤ n) (h2 : n < 767266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
