-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:12:31.921065+00:00
-- url     : https://prove2.me/submissions/253669fa-ac05-4e4f-a54b-88885affd6b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232194244 ≤ n < 232374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232195494 1250 232194244 232194251
    0x509010b031306021e0304020a05090106120c0201021308030d0b0f0a0302090603010209041b0e010309080a0804060f020a0203040504050a062904080a0b09010c030507050f0a090902120415 82
    0x406603140400300d03684940c2c0c8074445202404585045401390140150054601002181d04184104e4280145100e2802141c1d00d185843c0e450060100c5090700b801118000760840a03c61084152600b200743e010060344001807802c4180b0a40400d40c60171900b00a03000d4100086001204280780201c442c856011220301300400c8002d4006040c5401507c0028050510f0400080d50381e03401794141c4003005800b0300103010207402c05074011905264140580c0c0411104241d00419500c00e2103003049a503800300d4554502007455400343d50206000b00200c1d00c25464009211f03c120351800948250001a0005c0d91501d0070107042000380c2d0700041401c1812803502800b0081000c0c482418032050365030980d40a0000e00b42da0303101c466071107540c0094039a48560a924010001c0014038544281c40b050000c010052a000f0102c06880b019910b007400250107202020b04120044014141a40b032401c110a1540ea2140c038842a80c02c498014021081c1c2d0308100b009000076480107100d00c80c4042c4040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232196744 1250 232195494 232195499
    0x180b01050406121103090304210209011a0705100b040c170a05071701031112010b03122215030b0a030305070f02040b04020721020706050d09081e0c0106050901 70
    0x8100e40101e200b003200300141c1c81d07140b01008046910000c44d5082080501d80d0740e282c5020510b50300d5001c5d12030400188410101500440481d240351703940c00b540204035660380c0e40b074140c814030008500580881d00407000c10081001400030040c1042c000c461101c0492820f6007003041200b25170340c00c0011418071100c0b0030f000c042d80c1c018071314183d40102c1280d0001450380300c00104540c0c00100c1c0c4a030b824600040c42c0044180021880c03180c1d19000101c803494822003202c509103080e541c40c80841600f65006c882d10001400041010b000b0b00b1030007941f0100b090101d607441d0010034405500541e103586644409070441a8140100c1c04654415541c0862140c139580d8010310903c0359100c003a02c01e42c0c03494055011561640c00c4100c00110040042d900c0390702c94241034421900f501d2281000b480d40320f0291645600100703000040340c03c5501c0d01403d0034940da1040c4064018008112109002000031100b8031450803c60303400000e508500715100e60180410a085a1040d0000ca101d4480359004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232197994 1250 232196744 232196747
    0x70809150c1e0c0a0e090a05070902030105031209100e03010b06120405070f08060117010207170904200d09080409060308040905010f18021b071202090c03010830070804180b01 77
    0x144013225041035500005540c6e40206a0604401c80c00c014414041c585d00001c0d6007c468000d10b05846007181544d5009003442c040c0e00c000e1040e00000d0750880484550035680070301880101c5000c00b0064000701c4c216030801c0004500d540011000e0101d00420400d00c410310030100001c80c0a4100035801e0503100e4100300480b561b540b014400d24a480a16803504000e10301c0a40549a1003a0700c0504411340c144c2029070000c040e000060030718080c0d464011000509041c03038021052035050980c04074070f03102410404c180940040030040c0d40c1820304002c000340d03030324591040c0002180215501030712103003401e0700340045e1003042e0f11150909500300f4090003802c080e5581e1542e4185020401aa600046000302d1042c060707000307400106018400c00000e010314040b4048003014401c40342c0710700340d070348000010300280000c0c010718900d40c0c007961007440001482616084c09501c002d442d503211038080c24400302240c0c00514102d0780448040340070000707902500d0003000c0322042ca41c414084081710303000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232199244 1250 232197994 232198009
    0x1403090106180c02060f04080c0706050901030b0406030206090f0105121302100305091e0a0b010906080f0609190212010c0e0a140f010f030212040c1712070809150c1e0c 74
    0x880d1b507042070480402c04020541c01242c10201c0d0800030389101540c0d4100180a98000001840c0400d0038142103ca151500340700b0702d0f0989070f00801440c1000c80700c80900103013a10010001c0d06015003000317080c4480061504561040c42c1890f0100038a03442441480804600c3d510014103140c100ba060186a00c40803c0c1e5000110b151091b1121a0301381d039142e24640702c990017024202c610600000300b0090304070341021095a4020301143d0034807007041406503a4003401ca801c0900c681001c080c885900140d10003440100b03000401034031158000c10400d50841e042007402c00c1c08242c3c0c0c02142e2103d41441030f1024000c0c5000d850018003c82d6510109140c1509003401c10304104084601c00c05a50099040e02e8a00000e24640201c5141c2858540000c110310700680300c1403520040003101c10040000d1190843c0c5a0000050030800d4607aa0340d150342d00412007141e84540440c50034042c020400e000b07003c80c10100d50080c13186006202412180841d00d050862160b0040c0304074608540ba03948 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232200494 1250 232199244 232199251
    0x30f0402010503060402090405070207030512131a07080409090308010f03031e030f0612150510030311070e0f10081b010e03070e0c0703020c010c030903020904031403090106180c0206 80
    0x20201e50f039543d4500028000c2c400c0400c400e038051b207000248009076170300140344000d07680719504442c22811507142000c900e0003410140e071084d000030070042c4040c0c2180c1602991044060030300074104405075503840c1d080d0b002600042001c65070303508010709050b482815180100403042e18410304904544000f04495075900072042154200c0d185051024466030000c3e4201c1e654000401c0103c0e01e5550160003a00c0c41d04082d540c0520f9030b00302c404580c046201d0305000d900c842c40001078048c503540d0252005c10341d4002c005890b026500340051a40581c0c41028451500400701d04050b140c0b10b4221056a0b803650803520701c543c80840c0c85002c0c0c0c145544440c03058135090030002c51080515000914010240d0007002248010806024070304a90360050644948a40c0944032380d041900d0044810103080c041c0540080c00441040002d410040c0906400c24000d144c00822b00d080302c1e40c4c2c5041c0d5401541e80344142d80d90b0342c80402c4210020b155045500c0302002c020711012038691402035a95101a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232201744 1250 232200494 232200497
    0x6031f0f06080f10180f0f020a170c04030501050127060303021911150c0d1704080307020f0105100632031009090302062d01090e0f10060911030f040201 67
    0x880c041903080301c03152039190040000c0c040c103174242280c504807a40508101452220502c2c10041d0103452a5514001e80340040d41a550b10300c192080c0e011284843c120240500040784020031005c40826401e000f007e000c2c024100da00303240380d141c0c404650103039a6140521400c05103402400c0c40029404152050711420148800303101c1222800c14054035459440180da20640803120703662250401d001410140300780b58103444081c02c01e040b0560f625a480c481c4044001415000500002c58003005580c0040f40e034411685200441d914103802c442c070940f000ca0000e00094400c1251540c4403002d80c4204640c60b03032a54455090001071400c0d110702e1604801c5280012000480880200390020010165130900340424405814041c0d11441c09841c0c01940b1456500092541201030211040c0f0002c100780750b0541c4d030300c2c3c40c242900505c201e9541c600c035130140d4a405000c1400410401081e0a603038040011601d00d4039034504219003502003416420f480230710810203080c80402406d40e02540a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232202994 1250 232201744 232201771
    0x91710050a020c0f01090320060a1107020d1a0106050a0804020f031f0f060f141003060b0c0615030606061206030c1201020c0f03030c090409050c06031f0f0608 70
    0x240e00000303029000305645044607205070300c0b013103d12600541082e017800303001c0c0d142d221802d04c80c02c41c030528003a02076421510b141c0c48800459002e011960040403819588940c85062264903400900480102402602c1b0f03401200c110111441050100714018010b0b030030040d14044ca0b512000d090f1a01c0148080d03c00c1070440c5030400b0341d450a09c400540e00070440340d400e45c1030218140c90801070034140d980440f1070b450100e0100c0c00b40c07000400c240c00c0c1c80200c402d1031802c40040c01080300d00302c2101602e000301a180c520001d15000e40c000506018a42013020703004034a40508850b02180c00f84030a54482d50050b0180b04240e12040102c8030201001e50070b02c1c40da550340ca004245400c0c17104503078603000449003080d07811000c01035020b801200100b400744c3e070381e94945400b5a075483c00149c410084158007004041481c0c43d05501c007c055034851015681542244030002d070113600100c030250140e024940c001d0406d02031194001c0050b110030840712070154100100140092030041102d410f8079074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232204244 1250 232202994 232203001
    0x1209060f0804140601260a0b0109020d09140a030305130f02060d0219050702010f03090c050f0a0b03131205040303091809151b091508071e080709171005 67
    0x204110031402c00e0403c0890f135180d6501c0c5c0a07140c40340b4203d05200d43e600d441c0c0b100c4138003040c008148030700c00e2508028014070507428588060f001303510001036810819514415480000c5a0040040300784844002500c4c403a2040d08008c1d003507401c001c0091102c60050401c2c000002c0f0700e502c4500260750141c0300581c41d06180851400248114600106400841c8501c0d00748103034800028403e42e80300307aa40021034000000c050b4152015110010866008100180581e082941c3c0400754484020201c0e0a95a40c411001c12035074002e17159002c880954103100018080442080566200646040e80c507107440c1d605c1c01402c400080c06485c18003103c01142140c1200c440d000400d0898005070407450152070380f88950300030040105100752000060b40c03040545405101c4800840d40c500081400000200c1d60855400b20000c04004c18410b0464060321561034030091401141190b0704c1d6038800d401d051a01400487d002c0d8050782910144800c5c0540800300031a9240d070700c0610840c0032030b443c0c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232205494 1250 232204244 232204253
    0x506040f0c08010912301a06130510020f0613020d05100e0c0301060b0d0506011403010305030304020f120c010f050903030f030f060d020604031226041209060f0804 72
    0x18055803000d2025803c02084d00140b00202c0c9045802c0049901c1d13030003000d40d10503010401c9012022460210420114980c101d400c1c05810105200303018421040411004000140b00c2da00300111002880405203418132560130121104950461270f40000c1c034079a18445006955524002c09628501a02e019400115150000d00345c80465204040d58403803100300700d440307004102c1c0c4040c40c225481828029426810b040c418181612003c20200d0b14000b12401d0320400303490050f0580b0304007c4030703095000302503802d000070314041c600c180d01465680c10300780100703c118074680b4200c0d80310741c016044001e403c100002d52001810801e0030080003c00342c01106886034020381040d2505800300017240ca1090b12860700942c860304880214209031b40b100c0c42404050510000e009420603010030090020941c01d00c4c0d07600800384249081034204040c6850116031000098001610302d40c107605103c03c020b11400320200314200e528208040c54907142004240c407c00f44034540c00d02960901060610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232206744 1250 232205494 232205513
    0x3050702240d0f0c020a0b2e03051203151309140705011103070f170f120a0b011d100203250c0b04060801090513020315060a0b04030506040f 62
    0x203100d4840d4103240705421840d5001540c403010040b00c81038600205159000c129101d2135644101c0341c0e000f40b01100d0306a581d80c0f1031b0000074000d09403a1610400c290000524100110030300c0c100030385001ca01034503618200b460501202d18041226405004108005030386c0111800c0030101110304100035001c1004800c010407146c44090b1480308000070010081c01c00281070300841d1400c1e070314901d01e206801111030302d901500100a00c04120003440c0030100307a20b9006c04030104000d0000a24000c03202c502d0008923400041d0014418003501c0c10404001001d00c110004a0001e003061200a4160400c100f102c171046a0300900c51461801800031161080003592580c030b030941400c4801a0030103284003000244031038101c80d14088858081141c0303030b0f00020303101111040e0711a5056039082c0000701c0098200201400340c0b0030380f0403034102d0241c2d9040203000307107442c14500c03480c2030b606004040c010086075a4100300c1902c41c003000100b000800005040d54007a400240031441b080c0b1518140d0b804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232207994 1250 232206744 232206769
    0xc090c0a1101111e1207050310181a060a0f050d0b12030405040b01020a21120507030b0f03010606090504050705190201020c010b0d050619020c07090203011d010503060403050702 78
    0x15842d0807000007000c9040d000516200b254134008000a0007400d400307007518491025a1a400000240820142c5d03010303101a58000589840b621a03050300e51031012a0507804030010b144c2ca0342c55881035040301c91140f11031001c003035007564403605d481c803084005003101c04003418413810001c000900c81c04044560744550207808004114543e806240322565507250044d014003441b5500c2e001010784998000074080f100d4030390009050210f0203040c15000300024004464105101c481941880d801380e061050780e204880d130b45c800062407543c8400307100c0341003040750000e40660700d44202400700303a03000304e400300442c1c00499002c81d25903156101202d80d03000b40704030b40c0ea108242c58041400680c041d0060120400244000c003c103107056010000000300e58000503000b90459004240c5070010090064140317000d440015140450000b42c042c40c02d40140d0020315104e42c00702c014400e01d0b140c1404040c0f83c0188100b0299036504142c000b03034a50401400040c04e1040c00280c040440d00c0d0320201649 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232209244 1250 232207994 232208027
    0x60d06170a0b100321140c07080c0a1208090607020904080c010c11030d0b0a030c12030219150f0b190305060a0203040809060a09050612040201170103051b01051b0309120c090c0a 78
    0x1142c5030b001410303aa4404190289c100240102c0c2100c02090500403405421140d492581408110480e03e403181e459104441d00ba8000e90104038900168640e1580c090055101d440500d55801545040360300b115800400d100c200301c0c0c00d0b02c8444458000005596002d42c405d81d000501c4e4880d080000e0300c00e1600d910041003101d0420340050807100007404070a4540c069000d50320019941d80c9000c070560424039004001d240000c1140c8407140b510361041102000038840000c0c8982c0420015200d80c0101da1740919100f0741e94014010004140b00352500282118419030443c00d243d40c90801d1801424025400741da004540155010310549040d001400d01a110a41d80c1800049504031200100d0f070607408100e5807400450610390054260341221781182c0a410010581d00c400560003482c165814108001404480d80040c1381c0340c0707802c0c2d00322000001159502203841c18081003d442e00250540c50f00050701d84465a11110801e50340302c0100b00000d135945400354820754001105000d10f95 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232210494 1250 232209244 232209247
    0x90103032001020c0307110d21110a020603011208130603052202010906030f0f150503010b010f1407020414150a14010c02060d06170a0b10032114 64
    0x10905420144403909004004480a8104000410340d403c0c0e00c1130320324052050340300f004203602107210301c008143e50b0b89006000700203c082c2600e80405080680254404000c10350b089119104d130002d803001c1640700603070041c140d100c0071600021070340d0005218018417841c4203400b5070f080241c01030031030f008401c1d1102c0c0e90b0491611608020300401e03040701c00428103038050f5400b410304410078a0071400650305a5450544030f00b020000c401134840703818031860480c3c540000d90111307511400b82082725205800340d6040e43d480c0c02d00305402e490030b25252030b051007003c012158207e1b5003c1d14611074040d11041c00c50ba600700d24800700d0700404424086054842203141032200808504048040f0442d00720f400200780742c0c0318484082e0186c00028101d0111368601c00c3c210040c1040006044540c92040d000602a83d0329004140c0403d0810010785064100c08081410081d20542e0141c0046038085148111800c40d030b5174036511600090201c03602e021440500180c3da20030700c8001852003461040c079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232211744 1250 232210494 232210499
    0x203010905030c161d04030e0f03030408010213050411120603031303030e130c0e330307090812090f030a050d021f1a010c060b06030103030503090c0109080c0613050901 74
    0x1510762280c2c0146205840b4644d0703000400c207912000c0011181c41140d482603117500c5c1c0d950251141e03a40e480445800c030801e846050702c6030b40d00b0b201400003404442c002580c1c0d10490b0011040440658100c1d610a600d40f0308102c04000c04c16042d00d040c0c4200d205245050b480729000645140100b408050214140b410080708055106112440340e42054a0b01046401ca4402d00000e03a001c58292800080a881e14100240340c01c001c0c42d4030100c8160500c0092007140310030101492690a800506043d000042c0003407103500400c60001404107034007070300c600e0b803501890007450300c01c0d880e00034460401e50300048a40c4d0b4041c407119610701e80c41000c41d081003092100194907811890100584072074810188072450f08a4068a01c14000d94490420003103402801959510f410103c00c1da4410703a00c0383c2c03200e0580c0741d04000b103004c0c0d0300070b03101c40362a4138080541d01e24010354400c101c0c1c100801a0020009004000b0304102190411104941c03103009080701c0036000e1555900007a070007030102000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232212994 1250 232211744 232211767
    0x501090501030c2903010b180f0616230d0206010b07020603130201051c0f1d0d2006090705100203210604090206070807030305070908070e18010c030b0109050f090f04020301090503 79
    0x4190810b10800c802300700200d0042006201c8210340702c07440c0c1142007000110220032120700c15010b954465950911605031440281031121001000c07050709600c101c0c0c1c4426241d804104c018018040d8040007850803030207901144113130101070103c203909445100004110780c0a8416103810036030800d6445a1298240d13400c9000e481c80c070403600f20651510003241403880d10304000d65803400d40c2100a09204840d0305040f1102d01d135800a210311086d0003200644103640a0025501910200b03006042440c1840204901d01641000130001d5500c10440c04422948a4184000d140c14840f001c2c030381c42c0d03942004100078084414000358004000114102001003540151080300d000f5901008266240d40c002d1701e10000500440784964802c0c042004034081c0d01a03c964081c09a52503041c000200303400043c03e481034411014082a00c8000551180d6400391309070700180801c44114142404ce2030208942c0e41000c2c0041600391900130000302951002d400c15140f103075006007142c0d40d1b40f480a50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232214244 1250 232212994 232212997
    0x403020418120509030304170c0603040501140c040e1305120409020d0e060c03040605040f06050f060103141b0d020c030a090f0602070b1804060302030f01020406030501090501030c2903010b 83
    0x82200c0381e40c050380b01c040300d0b07038802c40650700c030650003800031840d01e41040040e040b40b20364101840c82e00c0c8205003000d011512807c01640c0a00c1c819400400c1c201441082c2050403040148804c540c240305000c00c00c000310004164a4010940140004d101681420001e0901564680d41000c0d80c3d0001400100290580d00908400090300400c12010404a4030161151415240d940c0b5078001070000c50045040340d44840d41191049081d000d03100c0c2a6500d040c2520310403110380c00990b1041d0108156541c1600481c001d0301e000310132400e242e19100c100c4207200303290402d042e402c0c0480840c1c11516040b09034101d03202d079601242200d4503440003c0c0000c00c00c80c264000c02c451b15451200003d0110300010b0b08105441519843c18180310981c4045040241c040c83c10960098a400340040582c40a000d185441d8581200269a450501e90054190750042e4025001d0303903c2d1a0040000ca44050100e90031b80e0800c540750040364860502c02c03038201800755500314180b18004000118000d1980 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232215494 1250 232214244 232214291
    0x1050709080601051c030f030f0f02040603050609061c0501020403080f0703110102031005010c08070b0f0711120307080916080d08090a0309050f01140d020903190c090f0204030204 79
    0x1120b141e6a00c41e001c0c032054035802d615084658a0b01c1d081040001d0203411114480c010343d01c2c001503044020890002592141f422084c149580054180003c9601d402030342d03405401030321000980c2c2050300215403c00440c5403200030340a0700e5208c000400c10290102d5000315044190039803910102c1c0d01d00e04103a840b80700c1c11808104008200329800c40c060080e00c0c1300389007034602555001d00e010015102408074070b804517480481044200c0000703010a6250b401810785c1031118855240200c0003604038240607400011a600010004403107890960132a540904645414050f9442c0e01070f1162600300240e5010402e5003c086001c5410440000c0e101e80f607490b17079136800800d81c0b1500b0515840d104002409000207021010600260902d400252818841031500c40c00c004401c19100c512500f04160080317246800040301c45407480d0803c40182c482072614500038144000da41c51201034103007446007000241c0c40c0c00c0e10050f03050349030381510025600036100b0321004501c00c0c0682c0f9040c4009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232216744 1250 232215494 232215509
    0x30a060207050c280605130503060f0a061211041505031c0f0306150309080405130209090601020114130f020909060a0507020309010e0103201308120901090302011d0301050709 77
    0x1150290164000d031300740c40c0700c072207002c940d06000d0929600725800d134441402c0f10040c0c1d480020000e0103440030408203201d200034210740304180c18000303454402d54401e54000b45001d924081400701107501580b2081802200712000102e40d00380b480c042c050020142e201590500405a10344200da098501074507400c03016640d50020b10300b018006400321541e5015060310519110302c808001c41c040e50014200c01e0140c03001d00c1c14965114009000d104c40b800418403255008200d00d0302d9410038181440e0040c8007400281f14030f4410481c400b80c4c900303005180506007402480c40005001400390b500314295006050b858140c0303421124280c1c0c420054a00c40a0b00780740000040801e840072041e01c5414105030340b030302d8083c1c80d00401140031b40728504540d00c404080382c02a41071100701b04024030260410140300c43e0b603075103003890720360500c600c540394081840c01c00c014488442e0b034801441015281c0c2420000b003011030b2000c40e01c08108420203060741641ca001d092007003240c0c000d5480d2080b101003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232217994 1250 232216744 232216759
    0x13060e0f06091633030e100b03030307080a091205030712060602070510021204060c05101802100516030206010906050a0509180307050307030806010f0c021e030a060207050c 76
    0x2d20855540d128241880d03600307402050034042c40130915941c28805052803190541880403401d2a103480b006102c40d20802c0803c0d40c400402e02241002d100440c61214074180401c40c4525031808603440c1d1000070110410081801c0001302c3c1b50134140d0002403c030303400a854400212008002500c0ea80c0103403040c00204075124012103101076140260015900c0c26406407405600c2c00b0140201c40000010000c154000c4081442818650002601c02400306036100ca414100c5400c00f40c1c20b188145c540e10401ea41850031600149001a880307100f00d80d4103541c0d0582c5c41d903d01c903048806004031800b401032464ac150b480e1080c950b00041d00d90581d001c84008204d241d41c0d990800c08080320a00c600c5410824000004a403103840030083d5944071461001d407441c10784a555601d041d075003d01c0e801c6000c90f401105205041d42d0009410b110582182071455103403ca90b0001502a62140b205040707001d011801e40c040342d00e007030100c400341540c05442035445605a00e4159150402c0f098024010a00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232219244 1250 232217994 232218001
    0x6041101120b030a02210f0a23060c0703050d0f0b0f0d1709030a0212010c0318081801050409140405060c0a090608060607020d03030e010e010e1513060e0f06 69
    0x1caa21503a481100018010301c3c40401d10703400d020304642d40b5040c480703020a00d140000305900040c4401032000c282c10001d071240b00420b01c0c0411200070962080d0221000e40500c110020100250003500400c0380c2d110b49131110120b2508840601c1411075903044641010400b00d07200803a40c020310000c2204036122501c40d0f10031010b000c1c0040c01441c000d005002145031118031646202d008100459001e0140c5403040015004520010341560340c041b19603540e0b4101e410301035418410030000d165007042c070710201011619460707868090454100325503001c941880186078020812140240100b040038061030440c400d40b8100450100c40c1581c06000d51b0f00002c00c2e030064181100d1030340303415882d010703241402d18030308440e10f450080100e46c002000304106000342c4d81c2e44003c001034a11a5501003a1804200c150383d0135501c44404030810f5038104000392007076031408a103500f0403030f4004048400c295190b01800100c0c5010303030303800b61034207107091b4000103404001b041116400398110101d813038070348 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232220494 1250 232219244 232219277
    0x212040203010e0309010c02010c020d050a050d110109081902010b030f0a06060506120f040804080105040605150108280603020402040f0608250c0206090a0618050405190b1206041101 80
    0x11a6107585c0c0c0c0010158402d00c001036004406000c415800600441c42480c40c0e9986c01e49001703454081500c032a401038038582011984455044484002e08000b4095161113035104802c5015241540d83c103140a4241c0002c070314402d520500b04c0038001000c6541e4440d002c2c0d14261110000001590b101d81000400714150811808850444d41d4a1369a08010b03510035102c0440181c2c083d10499001d40708203c0068005000d01a803800340d40202c00005003802e201007c039014a01e103031440ca05101c40e40c0300304072008400c507d07402c0c05a00440788004e00781d8801c0003144024403036034200942c01480450f01142d440d100010f04001d4581c15110b0410540300e001e02550083d000d121301c1c140d003140302c00003162240d1094400e65a56032028007010304203803880d0300081051007250440070020318021298640d551051141c2c4009041c261000c00c6107044c443c01d2142030345c08000701100340c1600c8040c507500a484110303002c40c074042101c0030786d5405c0c10300307181484968008900846c00144004030401014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232221744 1250 232220494 232220497
    0xb18010f06180b18040813090b0907081308040e040c0e010b0702040c0c02120c01030615080f18060109020c070609051f090b13030512030103021018090212040203010e03 74
    0x70b6111025002e0100c100d070009601424100803015040000303aa5550303000b03000c0450145c0941d05c620724464446290b850b0352104c0350300542c05800054140500c0e5245070b02c40c00042c941000036480c18400c04d50f18002001c81c10b04c10198000c0c0625000600050965400c400302801075100380040d5980303550700e4411403030001082c061501c03074400412101e00140390a502450b4802081c3c1041005003074542c000402c0c82500b114100711a820060b0700350720960b418800d48016186020a4032105150903400804454009111101810510000c24010343e2400c240e5101146e00404980d0a584c41e0565207000e900180d05a039407520400c6404912507016000d00410303241c01501e0f070484440003044401d03410030503e03884000e0242c2c52101155121a40c00200803046500c030806400c1c92071072805034030348598804405007090042c0300500044c1e551a640707180c0d0014500c2e00c0d110b80309420004040b01906a4000302e4070343c2c40080c00d8072008952041c4644aa402280200b00880007481940c0d141d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232222994 1250 232221744 232221749
    0x507050d03031b080606041710020406050c060f01060c0213200a1b17030a090816050601050402040f180b1003060302010225060c0c05040e01061e06020a020f04090b18010f06 76
    0x40c418401888104510784c120380d6540841c2003150442000c2c41d000b003042f82d00503000300c40003c1c1e000a60b00c0751003c0400100790000881c0703d003201e26600d0300100034040f168004c0c000b40b18900c409550310401440303800000500c1012a0085100102022003100d950702540030040403801c120035141600d10006003091302c160f00440b442624581440505010358402005000303281e68517000240401d01c4c1c1c601070969441d8003488620000322606000380b0f41001680036510a5004110078030400086030100da00310b4121041c0c02208010030325640c800361040206058014108050349242e59a05400a80849000380c082d1516080e44004d5251101a0b00e00c0c13207502a0682c500420040740701d500ba40340010b006102d688880c0e51941c001074281c0c0c020030304500c450380d110b660502040d03951190980c2d4482010703d030000024500f25005c1d444d4041380d14013910804041a40d0100350712035030000c9058661040c0c64016030310f0074000300420402100484a01da628061030340e4a24215407080405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232224244 1250 232222994 232222999
    0x210c0b04050a1d0a0c1b080409060b090f090603031b060a0b0118270f0204080f0f0a02011d0607060603051e0a0f0f0c230a05090a090507050d03031b0806 67
    0x50540e91300079401c0250914580740c50410008100d801c0d01c40c1c01c0402d851380024426108282c0c2c039460601e4900070f07262140c02c031b01c4000c00b00304100c01c09035031a6030300040130341819507030000e85507603000010b402c40c040c2441d4107040d58882c4528081004001c02c000e031260f00460b00800c681079500004440700003001c100c0f840605618042030003508441c10b21102c136542000c03010b101c541944101e000540f501041800b05017900428140030704102400070b815442a000c0050960800c1e21070003540c0c41d084040064140700b210001c0e0056420107034544850940060450340c0d4544030340ca0200c00030320040c44141c0e01400303056003080120717070a50401180480c107107004156550081d00c400080c00200c01049030602c1d1880c0410001078001284080101105800c113a121040a11949250305480c058144913542c804000d200c00e584541c0d600c1d401c00b000e00000540280c0740d00e41940b4110341c54009d194060741c0e520100c0c0c02c0542c103402c18403082012100d5896581c02141094032040400d452896 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232225494 1250 232224244 232224299
    0x50a06051e0a090c050301050901080d270f17150603070e0a091218050402070803010902090d02031002090109080d02031c14041a070216210c0b04050a 66
    0xa000c0d040480a038219100028034101a543d600c10b0500c0c112292030b804480030480220042105240c01c180701c900411611010380486001030390300405101102c403030210003070700060300720b01250101c10748a0302500b42040d00b04003103a116800b00c1006c00c1e80e60249002c1d4440c0c0c0000251511070b54800030300922001e40141341007410104660322500d40200366016081c0c4e03445402c0c010541c0700e1030040c118050740d1150345a20440680c000802c0c00e0326000325010b24010440407000442400449044030700701c202c0161580c0c51400041c0e020504440b020b94503105070900c048801c1d07450750061141103800d8a91403141ca036a41c0c50319444540c144c60032000b40e003082c414601244055401080882d003064400a4049006000401d800c0000d0b5004e868000481d03580b480400205890903801000c1070000304100c00c12803070b807080540c03021701441100c403c140310a4942e0621304407031a9219944031044400c0c040d107500c0e80151940007803049910404142c000000e04480c50441c0c10086006202501d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232226744 1250 232225494 232225519
    0x512030c0c06072d1b0b16021216050309040609060927060203071202030103030905090c0702030604020f0d081b07050618010c1112010b040b04060b1603110604030201090501050a0605 80
    0x30030741391080103a000188200b10326908903c1c01c01a08241c1d20038856006c8007018100040daa00b10789260200e40001d550103014081310390032a000c20f5407001c89031030764071001d20b422a01c0c006056018025100303410600304500400e00e071445420000503a10074040400102c00c3c40410115282088188103034403a40c1d522018010503940c0d0000d50303000342d2500740500031200c20310322001246e000742d0080c0d0000d1020308084c09145001d0150641181c1c01036102c03400c002d000d400180d21070102510081c8905280340d140000c1d41c44040f14003240da0307086600230780c4500e1480b15a03100840800c11101e41406056404034552900100780c8115050034043c20b81a039160030011759001c020018251040d102d80210403e40b552140b0402103280040302c0041501e00c1e50f101031005813040740022620403414103500340900b5400d14182c0c0d024544000c414484034900d0308050f103031603001d062819003d008034000c10003415015007004a82d144a040200241e55540c02c10703600300d4402d40103c03680704510107842c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232227994 1250 232226744 232226807
    0x307021509040b100e0a06091d04050f070303021c08070503070e030102040e010914280902040b0301050106080103030f020d081303030e190b0105040b0f06070512030c0c0607 76
    0x7a2109141c080c200180b040d02c05000a040c20030b004070102c1c00070f04104228242400d01550080050105041ca10151400c28098021702c0f20800254480d400701c00c0c0020f014050b04000007900b6003250401d84901c00c0d00d9040080d203034012049090010110092140d45d000d01c242c08403403040003030365521070541d100c03000110303201c2d01490107582d4159000e100c0815105442002c41c3d00070040c101c00042c1d420180303058031180d00b1004000215100713040000880341d42c7c1c42040c01c03022a41e10180016019140c0c40090700070404111150f803d0b6181a00218003280c00021040c103807802070301c41d0503174080e90b5101203a946125220000000f03011030081400000008541420240310f402c0110303100c0007450740c0506e800409540211145180e940520902c040004442d024140c10b503800d101c10b80508020030500c00040314001d00484001a050051100c203115036070080c0c40d4000007903645d06120f403c810141d00502600301160040c0c4010034202c40c05007102c02901c9503200f00c010a6044600308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232229244 1250 232227994 232227997
    0x606030f1305030c120306040c09050114070c09060f03050f07030302150601020f0d020c010e0415030215040902041202040f1406010305150d05010621080f1c09060f0b010203070215 79
    0x80c200c03000e1200b80040240c2000611501c0384a50044105c0c548a103030040410041e940c1032461030041c020040024002030364000482031f03400b0202060340c3d603079007005d2910030030014065208000b103a01e840d0000c80d041811200850441e80103004450040740c035924110346500c5039120040140e40101a005407030305801542c05c0d0b20023014015102d945607001106414182c080b80c050b00103030030070740301028950b80020a003100317408c0c01da03010450704084810010b0000c20a02011744a1654582001e03070f1845514201ca025003407141c029915560b840d0746002512898040481c400c0c4c4c107291144080ea90540305030311201d02201b0542c2c555489041c01500203103070103044641030001e2040c0031410b0351110030300c480000f07200b031000080c3c2c60f1801c0801103481d100c0c4603094089008070400440400c031014265440080700d021841d036980b03402d0380c0003150840f46a140c4030145040142000c20700103140d06ca8000903100060520240f0148001243c0303e201d482c0000703511064005105081610120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232230494 1250 232229244 232229281
    0x92108010f0608130b04111002010e072105030c010504031d0d140c0d030c050d0504050a090b041401060e1e0d03050c0a1a04050c0405010605040504050601140f0703080606030f 77
    0x2604102460100c2d04d0b156420174080390241d84040c04054019640d04140d9000e55070802c10344000c0111074400302c5d2068440003584110700450558611100403c0c1909410006032680720040f00e0780c0d421410181c41c00703400200c234160045480441025104d065541c4040b038035030002406020f21950301d0303541280d04407000081910610400481d103166486a1140031422402910f60340318060301072030020720f040010083c1c80e04010040c44100300740d44400030802c05441103403c01080c0e8a2110000c41d00418400980540082503100001500c0c1d40046e11250f01d0101503600b481c1c42e541d07114164603d5008051901d42041c2082840700110384600050491010020191140f01c24070343c070f07068840c2c00b98078003030482c14003680c051100700a003c12042040d00c5054400b0b2000d50314007107010349940210f10515018640350400a48035a10035040000c00c500380c0c2a10603114000460012130380e030070410303044011582d00780124100b850050b051300c0c0310300c05952002040f662807864060141603400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232231744 1250 232230494 232230511
    0x9010c0f0503030108150a06030507031514070509040e0606030316080904020f090a0909020d06090503160507050109052b050709020a030f060608040209041b0504092108010f0608 78
    0x1034681400286040c0000d40c0241741110061280d51409000e405042c035000d009020001d19006082002500204031101100d0300942c640200c20850410704015006110b1080c020010000810040640000103808042400d440070002c0c00c810300300003a40e039142a00c81c60340c141c1c014022004c240340006e0450041920031405c6e40d0820190384040340c01d9800128907880b01c10230104070000d0605040d80710000500c4031080620030b1080b140c010802d401251003001e84015103e515503403d00904004072440e080040203d000c0d000e0b0300b800c0c000e0300c5034000d007d0a070000d001e208000070340e850701d03941042851070700140303880000c94402068140d40c0c415080407117035070040040000f4500c0c0f0500c0a00b051a08645000c0398100d10030405c03100f120607a8110409120708402407101585504040e183e01503803090004190454020003507040315007980c440c1e9801400d10b0743e440c003000451700c1802e40c44080b442840103828080041503545081c24055100030074003004040050602c00d80d000c1d6040240c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232232994 1250 232231744 232231763
    0x3120e03160b010303080c030705030705072310050a02040501080a0902150403030302070510020a170a0e070915080708030f071104020f03060a0501110706030902030c030601080f0613030509010c 85
    0x12807503240845050564031000608010001c2c0f6800c07400c90340e402031140c42c2d100d1071481c0c13540000c0d18602002d8a00c2040001c0402c681c010850a0403003140800358034140701c002c0488100d4000e98941d000c0b40700303130500c5080101140c2201c03094001d680550314161510702c100d6454500d80001060940d00a981c0300c10320140015070018038034000c02c0a140a07982c0580d40e100b4904001e031802c04024036482001c3e03c108a441126036219985052800d6104070360f80454036405072a80281019400d0001d15005d82600029441c0265102c4100e22044e03c0c48400150354a01149481e0310261040f12105c0d04101b11010180450034014804180715011200c2c9122200c0049400ca805c070058116070044004203019462500d090401d00401e02483c01500c0044604200da440d001c0d50b2142c030b17081c15100d891300c008540d418040855000c2010381210b00a41c1c0d5101542d945100b072401403c4a80103000124409200c1a600c0440d01d5030180c9946282000359401118190004071082d50b43c03511 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232234244 1250 232232994 232233007
    0xa0317070618050c0307180b0f0301020a170105090f1b0408070f140312040b0d0603050105040303060608010b0313030809030d151e0f05120a060213180903120e03 71
    0x216219491602c003804800000740c540a103445450310340d90111940c4241e00103e001c001030944810700f81c401c40d02c1404081084810300c00407481041c400c00c201e0b6810b5001159141d26161300101038001540240a011426640ca20a01196010035124401ca42411200140090070103030b00c0c1001c01d0801c0c48505242070360311541c0d1800c0c0300386038015a501080b801c40402602d08910540e580b03010003100a807088900c6000c412140d0311440c81601066000400d650246c040c981d80b0000066400800900083c070b841c1c94018020500c84c0208400725409034004642d1800c80e80549105d0090256003143c104020f86081e64911001800b1340103d100800045030141030740c0c02010380149001e0f01d40c0c20524201280740c07d9400601c0c01c03e0302c81c4c9800c030b801000b004100c0800b040840e078090321800300b544c500408043c2042e41050000d44017600000d40340d1000070b4084000e0003219032120790a525034014003486010342c0c00d0542c01900081410001c4001c2c14026070100303400c504003c0c01c0780e1501c407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232235494 1250 232234244 232234253
    0x40c080a0510060e0f1501031103130218090a0204090f020d0507090c0e0a0b03130c0e150d02010806011103090d06050a0b01030e061b0708042408060a031707 69
    0x5001a0031a11030b00a00061103002c0414015040940003030401c010203490b2080c1c11080c4808020329441c21114201081c0781c55034040e60248000c000083e00da155a4a068030088000c011822801ca018404d4407610760f059468175109a402140755002506140d06d141d002c00000d48402c0f0030560b60361056074200d40050f91030710100441148114040c001080c42c00007458111210030082c0400d110f01100840c1060344c0d42400305d03068407840300c400358507500da08030320b09140d6500900c024100e200445001c111803030400c4800307124200d41c00ca2784200c6050141405901218400000d002c2062000440c40e69030003950b10385194000c0d40e08507030400e114107000a50300c820f20001a140a99280d09010b940840c0b8011a0700c005000c0c00c0502507000d00d42442552840c0040c114202421140c0440300d00d11244002c540c6801e8200d2852519641c0f144114140c0c240f00020b1280c06603680b403000c50341e0a019440d81c0c0d01c180802880b00b41d603146142c0b20900040481c0740d1400307003a503080183d00c0016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232236744 1250 232235494 232235503
    0x609270603031101050a05010501050403081e070f060606140702102106030212030a2a0f0b060310060e190207060c080403020d021c2006010b2a060f040c08 68
    0x7580241d07a41829455203107101421070390040d000801c0315081000500443c2d030418200c0c0c003240da001c03403460b5a0b100807100007420b8001800c01c411a49100090710403d0102080300028a01c0c003444e070400581e503560303030140c0e4cd00f1601c843d60560305405000c101c2c050716043c1142202a80907080003c03049654580454a1480c039440e800d102e543d840a040c020b50a00c07501e8410107203814401035151182c100c40c0904a500c1840d031a114001c85000642d0014002c000085c6040764401035440c810007551901e04028441100d10340e00038455074520382c07000c0c10a8000c200c2110709040403100c1a4490300564800041010201075019408001420008d603591050a00301c03460f03559040000d007010301e0001e00b0001042c82220442d403044004504483c2442d40308403014220303003031406200304a80d0412451560303c6401003071038002d9400004010b50464002d051400341249142c01404085d4050301c00802c170380800d4030940d40110001000903804d501d10715001405000312500407541c030104075140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232237994 1250 232236744 232236749
    0x904020702040f0f11090310050403020f1204090f1b0e0a03020d140106060809070909230619020a02071401270501080609091902010923150406092706 66
    0x500f84e9030b1484c05401403840c03140c2c24145900342450b5180c4035010300000da485003030103030001d12143d0382d00100301094003c00c200407001000d1825680314a03502d0603400d2140e0000e00c5a42d100d6800c060305020f406c942c071721075110000101d4011280b034000f000001c480c0e103485440c0701da820200c0b5100c0440541d41e8003000c40d400b01c1c03246110004511185040d03d0030354503d580700340d0900041100f4070181c6040400e081d0161040540c000491490600f00303040395201144460102c1d9000400a109000c408a0300c05d10605005601501e22001008401c049100d0913400c5001600180d5080c0601c2000c02801e60903d0014034046031032911a5868035030784001c0c46102da02024110313600300322550300043d00c0f0364004800c58041109103400380d0243e1f01d8056410041d020b03840c5501c1623604584c00307401e207180035102c1c104001c1d00c0c841880ca0b13103600c4c4000e010f40462140c01c2d082c0388011441e90744d8084070203958403580c4000e145844c048065001c1c41684100c03a0002d05880000e880c02101c1e445000c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232239244 1250 232237994 232238021
    0x50601023706150b1201090f060b0f0306100801052d03011d15040807080d09210e030303101211030d080402090906150118030f11181b090402070204 65
    0x311140e003a0554043d40da0075511410032802c092255065600d2410031060445214082c08601e420071502c840c1d00420f510341104006a10100361103144555060203903214040584550390381d11f8280c00c0c140d40c1c1310400d216295000940380c2e4010700c18450301c3c40075404020790000d403a04aa810310002402d4840f032541044071402c5900015002040c200000d44689003400d09218250504e0b440301c1100340720382c1a014241207000240c039401d0320300c19486148040c0d0030428020f00141c0f0710038166000395121944000152145040750824a00441180d0050b0071918000c20b0792860402507261000714980103035140d00c002001d098040d1000d20044812199907a64001c09180078410020740d014060074070790840d8001020072004a49031201140c6207402402c2004402881e40325111a503809500010070142d440030300c800070464180d0513028040340880d90000d81c50104407641c00d40440440b1039081c0c01400c4841c1908104151000703020b00342c1d001c1c2c000351410b4200d40100e0250f81d0092031045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232240494 1250 232239244 232239251
    0xa0212160507060e0307350708070801180f0c030507150801150f27080a05010b090417030a140702070311010309050325050a0501090b0109050601023706 67
    0x80801000b4050340300506031034100700b50071450001c0802c1d42d64100b070041c00c080d4403030914050a40c540e000180c0c1c90300d01b90341d0074002803c0007071511252030790410701c034417002c620844802188015041c000c500d0710240c0340e07a10403460113643d2101d840e95020884240c80c412070000f80400414070030301008000e010341d1154202d41039245040107020070300590203d4910918005100c0b10240d0203c90718031152410b2a220101152404001d16020204020707006420b0070b110002a003500d011491a49040c0124005c10294030744c032041c4120000200e50003400c2004e1210900c19000c102c00245402c60030300180040d1104c03030000da000c3d1450301603828102503449514100308000280e900c1408030242880d007400110b00d01e0356001d03624001c800188070081c000074001c4001d280c03890b294001454010303007100c03440c0f001418100d008212000d4283c42151004c8004604c80c801e80c01341728000d0406034000c00900d41e4540741203088541d41156a20520782d0959103a4442c02115082c049540c005c01e00007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232241744 1250 232240494 232240537
    0xe030604110118080a150f0c030608010f0b0d0f1505071d0a0f050625150506030c09040809030114070f030e0f06070c1e0305030604051003080f0a0212 66
    0x907100301500c602204540e404080c0c144034603080420f0b201c174240c2c0e0068590140c0c0c428000303000b000d0403101c40c00c284030724a0000f007221081d0703140c0c02120844407103100801540281a00701000d40e200c0860054110b119201d00000250841e40402800707401180b042301c1e600d0b044001e40d0117440d416604e000020348210304500c402a1a4010200d80010858205140501c5d00c661118007842c4c51003040e11950000c00e045017070018000d80c0c1e0661009900e0300c25118005e52400451110000740c070f10701c6440c0b901d0006005130400191207202813200130480314640c0c0d1103594080c040d900085155415540b40e41e6050300303030700c1d500f0003050149580341c55030049014508401404c48007019045805584100c055410b408404a19941c004880c0c0c600a4983d82d60790500214004080c0414040652082814000e240d400030146008050480b0140481d81701d0f0450382e030703907148070f404080c1c0124400c00c24101c900b6440b000800b030b41c10940c0141c40c420403494002c010240c1040702c4403003d02a841006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232242994 1250 232241744 232241747
    0x7030b0a0b1008040203061605070204230a09020607080906070b010e071214060d23031c020901020705091008100b0f03150105040f02250b06180402040c0e0306041101 73
    0x20b07030000910307603c1c0200c0c0c03030300d480e0f00020381d03810000c2c0c0710203d032105001c200901248903070112401141c004e00140b0001d04a00b803110402400c070201c8a001ca010540456454442405000e014070b030000d1000341040190b8030303050410750010310b806500040420121000800c078064090003400c0d819142c209074502204003918a01103518031815551400d403310b0006110340c01d5254100405584511031200545406140e03001445d2040c940000d4004581503418000070080180c440b03542181220f144d03902c603c0d582a401b41d03100031409a004007006101030f0a01582c86039200d0914241845240c0c2e450402c90b0424007044900c045050310380d803103c000d5003000d00b5142807142080e4010185400002021206000180906446240c81d8114140f1500864042e202d04c02d1840249440564541610819034003280c1d0044030308554079800035101d0324004528006ca050701e20a4080fa542ea1a420400249030100255003480700e419030800040d1000c1148901c03943c401c4440d1060100103100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232244244 1250 232242994 232243009
    0x304030e0406050409112103071103030f03010e011406071a0403120f0b0f0f06030f0c071e0b090316020f0a21060f0506010f081e090d0306050f180907030b0a0b 70
    0x8140f003108904c91520395107c3c000304451003c1d070008800c80c1c0d4400ba4200203401d520034206180302c1000040008a15001c01080e014121140c2e001c2c2c04142c0c0c00a2801c1c07082500500501030070b0a03100c40e68101c1070300250031405600074481d25001e881c000149418030304450b90600202003541e030720009001c0c0e80c180030400b51829030b0104c5049042512a038001032280c4070041180440140c0070003c5194050002c0964091651105100600032070055021802da840c00509481150345500858003401b004000c45004501400602c0501c50302ca0b02482411052950901d801203a003803400102070854071180c2203002c0d4101c0f00f83c44c41c01c25500b00300b8140c03048110208003e6150106000d0141c1c0c00909440d503640d1642028441580c40b0072200400024603243c5040c400c0e120410000040340c04500280184010348041221a0311401444802600310040c4c0e80c100f400c8440010544034000c1805e81d00c4240d85040360361458503a910400c00c240207a4110040c1d6071110364801c901d290941 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232245494 1250 232244244 232244269
    0x7050f040605030d12060819030f091a07081c1b05160201031112042405041e0c08030712030b0405074401030303051305030304030e040605040911 64
    0x210144907407030034840081e8039210307040301c104103116507000301c100040110b80103d00240100002e8400c0c0f070107c1c40340d0009400641004400140070200d5101485014850140c10f5504030241000800e2503089044c00a62100764141d80380c070b0050003010000c00001c04c9895101c0c107003610206000c42188143c0d4060545910034905001d4140100040110030f400d42c105069024038011603140420380c0c1c1c42c1443c1c451000400c001151050400c0180400c4e840c2e1f22512088d02c401281407600c4110858040b1103003643c0c0140030940c041000b2480c0050844d104504a000f805981b02c040c1d9500c50662856001e41c00446118918150700210b1980500c965911071105035802c0c0043e00d45000300901010701c1008204081083d10740310140000b0300c00402080440c2403520b500301c059003889092a410007480214006030030039000032100c2500d1481200c045d0b030b004009505640351682c068642500410130541c02640d40d8600042d0b07591130f1300030101a6406007e1080b070791b41885060026000080c1f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232246744 1250 232245494 232245499
    0x120108010e061605120703320105040c0801030f030905030f071e0501020d030c05040801090b160903030c0809010309020d2603240402040518091506060307030e0703060c0207050f 78
    0x180b9100d844144c02408441034407204820110b41540d03002016070040091a5440b450b1000c4c240441002592107180c0d00c19070351140e00303034000b0340e81c0e40c20800083d25900d80e0800005009000104001b92019101030082440b07400e10105281d00e690100746080000d4510700c405c3e03131004004011007082c070b44911400d0405940c5158003070341448c0003c1d50307440c0c051071100b00309542c900d0078038240c40c07040090700e0203041044001d00046165040610896005888900c82c264100d951268100c2c060309071032049a50585030707018440503645502c44103406c142c010034145600c0700c0d481c40043e07461180003032015100314400c0c9040e80d40090126000c1c807001948030031800c001c100384051605005030720b4981c0031200c64484106078031000428040d0065034455504030b2003808001c0b1301c10504500003449540500101c954500765100038100692064030480e400c51000c1010036500c1e8426042030082c204180200c0e81442d2fa60b80e80c220480c0c031920041d10050b041900103000c68030b800548035000d80c008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232247994 1250 232246744 232246771
    0x1d0402180f1b07020f010503041b060c05070e1b070c090204150e1210110903100c0215060105040e06030307051203060109050a0e0c03071b06020307080a0e0d050c03120108010e06 78
    0x1540d01003001c0d170b0360110341c043c144400417002404009000b10701004000440c803034000c6850355040d0140003a003039000e08070340900500b00080f031425042c1d00224800c0d088065000301c1501c40d142115469031202400f620450b2140c00041a000310f90300041c0010000d05900b07080062805000904022861002c0c1e0701c528000100800311100c00203058200300024040018000400b540f0182c80340b140c00411501805243e80080741e1110381c5e4865903860704240c0a9400c1c0030f0f14180c03035120848013101d405012880600c014060034180b09ca9165000d00054100c07440c2030002d880c2c0030300e00720300452030950f800c07000020400a96405440d40004082c2510405003841c1040e40300a8103010080206400c208080000741d40c00b48982c0092264100301c0d58130102d1540c050810102075032007210b030720003c110914046100140c0a105a200e00382c1800041c0914050403c81244c3c2c82e0302c02c030040080b80c80180b00201084a10018482c0240701c4000001121030100740d0341410050f005101d0003217100e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232249244 1250 232247994 232248007
    0x303120e010510090203070309021f0207170d051c0f050411100804260d0c08060909031603091a03100803091c0201050f0705030a02060a061d0402180f1b 67
    0x400c0000c64196984000c4c090307125962a10103c00420b100d55000c2d504c0481140c0049603101402c0c101d40104103d6800c0c1d560b0952a80446000c614007900300c1e41e02e0390302500782640c03514410703406854082d240558a02026000800042c01d94a51401050045642d4414442004501d100580c0304410664440c1c1000710300e03c038003528020005002402d400001c0403a0901e156501601a401c009450351183d11400f180039800c1c01040d403040161b0100d0260000300310540f5142d4251849074070000002d40c0740c00c1041c0861003100ca0b19180071410712100a602040318004035503140002c0078449030181c1c50f0b00c0d01c0b8415080e040255403159550b0b07002080441f040361500d03040d403c4004030368140008001058401259144902d4400200005c4040380d80020408088014030348491181e00311000c544a941e10b11040b12414400d2880140c0d203282d00b01d40c022100607131542e015000800c000443d042c0d40095201d000c82c21905500400079403c10083c641200c002c05800d800038012150707003801c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232250494 1250 232249244 232249261
    0x70314100b010801060e061c090803100501090b0403060c110105070e090a0605011b0f05030d060e0601080603030a1b0611030618060f011b0f110a0b1e031305010203010303120e0105 79
    0x1806d80e09a8080c1d4800900002d0500341d0fa0312004402030a1002007000016a0419480d203800665441110040c1c807003000506610800d002c00903034240c412802e1826213540e07151030040005c18101018004a801d0080750600b00388985442502d55485c4c02d04540d951380100601d07908010160310b5814134080302840300c0e0368030510184070302d0010b0246c054014140d0400340d8030754240c0a0018510721001881c0803104c009900548126121014404400e0700c480f801901d2221044030416090b43c01030041d90348461150043c4410f024080c652007058901c25254042642c410301c0d4500300d068000000d2205909284580b070040000c4588050401d04000c0002400260082c50b0713581045000040009100e6522102450b915840100c0a200740e0051600014500c0e210381000e01c1003009440000c1c4111000e4202e0340d00000f0f0303048010320030066400c4040e0607007001d4801c50300303c1e0011409000040c824030040d40654040c0e03d5420326110800850001d0307908a90524400da41000c05004030007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232251744 1250 232250494 232250507
    0x90c09120616050c070305060403090f050105070b04060f0b0904121103031003200d050109031d03060123030a080d0b0d0b04060f020c010c030204090506010c0b0c0c070314100b01080106 81
    0x11400f8645169103404d0440745905e4520035030400340050080301d040c4410190094845c07412a09019001c102155680006407518080d00c2c030080d001029401c00280007481a9000c0e40c0203030b42c608000100e80080101084082e42e08940480d44a060141003c034010b4120522100b94004400158514641010545102e03c5940f100a00c461084c0f00d042d00c2c4840f241200e0703000890054105c801d40f02c450f0511078013071712445406401280c0814080307800c000300c60020802d812000360003000527910b8103070f00c140166140c00c800501095000014121b41d0740601c140b01000c2c0c051603491b034803410600f8a0780101c0c0c0c050b0070490b20074250b080780030300040c014240203a40a900302e0000908411141b407040044c2c4140324020829520742506d140f04580c042d8040c2c4103541420f4400c01c06565000015103445034400800b614141d207150003c0e0b41101c84100030a105210901a60a141c2c0e481d551041100150780c0d00c3c6080d50080041da00110b0788602c1100c9041c0024079101ca07041d450004040d060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232252994 1250 232251744 232251781
    0x105060a03300e0103060e011a070809040509030a030e060402010c080a03060b0d020406121824050709032a0911070b090d091706010e1302090c091206 66
    0x1e1640161200346464941d07025103603100c100c402c6080d01011000003c1610300290380b010301080c5404c0c00031a83c07814840d0954144c40c100e10b0f010468002c0041c1815540e0000181258000c9041204854a441e240902406010b005005545401d4011005001d65540d03d0380703890251f104104101c0540c0e4051442182c50f500310089070b59a0542c442d0480c00742501d80c000c900300b410002090080358160303600400c201d0341c0640da50501c401403642020183c0f118052402c61107090450310760081198034517414500c02d01d106000305c60340030781d0000d04140c903001c807803602c04a41080410001c0c17010140c10401c0c110701c0768000280c40c1c0b140e0200d20005070300d207020701c0d181c050707480305080155107480b0221050140c129000001d0b0b0300e0055585c2d640c40b1805280746001a4554038006004000c03119150011300c01000030b8540b680c02d014a8038070508005015a460050f805010ba0160301c44200960084001c4007000795140040805e024040d81100c1c07002089a01200411500041f0013040041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232254244 1250 232252994 232253003
    0x28020c0f0d020a03051c0504050a1e09060b0403030908030c1b030a0b0c0406020c0109120b0a091a09190c12080c0d0f0f0e091f0f080c0906030105060a03 67
    0x244484108082201d00c00d1812000303400a00182c0040188800001c10400d0752045104102c0d402107001400c880600988c421a900300b08041c0d01409034840000d800f00340390604072145100c6655803801201a5010355210020f5448001014030616a11500c01806031070024019031508c00e1064820740c0c0c0d00b142480c003003000d01c2c901000c03030000d94041c010a00080d4004007580c1d454289242ca41559600130700c40c0350054031800882c1d4059501610b0448102c40043c9815081000c9a4803002e4018170700030030000c0c7c0c09a4940d207440c00204440390030200c002106c001809145000f911031031a08580c00c041100c0b500010300420000744041c050b1348262020310351100d8142d40b140c544100075000d8654204158002c000c400043e0940c08030600744100f41940e94458004000c06003074984054580906810620341c000140781a0701c4000384800c1071a40c05820500107035a0b42105031102c00c1504180c0280d000030321885143d1400754549030300203400310000c1150381040c400144186000d844000d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232255494 1250 232254244 232254259
    0x20f2704030c032a0b040203030d320106080a1a060703020c10050c030403031202070b040f0c09020f0429030c0a080f2701150b030403020105100b0a0c060b0d030528020c 74
    0x1800c5448c02c2c01a039111281e10070042c4011000b4030b00b001038501b009000e808014035190314082244902086140c100d030000e0312120b4141d102d01403141c1c06030151600580d103805074800d040c126620307404010300b0140d000c1c1d4085c2c10000411802c00c6894180c114150040002c00e0014828015000c41150106c0340d141c2080c40c03c80b80c0042d000c038003902804034040c00a60303000d0200800d02c0400244100c08034441c91070b88540795250141d0804a0080340b62030f14001e40103100130700401550388000d0081c5a80f000d10500000421406214141d008803644504060045100700d81b0030703000090640c10140300326103240e0500e8251006040e8048075400d01c9040d11066550901416007940001228648600c600141c83d4481ea111421035000340c504400642ca08400103008134160105c680c141e40004824501d003021141c421034061101c014290303141d43c0d4a100c7e550b1a940c81c02e4920048074401c0d01c400e51502c40030042c0d100004030b244400b002c0b4a2000b003000035020b502203030540300140201c80a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232256744 1250 232255494 232255501
    0x1e0902060a27080a1406070207050f06120117071703160f050114010e070c050c01080c120901090309122604030b070206040c090603020f2704030c032a0b 67
    0x207001e019040400010480b41000840d8444011a404100307074059101c048a0604e040743c0265502c00803500c0c04010b8001c40c2090040b8584108048001c0b2002041141003c4040502500200003030f40040c0540c5008118400300c00c10601c810f01c0207002d490138000d00402c21200c900c0c0c0724460f8001d664100040c1e00c0d952401c1041026200301e499421a00030443d40902907014034562000380901000540c02900003400c192044008003150341d03202c0b029000395015031006664056001e00800104601803005042c565500c00440c1d2040c1716a100220b00d002007420050300201c0386411034141c201030754418101041c0901e00c4410302c1d4030841020318903040004107102d11801180c00c0181306000003000e02c10044e50001e013050007180201807a160b01035403002d01d9012500d542c0710094020000503190324503890300c0c1d05010058070354041d1007040c40e8010313606072052940480701103010610b491528402d160307001c1445169004c404100c20340070710048907110344180e41000018581c41c15040013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232257994 1250 232256744 232256777
    0xc031b021509031204030309030506060a0b07020d02120f1b0406210203190605061306150503060a0806100806010602060601080604020703110106060302180603040f120c080403061e0902060a 83
    0xc2c286544d055042d9a0b191501c902c1c0c01452440790784030590317035842030f040860014a00211180100d58004809500e001c0c2c46a09208031015540d03000c3c1d920102d00b600d181414141445a45200c100d124064030511019000710359074100c000844600541c5403140038440c0d20340720441d24641a904280700020400244000381c40d1001060414a024030070074218810080395030840f43c02024102c03103030403800c59843d03020f9048a0b454032821b05e44e90740c0320061b90f90540c000c40042d5000b0101500d001519138840b90b20130b252160030358248400848210040268010612819001d48400d1010b09010f04148000800b100301c0585590300c030f0360b4002910340415002da800715003180d0500c4001d10106581d400050000d412a4040a42c030988070035246c4200e103060001c8030702c00d0b54810b100c0f413600c03a20394032080c5015442400781003e2015500ca10000f04241c1c0024200940c481c03040480ca800b18000500340040b40030395021481810801039400594030032058801ca09000c0c5080124403014148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232259244 1250 232257994 232258003
    0x801090209010e04171207110c0609010302160803090d0f0206010f260d09050a080105190b06070605010b19022b120e0c0906010c0c051e100c031b02150903 68
    0x5a000050000106c0d601241c0c0e02440541c45100c40d519214000309180031001e89400c0c00e011000d0b40400c0c1000030303940c151b004c1c3c7c0c0500544803104400315600242590742428650040d103070075289620504a02c2c0c00740d0742c40015100308407090303c00b0f01101c2d4980081a082c030299030042d010000c20024601c0382c150502604594100f05e00c2044500340c1500e108064444100c500846004046403400403c21090501449024400008501103081041c6c0385410050400b285d400764410300c200409000b01e0900d018560180400342d5a10783e0301c40d2038003072500c1140210808841950001041003440031520500110384800d07000c200000d040c1040d1045407103910705042c7c000685c0c5087d501c03400c41440090840b50b8040c00b1f41b00454141c8890005481c43d071003003d00223180c692a41c0e07040c400f604044007038924245142090790701e0304440740000381d505080145c10200103035902421100740f541c0030b00c4064090196441c1400a02c6040c0c0204440446007004003629403800112120b03103440801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232260494 1250 232259244 232259273
    0x4030c03030309080f0304060c090b180609011110153206130b0304020a0b040e1803070b070509040c0813140c0a030804031b050109050f130f060303090801090209010e04 74
    0x2e48180c0c1e00e11f45440c00e00c0041c151101b4070fa0014440071400f040004500c42100d0083c2e10451141c2103002c1c420b420005c0a610881c580b504002410300e086440313000400920300e11290721000030501c40344490082d1203148681e4000c9408030b450031240440009903990301204a04660f61a02c109110113000c1103151180e40140d40d00451848400a808010f0b0005140a58422aa80701410f90380c2d031448441d03400b40d030060309648ac0c5602d011503074203c1c0b02160f0016000c0340f48140c9040000540b90142005821100719001c01c00008001105141c1446001408031080c1080340d003a050442d14030240c5954480000c0c10313000145442003121404000005a807070b4000c2400c1c01858032403920301c0c01a04640701c1100d00503c1c441c40c030721120749200d0002083d5803041e500c8a031070ba0b107888100000503011411264200e480510b46110a1030240100c8040d40400caa000c00c0391490740c0f07001030011025a100c2d031a00d9140200350801a50383d100c10604542c000240f0f1085900c6605040e0780500201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232261744 1250 232260494 232260517
    0x60607020a03150e0d0f1404150f020120040501020c10052a0f0f0f010506090f0a020910030c020c01020a020f0f06040902030f040308011d010e13050709150b04030c0303030908 77
    0x10000365421071b48808400341d508284c0d0b0b55220006001c0c1002e0a0500170740c0a00b880c1c440d13400402c100c081c2d00c1118503600021043c030001c144c203500002d5481040070180c0300c0c0b8002c842c0021f03040c03000356010429444401000d450000c056074100300e005141c0d01801805041c0140c0c070412240075034034403095140d80c0c04400001c0c0d4080c0c80d007240c81d040c0d0741c00704408403e406000300b40c1080c01203132061141e144207640150045a8542d161030301c04081e044010903c0000950a100c07404007034441003800010b40e04240c800040300800c040e4041d2602149441290455101e0ba003140010b80300c001c0711000600041d1480c2c04070444083c000f51190041c3c2c2c01640c00c692001c4104085101400d00190082d80242c4425000313980f1401070840540c0c032034440c0051f9000311401000701070701002040c1c0e13002e03d500e9514403a026040c4e80d2039007007038603540c0304d640b40a495100782001191401b0115004005070f4080c1440c003869592043c12282840c84054181981c0340640024048180c2c215040c003100d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232262994 1250 232261744 232261753
    0x1c12120b060c070303031805070e3303011a030c060d0204031b15030204060c0f02040b1c14030304020307090c0e0a090e01050a0c0504030f110406080d08060607020a03150e 75
    0x441e1843da40301c0700e500c01500040d0901e61903011070380c10041003040c0260010007401d6900d09200740070b20303200c03c013401120080c9d00d00c201280c52103003513140d00c1580710401c18810540e013500301c1c03c042c00c2d41d000c0101d81c81201c1a01812902d00d6400140040e1910415540140c0340d201c1c1c84180802401151720242042e062620848202121001c0c1ba80a564950503200c02d90362541600710101c1c01640a4540428007000080000c107124a0080591910080c401301d08504402c012480190f0080c840c0d030305000c05520394008014034809448041a4150011401d6181c01c1e00041e540c0e510901ca900741c11903982c060741404500c81e542907a003410018020801280d540c61820004044040ca811401d500c0e14020403000d102e140141404030400d81d40d0030f400c05066031141d6040001020040314000903503119090381381c480c0d0140300d0080841c00c0c0a801401c01ca00000742c0084030040c00c56200f00000c00040340180d03900305119091301d401c501d90441814181c81d400c00104075072640e40c11144038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232264244 1250 232262994 232263007
    0x9040c030503030c370e210f010e0c090c030709150e03060a05060a180216030f1d060d0e01021b0f0118050a0209040201050d060806061c12120b06 64
    0x1440c2004000e890403012003014002113000b51120211405c10303241030180c112a4201242d070340b00340320035506d588008043c0310720307289007110a400c0c0c0f2420100190303184d0841400250060b50a201396190304078100c0141600403403800c0010200c1c41c006060622003413020000c546483d01c19001440a0000c900d8582e025076110f00025104400500900380700740315140000752030202c1e0303000b203d00960307002d407040750514100b20f040c42c449015042d404810aa080c4881052600d03416503800800e4080c0d211801880078084000f0003045155099499020543c03494400c0380d2100001c8400c1859800c100146070350984c00d00501a01c10070810b04812940041c0c200e024060104040901c0b0701810020880c000c90080d980d0100c034100a0060080e8210041a2026050046655522510514101d031a20449480d44000c4a071103421480c038640c080002c000d403038100900c0f5038211800c403400210840c50143d590568009103400414100703c4500c1c140804c9908640102814020007005140c072401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232265494 1250 232264244 232264261
    0x1909051c05091e01020606010302300402040501080d0503040204050411060c061f0f090203040309030b0a020406020d05090d0f020609060c0c090a020705060a020f0d050c18010f09030209040c03050303 87
    0x104900a4030303100d0400d5400f0140c042041074216094290103030007400481d682d18006400940002c1e00841c0a01c096600f03921002c07545040b515524000202c000b03107075040c00d0050004848050b0030182d070340e902000038040030320381010640740d0144c1e045070302040c40c1d0360360f18101442d0705550440c240c0000b8081481101030002250191007070094120b958800b0040e840e01c0c012240c058410b1a40441107860f00348500c079070039002940d00c0750080c2400f80d0b0351a5a641d90380c1010b04119a0743c0b1050f035001c1424441d05506101c443e109501c1858481e041030005400141c0c0c0c26040000188084845441c0074115110300003556940a030041903142c0701c4050310f428644542441c011a807080c039500c2c000411105041c400e0358441a0440f006080c9039840c8203500000354400301c0880e00b42e40c0706102d54490140d0034019148181d59400e00540c80d110307880c40c0410001428034801e410b00031810800c911b0300f90312500402c2140d404a4801b03043da01c990174020039504441d04090282d020001c100201c64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232266744 1250 232265494 232265497
    0x122508010b010e06071502120a0c030c0305071b0501140903180102011116030c02030f03120c21150a030c080c0f1309020111030301030b040c290a11060406050613051909051c05 77
    0x251900e440c1405020080302d4110100c0e2401c5a8fe0800324a0440540d403581e602200d0458031640f00e400000f03040960801104d841080440c0e00519590000814041c400848002c0741c0d03050500303000902142ca5103118020300781c020a0b041541d001408202c050a0510890581c150780ea00507098580030711201c2c0709140c03a5800380f08180003140030300e0702140502403110308895070400d08420000010103880c010040c000805000704c100300b50103211520503651252200c000130352040da031400c8102e150040d4142440d804004c628031038054007814204a8980303660f01c101041070070340005541d10f010320050b03a000c24408035843c0c880c44044008400c105034117000d913005900a0070241a03181d55104030200c607280580c0101070180711000000d052078009809010a04828207007440d1401009100b135160840466081d1005929502800803d00342410b440b00d14025080042c041494000d8004024540450600003003580d42d024840c00e100082c442500c0d0b03014001040c02d541804c1c40e070000c116 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232267994 1250 232266744 232266761
    0x91505180708030d0b01090312020303190504030903030f0c06090b180a0c060e0d0501020703020d09090e06010e060d02100201050106030f0603020f122508010b010e06071502120a 78
    0x4403001a080c40110040000d4803400c0307031421801186130202c00d00206018020070307040107051258081000c0300103924010080c510b40503e070300654691401444d03d0303951074064414415040e16140521001c2540f003420030050f00c0d01420120001040c0b103070100c410025180c40504130a280403996000c0140100c0080d0145a05041c00d2000710728040c000742c0c0300c5003000c0780140f070244030324070810a4170701071205100103801c010164001c800384d6450356400c2e40c0c820901100180c0100e15001e83d1a90408420001b61240e0320301042031540384051107036940d8060217a1500e0b440414000341e1682d4a1341440081264060900924134101e400040c2c0640401c0c010f40010a00701030468036842c07014840c3c60100ea8004041e543c60780c1c0080140b11022900d00c41e50380c042d0041c03801501000400000712074030803050310600340c82c0318038051400d401c4900c03a240d21410418425294100b0765141e1040d6940071380c10000c00c040001e81444108001d1081d001c1d00c418100f5408100b25841c003281c1d0040300c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232269244 1250 232267994 232268011
    0x9030d0213050906040506010c30050d1401060212030a1803080708060f060a0e01121a0a08061b0f130902040603050603010903020601120206310918080c01091505 71
    0xc5981303560b030800003550300450340c260000310702551007004505a10a040c0078004d1080b03283c64103031088410164002c180407034071008200001680310402c5414842c80355623413150071400d185d65040a0001391142d88250800300007039030202c00303e074140781c03103a010180c046800c40ae0080317034110b1441d01070510b0f101150005c1c089a20318001803854108542c240d02154001826985004501c940130303074507401030050003070400005034000020b4801904c03540c0304042c10118844c40100b400e4080001e250050780000166030055800c0c400103008032510340500d2071106100075207035080c4121a1143d80141d402036580c0100010002039480d903964000c2050751287e41e0144101d5035040107140c00d0f903052180c01001a4440c2c001000305503d6244094000c078030003000039140c2840b07886242410215580841cac051200b100d50010302c6444422100700401c0220380900c200310588020401040c59008085d045010000b203d6070919420743c0074143e900d500240010f081e06c080090b50700140411a5050b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232270494 1250 232269244 232269259
    0xc1a0106080919170304030c0204291903030e060f120f09031c0c030f090503030a0510030f020907090803130501090603141f0e0a0504030207060309051509030d021305 73
    0x1200d00744001e41103071000c4d03048130080e01c0014040388650510780c0010b10030740070080c0c0c0d0000840180e0b41c034000d01c7e400c405008900074101d0850000884000c1c400320455116441c88030203030805540c000350010840c1e0b05402d18403c00b11425010407642d10840521400c120b100040c400c0c600079503186101e000b9078a03095111401d03a81c030b15045a50344240100e00604214005100344e403040c50340c10000310601280b40100d0400c00c9e0400b6a8107075104550100c03115000401086811129845030680c485400c2010128080ca103440d40028403200c040302030300440c110b00c001248036002d502d000d0010001390b4200c96079407400b590907114040b00d84c0a07940c0090041c503000a20b1620070700075049000711413080258603031112841d1a512501300c403600d41050b0100e10002550010090b0124811600580c012416145c107180081c10f01030241c002c0828585072032541e0000c2134002821170070b140c184800040380360320750324450382c0345000c1d08004180c290300004500303c80300341c80e08982086540981d8030b030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232271744 1250 232270494 232270513
    0x31902010212060a050d260a1d01031116061d010b0f0a140f03010b040222080a03170a1b050c010f0e06041b050303030f1f14010c1a01060809 62
    0x1341400c0c035114599115030400c85141c0070640c00c58852800b0651442d10305113030001091904801d8000f41c0f060400301d04542d90685920381808503210900c0710134602080300d81e8040b1200c90301c5000c0d4103401e103841013036200003034108a82ca5100b41811403e1411654920090795203440c0a480004045070041c907188807840300340c0c02c041c00b0840c180c68241c0360903070348042110b090045010750103840d03d901d0341d00c0d01c6000415884e644024405484901c00c43e444400c01800700141148155200c80c9184d4002285030b40800d51100c4444051500a000c1d020161626403078030000d060702c41c1111044111030f103134904140c1e420000911200e808a0000d101d4006109a6081252120200c141c840d400250001f000103a0308084601041207008650003029101d0000c2480c603003044a88101e05c10f1a201400108500710b01c40c00c4550285000041042e0b003080f10301d031158110b00c0d48070390500c10b0341014081080300301c103045460201c0c01c180c186c100e5a50794500a110310006c2c0c1721510b0b98050701100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232272994 1250 232271744 232271749
    0x30207031a061e100c030c1505010501180308120601050d050708090f03131403030f0a0e010e0910051909020708030a060f030f0b04080c010516030509031c02030903190201021206 78
    0x7085207010f401041a0010010f64100b078a046154440407001c0141110030900010031007818a00750310b1666400060640c1810005804000b030600b60304402181d01000b000050b84c01d0b42205c01a142c280c00590b40780c0c50380c0d00141c407030740607244400c01c400b03062000700807555610080040c4140802011151019110411142c40303100d150b244d1401109801e0b4140302c0d296504507840210700c40642160300c0d001e2207100d1441503400560304580000c40c00c0c0d2000c2030569015100b07020200c001c031070724512411b0145450110901e6889014050a034061940c800081c600c1811001081b031100295507a10b0f03240f802030460b500c125070340d15102d0310341240894058020f410790b40980c2c0d880741c20061050055245c0a0b01200b0081c0300302c510100411484a05580c280035041c0031f448098240d06501c10031140c06016104014041c4669038001c0c48400ca00c2200c081a0301c5150341c40c2c0d180140ea03030b124848032a06621544807050618031442000018180e8154011f0a8070700340601c0642040d140c0004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232274244 1250 232272994 232273039
    0x1b050a0606050607020a090c350709060509010f1407050a060e0f1f020d060b0d060605030603100f06050301140103060b0a03020d02040b04060806070c11030127030207031a06 76
    0x10041d400c40c200603c07d1048044030b1340010305c016510b041c000190321307a60065100c142d8440e0010059102e00e5034034107001c0300001c181103801c040c180c207064100a0421100400394020303a8a0581003080c5104082036542c0690070501c401c2c54040c1b01980e8500041c1043c3d0b43e0355045050440d292494242011452400440e1401f2038000c40000b070131411107054415054041c194000405d10b582c2088151040c41ca14441d12000340a400503c0362030b0a12106614200c4030b45a0045045c0b0408008002003690040b40d0480e100d190700600203540340c00c040c0d01c01c00401c1d840c0c001d641c2640ca050b800c80340c0e8495000000e030407203105442c18002d5a01000c03d0020584091000079003244c40810303201c0040c42c20f03411403800c4c00c03c0604009001540c1d401c08078600700d015600c9401188186032200c0610a50748144031004030305030b0003404065003c0b00040f07034202c1c2282046074115aa03103410410144203010000086400050310030340c040c892070b4050382c0c03000f0594085114460600700d071449080d1240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232275494 1250 232274244 232274257
    0x305060a0c081b0405130204050621060a0620030d061412010e0607030203090a0c24091d091002030901020909070c0314160204021b070501020a05070b0a1b050a06060506 74
    0x110035013003e01d068284003403808103140d8040590307000c0c0310205182d107800d40a044055102103c03920506d581c52810241d075180a0a010302403000c9040074040340360861005180b042c00c0201e582a15002000c9041c1940550100b400050341080c00000f203a03280c0510032078000d402218840c060041300341e515422155950000c00c1070350018800a05298020350141d540044803074180c0b04030341e019584404451149810149025041c641e61400c4100401d030410000003042c01d007480c00031f0030051a12581903112041e03c060024034000520421003d00c0f214115882910f1b0940d05d80c2818203605010b5040b881a090040140000040c52180f003840111000f9030140c5901e28002d0040032100340c00c0d840188041c40c602c0844000200585562008201170003e503c1e03240a2040701c10340140c104170003a40010f0442d0301c45c450003400b042004c14500f04880e10401880d41d1443c03848025201440c201c22010b1215003296420801e000010483c2d01d0040c0c46a04100070b190344580804c413090040390b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232276744 1250 232275494 232275541
    0x3020606180a0209010c050303040b01030b01120804170304150908011a0f10110304030812010b04050319240c030501091a01080402060d090503190c08071b0305060a0c08 74
    0x11404074540c10340b16402070025000c1894000b01c074039600d8884901d59801075400301d075259608030040052100f1a0741240c0900b61501d0064010b0181e5211814580580d0080103906950102e1147c1c20340c2c81001101e005060392040031040f1034602d10060550100c0f4031413041d40e9420819481d040d8075046801481c040f42c010320f002c489820100c24002440c045070044014000c05c20302606602030100090802584a0b06003203580f5443c2104000740a8010ba1083c00d100c0e5040c0310922003aa0041408040c0389046446c000b11005181881c50640c0f54008204c500d4128402c1104a480402d8200c0300c19401c0c1a01c040c02243d03a9440d166044070700c043c1034143c40e21540039035600150301c929415038015000a09403824000403a061402b119450881280d040c2d000052040010301c000ea24680304003024104a041070009032510100da10901000a00c400c40600e9280081c82114101e035016503000400c854452400c440c0c50b6008080b281203040c0800d40e414005211600343d4044544000200c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232277994 1250 232276744 232276789
    0x20c19032f0901060816111204140a0b040605070807020d0f03031406030607030218060d0b100504030f020d02042309151e090a120207060e0d0506040201110115030f03020606 76
    0x6d800242c0c0b440c4030345d441110700f041408403040a50240400030740101c03640c00d0074211780d200c4c41d12140302140baa01a206a0240300026020028500c0c000c05590454050b4180141d031100c1600d0458000e206285001758002000b001c840c3c11f01c402c1030041400b0a10030380b42045800c540000c0038031254812621141e150344000d0000d0b0340310f442038014000c668000e8042610809441c0005401904020700ca085400e0b039580211640b4035090821111111690138001c1c900b5085032a07001c00b02d80302c3c80029002d030014452000c1103441d2980035a01d85902c004480a0380400550b140002d0203050781d510915120701ca10140124008940b4140103241206080000502c15071000041d000d004194dd0356601402035450041684107a030294074100726400351081c00c2c18000003501070710ba5045054001c03c400e000d4400001c00001d0f1441c0c0090f02400c0680000d448551003901404000900c151f0282803000300108210a200dc0160035901c01d4095400b60361b80c0b0028400f481000c0104860304d0340c1c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232279244 1250 232277994 232278001
    0x6031515060e0d0c0e0402040c140409150b03070c0b1b07060f060810091b05030d14040f03050a020406060f05040e0606070b0411030105010b0901020c19032f09010608 73
    0x10b80100c0001d90003e0100c1030036040c07584904468100644c019075040800e003040004600d441d01c15101c1c0900182407444004003034007401c4145001c0d07401400100b80c0c0e94200e999810700d10513034a00041507000825592031a007600300910012043c0e504856180f06a40401c0744a00d00480540000c008801c026050012945544010300150050300c008107640c0c038400f00d0140d10910001103a5031806401050407907a51520304074401c0a840706d0300c41e13101e29080600070341d03902069864842c180c41c40c044002940351090708165201d2a0301c00e01510841410005c104030303001c904c3d08a01c6000702d80c20462260384600c15903e4142c0c044030040011020482403280f40c0d00d00d8801908400054509418040142d031041480b28058038140c038005520181201185002d0240c40d0140900031191410000c1c5140040e40da0008501103520a00c15024030005145205d071038140296044402c0c0c1440400480310802c0c0b40c460080382658118080c5039020090404001c00f80c1220503541d6034103044ea5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232280494 1250 232279244 232279247
    0x71a0a09050a0b16060b0301060b0a0e040b0109060c03090e01080a05070b09150d0b061b0f070303021b040e0d17010b03010e061201020c06090d12050c030f040807080408010603151506 80
    0x11002c0c05c9502c10340c0c440e0b0b070307100790b85003441000007a1040e6210541c0d188004000074081041d091a9207102d030f810804000300590b0700c082c0201c2150f2043c2401500c1ea01c2c54542929400c80c10b801944414050030000036800c00300140800002d0300410a076407410303498140e074130034921a18841942002940e081c0c0940310341d014000380345d401403243c80011130090740f0000450542c04407103c0c1c00d0006031032081d0741c801c3e5014090b5001035103c0354010040d140c0386560186d140c4031203444007103100d9070140414400342c80c0d90700720b020021785210645414131010500a401c203a01e0684100c0740d44010400881c456002c181100c4c16a030348038800140540d03550041000844010f0f4064402e95001c2c803402c8000300c2c0820034140070310104406030048103980003000340f041c010400000c40c280c2c10401840a1150ba040489030010b0741c2194114069030b540c10410b0395071240100041a2400018001524100c19400001520700c1a803101c10310301e403000680010380b080040c60910540449004100f9035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 232281744 1250 232280494 232280527
    0x51b070b04031e0506011212030c1d010908100c03152702040909050f06060609330409140105010512060f040b100c0519030c030f02071a0a09050a0b 65
    0x684404049807a843c4284e0b02d0301e05044080c0d1110496600c0005004100811642030145c2c4d200039140401c8500c4038058018940a200e40001c002044040c00c010081c2c0d11468203c1d001c0d100b401c00f01c0b109a428500c003075008042c80144100001d16045045200310703a108000421100081d0844100342b5000c4010750406502044840005500304400500d1314450f01a00b25958011006400400300c1044400d0520900504840c40386004010800c510356034980d0a8042a9201c01c00e82c1000c294549145841c003400200d85428960100d000100300ca01030300f00c0100d61010b011034a0090741d8840066400303008202c03400158070b02e0303100010910b0606140c500c100300002000801e4090b80780011500c0b010b90041114002824113030f1740300038018100a6030303240e800c021601c1c00c00303d134080c0c800814402c072003100281000801e0402888880c404c00c030490251040c200c10980b10000088120125441081d1304c1d008140b00c3e02c4005413524040400100302c074a610707905440c01d8504000035806 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 232282994 1250 232281744 232281773
    0x60e0d080c0a020118080910180b0f09181501080402010512090a08040807030314040f050105030a0e01051003050c04050702030d1503060f090b0c0301030507030210050910051b070b0403 81
    0x11503503136140c0d85d08031144602020380102d002e1006c0c2a40d804214040c000c00c40181881ea4003404004015015110007120402c011100207891554442c0300040100e0382d41e100708003980ba484440305152511110328001c1c00c5000d18440181c1c036011079605130041d0f0310180300700c4029006c50301c1401200100600f040a4a50040444050b0365401002d551000359070b03000754214208640c0404010f00c10190014101c03108040c0c2801e1290a2500c0d0494819240b1007501455040100201c040380024072a0341001c0681c541c0f21009114038070f8101040b1890030b900788003e44107445182e00310300c2e41e810544119401544d035913000d5860040d0102508000e000320b0600c003a5105010000000400c00d01c0c4034a00c041e0b01510030215a179000c41c18011450301001d024211541c1080004000090000940f80200c0c3d9058603490402c0f41514416102e6000d4603820503080035440c0001c80703c40754881e00900c0300701c01c000002400240400340710760755501140103a0b20409800c00c0284082403411880030301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 232284244 1250 232282994 232282997
    0x9020a08011d0705090409030c0b070908010c030e122d0a030b010f2c0d110108240f0607020303280504030f0209060604180603050106061d090402031e0307060e0d080c0a 74
    0xa844a142e49405480c0707003c0b42c0e10750001d00c11080c140601cdd0300038000c451407900d591505101e03251003415001d4072008905a00c2c200e8000002c3e0651070140840c1e10440c04000701140c52494040c0b01070740d0b11582c0c0c083e6690b100000d241041c035410315800f494083c1c041400c1c0d5a20700106a00410110f005404156118a182c4005001c640541c0c2e40d0700c000b20349041c1c484c118110b20710090100244c0840c0020380300c4280702c00b411000a080316003c4102c2d91600344101c8a04c221400c80001149980c0301c0c0c410069010300000494400c1001070700740396281c0070500b031a1074254031030803c0100c2d85801640030081440d181d00d2449000b500e80040d0140c1c00580040100386415541c48043e41c28940c500c0b0700031031041c5c6a05040050203028441c2500510050814003442c00c910b004028021a410101e180b181d035102c0041000d40d1001c00c0507101d1440e20820070074030364190080c419070700e400440007152401c2c2410f0103a1301d16507001c01c510f10207440689031200e05031540d524040c265008900401c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 232285494 1250 232284244 232284257
    0xa08040f150c0e0a06080402030615010909020c060618151509031e071e09020307022e0b062113020411040612060501091e09020a08011d070509040903 66
    0x4810405200b076031040c15041d15061807000c50081071110742d030016031282050001040420000d41ca000c2412075105880c00704603403409441500584101c1800d42001d118148082503100c00b19a0001c0c410740107510442e0017041c100800034808021039412aa0a0000c200e0201490312509101240c0902d803502c02d102c40d4107220025010a01e45070f401010032003035a84284002c0425041480341c0c00c01b03031030550850071187c003005410000b650940c1c400d500c20b0315400070014004500c2801003042910078000c0304440c000c038500b40000b450a0131034500b40401e00c1c0c850081000c0c54000201c1c0e4074000b12090280304d50f0080c481c0041c1b140d500a10140440d00304964000040e59940f10701c482084143c8101340d00c40c4d0070140c004000000da06812800c281c0740c49828420751b030300441400c00311218583c5854404111404d00d8089642660100b150075001050742144a9003103d07126041c1c44008443c0380100710000042240a9800d880c0c010120341c003000556260b050641100200d5070082c00c002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 232286744 1250 232285494 232285523
    0x3200609040e0a0308010e0c180316030305250f0b0606041d150d0203070308030a020f0412060b06070b150d120f08130c0b07050f0307060207060c03020a08040f 70
    0x3810354070b1140a518a541040303d00b4410035070011505405400145801829407504c030740348409920407110000e0182022080040710ba039010050b03c0171445440f4005c403401580c034a4007400940100d031140c0752040e4001c07c0090706800d644011005260880014103101c046074031041c1240e48040d2141d50803100c02c05c408254494051614900e2040031803806540346411840b00c0007a844014002e44a4040b030107801c40540c0d4000303500003e894008003850340d2900c480e4103080003032044000c0405841004140080c4005103810144056801042c0900c070740e4441c1420800d50f031040e200c000340003a500c013010450841d550411441864070141c0b00c0c80001c0d074640c480760b071660030b51503005002500c3c400001c500d05a000ea83c180d08035003040c51403d280010359460030b5810b0800c0c054400d4030503010030142c0c1404400c0103041c580c0c40c00c50058030703076610084c20000b0103980000401c0d15014180b50b10014030900c68400c80c2c0300d072142030baa1007203a600c4940d55040041c20004003643e40380c0b00c00001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 232287994 1250 232286744 232286749
    0x2030415030e03040b0a0f0507020f0103050711010f0e0d020a1515050a080d1d011706030304030f050d02010e030306010c0320060a0b09010b042105150a02030f1003200609 75
    0x140301802d05d12407100d880c0c0c0c1c11620010b01200949845d4410048184030a500603115540b04043c44c00090a0100356036884c890200c0b004a0b1240d02c0c6e902541c01c2030b9034850180450340c00000c05401c40d01c01e442c524600740000380e91f9882d10840003080b182d0040c290a034440c203103600c0f00081c03100b4054400146613607000068a0001d25801030000d40d040118600c0103247c0009044240504503140f403c0852072010019284409124051224010000000d00169024000c51b070165a0000031406044128140b20390707605910440c80d8051340c600150f0052650002040c4c901ca00030594641e87c3c0d40d9030546d005c8030b400c070b00aa0020310103000c14034002d000c22018069a0301c128075807080010404110070821100c48410390190720b441c8810041408681109102c08114a0300703566500c0a5550700e1401c54607114420200c48103402c600c5017805100da4564006500070003a4000c9400c2a450b41c0e0640d400c10100b901c0028a044102c24100c00c0382c150b800160f18100d41c0082006040c201550007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 232289244 1250 232287994 232287997
    0x4030b0124030c02100911060703020303010e090703020d080706090b010e0a060504020306060d051003060c030504060e010c021c09090908070314070312090c1d0a0501060c020102030415030e03 84
    0x42030a440c5464a4079400e010203031505900c40c181d0a00d801c1c001e10502e01c1c0e02a4a411103040400700003a22507010304e0a01400c00e81030341c08600302030b000c075903a10030341d060080d120f800030b02a05840b03032008400b003500307a6000614141541e40040c50030f94219880c0c0d40705100f40c1c1c80034504888003034403200f80740c011403021064a4001d104982e140d002c89d1030851902e00480d042030b0800c41c8540c0c03043c020f00200d500c40c00c0c2a1054040070030000140c0f5200c00141d4090903405510003007a1a05080003032400952640007d40034620510b01030007d1800941e00c1826204035081c2800142d010035040b00e400004c102a414126100d410b00c0300010341c40f00a0101a60000303c8269110307100051060308050f030181c0c0703510b000704403484040d08003004e070b0398001c003403501844000341d0090312184000700342300d1510384100c01030004511410384603a407035411f10884030044a01c492800e1a190000640078040c2496a9000e581640958034050400d0b200762250f05aa881540c10580e550020f5074410f1010170 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 232290494 1250 232289244 232289249
    0xc120207060501080d0203040f1208120103030201021806090609010f0e030a0c24020a1106040f1211030c061b150907090b04061202040b040f11090f0405040201020c100504030b01 78
    0x81c0807986604003129540f9005a07003052104660080104108004013a0420701c266104140000e940d40124100000c1a0142d00e031a07070209017186d000001010380550080c00c01d89c22038401010f0340c4001c0c104018113030180308403007031304158100704c429102e41c4165014201c4280a040002c51404040046403801e5818081152540b003800c03024804030a00e86034207000007101d0100c80100e891021402902e641900c240200090290a03030117407242d46070400e075009482c041c0c0d01400391039620111210300c0910350b6401e86032012410b4518803541008203042408881c0a8007032403a00510807003a0000c00510700d42c2c00c1d041d0007003072029042e1400c1d0041aa02030b2388245c0080041c0c0341070802182c00c44510007a0076200320724040f41085060380d4031107401130b000d40445002808503808004200a0b2101d505084841c5142c211440c070300d104040c02914600200741c40d8074487c1c40c1483c090100b01c2e0001c3d9406400343c1c3c06014400810b1501c01c480500c149141c1c0b808908159903544c0c1c201c0c00c81800c3c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 232291744 1250 232290494 232290503
    0x9060112091509110609010c080a09080102030a1b020c092206020a0c1a040b04020d06020d0606020d1106060d0b073c0e100e06071e03020106170c040c120207 69
    0x103c0c2d1000c284507580c2d80460701c0040898200c5c3c5040c40390b070000b03004402481c000800c07508001c03620300c5002c1e00421140300180309880095543c3d181203d0140010000c18100019070352b10603021102c03071403001503612000d00c0054a00c00f1a5100c0314a10f15042d041c40030b00044010000740400300082450000c1c0848240f95102c0303c0d000c803014941200c6c0140701c12580054088074004110101e5a0300c0e90041d04a42c041d01c0303c40000d061400d08601030700c28060610b400314101540020255800100da103090001d41e6540000280e29a03002c0f500c810301038402544c4142190002800318004450164106146040050040d240017275420b02e29081499003602c00324282030100d2091060340c1202d50031075440d2402c140401e141078001000041d000b020b030b4081054604440f422a00c4150490b140140c02210b03d000f0b1104141e40784075030024a100440065080200c001034a000c08410b808030b1702590006401410380c00c505000060001d40394000c1006100300d0b0306502e00105200420702c19006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 232292994 1250 232291744 232291751
    0x309270f041e0b18070f3003120b120d0c0b160816020c09070e150304021e030c03390604030b0a0f020d020309010e16120507050306090708060114090601120915 70
    0x8640f41f0943ca034030910315221905011500340000e41c1c040c0800c1e10130907000c0d4001400b161004045000d145420a40c0b5007a40b00c1c0800709045030b1741110135081c42c2c0d4481c07250980c40e541c07041d50020740d5485054220002c10a10404a86103560301d032080700000a592040318110a161701c0010081c4c102a14280e01055082018a2850506120b00b6007420400c20100d032450800c3d81c0814240352f070b20349030001707144802c00c0d1a091070b580034412180d49100c000c0841720707094505d02287e9920780400144540c2c1c00d1800e07180d07518234151400c003c010f03444024440390500c0e15680b40c401c2c0c19080107101000c0e1030f544101214840350248050b28080c803100750010384a01c6e242510608480c03500341d02014561210410042c000c55240c2d24200f901d16000440318914000c4c82c000741340c05443d0300440d9140c050042006281d20300021454110b0703040790102c8845036a07509240b030242c618a841c0541042c08000054000d5000d1403050301402000c40300000d05600b0f54440b0711043c42c1c0700d581d03a5441030300c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 232294244 1250 232292994 232293029
    0x170d06061206090b012709050a1d0606010e06030406110304060f0e0a150b0406090207060507020d0908030a030b0d060e0d0f0503090309270f041e0b18070f 68
    0x5500c28440640035540e0200325a035580784c006001c0011400e0084c0780c192808050107100810150040d004000180c01400241402e49040380503003d403150300441d49568900d24100803400041c4107001d01010b0710b5400040ca48007003032001c80c0d440100181d40080d1662100f240c1d000d800d100951003240a20400210150611020b000303641d0901e01200c1c41f6481034416402150b44035080d0180110861400900700f102e5001160240466501003038409102168800030310000b07400492003800e040c1d09403045604808815240019a8025012154070178403841c084140254001011010000d1a24000400030b0b9180000d6800c1010070000030340100700071007000b981001e441d418001032402c02904500d071a151403503590141000c414446c10f03d411005da401c45040816098404070101d1141c0c143c030300412103512201050ba4119484030034015003005406c10b401c01c041030650321401d882200d450303070300a0400710360b15041c0110450240b000300007200614004c01400504800c80108241d5a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 232295494 1250 232294244 232294277
    0x1e040e0c0406080f091b030a020301050c0712021507030c0e1c030801060c02010e0910050d050a03080a05040f12120c030e010c091a130f03050f060a0e0a170d0606 71
    0x100060510307024440704006112100c10003003580c1c0e0700d411480c5016851881c6c1da00003c2d16200c41c00c580a90154070308424013a00d01040001001690702500d40742d41808681701e01280d941d00703c0e5007905410700103000802c1d10f55200b904044100000c519000b01d9507001680011541c800590943c1c00f13000394001004c04050304450080e00618045c02d0905940615800180c0f4100401621501c03608014002035101200d0703071507034400780001030700003107050726503141c49907848400c554164040340101000821f6000240500c0c1d106a60100740803004004660f24424160b8442000d0424030140000485201495104981c2142c940d580c0201e60068103540003404c40701a00400000c000c0028405c1c0701440e20506608131521002035401d03521034403070500143c00c2c00980c1142031b4603030b15140000305120000a14003119420642526519140c240d091012550544d00100603900008007840115070300d612001001c0e0418980e840c98581c803001d2100880c0c01c0303030b04440040f9843c05966009034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 232296744 1250 232295494 232295507
    0x50105010609050307260706090333091a070201020904060b0a0807120209030714031605100c03021f050f011a03061c050a050c01030f050402061e040e0c0406 69
    0x41c90380e401c20042803400c29002c43d8070748001e070140803036400740c80491001503201c808000c452120a5010758503804c2d15204005c04009903440107503225414105241c541d0740684c082d4411003507c10f80c079400510840503112018002c41300040c0c42d202c0d040c080380300c030440d040300c21988201000e900050740c4156100410048440320f4000211900c02400210152600034a510b900702009040c25a0706107600c21610300603100f07100c42c503501030150041c0050480352681401501c46000c4081d2504115a4858811078540a10032661f002c2c08180c0c03101603081c01902e0703c0395001e02a106540006022904840008101581e1100c040c0d039038004105888141c401e00b00d0142145955040034032914030306da9074140c00040d01181c4200e880c0c60000c00b24080a01c2000629a400700035640040d1040c10056150400340340c4840c0481d0400c03c03208a402e4582c400c492040b90f00401860400904000125080d05202070701014101c041001246141c1200d1049100740310a501055a50b41017a0703004211 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 232297994 1250 232296744 232296749
    0x14090a060801091a060a0c0c0308070305070c150c03050a020304170a0c05090f06012609060105031b22061d0103020102010b01050307081b1b011b0f08070e04020904020406050705010501 81
    0x10116071000120b45c2d9418112501e00150746004940d11105040243e0a0407141c0c1c0020410308000950100b010f82003405041d00d0b80c0620040f0386003a580340320101302d03204d0b002c80c0500010301009845002074007503400740118156900c102d034101503c50044410704032541e402282c5580c8451180c3c010044072415a0b0b011f02401c1d00c500c0310b5400c144041c0654002d0140015060198000030720342d041c0030810710798808442e43c16030075100e4140066119180c01d401c0c05140e009002c1d00c04c00c80040500701210341d00c40c8002410301004443c8050103d111039084540c68240281c507a50000342a1010440c8407090121034064400d982d4510710002e4219187c2041c01c0b0305010381030041160881e00f000344250b00121030f0b10451101c18104007282078074883c0341900101c40001c1070403c5000c05056124401c54042c01087d01c043c441159005d94611000302c580c0c2d000120f0000c000303040980300d810300c4d048059000e0805420100d203100010140e8001e600481d0000301e001c2669014000d0074080c5500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 232299244 1250 232297994 232298021
    0x9040b010c03050d050a0f090807020a050907021e0f030c150a050402100518030105010f030506010f0b0a1103040518060f090c030c1606111b031914090a06080109 71
    0x140700c070650754050060b014015007220441d5a9500003102c81c00144c00440c83c003841501c0070803c100312840c1a02c5d03242c000b440241e0003402c1d8a040404e1030b08000420364091021a001407218007540c000306104085094900301c42409400d4201c805190f040014020f01012000a0120822030340c030030100c0040007d10108000b414801804050703110302520300702520492424030750342c3c41c1314102920400056200c6503015881c00c000080c103080154041801d036849602546e0745643c2c0c1d00c11500455009004414070b9180411566a01d9405101d044144003000710589092942d43c100003558900401903004813541c125003002246d26000d012403114040072940901903003010070404c20301f03001c01000418402400601c003024000300e500c01d40e241a500003130070301c035480000c980510290410011019003040914081d4071141c008010307941445130107078601402d603c084504903052480d00d82031650360b030070402181a00c0c3d1150300d141c0c409031001d9160380080d9450401d481040b9000c1c00b440c00e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 232300494 1250 232299244 232299257
    0x10203090f01060302130902221a0d0c06030c0915020d0801080d0c02040218040510081e2517010c020f03090f060d06050a030b060a0e063f010209040b01 67
    0x60360b406c0c0700509800c0f0402400507500441e44082003c41d1240ba684c6108006202808400c0001a800094895081c007601c11840c03035110301407050b14028284010140420020240304031482940000d11103c258a003d00781513644100c10f50b807072101c0010100051f00800003018400c0d40040740c00340101250f900030000e52002c03c000a20005100200a1042d600021084d01c40030810001c880c40d4200103108002c2c904102030242c80c6900f50f48103440c200e001b2102001c49010400d1322100c40d000700300b8050048805c50100c0161554182207003414034414400c0003060441c04e0984101c50741700400b0002070b01e40c6d07241c5400391904001c244204030550040000c119a074699501110320b4030801d54015071034110141c085000790025800c5070342c0041415000205110410340b00c00d0254100707a81050402d40c40d0500319400714011181d158000607240b4405104c280a112002c03248109c02c021202019081414121445480100d45005039000b240048543c44d15100d003603481d403824280315 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 232301744 1250 232300494 232300499
    0x311090303030f06060c150912090303030c0705100504030309020a23012610090b030a0b010b07030c17040509100e0402060a09080312090c0a08030f13030c0305010203090f0106 77
    0x3a40c0c03031000402c00c15446031032101007440341c5c4844040d101c5100341c28050714000340e032107603900d5402c0404860042c0c19101c0c40540303d9409041700211841651b020b0050f51455454000d142d8036035001d000121498810000c9042e8220300031700c61640a18440ea90200340d100c86801005001ca40d1600301c8a200d5602d1a5035007222180140100e00c076800030300380b5000b00c01180c10400c11381001054104c0c1c4020b40d0744c0400010003050541c1c00c09450fa404410060310014078241540c400040c1d000130105080c0034014002e901003100542a4144a403078004002e80d10340d40c80f003201c01e80500d1414040b60f0082003e00c140e1034403490b156449854000708100701c0340ba2040101d200c0d400680041d01070440000c0c0010700710710a0072000090000c5408480c1d50700c40051481f40c2c404001c40304071035640140c4407407882c0c604d8070091910491352020001e5052400003603022907035520440b005444007078010000400a074040321b8400055020b0000182c0303070310f0b00c0c0c0103250810883d080c84011691600d0b409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 232302994 1250 232301744 232301749
    0x1615020313060c0311091c020607060b010207120b060d110307060914040b030a0b040503040e130210030e0604080904020c062d0709182a03180f020409060b130c031109 73
    0x20f5a02c008030447e10a8501c003014500e070366071050020800394008800013070780018001580c2114465035403c1e03003281d1003955903d8044001c0048000c005001452400201304113281444440d0f068500038000c481c0314502c801c00103440d0541c0c50b0301c28404101340c0c21007003207044195040e0345102c040a07501030000d410b4090000c0d03110700384804008c00102115002c42c00f4044d040095601a003400450364055090801c1c401900340705c0d0420481c400d200d030200342c1c02c1e054442c0c000d0510300c8041800514254a42d039880c0c81068009c03050141d0015401d01400c426401c081003c1030003041e24440d125140b083c1d120303036030303101101614010184604100a01280a078442e10316021181481e9110844e26070b00b5a501000d45510120b0b01d69480e22482081e40c008450400650254103d0301e0810a80c01c40032215051085403060140c10031640380c204402600f019040f0085141c07040e400016080303194400100d11055421203005031a5031080c3c0b000e01a078051140e480c1003407802140f942040400d000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 232304244 1250 232302994 232302997
    0x30605130b130f141c03020a0203030a0b0312072d0203030a030c0912030f0801230607020301110f072d06020705012c211615020313060c0311 62
    0x4054180702d05001c0501c0395000c1e0681c0c40c142c0c0500c65900288000d801c40d90b45508024200100c3c6000801e82801c083c024400c841d404581c3d50003450a41d03545400400040000c80101a0513004200303c0e2061000080000c06010b4030800b41d06000290820f08001040115000c4501c1c44081d00b0000001d81e80000640d800b0108900c7c0c0865401c82c490812181d00030664010031100140c2d5204030101500403a40203521049591441d48a82c0d0f1000403a0a12039040d82400340344440c00004081d5040c0f801c018410580080d0000c581c1c5220703000522044e0340101d502011464010921030104100c5a20f4100c2e59203d0000c95006826006244549412401001081c0590004485080100170b40245140b0710481a06248010098074015102c00b4018401041f50086588405092401106045442c0503a40c50f1a0a1101c03504180c0c2054502c1c41e4180c3c0c0c0b08181c5400740a05901034002503201e550b8000c02d00d103080b181854034400781c076400030006062505002001061502590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 232305494 1250 232304244 232304251
    0x503030c0a1b0905070e030d0905090117030c06070c02030d021609180c06050a09060327080c0102070f060b06030402130b0d05060a02040f0e0129040b13030605130b 72
    0x18580c0c01408810954494002d0141e120108050415041204241c0c001c141920100c1054090354a02c0140e4401250210094054240d01008610051242d1a0b41081c52408107020303a00301e9142135041813481c0d00d440011180d840018420b00c82c0d550071400d061112210b0001140010181aa080d5080564940f214000c0c41c802517540c40d1103005074031605000350459034100caa03c800d03041d21008024110b501108842011031000d20001170110301c24800c151809400ca19803d00c401610f02060710560388025003592030b01800d1040c41c1000000f1b2004003000c0e4418184031821480c02d103004802d560340c1c840f940d88515030510401015840e206a0401c510768146000100f55683c000014030f5070b00c612401401600c2881e0400604103043d50040c0705032501504840200b40c0d0724150044052401d0140151070801100c6504c0c00c01ca01d0701c802c101c01c195444003142450740740c000c00346042c0c22001c03445c042c40345400020018030000388655134000385400700440c9101110340b244040c00c00c024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 232306744 1250 232305494 232305503
    0x6200301081209040f020307030506011112070215040e09030403060c080f190f0216050c060403150509191505090c0f060c0c0a1e05031b010305100302030f10060503030c0a 75
    0x514074010341d4640e440304200c170701c80c3d142c11900c904040d4401401890111840c1d400b0900c8000001d00116000516540002903030142c245412425401d100c180300240340d42c00645201400040780c3c01841405461040000341d0096844034a18149041070380d40825840302400fa2050a01440c6400c180f07859500ca925100c5821110440750f460a00924140304101c0140348046080110302001000d130010031801070307044070761040b484000c021041c440c0e844010010072100121858403c01ca8004c0355000c8000b1082d520307580b01d1a440301107100301c0f01200b1240c201460481600130b24041c450b0310307000b4a101008211040d4107001058404a010000500c68440812140c407103030030400c0205500400a00140c100a5a079802003601000c1031181f1010814840b9000c601400d00044c9440c3c503c0c0103d034134280c1541c0b101c0c015002000d015119100c00c00c242c1d80d010002d61001c10070421070b5285a4000e080569002103e44100c850340e0700543d210780c00400c2002803000c0002800400640c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 232307994 1250 232306744 232306747
    0x30403020a0c08070501030605030f070e040807050a030e1003091509050102040f030309030506090111030109111204050c030c030601030b0f0c130b04030606090e060412020c0d062003010812 83
    0x11810141e1619070300340c200a205122000021800501c0860103e0480e002a2000e01c501a2034074101170b250303800c0700100d0401d0b5100050400c6000100700400f07411502504219240c1000303502d5460500605040660100d840c81c9a50380d4641404141404801c2a07440c04010170003640c2d94100c07610303190400c0e1601041d2a402c6000600100303504980090612544e141005d44d42d0780360203411090b080c841503400340620720004401a0b410300840150a8030800c0c01c0d46583e081c03010317072001000169014440c4030070611090401c03042d40a0660701540c080c00050680c1c7c001e0b80109454030410b103076034500a4021000404c0041c0b555003116400020800c010351403965200c1d00c0d0503003405208424440c000060200180810f81400104180e90240c0710a101c40d64440d0098002e1b11014045074605901800004011031800884030484150790701c10b507402c0f1034103d030024400f148002400e07034440b0b0f6104c068030800c081644002e4002003406a2460942d8034204499460340c1461903c00f0b01c05c0030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 232309244 1250 232307994 232308001
    0x90406050705121503070b0c0303040204020a140715051602060a02031302030d080f0703020c0316020a09020d1e0c020a0321020301030b181c050913050c030a0f0b090c03 74
    0x82007a607540b0028002100c29a141a408030064001e00c02e100034000d00606c480031a102144404440301d81c0001b800951039601e8a0b42840001d40c4100b10f19403c0108096030341c0c605821500007800700a000c4d1b114103842c1c0744606c0c61202100c1000d0500b00802a09554040080d42c001c91415132001044800685035900c040e01094091280d90000b035042c0074407040316a07400c0e0403042080c00703280f40c500c041045a90b02082a402c030b00c504903c00d55503a10500c80c0e00600d000103420410700c0341c400346c01e070320016030344106813070a070b81003003c9019540c1c0d100d40b00b1204160140c005c400010781c2c2032009000803103142c10083d403184d03201d000103010010760100c2d06402440348041e0400c1105802d604650341c5d13070340e814900b0241c0c40640700101d000e0340344501185c40c01d00c0010010b0800010352501201b030510799070103803050340c00040d4441d0004010006154100c14a108141c440d07041c2d00d01c299030320b24024403194221540300900341805460444c2090b0641c0307544d134400d60300c106840c000598944 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 232310494 1250 232309244 232309247
    0xd0209040f02040903050a0810030b1303120e1b04020403020105220e13030e0111060109021b07060c0b0c0c0d050315041b12020f0307181509180b0904060507 69
    0x3001c000001e90801d003481e884904241d409401403c811400d65680001d03034940001c1e01d0404400ca12010784151f241c4e0000c50b20f414018609545254800d04041c2000c4140c05004821307a0742d81a000d13413446d00718030041c1c00003400200070601995801c1b20118541411a40040c01c1ca00030604601403411740c0600088100c1020760002c0091b000c0300000280c00d140c22030706d0862030071005408500041c0c0700901c140c05540a000809403c010081c050702990b800c10fa4241d000750840e0940c0030032000304032100c0010074070520031039025020340d9550141414003410422000c440c003601000f120b03e0200708080502c6000b183d1414450030a24109a40b500c3c0e6480e60201069110565607009103000003d400403500740440c07501300c407600c1e103a4103090f0b10308906090890041d42d2003124200010000200a03d11501e10380c1c1b00c440b4100690f0600e180c0b98290717501c035681440e0340c070404a403d100c030520090710b0700074101803400c0e1340b0303d03040c40100c2c10040402e400c8800604010101c1e520761021400c201d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 232311744 1250 232310494 232310513
    0x5180106080f100e160e04021203160b060a18050103050d02060c070f0f14010902040e011103060f0613080105010612020406050901030c03020f0a0203071e0b0f070c060c050c0c040b0d020904 83
    0x207601861007010058840003401b00c0c08400740c4049100388010320310b0700c40408011060722a071a410f00d2070b140400c20382d40c688400c00c4900400e8654854668800402c4100348000781f0840d6400007100001c03d581103103015468200c2947c020000d65100c03000708200000000704aa91142e441540040da04911746000c01d1000c80ca00f000420728242c3c10740c141d81c2400305600c41004607000315800d01c102c0c40715001a500700c0b8500f040840107040704100142581c1171084c0e00c0e004240c005440103291074000713030142c00740400c1c035045410141d44580040041d00d500407110349540150701011443c0500e480005003203403140005081c10301d901c031142c88107524001e0741503a950f520300101c01a03544450000081d00d940c40101c04456511103645281d000003a019480203889501031740461042d21440034009000100600032010042d0f1f0061550020f40301d80030703480d5002c8880e103070541c03074142a00c40603007000c1c600c0000b00c0c015880c010b54120159104440c006155405580c002d4503910fa908001102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 232312994 1250 232311744 232311763
    0x10b060a120c0810170a0503030408130b0412030e010e04021b01050f06030d120b0a090605130504081806070812060a0b0412030e1305180106080f100e 66
    0x800030500c0109a504240c0754482030800c6102003001456005041d41d00d4203041d0740800310440d80c0f4009018091640c000780b41014001d10440c3c191141c0c5686080c41c1d90710850742125000004900c10355049400c4003048040d08040a03518141820324040902102d180c03c009400c100065003110580d901400303520304002e1018000391b65a072b24014045403034220380d1000030519031030400007031004c0c1c1c40c820085015060050260120003070700401240c545005031050f100f07469903401c00f0780407a51542109401844240c5000c158246050100000020b405810a0006080c6402c000000e201d040c2101d03416161001c1c002724000480c004a94240120840104107000c001042001e000c1c81885083c4968401c41311202d80580303800650205009603c50514120441e10381d03400040e0082c0129400c0e00c4018112482500c1c0c84944441500c10a45800c00760750b08401c44178031030310006e0180c3e00c080c1c5454001490318080b500c8031240c0e104a151491202d00b542c60100b550a0380d0103010700180e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 232314244 1250 232312994 232312999
    0x1106090d0f0516060306030210140f040e07120c080609090f07090509070605040e010509040305120a050412030c09050607030306150905011e080a0504050f070e0f0630010b 75
    0xd1005161405640c0e642180703401c0e45082d0204000095107174403074014881036940c0a010003280344803140060380d00054560210403e42d00074000c09100c90300c401c0103040145802c01c8a840c1c0e6040440c1d026041c0c000c140b5400101e41d0030041c4c0000c445402000d526000901516a03001903612404080d0406846000c4030680380a15500000e03045000d1704098018089a4243d56000788e80d18002e8075148030781d02c03550401014400c010400c901e041181c1e140d029000f41065803a05840302c0c0c140c0758011040701d4501c4500e40c0c40c000c3c4410302c14504d04a00030300542c1e0404000038a01110094403070300340c81c030825103c0c0e01c0c000750b00020544250440c500420154001100c4aa465000500041181d0241c94006215244408840280200c849205140c0d68031402c10307540b151b0700c80b007020b018000c000340d0340c42c031410804c1e003d10002040000010200f0802d40100c03400c2c421652240c0c0d4901909a61007081400105400114450805104c00c103445915160700300440c540c00780545031440100c1d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 232315494 1250 232314244 232314263
    0x607021009080d0302040f050f030a0b0c2503021002130e04050102070816170f09010f020f060a0b010e03121c0f06060906030e150c0a0c0605070905130501031106090d 73
    0x2040c5400d500540291f8500e5092081e545468009120340106c41c885056410b0b488103c01c3d0380414100600c0f1504040c0044580d403510b40040f001000213800361601400700702c151a1101c0602d54140078070100034080403c2507140c400c003e1070240c80c405039800b500034001c032841e000c03408000095044501c0036030301c40a110b80350046100d00b024048005c04055807140b01c525411400c1e41000c01c1140c01204040c000d403428241c0318001185d4081180e98118198800c2030040f050f08942009020300c61150440c012030040b031900001410300c00d54914150095110790180b080209004041e2940c0c1200c60100d0003e8918030342006003d81020700d0301d0f40040d0b03e80200816001e40c00040081a40c10303a80303007400303494a00d0b000302e0b83d620010000000500c0c010000304410284000060982d40f40341e291154158180b611880c00b00c45040d10010082490b81104000d50302b01114404c0d00000500010402c6600d540c45002c1c060100201440c89a240041c100c0155911801c02c18461078025080c4e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 232316744 1250 232315494 232315513
    0x10050c031e040f0618091a040e060714040f270509010501060f05031003030e0103020d051518070f050708072f040b01200c0d15050a060302060702100908 67
    0x2058107070310034001d1042c0b03074200711030100350384c1d00070b50741010070b000001c22070b00503c0c2c41c1610010081c603403c2c29259082001d030541d14070550700e030300400841031281c4001e06858204084081c01054112543d182141814481042000c844209202c01c5030045100d94444400d2030201c0c803000d031050411100058074100600080c0310055000c0703410b8070110f45030051040c4030034100b41d41c280022a1191403450724544148006445080b880e03e1020044c1000b500300307050340c0c0c071001c00d40f4011034041c4071200220101b4035a03481c2004000702a101c07540b01b05203d03410468001056068008002c00921400044d040d0410200c10f04840c01d068021820103008510641c0300c80821101c4658010301d642d202e0760340011480c2520400d0520795050310b0f1901c1c1503805880c020540128410040f0441c0140c03034032090b41c0d03101c0440482205110300d6021025203003804590b001c0b560b01408140700c261401d4400d000580700c00040310070307880c0c04481d0207003401051030084030320340003079000080940640000c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 232317994 1250 232316744 232316797
    0x7080601030210030b130e030c07030303050412090b0f07030c060203090c28050904060e0111030f0c13090b0a15090810050c090d050a050a12020f060610050c03 70
    0x1264180ea208403442e4101e40c03583e001c12020b036041c01078030540c040017100038641d0304110303a0300400205031141c040d00c0c201300071413900d00c1c240f410952080c0c000c0b0f0744610070031040140030680f80c40003c00d6801c224100780e0410b8042038184c001d0403000034020000081e030009041c010144d0803522a4040750030b55480c0b4001d08010344460300000002d0042d2038516400c807000d0407254401543c000d40000905200d2720307090400004480181040c1c1da240d0b514880014403500a0286003408408003040c03556030700f0a21405224a000100401d000810912924412007440640d42d0103c401815011991841550026220070081e1744252500e03050000c0008225400207070201c1203c0d103e90645100000951100c2c0607203001726211130039174008001d0706131940b40c5405d4913051180603104030360011005e541c0d4103107400b10103002524000142026445150341c10001002c90f0262a00600000d007403c0000c82c0c1c0100400244006025021642c2c01c50760f2010000d541080ba00c000c4c1e104525001d0412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 232319244 1250 232317994 232318003
    0x2107080712121b030b01050d0203040303060303110f060f070215100603060905040b0402010804050703060204080a0b0a141605120a09020f010206040f08031308031005091006050414030304080708 85
    0x800c1c8011800041c10814440110300c00c8000c0000100000070b09801210710840c0103040b00d4103d01e0600400b030050908000d11480074600c282e03c00c4c0c8002070518198240548200c00001c42c00300c1681c0900c1d07803008080e101045140c1c200c2c0c4860940115600c6810051341004502c41c511001c000035001000780303201c0d580804000301c03007003600d08201651f01ea8840e20161a0b0403a009080407150308041001540301c5c0301010390141c01042030340c2149071241d0f03810081c0d034410303800040d4540c0b01135000303014000007148942c1c20101d00c6104000c0540924904129080000c0c40f082d41882c40140400200c2e02034800c41c1c1c1c0c0d141c0c8011f003500b40e030318020018030002e103035050040c0e000d6408000007400c0c079400040c2240c001c0c3d8104140984450f170130341d60f1502e15400141845411420f50400000081103070000c0e50290211265922450341440207001c1884401061450f0300901c07071104210054014085900381c0d070000d80c4c80e080c07002c00500441c0c03035407045a03c40c1c002c0b840780080000b440140400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 232320494 1250 232319244 232319273
    0x20a1b0b0f0a020a052a0604051f05091903030e12040e010b03060108011404110315040509070515030a060e1e0a0b06040b210a090308160221070807 65
    0x965800700e0b445000d806000c90281c004c1a1001c6282002940680d140c0c5800142042e082c0900c3c10350320003262401d0b00d00301603041d1800c403202d6205d4403c00da0002078003d821101c11035103180401070341c90031f4510300d90340700b491001000e405600d06080001b818440d40105500b950882d08817810440e900310500700c507034054420b107107400f82e44070004107802180e001164065030050352a58072690070b00096001c0d8034055a14254007596801d250034080448801862051442c030152490004400b410700064507801040c80300c15402071030040c4200d965510364407600c0c0740f444241640320758540118000038803042c1c00540d10404c41c3d10401c840b411201c001084221107550f14000c15483e030300304440513100d00700c1d0705a034007140a0106002c45e109a40190110317403003419220010752004d01d05502080c40c01c1e190150501c1d10707400100d0515811002082d000241c0e40d80031400302424101c02500c414190503030b445140d4921201012010042060310340940d00400c03006c0c1e9480c0710745420f25001500a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 232321744 1250 232320494 232320511
    0xc05040608100f0510020f010501060302071104050c1c0e06040503131505070b09150103050304060f05030417030403021f05061c03020601210501180203070509010f0603020a1b0b 78
    0x440001e41269002e0001d07404580070005003071012400e044c108203000043c4403020381144541c0c1e034140c009a00034001d26000b04050f0f01c00503940c102c54140b0310882545200400e02130703420f100520140c4d00800d0700700c4481c0c00d25540700b17032074512400d0a044050300003035200109a01c242d10a004c14048040b004000200b110100c05103e44e507106841c1c04807940e903418042c045502071102d83e0200b4031141e441075000201d841500c160b0540c08a414810a400303030026502c560022500703000058100c0010380050074103040c25801c62030103542e850703041001e811080c03812900c040040303820103000b0048a080d0112001d081c260840c2d9510380b16004001c1140c5e654410071501183c2c03001072000c03a4000c03545680580c054600c60703080540a8040045501c1d4440e100ca8480040360007182d82031082403030342ca90f0555a4504c1100600416181135001d4001c6031141008800420032454001108000c5800a080c00740e00d408021707406a418603485a070341ca0094000740044820451255509481440c17403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 232322994 1250 232321744 232321757
    0x10c020d121823060f010915050d030c020109090213180e070902090915090a09110d05010228051c020d090813081903110708010e06180a02010e01080a06090c050406 72
    0xa400302d95513804c096461550401040d0700500080c0701c1074118014107204080c004604039603030004101e0b5446241000e0b000500e0b02040c0c4000c541c0e001c2e9040b00201410801541485501480e940f036081e0749201c1c005003000e00c0344000008070035642000420481e6001544d00e0316644140150103076010240c580d12480d075510019654240c410340550110801402800c0d45070f441d0140c0c2001008110802c1d11a410500c030602d40a9484000c5540102e11641c000342c1c40d440e5250f41c240031071000134184c0000000000b402601d06602209981a5054002c0702422490041c0c0b1503078001d01c20025030104181c00c01c8030f800d091005400c018056800c13075800d0f8007a03007591000000e8480c4440e144400510b1b40c0102d60308080f0307200d03003241104a814042a1a203843e80c0d29003480c00c44020b02450b1010381c004608000780ca04c0040801c0e40c0340100c01c80905003806096000a110f80389243c032041c1400981c41c08282d0f2401036601040140600766810800000701e840054400e030460301c500c8000500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 232324244 1250 232322994 232323053
    0x28090501080d02150403050d1a040c1809110306010507140703060204030212150112110405090607110718050a0902030d020102031f030b04030c05030c060a090212010c020d1218 77
    0x11301c40007244100c0d05a0341e514146041e0030707505030251041c1c01e60142c030b0340d0200180342c00c00d0355680b00e0090b0158154480180c2074000340700d0041c1a8110b6071080b9491450078519103180c10070642103a500c65024a01075a4490040c60000ca00310850701482120348148000441004100e1f8000c4c02902c1c002c0f55410385481c510f050f1995501d00f80d00002c000160010300400100c4038040942c900d1a1041080384000c082c003402040889504884903101944890280020700d038220340700481d0950301038043c150306810301010305440350310326000b800e416941d40d0001d210880700c4d52056803425030050030f682a20940b454003c2c00b030340065401c0b0310b10141d04490b02000d0404144104d048962140e07030b0701c480307590b81d032415101503140d44820f1b01c00c0d000c10880b00d111a2802c0c031400b403144488080025002c0d036203006100a0f0301222000b01071980c074052a6a1f0a079800042e00703600d404080c03030070140841540261501504210343d54411100c003800800042021302408695503030300ba0f0403803540d040e5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 232325494 1250 232324244 232324273
    0x70e01150324032019090b0604030b04020108071b050a1b0303020a02240c0114070804021c0309050301020d0209040c020c0607030c0c05090901050613050628090501080d02 75
    0x2c2c08000c000c003001c150b24010400207840600d102211400603954401000001c00030500300035500900e0051100f04a03018170110001c1d205507915110180c80403030800d400c594400480c2c1c035010744040e05102d8803400050003244504080541c0c000580c0e10341d0040c901518029684061a842c100e0b100304550350182d407100003000d0000d0451750103600034150709015400780b0200c0c20314140c00340d04118030044840c5441386100d005003c2c034100d00e400041c00c040022820590058051301c82820801001c0c03d010150703403009003148110b9251f2140120307031440c524050300d20181c0ca0740840c1e00b41d40049402d034881c0082d0b03400380c000e54800f6142403201c0e00e24110201c0e182c0001181c42ea502001c14040070002c41d02c241c0544811034030030702c06641c002c0c1e1180c00040b2001c00480d600e41080e17440b04100062800e144e51005002c00e80003c0c140181d007000c8000400c802e20212020300244940c10000800c0106401100018401010100010b5840b149115100c0c80d03040024030144c0b040321030b9600b054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 232326744 1250 232325494 232325531
    0x903010f0509031b070816090c0309030c080307091e03051606140a0207051302030103060b123c070518010f0b09060d0606030f060503030c03030406090203070e011503 73
    0x15854040510b2800c0e0b148522040401d5081000d03a0702c910821701d0104d052442000964804242c260214010f9031030040d51009441c0d451454004040c1444603090000b03800100420320f56070302035840ba460341d5842d03101325103051680d881101c072600c0d1034040d40c400c050500411410f4a018034151081154043d1508054041c60301c00c0314006044124011115010300028140c5502203105130781c100d958403c001550100e052104060040d40040100f041042c10300c42e84001c110142c40140700f0312a002a400e4981c1a03903003603c0b1003528080202996203541b80c10003030042040d946003044040480a4041d030b0703104d0310300406000300000141c441c40410308020860403980e990f124402c8007408d0648002298002c250040e8201e0824800d05c003c2d09824007800c0050029a540026458155401001034401a90185020350400c00c15585410008012258000e42180300416030308001d101283c54000f1941c0030042d00b039080000840c21024100c84004003021036601440100c284c0712680d2484c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 232327994 1250 232326744 232326751
    0xb030d02121801140403060f0b010e0a0506220b0702010201141312050903010e1506010c0209010302040207080408030316020c091509092401090c03110f0c1e01020903010f05 76
    0x1806001e0080d2258442041c0e02e586040406240140c0c0d044003880c0d2100c295042900704035000c1e604c4002441d18088588102600301c802440e01e8080c1d02103640c04605005882d001e400e01403407000800c11420880b8445c034482000443d09600c50559680c40c0c4184582c00000003203006500b001444d40d2600b14180019029400c0c6042160040d040c950714107070701381c8a00c1f950006000b41806400201d035004e108450038515a040a081318602c0180300b1035002c0c00003400300707041c0450102d00d00c01584903058543e06480e4191070042e590941c0781442e581314000ea50007000d1070302c40007040254552208400468501030b5400311240139100e142000358110088540000311400d03000420400d142200401760080380e910141d4422149540b0080d00c45403001c1030501030903019800401800c035603031140c104401c5082c07904010780c149100b18441c50344240740f01704a60b81004600000c203107400b482004d100e140341c1d26600c9040c1441231140f501075040070b07544520035440d2840c1a5118003150142c14071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 232329244 1250 232327994 232328023
    0x1606030212010b091807050a020616090311041b02160902120703020a120204060c020a0806010803030f0c0d0f0506090f0c0a0c032006011505091c021f030b030d02 71
    0x10907820300d10f0f186020b070000c07a91036500224203051070404107600f6403001c4c00740d08a907031006c0e42c40c665101c0280ca00340c4060110900841e1030941d01200652003064802902e0307002d07944495001440300040d01038a04900c241c0d94014207585502d110580001c0c0c11600c2c04017440001c1283c80d03032060142c00328007880b007002c0100d000a80008060f03d00c02e074020204802182040da0041200c00c29040483c0c21542141c408901a40340640035131400c01c07a10300040005000621280d81000d00880e16804060105829a401c55001c20101307121070301a201c0401000100304a10070284184c0c401400040e9000c0f0300490913017006c07404441a0499035481459010070052806a0700340e0101c1d0a0402c60005600700b003041c0d0300100d6400c2031040031801c00d1540c02c0c0248881d50400c40d03c42d1984c84011055001c1c05800c01c00c0c403c40d44c46041c030039a0203000c031815066100c10a4004581c10005901540e46070807000805044080d405500102c401c9900750110703544103051683c141c0c2d40300300b0b0b0b050000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 232330494 1250 232329244 232329277
    0xc0430020108040213060308041805090316241d0a020f060a0e04090f02011e09050f0117090115060207030506180c06040602030c010f060e0402011d1216060302 70
    0x280594000d022550b00107102400040c28221401200c10071207000d84c0046400ca100010304100f074250000102600b151043c200300943e04014010a58a00c1042005a0703807074a5100ca03241840707501085011150060040041c4c000aa0030780000100705e81c203034200c1811102c0308121101d400c0041c000844a50180140000d0780f42d02c0100400307074100c0e2840c00b00708404488071110b035440350b0142c809180c1c85890008204070180c0300140c84552201ca800007911183c041550b841503000c0c03045012500191859404001100012110a480003c401d080c0981010510803040c505612540d10020f000611011454540384200e88500180c170001e88035510880c0820100346800700a203141c0c1c002d03134007114003200d448400304003150460313401b600251b0000b248040c0005000c0c0078268201c1c145a401b00f05060404901d240c07049005400a0304000710f40303500b480c1d0071400f00014003e051340142092240c1090a01090340c0d100707246265645e02510802c0064040c2c0203000f40c1b201545000e0031030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 232331744 1250 232330494 232330589
    0x50706030501150206070e040e0d03090b0601170c160c06020609120408070b030c1603121b0507030f0e1c021305010506030c0c0721141506040c0201090b0c04 69
    0x407035074040760740c281c0d0ba031080d070f00ca5440403a100c9c10041d070b0b00e40032001d0301c0200c1e08070b5090804000c0c8a100404103410300c107841d448860000c821000d00b43e40400308129458035142c034000c1e048249010318000030700040f14540041131054000809500c2100e1540840fa0981c00b400000b8a1a020320300c66100668850001804005199000385034040e80068130340707040c095108542c608070300c00c100055003c00d048109403c01007459000d6644002d00c1d1440030005090b20940c020044c1c4a0110054204040c8110f003000702c03886818003941c0290300528050030346007000c200c1c5003602c0705041e00b01d106559911549000000ea406418101c03400181068196a0b44402140b0168001010f51001c1d000350781001c110540c000250400c062034941030044403c0d107a18000302c500f880840e440d81c207640180c0354041e01d1902c203600994021015a80803035141d501081c00e9015080c5803100411114041d000c1160100d0081d0161044480c440a01a44202c084803c0c001003002040c1090318000c400c202c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 232332994 1250 232331744 232331747
    0x513090201080a270c0513140a05060d0b0106091818110303120a15080114010b0c0712080307080612030a051804050a0e060c0a0503130203010b0d05070603050115020607 74
    0x44000d54541c07850300804c03d400c1c2d03000e6641c076136880c80100c2c5d1000c440c3d0b81c2172003207003044142410845000c0404004000300d1142d5081c40d0b1600500b00010551640b0008080c2d88500511401065100c541c0c800c0c20750715000041d20082041c050702112128040000e000d03508580a0700305030284141c0da03e800801e0320383702d1000c0b011540200740e80501c4200000307452881c160323881e02d01c039000040000625018144041c1c03101c1400354804210360f0706000321031060510401d52941152004241d050383c561a02d1422400d1694603070014400e8503500da80c1e4414880d014005510489556548924540e40c26041050650a9280c0c0081551082c400042c01c0c602803001000201e28444c2c403940c00d862020002030540b202102e854010310b4850007203000c0c00c4e1042288541003210385000600300741b1303100f500800c140802081980f1410020032036400b5503d00303602c1101107900143c058120311040c1d0901c5580c4803524818800002d18140000928968044d10a010f543d490b5001c1d12881d00ca0510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 232334244 1250 232332994 232333001
    0x160e0f0a09021201050f101d060a150c060b03030c1c020307020a1e1502101104050429060f070311070510030c18080d0c1502130513090201080a 63
    0x8500d10140c0d01d805a10250b41c1d0140601c850303c440500124042c54000c0303500c4440c080c00b03401079564042c21031003881060f203420402c2200c64442420320300540e84250004003584501d40c0084401d88604907041c011960141051044600070a000d000703002004040c140d40344510305006041c0d4119a80040410030642e00303011140d1750520490f82030542940005c0c0003404281e000441080450b041c001e1880c22840443d0b00900502000b00020010309001a407645202e00c201384041c1d982d00b6507054081904401e54000e400080c2c01008200c4c01d0070708105a030700c901900e06101019501030328941c0e1400000300e41d40000000282801c08160341e400b0b580e400800f842000b40350183c2100072429488945200c6a06011a42d000c9010202c0c2c0300302030042c1000c180c88070140c0c14110014400ba0340c1c001508512100c0034604001582101e04120011115054048554500000d048020411498003182c103541003210078440549461091500b02d8024400c02030119044400090305c80c5425407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 232335494 1250 232334244 232334251
    0x240a0807030e01022a01050f0105010c060912021f0e030904050408160302100e0c091303050408030a0c03090506160b090309030609010c0f09080a0602090607080c070602160e0f 77
    0x1804504482ca400e1014266000500114400440341101741100035070301750b600e141100090020010f42c18090111945903905004507814030040b95801c00800c0465030109540e1500412105940700c0b60210082d201c0e0241c0c0400c40d6280321207070340c401d440f046521401001900c980f00139072604d00c400781880040d100041c001d841034501889030b80c030307207010b40c200c0d41400702d2080c0c1c00303030140001c07051155003100c2e00001820490b50080002d2134882d01d40001ca540c1000500e6580c1c8070035a01440d040b076052240342c115649500010403014040d98000b07644841c0103101b920303a40d0015495a00380000307401000c0c01c000c040940300d0400c00100c0d401640d030581010b407207c180c9103040d54034400f00b40740c503009492007202c4d0f030b6440349015030307190f40440c1d1000c2c01c0859140850354140340030015581c802d40080081d01c0316900046c00d28095942c001104e180f00c0e40108543e4881100c20129a1213900b00d100310009070084800710028480e000380e40c4015680340080c24082615100c08803481030070002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 232336744 1250 232335494 232335497
    0xf060609152c060313140712111c08040810020f0a0f0203211b030402101d0d050a0b0108010e0d052104050d02190804050907020a02041109240a0807 65
    0x201d1001090386510005610500720044605d050045070303e000a03610102c020030400b80d4010404c00d010001030541c0300401d2942040c50b0b01c1d070340c1c035180000990140351a2030110980d02060201c80802c0540c034054400c4400e20029a00c2880d04601c116040e482101c40f6011b40103800c002a0002a016000042c8500e001d481100d003030030380d01000c981c1c00404200c500f54503824088100b18880146032490180b4030324940300c0a045040a50118405000344030004092220000303174180c6429140d5961041c0440040904103103181a05000d07864100f40102651450311010000c40c0d0303d241409088082c115080040c08864081d4104540c1500000c40d43e15144035648d0307000c4169011341200e1800b40b0f015202420802d2a441c1d000381c40e00c0c401003000d16400301d4451a40c0082580882554122501a02c8e1304903a907481200c200d00703242d143e040083d0b21500d00f02120180c0c5442e100980001c07001034400b0072104148403a54031200201740285041000c003000010007581c8035002440e000b4095 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 232337994 1250 232336744 232336817
    0x1050327010e0d02010f0f0212180a0b04060c030510050a05010507080c0604030f020d08010e04121b0501050a0c05091509010908070e0609010b090f090601120f06060915 74
    0x20100b2950a00c40d10300e40d1440107130346400f4809a0301440c1c0c03140302d00510300c204046140c0108048507100c142c400810241da0311103500392050b1218014002d04410355800454035110b40b4040c5050b2005154580c60b4400103403501d03000949046004100324103a60000f80800d10803844c1c4401156103a000078400c540203075051000c000071803820811140100e10a131140d50110908080c020300c1d10090704044800c200000004028030345521041c80e400a800c0a0590b1001010000648070343c1c800210504045402010a009002041d80003600a117400c400a00201140034000c507124040d040546501001c0156100170a01c510402041c0300201810413400f15a5036044181c100052613003c544d41c1d80f0f0580c100702c1189808801d907405403505500725400c10a209010640c0c842044041034000c0860f20085144c903809035403100c42c4039418080c1803003010761403545280a040c01c0c3c802e0030085140c05001086061400450624050503a582c041442c50454280070b425520700e010114541c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 232339244 1250 232337994 232338011
    0x9030809030c0904080409050c180d020409050313090f0e060c03040302070308030127092a051c020f011e0c08120108031902010204060c030e0402040e040b04110105032701 75
    0x150b000c3c0d26846036018030a1182c8881c5407014100035907000500420400500300301010314414a0b0005403503e0005440c400d0301801c003032001c01c0040068860150517844046001260606e91692050960303455a0090280384c3e038070251041503820b81e109401c2160410b5002030000050300005d1a8460302030301c1207032016942d07a112900164801c1e004095840740800c0c04031381c5680e916140f1b00c402001d61400b08001039554881c085010031001100d1070003038483c030b0071220380c1d15094102e00241c40002c1414111007200e00041c10908440c00c001c034014610901c90450660140712194480c0c1e00c0000ea009600050000c21100c45060400460310050306101080740c184050ad00180684071140055903204042400200525001103000c02103a00401061084988c40010000642e505041c038943c11818031000130040e018513040800e00c01048002c1005101031081c0b050700950050400c1d10200c1c1c40f0200450f281e10045800300c0480c9610800350b03288045500f00d40c09040d0703200000051010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 232340494 1250 232339244 232339249
    0x9070506030702031305090f0105040c0314090d0905040203040201050319061a03011d1b1c0e06011a070b0606180d060b01020d03060f1418070504060806040b0109030809030c 76
    0xc10582d007080060380f000c5000705542410840b801c010700381c215051f00c21b07031410520240401c1c00500070305000c5c50300c1e46898005030b80203410494641840081040321850700c006059600d403441c0021000050280c0000034882c1030a1085034020360301039440310320303513612905840c0c0100d00b40513800707003590b0b40c031080003810080c5900e8442c0c0c0e411040d5580c1d40e4030b5242248404580c1800b986030814111000c0c14020362012265031980c816003803440c100c0e01c84000c10052229a5505000c0c90b640c0d9003081a1206412004a0107605949a01161140410030b10340f00003028090780500800180c01d00d0045a55031078400c015140c1c0c40c41031507842c90302c207004c100425001e07621108100c440e02e0702d07120302140315078060003440385440c8549810040d251409540d88110100c910644241c0d01c042a00340341c10707842d40100310001484000d4940c2c51402d1662008010f03074814452800080c401d20080f410314030f040e003d00240740205959414545065841d80901540b040741c0340b41c0e05105040300ca0b95580c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 232341744 1250 232340494 232340497
    0x5010203040b01090b012f0114130501061502100b040b190503010b040e0c151308031206040c02150a1d0c150703090b0915030109051006020601060c0b09070506 70
    0x141c0c0b2a881101c0194500440481034507803448895060004400300300540600c209201c07404800003130300400352521003500d80c3c0c1c01445822401c40310b400d0071004001804060048241c04144948020011036603160340c05111800100403103070050304250b9454a10801d1600601b800c076000400000390042c22400003900f584003074846044a0100341020441c502d001e00c540b0180b14030544051040c0910700c0e5100703888482c4650498032480e1010b10b007a62a10035002640c29107a8100200c1403465204d0400030b9580d0041c0c0c0c03000540d00600e4001038640c0c01c2600540c2a55000c9400503c0d51414000003901000b100814214007517684891203c00082a43c0c2541e40d4083d01d40e01070310104203000144000e45807201c642d10a1b41408000c01c50000390f0104112080b500402c200d1522844410001480300c001080d240360300d10340100010848991607442140141d8408400e10143e0b650ad6006a0700e43e80c091043c64003003891410303440301041100c0720565004000d8802c5d40c40c00b680301c000048a0307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 232342994 1250 232341744 232341751
    0xf05070309020108060306060616050307080c06010806100b0301090c0e03030409020c010f051303080405150a2f0910120c0c0c0803090a0603020c0c0a14031b06031308040305010203 79
    0x29840703403805000d5581010400ba08580d085d405007030146002e001151031485404880110202140c00c018103000061060b00e134015846180d1980e2010030300100b982d541420700038a078060061101140c40355110404200850304142c088030f0441c1e103031144110080859208500911101c00d044052940d01800240060240c682e401a11402e180c1ea441d801c5854100c2c07445611442c6c00c090240c5074425174440104180d140c507000180c0d41d25442c2c0300e0b081180850250300403001c03c43c10b0040103085034000f0000000315507a060445507400b0b01c000042c5072540c80107500c5000070427418505040813080d000c0d00f40b0407400c061b0301d135104107003c036021141d920492a00050413400700d1401c1014040b44a0000d10b0040e0003075052248190004800c1c2d0010b21646003410740c0011600c02c10304007031140340d01e003580081401d40a569582e1022811404002c5218428054a841da202c2a20400d1312090700c5600500011b096a50b401113032000809015008c1c0d4600780c06000c00030000f1000d00040d1720 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 232344244 1250 232342994 232342997
    0x70c02120d0c231c03290f011403090303220b01051e03031b0c18060f010e0301090f1104020a0e06090a0f0602010204140901031a250512090708031b010f0507 69
    0xa054038000402801c9501ca649000b00403440e4001304000a80c42c040750300d58201c0212202c0d808864900f0041c0c405501c07450742c0342105600402001094140030cc0a188904171140d48060820b400602c035000c060803150004083c640000c00620250038008100e000c0f428203101201c60096101c40040c1c5075801c092100721142e03089481c04c4411620520103c1802a0141c0b1414110000c031398900321072200080c1000e000d54140101e00f02c40b680308000b00750401c01d016000304a12005030a02607181d05000c9003c0d541d2810210380c1416908052088030011841a40c40324140d400c5901004029031000c1d002a9216445c0031011950391040d81d03240740204465000180d44900c0e040c40703415100b04d01000703140701b242204c0040020440248808041d41c1018403400100d55a550b400c000049950390a400a40004824400034030f41140013082548a0300d6292000c0c1d0b80e901840d150341d40034600070105103800901450200b20700302d984030708244040c072001107403009011076a44d044a508030784050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 232345494 1250 232344244 232344283
    0xb060a1205091e030301031b060203030a0209010c1a07171512012307080c0301060e0f0102210405040f06031a070c050a0f020907090605180d0506070c02120d0c23 71
    0x408c000036142d0702d942c001c04950407508010b2030b00c180a901d900001b01440c50083e000188114940c0c49020076006107a4000781c400380d80c11062040c4485d000084a001004c1511254151015038660040c10301c90b00d940c200407440703010180c05100007051000c500e10000d41d2940701038000003000032482c40f181d80c1a44801d103180e00d00b58100a004040140c11a0380c40802040140080c0da0300a00c101810329050342c00c1850070841d000104d2a003541811104502d10080340d0080c0303542403d034020012110304441c2801000600440c9004442a6100c0144510304480e0004940c103500040194000c4071424180310b81075098680600306115424212110641003581404516150301c600741c01000514100c201e036410054050102c0c49918049036030f00e0060700510075145e8030114102001a48141a1012030034840ca015000e600b2001003284034204c1d40b01e07030540e41d07040000c9400c070390307480c990703460001c2c0b8590b448003103100f01d0f04031984426040800b4503201400003004506074100e40340c0c9020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 232346744 1250 232345494 232345499
    0x15031101080117070e0c07050f060601022802040507050d0606030f05070512010b0d09080c01051006020a0f150608061e060a0302033d0f0b060a1205091e030301 70
    0x40800700142c00c4a002d00c011904a00f0041c0c2e0001642c0050b2030001c8003146594841c2c15802d14180a001c60080c4039105039051015000000b050382401030301c0a1f0200c50040641c070b50031403448184c041c10300007842c20111040b400341c5001e400464118002d4186a850001400010000d40d5030907003050000c84e403201a0a041001140f0070280c1c4603c0c149045d5003000c0c10f88800c040031920600c00c1200c1c034000810104090b00e403507404000b0380c580c0141500e5444400c103840c3e60180004440b181c4006060143c0061940e002250210703004c0d6000c028544c1e0280195145203501600605030340711a41c0c2c8401c0803030321075001c0180c54011408940b540907c881e40c500302c075900f003a006120500400c480c407400c000689001849100c4011b01420114081d0110903043e82817150800c007035036606442e0070b84003813266030a5001804100d1030300c000303020700580345061040c00d229401c1d099002840d04141d01c1c2c005202c913480079800c078200d242510f60a880421010b190902d00a41c5182985c1000004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 232347994 1250 232346744 232346747
    0x7030206100e131101030f02041409090708030d0e010204090c0509040605030c0a05010c02120105010314100c12020c07150e18132904060f0b03010501030203070b070615031101 77
    0x100148a04031503000c0da450040c001c58141c81da141e4000b040100c4d12516400180c1c02504200a400482041151590b13500c224144003803454409d00d40c00380000002044c8205c07404505c18040e211a18011844e101c5040380c01d0004207203400c0d01d02c901d95424040401c0315407590203104000e006950320383e502e0f44045030400088500d0390f071205101c0e5014110303160550315814190400c841c1d003403c000301400c00900208586e00d04140e98000c0c2035281c8000401009130303082c0b6650220084104440c031080744207240504507118403840e400800e1400314511404501c0f82c004141c1140c040041d40c9206540301415050180c1049a480102c0e500c9076904503182400d50010800d4140c0c40d084c00c1403810000d40590344043c0b4003801070100710f001410742c140900f41690502a00e504600c0c00081d9140034140a0300410610748000820b5051054070000c80c03405000d1527042e250020b028002081c41e2010060040d4450001181c425449001da907891071b240580f5100250f00849a4021000d0328000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 232349244 1250 232347994 232348021
    0x50102010b010c120f03020412080406020607020a050a0b09010f15140a150c0507032405070305040213150b13140613140a18090308090c0d120c050307030206 69
    0x107910b81040204044440800c0c05a1180c1c0b0210b01c440c100300469403084e400450280c8034540044000c00543d0f00c003c02000a018010320840d8800c2d800e035492503d0381300d03003240c64000c101c1c80a481d50b030040329800007150920015a801a0445000054000c0c1d09010102918201d4005400d03c0b01c014100304007441c182c074813142107038100f210001001420440a24101d8500400d1748040003407190302c1c83c0070080b04000b15000745401100c00031054400c810301c10b940d0b2000030a014601c03401c24020032082ea0190140c240603e50041c030b25046003400503e000018a00080c081c040000d0f90640000c442565600400d030107c030030a40d0102c2c0303500b840c0b40808175208503c240c5005140402403e20b4804030940b0610a842c60400019040c00720200080c40415031900500d80300c6060115080c2d0303011055104103050b40c825201c0c2c4080340d80382d0a9060301da24a080000c1c0d00040341945d007800240004405910b0011030b42400401284036464851454002003002c1380941c0c131070014030a441c0c07224003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 232350494 1250 232349244 232349261
    0xa05040308070c0314031308030a0204060306050d03050328060611060708060307090b01023f0c150901140408040f0e1e070c060203190b1c1e06090c05010201 69
    0xb45031000c41c0031660010a01c528000030b07001760350000f0020803a038a907501c070707071220450b003000c000754a03410811203000003540640b0442c0042032070003e00040d14180f5859049900d40c043d11550306654402044032803012051001102c440c91804010240d00a20703c100b42c05080140d543c000003402c01b01c40c2600d020400f810705020b00c403c2a080092a0b0760010360301c0c003501d03a4035001080040c2c203680140e15002c008801c10140aa080c02004180da44030072000c502d00710303c0f00080c9140740d85008045464840c1c4c0c001c01780603410100d106205030b951070000a400401721800041d4404401002890110702520101c8010a00150400490042c07a2014000d0000340d0614880383c1007070007401c2c1d0b00c180840e940700140c01591000450841c09049030812250300f042040d541d91800c803030740155200803210600122442c2c018050714a0400e180707130321402c5201d45e80040c420517041d00d40e40c0c0c0b5508106942c810f182130b0380741e03180c00081c264020800c80724070030400701d807842d03042c20b0002e0300752594103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 232351744 1250 232350494 232350497
    0x5130c02010e0c280f06080402011e14092b0209070201060f09091e0503090423010302041e021305120a021f1b050307020306010515030c0912060a0504030807 69
    0x440c8090030907034403807150092024560103000d400d1a8542107180c4c0c0d4106a42c050801c4848210000952075000034880d03108034030036030300c0404065584681c0001c0402c88406100000c5c504202250f12468400003001800002480d100b0340c150611415980300150000782001403808800b6102142403440445030001e034140000d001840c184003d004a482861080031545a29120b07200705014914071301c0c4a02c0d698080c0581e10005050602650782d522822040e03010314600f039504c0401b1485061580e1081034140b8100180e81d10356020000900b41e880c034560b4042c0100404203400808a00c0103018150280010580e210302c5c2c103040100d02504a000c0c0704150f00107d01490040c0c0c2c4510302c0602140500e18107800d0b102c00b01e04210382c003001021622250700041d048080a1250000203042c0e039520031011596143e0703c0380203200842d40000d002c2d40502a013407003c6002003290030b0240180e2031000d801e00180307225401c03c00f454a0020742d540a001c2e0790700c8041c001410380c01f0a18540c13060740c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 232352994 1250 232351744 232351753
    0x8030702090f0f041b03060c0e10021506040e151005030d0306030206070f110a300f0807060209090109090b060f0a030308190e030a08071e120605130c02010e 69
    0xe030408605104000d2001702006004c454117030446030901c00c9100036581010f020030258114480103441c0001d100207072403040320b81850078041d06100007988045440518040346446e05d541d0240806000940350b0500d1900803010070301143c41c504051284100b1a003074860440f1031034207080c18140b400c000088804c2509004080c400341c2c90389001c803521164000e00f4880407c1803410002c03050044841c516500c041032002c00a06d142480c0e01d070390b100f0f0121848000c0321800307403c0038954001c0b03100d40007070200300110149070206003400003415000d1701403c0c0c05850841c583d00014180c05090304140e1546075145009028405e400b168940d014038280d1398004840303003d10004120241c644001420030078040005054034940340807411250298682c1071100e0070400a420340c903a0000d4840900090710311000400213440340502c82440345894140f4160044070340d508070b405100007041040e01607250100040d0b00d032211090a00c1407483c0c10000100c0346109070009094464446409016502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 232354244 1250 232352994 232353001
    0x60e06041208040b0402010818010501090b1905030a03110c061303121809020a02030d0c03052401050d020901030207141b06040506030a050402011101050703140109140c0d0e030408030702090f 84
    0x22070143c1585c00c40d4090800c1401641e92010b180314803605c540d5030f906c555081200000c0c00e4005d542000c40c2410003155000c010340380fa0400e00f11508054401c0c280c0c10383c0950403000109001e92240d440c2400301d4400d5644001c50103002c20a2644001d00d004810b60f8000c44c00c200f40408034251650300e040618200c8014451307a003082c0b500c2200c4c0d0140c00c070340c2a8005104e01040b4020002c8520700c1220039420301402c40e08620180080030700b1036040b6115523800292641030741a10030352680c0c11905850b2603080800c201e0b5988006e42198a1043c149642006880045004844100e8800782e16030010240650101c1c0e05103401002801c00c103000e56024031007440701c0c2e66114290f079440068032400103070076511400101d4602e809024001d109510f0b000a000d506541500721741400354110500703155a0345e031407152000b00c900304050a0004204400892500c1070100014400d14040c80c101040701594901400c0c2158002c0d400303010319600c0000d0745411410d040c085182e204c861003800441038079 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 232355494 1250 232354244 232354253
    0xb070908160303050c160b07290705030a0e0a060c030b0301020a0903060b010c0c090b0f06070f030f0504050a08010524030a0327090b030c0301230a09060e0604120804 73
    0x705408000d040c0100410002595682006410b0000b001d1034061100c0035642c03442c2c0c02d0541d00000e403e5403540c07030203c4c00c0e03040545c281c48003d610250400c003200d200c3d5150101181c5a400c00703401351001030f44903070000c3c514900c00c024100c2d00d54000c000000d00480f640c00090100c1c2c0040505a0007030b401484140041c40d0042170100c1202d4100801046400101004079089449030310700600103280340ca0041400c5800d030344880720b540000d5418180b0039080d03008001c0c040c01061001480440100c40c5c0c03400180c0b141d1341e005060f1400c0d0400c50700780b60703e41c000600342044035001103045a40d2642000301e509403154032901201d4040f4041440c0e29501000300e5129680584084c0504c100c058498407014083c444024905840100081041d0707220070382403001c6c040d40c1c0d074a00d104c1e102e1001401224a0184154400004440300011200701c5032981d00c07048840017050110216640c1a0f0403004c03070410f004039007415210303002501d5903281c41e24100c0b881b541c110000c20704001c4408108030006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 232356744 1250 232355494 232355533
    0x106121506050d081917011e0b0313030e0d0c1502030d060b040527070e01030b0315010501140301080c04090f050f0303070e0d0209060111030c01090b070908 69
    0x45412104005150300c01031004409040254015600260b041c2c40c24802d2200103805066028011400c20710740410020007200c440e510901c21503000d4800c42c0c01000300049010141c00b0081501102440070755480301c00c4401500110b5150385121550120001010b82c040900c40c04600c04444008003000d41c1c0e01c0e2001c1084460050b03800e640d99181042440314004c101b91040807084140c14403042d62140044282d45c7c00c207105032400351b061503aa5840c2e005a00004030440f00c2d44003000581b540ea1001c045800312400260f590515a40d880000b080b61010701500610003000001443c842d407406000400c01c8a24100c2d40300d100806100501c8441e102140c064a2940c0c02c640100701c2ca8080e0900046c1c0850586005041c0c0c03141508103561114048042c43c4201d0f0242c503400c0b0020342c0a03080c0504a0340b043c1000f54001066000166a9800b0f1119800704c0d4846000312800e01d1b060b060b4842c21100c1580082d100d84014508011740194810f600d180031b030150350b028040e0104040da000180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 232357994 1250 232356744 232356779
    0xa0b0607120e031905150901020715050c0d0501080102070308240103200d0c020705100909150315060305060709060806120f030a0c1115040b130512030a110106 70
    0x810222002c0c5000b40e5038100054840ea030361905040c049040d240c5041903030741c8040a00d8001d1042c100e800140c074504107100392410140c101940008590b0300c040729000a28001384030051082c0c00340101e020403105407281a020f00506000140c1c1c50a5604001e082c90b04000c001c0d1801200b20b41010603551125031560150309400e0801044c90466940b07404010f02c8041b100c110701c0d08003c902c50480c0c0e070441d0050003c0c030000d502551112602c51041c0004010340340c4c294002305440880410098146a1280c10400303c410300d035444181c1c40c1d0780c40e00c1420590844082c0610385410003401402000c0c003440341c2050050801070752082c50220041c102c5ca0004140703a2207403298801514008005109041e416240f0742e0580340e603084c030280d0103011501110307000c2c0c49034040d43c080122241001c180c07184d2014404100c0b9420700340b4000305551640e003d0300c0c0c80e1058040b21000094240c581c12540c00b044100c00c4051612011130110041c803036081c41d00740090360380c10904204020000d448016a5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 232359244 1250 232357994 232357997
    0x6040909080403020409050309010806030c06120a11042702091c2a210c05120f100b01030e01090201050906070521040e0c180d0f0203060f0a0b060712 66
    0x4869203203040030740d154060b0340d0000e50420700b4140e00c0d000b005400320080100344c0003601d6000840e11350206044c2c0d652821440300f50455010011190395807010405940c0c0031400002c081000c41158174854510b8109038001983c510303100281da001410703015040640c16120f200110704104502c1c00080d114240768401c10510801200c0c803d090002c030f10340c200c2149052449240000b4000c0c21511483c640901c01c001c034585c60388118008085514640c20545e03a001500d0850f014200307001c11103501da8032802039080c2e100c1c0c43d0300e90000100a00c808001c004080c01c000580280c20000501500d0400f072030461144d1611a1240060380c02000741c1d0181d041c1510100d03111640d0b8a480c914011070a0f9819a07040710801c28292568203d42c0100159061246e880030f00d502e804c4a60406402068414a840d402c103500c415614208113000081080c0524990842e40100e50082402d10405403552405994030b0310410420040b00d000e08840c0541c1591002e1406009446800014680301815070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232360494 1250 232359244 232359251
    0x706020a020a1a07111902101e0f0306080a02010c061a0405010905010306140108071e09020c0a060605100215040203030c1b0126070c0302071509080f010605060409 72
    0x106000d10801078502d000740e102c0484203504031911089603603008110768070300004411030102100d1581c0400c1614440644031203c4045c4502c80e802c00ca010340c18007016100700b00e101c0316070b004c21040a118401308085183c40e04500c10811241c0102642d00e2030300186507540c8110b0003200180d0303004c803c005010f6009180003500345000341c040c2101002039448598000c0c140400805c428801c1da216604030785c0308200400c4080e01c01c05a68030401003d2041c0b4045400c280e10410500c114080e030013560826820010495a845030508001c90300105e41c8840c05501c40c6290000f0054a445540050542260301900680d5070803002503076210003907180d4150000940208007191010803d55036280621400c1d98800b4000341540700f0f4550300c642c81940080c00540b141609060444207403018020b0121084015984a42d801d480224141200b101107106000c40005d40c0380c403107043c0e49188a051303915412424942540c1c1494092001031405c1280d140501c204a250394010465045907141103010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232361744 1250 232360494 232360507
    0x9011203110118030203030a050f04080403080a02010f1a010e01050f0d0b0f04090803070e04020703050306040e1005100503070807060c171608120702010608101d1e19030203070602 79
    0x30b805072124500306000b46076644403d00415030084041c40c4034a40341c0d18100f00a64032140c0048000030180c4025000400c00c100c03e00109140c03030002d01c0c0792940750002044900d1580c1896003100c42184043e4919074460320415100d41c0c0c03050b10303201541c4003460800e00b480311100481e1424443c28040c0b040c0341da07644045400c5611644120350092200810070481a03665080110080d481100c40e80000380b602440c1d8411031500c0e1080c0c40413a0f41503540c090541d520a014840223245a0507a01010711a080220040c090f16010b03440c400c0e801801c01d10403152a003070500d8501a555001500d4640040000b404001d90158400c0a940d80007026000c0300451046c103124640310b4800d41800481c0014bc0b4081170002c4000101007400b0002a02429179032503c2d8100d08a516500420085410003148003d000340302d90084514104050b03c00445001c0c0c10b4851440c100751200100c2c2100810f41b0812220403090011494810901b042c0c4074800b141903400075100d10844800400c901e44c00300d40d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232362994 1250 232361744 232361777
    0x1203051b1b3d09050a02090a14070504060e010201050105030d05070224041d1b0f090607060515090c090607060e0102071a01050627062a010b09011203 66
    0xe0602e5891025040c600028501c141c0181003101848210030301c00158190078080c07842d40f242d920415000000380080f44080d500b080701e007000150a03100001c0e00c6142d2600c1c0345200a847c03501607040c03030b11015500c610b00179001d04030000c5030b0140c50542e450040104059140820440d410740101d21b40242c2d5015a48001901c810107050b020800001ea80302c281600000702008006584140e0201c204480784201c0101e002c0c9406c959606208203404c0340318800d226010041e209a0031030340c0d41581408000000314025412859003a5902c546800a20002c8001e40b044034459550170b40d0701c840e13070340b502003070224482c410040500c1c000c08001130b1100502c1403c0c1d0007085100c81c2240255543d10041c10041c00c002c08002e00340c03c1e1008200000140c2d881d004003124031301161404100110304070051590760000000d84c000b90840c40070411070306030100c80b030340141000c0e01c0c440e00d18624071a640010f900f121003a420b03c0c2d00602c00000180600c401340c0d411100c030680e040c0f402500302c0555050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232364244 1250 232362994 232363003
    0x1180e0c210604030228150518010f02090901090b030307032715080a020a0e06070206090d030804150b010e040903090b300c0f0f070f1203051b1b 64
    0x1224550b000e10000d000815501091010310b030741809100000d5480f041072036003000840034100810742203003010315503010788a5400480d032040c2c030040c01c603541034140c607440ca0940744070740312580c8410b40c0007458281c2490400782c0c4074003504442004221301030011010035601e2281000c041c0c24004881d00035070810601c6a07000300101c0c40402c4400b09141c1d034502c1461000380d03958403840032402d4040000e0b5406114801da0744690402c4e9900e601c091114028880f482e07001000030b9800c04020800002a03441d11000380781d0f980d100c0e03945d00203249040d040620407200c12100e400100390400503403120340c0e03a100410313819058084030005404071441c9400d48540311681d009400c01d01000c58401c20702c03504942e8011603040000c0030451024010368403060a804200d460a039454400d0000303240b40003889001d042c2c80001c01d807003d03107030440c1c9803542c0c8100c0e250904226000750001c504205612382c5401b849411070fa40d00b80100342040b20145400c2140200307001668035013101007070520300540400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232365494 1250 232364244 232364299
    0x6050f091011010c0e0f060a12020a080613140705090409051f0e01090b011203050c01090602180f0f0405090106050405040f0506090a0f0b10090c020601180e0c 70
    0x1c00d8498040400180901500b480303071000302d00ea5103402c12448045004501da10303410b9400030800a61009900f04100260304500340990402c4240070300348070480440e01c0104102251500c2d41c800d5442d1910030028240203859001c2044c50400c0c0614218500300070031241c001c222070405503196161000401c1c02081494806041c41c412103481c2e0340910840c80c140b03102102c9206003400103805d080159800e032103c07964021700016021004004040e100c2c80c82c090038506ca442c1041ca484111080c003429204911410342e025940020901485205402a000c0b07000c000c1c0c0e080698241c0c1c1c600059045652901114003641c2c40b031300000e400c448290302c03003030103407a00510400c21802c1c41d0800c0d03a40c650300060111241e100c0d02c0d0108481e0400095051142c40d4890290409607104d5600d030450b143c0301901e010001c01003040c010a00c007a40b8010f0240c03401c01075004201561620605080b0800241c4456105526050703481d18811300200e4210181802511240c02c41c4109a41040741002d070321 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232366744 1250 232365494 232365499
    0xc0c03070c030c080708030403020402090102032209050f06090a0f06051305010306060602060f07050c0712050f0c120304060503060a0b040e07080603010203071218050601090c1409060406050f09 85
    0x10034404100c1c0c15000e11041e80e0240a0544916444080c0140e40e013842d8016000c2e554400d0004100600c0d00350001c118030038041c81941d0500400324200c040152560a0f48103035000010f10501c9000f64911900303900c0a11042101a1420705501144030740c00c026005103070f000c4e03d42a1050350340c00540c01810091038023074480090f000c04004032100514080c041100d00a040c80c00004590748001001030160012615003c1203447e050000d41d025171048071040342c14000e00c9000179500443c1080d40104c01d0003440a00001064160028203042005981a208014540300340000403800403c0d141035500305c0c06d080b07540b80c681c9000030384002d409601949003034000240c045184419844918084c01c003540710030409450f00d608141c00c0c0e000494202d00000c440500441600b10107420414030111940e045600e2000541c0300e4500707000b4247c00030241643c41e40744bc4025241d002c1250784000d00d0400c4280c0c24008420002440ca214074468803081100c080b41c40e16401500004840411000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232367994 1250 232366744 232366747
    0x8160c06050a0909050c0a050310050301060b030f06044104080c06070201020f0702090a2a0f0503130b06060c010606020703020a060302071203050a15030f0c150203120c0c03 76
    0x1038400003081544040209800503c58010000700c03607005024407409069070440140c00d0440c0007104a903950030080c4a43c0c0e6940038107400180300d803003e218860151807000c1181c2c1d42c0f0703d0305041900c0300c4040500024003e600d0301200c0210008030701c0b80c00a100011100310200807030881d5012030129000350b2a4100740444405010030000c00c40020075a171030994007035809559034042c00b0b034206e000d100615804482d04016030001840d120100b6980702a16100010301000d40c0b194401040d115400000030b04d21407191584685500010b4425a158091600519514201c0c10030324100c04120300c0207114010030300104000f0360742c0c0000c2e20f981d02c20500003000381681e1460020355400e00c0c0c1c40141d0284071141c10201c1c0480c0b003070007283e038150341207902c41100c107501180480040000514021665039135100300c01c403440040344442d0055004012442c4401c046081c000c07041002c0e0b40c0a848018103404444070380030740200070fa80f59030b0590000e110450b902d0b400d44100e248a503642c0c0c0504d6000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232369244 1250 232367994 232367999
    0x102010902190e160e060703090b22080714040b01020c060a020105100e011d040c0506070c030b060103090c0608060604050a0306050a1a010c1b050a0f0602190c0308160c 74
    0xba25880a04503041924204204c0c0c40e48075032980300030080c040c0000003d450740a03c440d641040c4008120b140d21a107040d04880396a03450703002c1c0f030340c01214455205801000c90040c01380804000000903003400340140c00007900c1c00305082c1ca20403176035810501960b101c2011090680c0213020205e030510001c0d04440d40d8102100d00280240021100c1c0700c14010a20000700c0d09900407102c203816202c496072401c0080b81562083c2c2d440080042c812104003441c2c030408542600d075400600319052050b05000d410341c0c00d500c2c11100f0001c2c018480d40c10545406203900200300c03090402c000720b800a040c0041c0507110071010414170311464002c141c002d254030300000100542c5078481440f90a0603641088030440304104c0c0e15802c002d54461074000360120403000041500b024658140c001d204000b80e00340350f5035002044010505138402440c0200340d0750200080b54040c4030300c2042001904034010004460781e07072000701020700e0002500d9040c0110300b07014809031b22299510700c01d400210310502e403035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232370494 1250 232369244 232369279
    0x50106032102070602010605090f0907091a2b1e080f070b100b0d0b030c031e10060b0f07080d0f0c09050105120a020306010203070c08010f060e0601090608060102010902 74
    0x201201c03440c8010702c42e900740010128030601c1400252000142110040c1c1c45411080307881d800d010b03207250540d008918000650140c0c51040e0301d10540740001a110359a02e50341000400c0100403500020b5107110010415020451a1100a2298800689035040c404480304104c9403985480040c018400014880001d042c84000741030700501c5003000041326a0351100481240a40d441400d02d604802d000403880c25403650040a80b100000c0c04031800740e01450300181c5028103445c001184958003070303070504040c5001d2181c001041014001404401c0c0380c550f114505200740c0c404070358804408585a000c01249000f1501d1aa040c04008d01c41c10411900c110b008050f500d4101001c9001440c0008055010300141e03048410061102e0b4080d60716480c0c0e81c406940014a554118001007101400150030a603420020300740074000024415281c0340750400325109034200e0841400c02000f000542e0f80d02000c5c020a0300c6692501e40d00607160b680040c3d001d4880c0c07203c002d502255001c80c0c6071544 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232371744 1250 232370494 232370543
    0x70516090213050d12053f090a08090f06070206070b010e01050d020d1b05060d020a02010501140d020d110301090503180d1e241d0609030a0c05010603 66
    0x45610034400d2420a0350b803c208000e0000c640e03001042440c001d001ca04a480c021700150111030594445900c400d60311507410410801d01d442e601000140d011450002030315540304150340180d404c8010620740d40c043e11101c49a000354142544505440815202540c41d8101940e061039030107070400f034a40380c280c80e00001d100d9090050165840005000046600c2e100c910000e4054003c0c0490070400c0c000e48920341c00460100101c404420f1140c0000740d5502e6a500502034041d628000503101c0da140d004c028250354060780010030058507000c101c43d45a41d015600201103074120f031400e914190b9442c050503d00800e00307000b5415407820b040b503820720201100800c51910a219000400303004c2004200810365603400241400c2c040f40420344c0480f02c1205000a080d000d00f80355098507105000704e42c84a1110f0040f0350983d0384641481080e1a46122034840e024540c0d000380c9260300d002c03070700c4603034a000c1c1503000c2c010800e0741c0c206201801000c0d80700c1340145400a031290800040f1403031501c0c2a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232372994 1250 232371744 232371757
    0x121012110411090105041202032508010b011e0f020c060d0c020115081207031106150906030d1211090402040e06090c0c0601090c18080c10180b0705160902 68
    0x950802074860b40d09014103080303503001481616220f081c07a04140110007501d00d13101c800c90309803140941c5155091a9112a040500c85146801c9102800c0244160960ba820741c0803505004410a88454005000e090040803450514020601c107250940c100d191180004d0b02681000001a048000e0b254940140d0f0313201328903400910607640c4d01004550520514801c035070396508003035100c24034074040a008000f20b50081c42c2ca00702c2500e00c0004542001e1003540d8615104d089080302e0300c01070800710607480d0322140c105c0190100700d12400e00a03045510000b20301100381d596403120000c034500c000584504c500c020f4400c5482d45d813240f458030404803090b0303403092103a01c0510000b060049204101c4000e54100005020580d1038140d1160140000070784840031305c5901c0741180345000d5410002c50040543d0002011640844005d12032101c0641015004000ca0070609243c580503a0240300202d07120300c81e01c00c1d528170040c01e08505000180d40c5440c0b2280040301c2c0001c00806ea03070094040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232374100 1106 232372994 232372999
    0xe25051005210609010905150415080604050618030a0f0f051c140c160b0403030207050f0d022b030b0a0506070f200612101211 56
    0x205003141640e0401524030510030803c1500d080255140105100e10040085040c80e0079500710030801624085d000d0394550034684482c078086a061001094200141c89803070400b4900703261505000d8844411000002c0074041c15920040111460181035840700000144d82038805d0380c040c51084c1d00b0100703018082c003540c20914600210800c00522603900040d80d07016104500c812000041c12101900e20240b01c200e181000b1012041c1b1580c1c0c00c441801250f581d90700d0200c01a1240210080c100c2c043c0c0f0441c001c0990000481c003040304180d40a072240b0001a000c20a290380788809905a240040c0400c0c1017081e0082e4050300e108800a0b140040e800d0304d074004684168000d60b001c0302c0a940300803820b011301c90247d140c1e400b11803190928004000e80000011010701400a01c01e0b40701a00781c0c04a0031042d0103074032510003020313005041d0b80054204d050100103080d21403c040d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 232194244 232374100 := by
  have h0 := BRFrame.cov_init 232194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232194244 ≤ n) (h2 : n < 232374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
