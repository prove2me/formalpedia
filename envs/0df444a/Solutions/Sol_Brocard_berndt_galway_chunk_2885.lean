-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2885
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:41.521418+00:00
-- url     : https://prove2.me/submissions/a24c9923-7e34-4f1f-b761-5ea30cb9b69b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 518705035 ≤ n < 518884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 518706285 1250 518705035 518705053
    0x230a0605010b0301031707030c0512071101090e0109021c110306091b0711212404120507050a0c080d030501080114010e0a090b1303110609060105040c03090f060b03 72
    0xe00390041e64100d9500c4002080021800003c84800e87c100c0341c0100c05200813400f454000034418881d0000c0000313041a019100d02c1c850404a404040b0100707914103008001005119421380390314128155500c0072400340c1e8481031225800721800000c0740c00d104052614650310300e4072055500035402000c044a02580d00c0d00c2d03c0d078101c085040c10090152548504000c1c1c0301c0041c2070313401c00b00d201c0c01005040c15140f09100302d0000e9404104512079280340c101c41102d0110742010742c1e8004494110702010501880c05603255031922a5007241c5d00244840403490b0004c000003005083c2c0c80c2c40c2d00c03070840d000e80c03a03813840074a40d628040c043d0300300824100300004c0b45504c0140b10340040c0c08841c1e0b00c1d041c40d592030141c081058038030151204d2186525904a44042542080842d024005200b0b00542c2c205207070a00030001c500d40e020801d0550030400601c090040001135081c19204100c40000308500c80c10000d40080c0718071079005145a1031a907103002404510340c4489000c080079000c0c2d500b410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 518707535 1250 518706285 518706299
    0x7050f060601110c090618180f0d360303080f13050c040c120c05030f070e0102071502030d0606020c0f090106050d1e060b25030804030507230a060501 66
    0xc038480760a00c502c4d4018901c0780c140780b4003104600c0d0040000b404c4d5500c039001840d40010740001c2103400c035142d0549003c0a80302c02204201c000e64844603900035000d5010301c2c000c0100242d9000c0c44182004081e042c40c0f0621004c00090742c3d10000d00000c1103411590340e860040c1c81c001c41162080c402c0c5400d400011000c009000e603015415900002400071101d00d801000000c141140415003000035042e607040802900f88142403800e00c09440303098891410350960070411000a10990402150018100450341c0000c1c05800359070682a0780c156a101201089203503020b6410116012400c00700c0016000d9004035140ba4800c20549218000d0400c0c4828800c0b414000c1c4924030000b80c040141d61001400d60780402410500041106160b00315038591409480041d00003040c82e0100051140604000001c401d1501c405092629107403032407174501509070100144040c00b031000006007c0c003000116441441c01c891f40c40f1409508403a0010103640d2110804801c5420038a0180003140351 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 518708785 1250 518707535 518707547
    0x1508010203071e092402011e141828020316050906011817070312030506011806050d0504031803150c0206190b0d080a05070623040b1005030307050f060601 68
    0x1861100002003c103503500008085c10001c643d41420455585962403919019052400008690740070030208070382c022140c001000301d03405095080d41124840d42d20548940c0420a89a8000c401401080510082e100030600950f207e01c001d5043c059030544900c07580b0a4000f000c103940c010786a05449580300001503401c1818604c0000851803102030400550090320240700c6030840d000c017568101b69503507450070004043c804041d004a521142000700c1940e2128450081c032008480706115546006c2c2c010b0f00d903205100b64059640e450b10005400d05004400b14441d503480803400185099482c00d1031181040d90310325840b490f038108001c519542d8400603150340200b00c8641e0011021103610f0002d4002d042d43c0b4841038002120b1360a6501207043c120207800300d00800d8441c103a80303d07100c1c540342040712070500f02d40004040c441c00700c90704075090b504444d40c02030340b240101c18941c40b405501418241246d00a9034580300000b10303602008000304040640d011800200c407255118100190b601e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 518710035 1250 518708785 518708789
    0x906030c09061707050907111f05091603080d02090d0f12020106141320040603060504020408030706110c03041e05010207050112020a140409090c06140405041508010203071e09 77
    0x11358070103101800035150020785a41c01c181d09090038029001c41c10b0f106800c111a0340d2079909007500c04070800104110a02480364001c035002d000d05810301150340b95060740382c2700d400003078076090010650300400b04032503040701c1301054010300e003010401b0189091131412001000866200099540142e00d442c014000c0e0170650342500c10010709211014144107240c2181c803001402113413154508001903c460f200685001c0000a0440d0b0719070070007030080d091b00d910703900c142e010310300c10042040b80100200c1960800c0754050790104060400b1085414280280140013519010018001410344038051714121210501c6c03142641e40d6513108016038980c8101d100c0d1601240a90030394140314509a402800701d0f88940c2014030300c01001000d5400140c0017500300302e081c0780e501c0d0005030611280403907540c0240396501e000c000c01841750900718024042c61141a004a4440501c9401d10b07a0013800a4054107288008544900c1c00c400d0082c4002c244503042802c0d558548a02c65440b0f2140140d242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 518711285 1250 518710035 518710079
    0x1060e06060702120118141501060e010807090f090c080603070b030112210e03210f0f39010b370611010c081b03100906030c0906 57
    0x800d202c1c4640034020600350f0075840040555841c42c01d0000c5001d11a150300409019045035680324000403003580c44c2403461005002d0aa4001c40104400c2d94009150701d512582071a0240c074130744841d0000d80d107540154001e120304801c524000705110b1816441441c42c03010b66902d1503250344600044c1500c1c1c0c2c4603400b42e040740d05410401407021002d005008149a40f180300c403032514103c2980b0310b090400390038002d480062400c0f0201e2400746000c01841c080081e0513070200305120140041815603100e0540720725002003000ca513550700c0d850540251100405201040a821384e1352440003600031040c0c10351a01055080b1030320410b03a080501c284a030300c400c064a02d92841070903a6100c81c0244c501a8145242c0030320100315130844a480c02d03044020001501c412940592040c25142500c98480613182007090400401c2290a07842007841504281c040b00244e8940f200004010944150b400c5861040d04100000040214420341c0c2c0080b501c2c2100308200d01d940760030300380a2000c4030450071a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 518712535 1250 518711285 518711287
    0x150306061403130317090a02132c070f0f15080705030a0504060e0a0f0605060f090604021806040303050c07092d1b02070302031c020a080a0c080c0f01060e0606 70
    0x20100c0c26a1540301c0f0410703000f070820300c2d1804410210140307000406c46018030282c00055010003141000d591100034200c105405218000c0ca44004c2000c02405199000c092410035401c1d00f0740540601c00c0b1406486c5081000b6003268980000030740e100030391b11071a0300c1808142c40d04038400e441200d00703138040d0706a980c48074950b0712041e000700058800034000b40c0740242d6414041c1c40d030001c2002a81c20242c400c070040e64048002d810f1600440d0700080035940604c00500180811f9a26181d515501c200d0071a00140c9421495130441c603540b200c90810394010070006004020305030480c0140040c42c0c50f0600b02c401e540e03103a103c1c100c15151411600c0c13003071550400c641c00703c0902c18095201c00607000c1c040011030302080c040800c1501e00f0100710b5409070300031103170038400d60400f440034484007a24120341a81030000d07110000e690b40301d9090094406040400c074010034603ca00c2000e5211b5410030070321600d070301490101544075010000315814a62030100c0000f10000e0440306907101e2a0020141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 518713785 1250 518712535 518712541
    0x91501060f05030c0409060e0f180a021201140112050610181e0c1d0a030302030a080403090e0c0a030e010908090d030302091302120a090206031803070c150306061403 73
    0x742c409400c003034000c0e0300f044400d00001c502080f40e449003000a1514500c80d0301d041c104070a500c0600e2308060603030b40300803d00d10301040d441304d00041c0c11460180c2c10307541107405180310461940103002141d0701c1a00d1034240c400004180041600e0351075154056010744200d900c901d8040c038880b02c82c034450140160f062181000c04207000e50701002280303507421401071009001000d0794040355001c0d03003000041017580d1110805021102c50503400200207880b403403142419900e000e540c134080c0f07010400800401c1c400007000c16100e0031480b401446000700403c01c84c10181099010f540040640384e0004c0d00e04000d010112205020750f40541c1d801c02c02c100e180040c100c06105000a030450705406040d02004485803540340d441070030000ca400004016140d05110204c0e2014510250508007001c0c1440090000b5944400c1101d41002e4504500488458044c00c5141140600035004e00003541c0c5180000700d0b0203070307e54a05d002d05640c1e541040540c1d103443c400d0340c590540c0e500d10b0845240074400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 518715035 1250 518713785 518713787
    0x3090a0803060303070611180a0b040902090d2111011a01180f0b04050909240a0908070c031403040e010b0a020316050703030801120209190b04090506091501060f 71
    0xa42e00000c024054030b2a1625503103802c1d050f1240c1c1d4402410f803110000302c1e54014903881c0c4c00360480ea00100c0e0500001494140300b0700c0b60703000318003600707111550010b4400480d50340c051080d4031455020f0f65100d243c00d0003446148442c40140d1107200461080a0700007200803062181407901c4604185011019806600440b00018203080080c8510768480d00440c0004a00c40c0e6940203007140192140d59070b052000342301c62540c010b4804076440d40300c3c0b40c0d508480f403541c1c4028a1050328445c1a03a980d0b540f000c5038207010300707a144000f070321785c02000a80000780000c0142c1c50041c0c074000c02030340e03102c281a1110b02d90b80f840760703100300c446400200380140b1120340c0f22001850170750503510490f4184000140c2c1f003101d2500315001120f5030342c00342c1e20800070590080344290040c0084034801340301c1c24840d00890b4860300c6c0103100010b111400c0701c06c040003000651215411032806441008103500a04c2d007940d6440d8142e680b0303003d5100e00d001503403c08810a11803810b03183c296545145120052070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 518716285 1250 518715035 518715037
    0xb04051501020d0f26010305161815050d03050705070b090d02131b1e0f0c0605070c08030907061202130e100803070b070305060427060219111203090a08 67
    0x2a80e804100517000c058403030b001080f154600043c0c48840b03040b425403462a0a600d03004101c048181700682e0781c40e04001440b04e10b00d201607040422030340410b0651108412605401441d000340b40d00c0013419245105060340000901140c80c030800486159507181c4c010b2150034018030051a61000c2d540341c2c008010f0500c00451007510242c8400401c4008083e0500250306003c100d208000404042c0001c0d609803050340c010601380b509080200380074a031002c1c02060000c16500162120f0744540200318031501c24240701d940c00d030300b01c0407042d2281400c1e49010740300c0d0200c1c440e41001441041d0203030b840310726900c200d03501814015411020b05280c01d50b00c4110010003022003100d12454280012104400d00040840c40d00c1803406862510b40302c0d001808580000c0e05d010f00441c86d00c080c0343c1d0307041c101301c180f62071008040500200d511040e1405c10b0182c815a4800c40003510a00220140550416940808002403905641600381c00c0340c414002d81c0030407103010810b6400080c1c5040800c4100c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 518717535 1250 518716285 518716307
    0x60f010e030c03031803060a06060203030612030c01060803040906060806090f13050a1208090a02030a170405030f03090120150a02120708010503120a0509090c04180b04051501020d 79
    0x241c10345090710b00c02000241150801e07406504840780450821301c40c0c0c0750600000b540a80f00c1d14040180c0c0e070610000075641d010080030940242a66418190030039000c02c10390781d45e0002500207221540d110300c040fa0303ea8100b480341c5008582040408079880e03004454640c8502400351400080e5540c06160020001024000044803018090004003061080c00704444450040c0b07040240550400710080440900614004258011190000c0140e4010802050803900300180ba501741542021080140c440c030752001e6414801c4080701d980b00131021000c0c002c0400241c9400b011208440c1039030a403a500c9131594803250700300051049602901e4050150858481000107003004801c4500d22018a01551a400401c1001004000c0351404020700341209010b4002e09042c0500380d1005071150295120140c4070341ca9000010310000f42d10800d41e002465040c442924144003100c6c48002003d4142c5002d0081e030400c0e00140c0708540c08003112f0700f441010f03401801220165101101c0540c545 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 518718785 1250 518717535 518717539
    0x10908190f0c0e0c0301030c0f03030816030e0304090e010605150d320f090d0c0b040f0f0c0e09120301050d0609020a08010b03010b310f050a0207020f0405060f010e 72
    0x424003c00c00090070402648101d4a15100d250b81c0d5055041c416800740a641c400306104400320820700c0044d40c49100780f5003120303031030400740080004483c00307038040c01880c2c0e0010080e2001140000d4029a95008041c20019440081008a0300c4105022450f0310265020000305020452003103035544035401003e0188843d05c1c0c8e07400304001d082c010300000001603002522080303c8010302c050502400c2c0c1d0150040e0304c8000524001d444041c010f04007520b1010040c0c205900d0720000350500c904080c9080e005540a0f40c40c82d0100703001d1130003490a10081c002d03d0041d251000c001018407100203000b443e09030b1032014860650b0b20705410424506850041101c0781350b101c031058001600c0d0307103006d00d02601c4184008203104002c201410308440ca820340d2144944124265115640c1d80141401c418001d41a40794070300070701ca040401c0180c0f00800055804515140800130102c1040c1d0140030740c2407003223651100000805042000741e400503622240c1c4041c1325100c0c42241c1d0301460942c4000500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518720035 1250 518718785 518718803
    0x6060111030d0204180b030706082d10060f0906020a0b07020f010f0f0c1403010b090d0c0f0323060a050a0603050a050105221e030e1c02010908190f 65
    0x5800d60b0030702a600103602604042d1380c4501010303191400ca0003981c141c1c86003075008043c450714200d00206145006041c0d01c006001d810a500c46107400e064102070040308502846000d410002a070101d1081d062044400045102c003d04940ca88200e50203000c0b54100e50091070010129141c88010001c050405002d6200304052014801e90038083c9405c2c0090000c2d00185158410b0904004d649042403034408006039550719050b00070040080d2410343d00ca143c81980c0b2100031201040600203a61005400030007808400a526201d02d00c4031401d8074400d070b40ca4001d45519041e00c14400e00007240f05030058100c00f000807002031042e40000d911a0b0390380408101c01d43c0e00c3e141d060030200740001c281c2d9265120230803c020b400040c00d040c1eaa0201450040c6070070005501c5a4051900c1c1012055050504140c98800c1c14482c480d407048400c0300400c0c02201211303281105d0803180c3c800004034003003403c03168000395914001c00d01b89405234010381510171051880d5039482040e21481c0b42241c44140d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518721285 1250 518720035 518720047
    0x90b03030c0307120c1b060906090b0409200318010b04020f070303090203070f0f0503010c0c240b09010608061207140d0c08010c1112090f09130b19050a0902030606011103 75
    0x41240700c24011b0204030b5110300c48440c14008000c000f080690002814800c0104041010542101c1103d04541410700005a0465034403441c50803900b0000500003507079404010720488081c182400b1480c161100020012803002c2c01c281310036070288070041d40d2400801d11144020a00070b40010020502c01019200507540302e4464078000c040c0c80d00400c00c1041010b40c184010b003424410860f1400e07040c00c280020361215900c0e00181c4039085403034021240e20381c0740007402d450355410180384640010306030380417503850700350060a00c54110f0300c2078401e295004001080007404108041640e0607203919002c40003500c405d20020041e9040300701d0f0080055200003131000d00a218081d0807000c01e507140780900c40c1a600b410701c3c01c0811180c8815440082080b0665076490103041e0500c82c0050310000c10a981304110340030b00710310061001d0902c20040e020801c00c516400c80c01d44400b0180310003084180c407550b11070030480304444e00094244e8401404a04591302907040107020311840804c480c1ba100b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518722535 1250 518721285 518721293
    0x905030303070f030614150f1614060708190c0c0614040203060109060e1513060602010b15040308030112080705010603050c01080c0306130b0d08040b04090b03030c0307120c 76
    0xd407044031450002000fa154444481e541809000000c21461100c0946c0b080344a00042c50f22104003c520035000c400141c4654040d18a000d48283c4208035007034054040300c504044000c8460021580f0060140000080510b4054aa900d0080711103071903901d200803201e031030350f401806420209820701017088111000100c1c90b01600b416000ca200c0c4c01c2c0460700f1300344103040c03529070103030005035580341000300600c0180d0039030301c006900008152020701401c0d004800f00d076102401c0071001c41c1c0241004004541c2d5030701508a041c00703d1080c0c51002210b0000c1a120059014501000b00703200e90410041003c40300c440080040c1d54042d60407646018440e66680b42100c20300d03407044030075030000e0211030803d42e00720000c180d224000301d20311032441c03600100050034440c8019604506030350340c01c0c80d03504c00d8446140042600f80e205000d2580d880d200e0b0000314542e0858401c004581d802c0c03a500008a04010003507541807419400114100102552403110004c1300400000c1084030401e0303284081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518723785 1250 518722535 518722537
    0x50903131701290d021c24090c0b07060212090f0c0105072103022208070801060509130203031201171005060604030f1a04030f090504110304110109050303 68
    0x6141401140485081d03140d5078600b5a944103084444410303040d691202909941c035607800300d500c0221400f400d402490300c00511380c0e02c07140b40204040e0081e000c3e10030800c9421183e050351040c1d0401000505076a0200c56003d65007107000c0141084000d030010400462000041c009241c4100340140c00c201001540f4480a0310485d034004481d8003481103910440018884003400b18400e1800b549400001d40703c4582c0c07a1503040c5490786c400c401b00c02c98019140700703906a030030444100e00c11481112000c1ca9a04a60728980202d04e818003892800042e0244144501002c031a00944400c280d40c0c0c0d200c10803514071083c080160313054001045801c20380d403100d042c2c1d24041c0100d40e0b0444460301c41130410524106500f409586180c1c908002d200c881c1d500c1c41c0c156001c99920110382c1ca201080d40c0341500c1e00c8481801c1949207100d40c8801e200405411062001d010303849982c52100c42c070359960801060351529941520820401c0001c180030640e0417000318508607041c1003000801d5501c001091031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518725035 1250 518723785 518723789
    0x6060a1b0f050a1b050603010302013b0109170c100302040f0f140a031709010e0d03020303090d0207050d030e01020c210c0901030809060310150822030e0405090313 72
    0x40f40c0081c4006403c102c03400e14100068180c1d800103001080c2050007190203448103010181c1804802c440d008074200200c031100c2c00c00106544007411a58005112501c0c0215004140380070806012001c14049044140b200601e0500f6008024841d00582486442c600784218001095001c000202c0c402c035040084030000c040d4490f491100c0351074400010f81114030b5201403489111110020808071301c140e440c102c40c08000010300340d40d4258810040c0c0b0503080b5484600d0b00401000d03044414541c02201562040d4201130960380346e2003021038101d071210080d005256002040c0e403084800b082c800d01c5103503a00007060046468424000001900ea29022030240400f5501c0000040001400b44034480400c80103441c8205c0341d50642c1d450202d90302905240c94000c140c00300000741d0100c1252080e0b4000c104100c1d43d0b41003103800c008020404041220a0303410910010448452410060761500e0034a41565440c0b00382d01c40d12041101a01e4080c1c03032982240310034820420001185424040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518726285 1250 518725035 518725043
    0x9021804120f050a090b16020d0807020108090a03090e04060f0e060a111c05040204020f0406030c1814041505150403050609071d070c060f200306060a1b0f 68
    0x441d510440006180940c50510344081007001e00820342a26007207080e03102600c0c88407008a0300c45c9190400003d99415a0102a52000c2c1c010300c001c00348800003000305030440c000e0f601c1c804d15a03101c4030f103140c0d20741403800000d0000d4803041c02040400140404c2e030b6006031140d2404a000724080c400c1d40140c03000440c8012705134011006100240d8080d01c907050000c0e21000311070341011040000401d030340044400b564021030702c40340041c00f1907407250f0440e00c10318000102c0507255078883d48014004c0a640d200140411f0f04034120b000307082c8501e020b44040340d80340c402e0a1b000500c1d0000b8000600a12000e9481d0f804280758040703400d9950340884065240e403200429140c5186003050b07403030107801038110521500a9282400803281c01d4005451030315680410600c2611030001c110ba040c00501e202902d800c0c5130050388024070b46144c0100205060324228000501020340100b400ca1105031041640900c003001184100c074090341c0c000b0040e501c407034071500c25400c090300c07502c6010441100c102d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518727535 1250 518726285 518726303
    0x60504151d1608150406150b03010603060b280c0212030a031a0307030f05070302040203070507050d030c2a05060c03010303090e090a020103090516140a0e0f010909021804 75
    0x18550380c040002c0401181c19100016903240750400c401d48584090070210041245500001c041c0242c603009064030070610745d02450065690302d04605213400030301804000074105000014152008000c0c4c505002e01602c84101c410415910090407501905d00e10050004040c09200540e075602d280b1a2043da040c1c01540d9600e0744494003d00b00c410400308c401000c0b48044c1440c1c61501c1c002a80c20a0720350000d10b03100b40c0e90103401c0c468508520b503440250302c00c0c000800c020680780d01c0b001234042240325504480100d2aa06001d03400c0d211507540f55400500d04110380011086003880395607002082000780160800192070f0b07a03080003403c81b04d40b00070140010040007010b07404540100106284c17005103056003403034040c541e200e01440c0c1010b410192558604014024148408040c603003c424140110700d136100c1424141d0400c560800780300b07000310b0f2400a4201f19564095102d9010f000039554642e007804a03820080c425107800b42d0b0042d07640294644800340c503144040c01a070061200d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518728785 1250 518727535 518727581
    0x2040e070602010e01051e090a0b010f060f03141f0e1f0806010b0703120e012a0e06120408040b0d0509061005010c0b0a0b0a1404230406050415 63
    0x19084d2000500e2090450785030404000c0703240c0c0259000303021680d02191000307a40e107481c0081481d0040c5400b0180a00e000031000007000b0207160183d00444860f6142d2602000044406a0840f49050360001c00700c850080000c00c041c01c50403036614199001c00d440f000054448901c911541b6049900300d030360110070b076008643c00658085600080400c1001080c282d03060204249080c059090b005083c440d40340718016511070316801200c010380c0100020410010444038140707586440022400c00c03c0110300c02d20482d41d01c04c451156203840058202e600c2e180c000380c921203008400400a4031f41117001e00c800b14102e03880c10010301200c030182d80d006c03441e401e050032581d0030300d000a05450b0002800480402ca142d070061803080900c1d0f0410300981d91507031549400e03c0034115050071070780d00041c001c60108409034407062900880c00c00707071001c01441a11002403542e519041c80c80b80d010380f1b101000500014055003000c1c0e40644030300ea0a0709018561a1080700b628601c191059000341d0300021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518730035 1250 518728785 518728787
    0x309010f0306180207150606020d0c2d0b01080c0d0201050f070209010609080c0409020120070e10090b0f030c09040305070204021c0509060402100c08070f080405030727020306010c02040e0706 84
    0x75906500c00c6c1d4100130032026103042406541e0b41100500748050103125092031091100f10f040b89203c01000386081d48405506500d901c09c403001d919002c0f99070821920000c50305140001c2c49101002000e0440e40f01980c541c0c00644c0e040d00310011170034110307004114000058540748042402810a600d81c019154100a030385400c0410f01200c4034020b501d07001c6182c02603a03222520b030448902e0041da581d0130100454540303042c1400d503086403540021803014002e10800c05904842121034423881005076041181c100a081c244803100c00e5819400a20145007520300152080c0c0c01910038148a850102e203640451300340c3c7c000c0c501124500800095542c18001c441c0601e0b0b500c080c01601078001481e0070350000e400c00300448142c3c010044101d0082c401c02034040100c0300c080e0341018035005140703070170b20b0080016480307401020f00030f0180c5000044d10301ca040c01002042c8004e588841c8107900c0e8110070340c000350401032040341041030380070101000d038940c2d00c00c04c00c8070000c00029295944c24550 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518731285 1250 518730035 518730053
    0x1b0f0908010c0207030b1317130501020a0213023604050a18060c090806090303060109050303070503030406020f09060a0f030b01050c0703020f040e030a0e011803050309010f0306180207 81
    0x84100e03080e90400400e200c80340e43c00301d2080b09481c1e1200b082070113921a521000c111364250500100031640a04c216107103050888017038413503940c01c00a001c1b00c8031340300e01c01240c81d640e2a44000b500440207410141c0c0316221a0050f0020980c0342020103000c410b044c0c009426083c2505200744643e0755001c86c080c4604060141d0796008504910501100300d0304286000045000c2d500a00025602c0c1e100e50b12091050345600300500300c200448901c2d007003250105850768401c0d101e0a002c0342500b20b0005013404c001c010f6816041d001800b560644d51185c1340d885c00381d4080420403040c42c0d01000901280d55034003003d0403e03109036a960100c120722020001d030840d010305115606001080c02841144a400103821003900d178142d461842107590500850080c01104083d44040d000101da008030896104000c40c12180c000da840350701c01107241c0c1d0080f81c884e08600024000743c0042104120a5005e03422204d0030750840e02e0002201540c031846064a46410b000940b2815000100341c414418414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518732535 1250 518731285 518731289
    0x402010807050c0d0c051f0203150d020d1e0b04050604202803060212071b021305060136090c020604120c020d0602030603240612011b0f09 61
    0xb00301640761101d91940c9a40c0c442c168061201008010079251003080b80522104040c84803010042180c0690810f4160180d0003c58000218268014034070320940303400000d0303154486d005400d40002c3e251503140c5101281c2a038003d00340261031a42c0380e40010345040310391031090780120040c0c0b020341010b180000008140700c40b01110100c003244043e0284c1d55031001c2ea002000541008110200701d036104065200503079101410980c804a0080d40251141c039205200304032558500402c01e0184c4010410750940300c4019400c868900c0c105c030f81803240c03580070302e0f0001c03014140202d000420b12a905400d0b00d440c104000d0781c0c1e1542140b03480a80710040307140b0240c81006010310011942e031500039600d43c401000079110b603552074014066107000b04141fa0301a030700074210343c8030f11702d0720b00301038010313520696485000e80b01e01c1c2010041005204c9807110704400380000d078141520fa10341004200c03010305075051600d56981500d502c448880a40b1000340b20159103500c1d07683d00b43e0701c0c0043c00402d0300d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518733785 1250 518732535 518732537
    0x3091101030b090112050c0619140a121d0a03020c0307080f061605070503040308033108030711150601111506041112070207230f0d02040b0a0e0402010807 68
    0x10204101c2c1d0b6a0381e030b040c207034152400310800d00407150325420034070314280380d144110707810040000e2102c420070680c00c40f12040b0381440e01c2e00d1101c21401001e10065205100700032000074034240503054010a1504006000c880b4041c48480c001945000142400d240788422805a4002c1d16510300c103040c1800041c0041c0340301c0005e400807042c8100d603140ca03250014482c0a05000300899220403a0040c016580055000811241c58986a21b04a43e0944c4296075084141410000120748601440148412102104040c3c0c01454080d59012840e40001d0b14030010700072800701c807566141041104400c1502d000c0a90358403420000000341801d07041111410f05504a60504070394030044118058000340152400139985a10500100030ba000380d142c45160070903403030240803100750300140311000e48580c0b0301d41c051f84602c20319640b40090441100d1a401910b0509510303902e141558012840600251001c1002c0c0a01400501e01a0450b00518400041074050009550703001460035880b00007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518735035 1250 518733785 518733791
    0x41d0706030204050d0f02010c050a0803100e0903070605040c0918020a080607020d0f02070b0c1b2202030a1d06011503020307091203090305102004062102070b070309110103 76
    0x525021924500001901400380081c01c4400000c592040d9409c0b0030701354000c0141c840500148c908512070354000d07104030b240780c00355040102d9112000400d00d802110323040000c618040d2103a440102500b8001d00507107951703201c0080010b51a403d8010303000c01e6210b03050085105c0361244100102000d0540010329190310040401c03403000c4d000562400d2440190130705984030310b46010201d01d800d809801610141502103001c030a80301d000250925841c401c03140491807a008079040c4a2610304c0324005040070707254502e8103010310501c0c0c2c1c020b54120206400206a9501c103100c0382984103800840c101c2103602c01001040070a4549100c5100d101203807806614505150400410354a4280102c14107405003c407840c04260080c1c211000855110042e02c0b41407400310841c0c1c006240342400310210190068600b28500750120444007902c5c42d54841409074031450050907400c0042020855496600300088070200340312903140c034860b03940342d40c002c0f61141903803130081030f207082c210241c605140c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518736285 1250 518735035 518735039
    0x10e0f030f0913060801020d06030b1e1503071502070305060f090a03030506180411030c0a0b0a0e030a0f0c03020f090403090303030c1b0803040b340e041d0706030204 73
    0x1c40c110350411100701c90080e00c07902400071450044c082507009095641c03000480000c94501c60b00400d0489014460351902652060003159a03108112005402e0003842d000051a0340002c40031603030000f030054111404036845215090f1707084036004049000d6801802d0030020058200001c5511021318218110329042c44442143d4405080c0d80041c00c3c50344807000210261507850096401180c0740f0004002410503040021400c95441d0141e0300a000c0d0881440c41d03030820880820458015850b0a0715082425004582c11500880c113150705010742a103c40200380002160034030079004888138195a0324620400060380182c101035805003203948200000b29400a0030541100d070907090120700101805000c44800c1d030a43e01a0340554038095040060000c680003035849984200313058403494460f14104550008a0490f50007420a032803400d0312201c118458224104455052804c02005094001800c1c0c440101c41311004401c40d500b0105030060412182c1c000780076600782113283c14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518737535 1250 518736285 518736307
    0x50705100509043602030705010203090a1703070f030e09100b07030f030b0d3206011806260c0a08120c0709090506100501021501180b12010e0f03 64
    0x40602c024540c440c6075200010b0b42c600b1250300401c5611000f1500c04000140507000099104052804c168064490a8004035665000200711169140b00510413140c80e441c00c074600e0200c40c240d80c6c0306851030005000e000c00040d00910321080491103910b40e074001c031194405208105400401507461984c405208020201d0000d00700c600b081d0301440c0041c1075a0700706a055020700038a41007281c218080e09030180a00a110312640344208804409800d42e01c50154400c0c43c00c00c4880d400040740d0008401041120a040b024008081000b240800c9181c1e40e5825500c0c0b0708240e400564980342400200a114401801031006064080f40d00f43c48041c14110015a1140d400031030b111506400200444d158204101840040c40542d0007030042c0d00052030160380741c04060b1024100d140c00100003180750341c00481c00c07111701800c040707103002580c1c03074620002d0800800303204030a0b1240c0c0c0d0301440301d840e44840c03200401030a40c40c00041803040100422903d00400000c0302411900300f4425025a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518738785 1250 518737535 518737537
    0x406080103080309070f09020c01050a0203010b161704090911010c05100902060c010608031b0a0b06010f17150307090605061801090f09090b09060403080601030e010917070507051005 80
    0x340b604a04800d07129501c81c070855181c1000c503003121500041c030f0036000540410b150020808148140f000b8082626458078180c1030380000c0c05551b08500d02400305181488503d180020454040c1c0c038050010800c0008440c1c0f41e0f071041d04401c0300641c4aa01d481c00384101c124000901e80001e281826440946032103070350b00d0795640b10b000100645c84102c2c0f10b00759500c420036100584e0005008001c1d031075841d01304981c2c13644020500b0b03400d02a00010076611003400f18219103000c0c1c00a2004030195500401103415a030142d8013a8280075481c3d0a802e400c1d00c006807600d01c00d0b140c842948031014403440070180381c4003069100c060303824103000c010311480e1070318016031f884c1010510012140d4800a80184c5501d0b500303410420485005000c0002c041c0c100790414580d03c0c1c040e40b50a00b0a0704c41228690312404101c5014001c1444180070a805500c0303a44004d40411149000043d516096501c2140c944003114034071600c15408614503051040501c5141c008201c02c5400b903006601a2001070300c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518740035 1250 518738785 518738789
    0x3030b030d0804021509060f030a0e030703120203130501090f152a02070816060f05040506090f13090b0a0e072402010219050c06150109050d1a1003120504060801 71
    0x150117200411071554500c00180c4212a100a00035612414000d2400302d160b042100c0702400c1a0800003840d500e010003008503000e50350107550712064130461082c0705010f98805041c030041c0e1110340003103002080d020f200b0781000768070a02d494006990b50742030200b1106021704070004041d00c1e051400d078500300c2c0c0d20390903041c41129007203082403200c0f160816810300007640c3c400c00c002d01942181d094184074801d164401d60700302d9280c8030545070604204883c14000e602440d40c201c2810000380c0d081e450071151a105140d8028180d00f01210b07120706a509845030000308507240c4c510031062041e0402c642c002c84060304030150040400d249400d910000d080c141c1b100a02c0c06407000b54100c58160302c01e40448104000186c800c0e2061401058002d045a00030501e1104501544004c1507120ba5205100d6150f600141d5805104504140801168027121a03080b00c2241814043c01c4501c00503120f070900c107280e070203651400c16265080c0180314494920b4403004110b400c01050000c90b80100d20941 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518741285 1250 518740035 518740039
    0x40b0a060c06021b0607080a0501060806012012070212010b03060711030c061005030d030e1c0306031e052103040b0a180803100801020304050a080310090501030f03030b030d080402 79
    0x5646252400c01c2e0300244201c03403e10300c8101e166000d8821034040050602e000740c0c001c1d17440e101940d4640241400301c4000780034030400180c6910101e01e256100d0004090743e06968040600d02c02c3d107203901c0d43c0c9848510707408144140e101040f00c1e03095203854044852268040b10003800031114060019481d51801080c0d0014800c16849002d2601020002d0f10481c00e40d200072202c1c641082014007007442c0746886454400d218079200080a28401d0180c0d9291820f100e00070014641018080c4001940d211556400c040d82d4030000030215101c0300e20034045204840c0c10100c82121810002d0030b1503004d03400100d0801c05604440c41103d1020120b07944950018811a0f1944500510358060450420501040d150b02c20660007030004050003035002c1c140700c80c0791200b00380e07507002e60509034002158041c06503007100030080042500400103551120400c20080c1049403610b4a071421038000382c1060b1903650080d55080105a094032420300b1001d012001440c019400c16001801c1c5500200024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518742535 1250 518741285 518741297
    0x904030323071e05090f01120905031209010c020303070203222303010510060203120403110601090c030c0801030809150415020c27042409060c030506040b0a06 70
    0x41d9008a4803082032600c1054218041460900000051841000e2442d048049044030f10680c1503070302400403141c1070170000d041d06003140d149000541d0665009000c80c4c5601e03071289240c80000d2800c0c402800b006091500c000c006081132088203003100c3e402c07030700002558801c1041c042000c0c1c0010640c0c4500c42c00314043d010120141490048410040c1d00c07407500074841c0200c50669a014034030220030618141c00800507a1b480101000b0b06064911130311002d0b030420000d4044070b4500d4000c0c2c03540316000341089500459040704039860514240e10000d0905d80c0c5441c02d0400c0340e418000c184060303541c4d160078180da5045456032070080c03240c084454858044420700c00b2241e00007a041e10b00815500a40c003400d10300e20701003c1d45940520b1100351149159030034102c0f020b452040300c882000d104203255180703035640b55585200c10001840c0c41710404604084080041a40d00030805130b5442a440820070801d41c0102805903000a40710718482d504040c8208215201c1e0391000d0119039240c6448 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518743785 1250 518742535 518742551
    0x7050105030c041e17012306010f03050604180803010306050115051c09050102040b0c060a09030837020c150601020d03090c050402070f20061b1608010b01120b09040303 74
    0x38109580c145c2c0802482c0005490051210806520074070b04032028680c2c401500c1c10003940d16822040803200c90f808102400400f0300d0003446944078952000f0082d10001c1e0b020300c00403060240340c041e074004a46c66400000113000b044035501441b8010181120b0101c0c02c1c4a09a00c058098010b481c204005400c170400c00b10160b40503a0000d440780d41d0000000c658450301c5803028403041d4030441850000c1d1280c50041046c9040a20409600c5509130382c0f00406d58465402c0b10110100d037045041d100101d404180d58110b88100c0103003002d0340028001a59809941c1440c1d0030500034071640c0064090030020481d5590700441c0c10200354070706180006841084e8030380144032400c00c1c0c0040e60030510200e403100400481d9016504054040c0d102e5103090000011a94003040c85120002e0b0005c07001c1c0b09949024241d500298035500d1681700f95405192f0044d8035205414141d440b00304580c4d1242035650a6580201c5040310004004a05015040c0040301003802c00d04094030003410503030b4540c0c131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518745035 1250 518743785 518743829
    0x30605010c0822090510050108060a03081e0316030b01081510031d0c0307050306240d0f0f0606050307062309060a0e090a290112090b010807050105030c04 68
    0x15800c104000c84543c01100d0344a844010013008116514845880b1303801e000b00b01c035030003071044e01c4c800c41008080c80ca42c141103a135585225000081c90b01171410740f08801c150a403190030044d41c85201304410b220003610705840001d05407009500b509040c0b19a045c240300208803c070340920084242a80e1040c03161014180440c011f1002540300c160003004440c201e0302c800c0b40851000741c19034045003116a0280c9900815071145c0741540e244003189420110b002a40e48038110910060100074510000d156454403201409000c088003290181d180356603141c104800303441488060b000950003401864280307000a4400c4001800d1744591500c40240800340220102c1142c109003005041c1030340301d200302c2030040e0001000b00b40746c511a03c842000512401054420510180b8001000100721489101c60721008000680001c0c1001524071003081c0f0100703607028420000c4c5c41014050141c1d80f40040683c10440c86400c924100328040080c040c040040c0b000b41d405540011503692114084200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518746285 1250 518745035 518745067
    0xb0d080909101505132117070803040b0a061410050310050a0314010e0303060f060a021518070b31030507150e010905010207121b080715030605010c08 66
    0x21200c007030f042e002c050400645501001600740000c00c842c2c2c1804981e203884070a2060500940070b0101c0310f80042c6240040780d50940c01d40c0701070200e80c4132546402c2c415115410141d000f1542910b480700340b0018045141031a11414000701102c07494840b003120610006006038010141050400c58040046854101d81c0c082040040c40c005141943c4a5624585541d040c004003002c000c555290030301000201c800401140c0c0f1880c8006c20080c5041070010030440d543d044a0500380440c86040c42c0c180c21101c11820507405464041d50764181040c1d42c200391868a080ca400800859005101d8014003a0310440070a40c2c807410044500e10300d040d079040740c0035008019071000d403c911400e00d0000304001588010f01c9022115903841e01d81d04402401511506a103102d07690043c1e01c424420403d203644811208241d1740b0802d046241403c1040c0c84a0036551160441c1d0500d4000740010820680404464240d1181508051007203a24200020f01101e43c0c0a00c00381c03910070002003102c00511101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518747535 1250 518746285 518746289
    0x4060507022205061806150c0102130b0421020d080304030c0510051b0702090403030507030b0a0e07020c011e0c080904050403020a0209090a0c0b25080d0b0d08090910 73
    0xd45a038020b03103248182801401c4107990180c05204040041a4035000007201c007031055801500302104014601410396032644502c2151095540c00d1149074400c01e071818500004010440c50035032100d041a22442c2d0903800351020441003900443c0303880c0141c0700c10048070306030398220110f2a00c954903030905a80001a1010080081c02015100341079142d441d808240222801921240e00c024803414010661045900c046e5006404d4400100028401d40005078808070520740443c40c0f030042d802040c900c03c031035002064203103010301c10006080d60410014401c10024a000159680e0030400341c00000d40b406800c20030040a002c0020600c50810700302c1e589000d011704104440c0c5054180207440789d44210040f0710a29921300821009000068551038160b0042d1141c0c2441d0300c2c0c50486600e503408404030300b114680c0d60148102c0c4408201c4001c00080c09040c16690b03c0e01316a86020480e101142e5203403044044441541c08102e9075800d4030039545054031400c00940b01d003051000c0e050029 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518748785 1250 518747535 518747569
    0x90e1207082101030b071403041103070f030507090c02030a0c0f020d021c050f011505120f010e1027120e04020a0c140601060215040f0b131401110406050702 69
    0x4a148039100b5629003005a0482e805054102c1007900c44540407501905500c51144502c4801e0002c64046104c1e000110a02c0000804540700c0c036907590160100e4130307400d601c02d480e0f50b041a5020040301c01d180c0519007000c09070784040c41c40c01c2c08844018295101c4404040c2c40d20039903040002c21034844c4d10750030150580003043da107000c00c00c0c0d02d00415501641c0001300c8013070141551070aa202c0781406000641e00308a001107a0041c1401c0a10400c03244850701c20101d403280300b02e5540c03614400c3c81010101c131481406001c40c0c0c5c10180a140c1a1031001e01c451300140242c0506020312112403001030b5000358080000240e29030301c43c2d0201c5011481000030355010744000f900c50788164000104403c102e10400004141d00030500c40140c95102c01d2003900c015802005d20b07144075504050b00e60707502c00c4c400c01e042401505991601108980111500400110f00030706243c240002d0a10364801c581c0300358020700c004400c41030769041c1400340e4031038401482400f0845030115694141030455841a07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518750035 1250 518748785 518748817
    0x10f151217070f0302010c020115180f18020a060804080f0309100e01020c0721170c07030302070513021305010f020a080304050303070305090303010806010509070908190c090e120708 80
    0x1803d040608403072898080700035610f41105884c007140107004100c40780094950409005192440b403160110798031103d8101a83c0e42c0c0950704001c82a44114001c4040e590f40c0484001410300c180404402c1f00d03000542030201c96001c00c0700045000c1c003140ca100c25079401c030540300e445659000f4074103030010b454524158240180c035503280c0e20542c0038190030091642100e5100d503840301150010070300405a07280c8480c44e28a040e0100e0301c0c880140352201c6252000600e84282503000c1400d00d5850b42040340160021031040025181c220400c50360400b810b0811072901000480900216550b48207050500a02c1d000c0f0311451402071051102c1035400c104801d540e454070f443c050342c6960044078100042803511001c102d28640000660307060f034401c0c0b001841c1c2c0b0390900e0100004404020540b4003040307940d120208407140240040d03499218140080da060644501d84000c82c25520b800000e0094681120910000c0000640c0c40c104030810306c2c62560343c4e081d030610101074032541c120080103a007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518751285 1250 518750035 518750047
    0x90819060615020a0302072c0402030307020a03060c090608160e0f1003020d1b080a2408030a021213060c020a0b130603060501050307080a021821010f151217 69
    0x14010444d40e01c000d110782c3c25104540c3d220080c082c0e082c15400f0290b00d010080e6840c4070080b030a180b145540043c001000c0b6030070a02907a002524480f55038100700c41143e110246c076064242c01100e03540c05000541800d00d030900e08641c04510074092044420100140c01251860382d4560084641c2d4041c00a41010710780d280420303014001c1c0d4031100c1d401d200146041c1b42201c1050b80c10b4020044224141e031440d40688074510408064100080f255614010340c0c01113500e09032580419030000d0581802440d00d4820300708001c1e09002550f2600714000004005040c060702152050105842280c203003546401403600204d50100f81c10307007005408000c0014001c02c0111005290011108142c0d8144130b05501e450045641b40801e0700c2c1d28012403024004201d404110f41c015204150041680040f0003411400260030402c4d6248440541c00d807000342140c420b0028002c00303400101743c541c1071100165846000000007501e2254044a00c020310b03c039020480644a0900d00240303a10744691a20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518752535 1250 518751285 518751287
    0x50f060711060a0f1403101e050d030c05210d1109180412111209130609020a0311040803040e07021e0c010f0e0d141002030a060e07090819060615 64
    0x1d4162104c201c0401d503191116401c9000c440122803288050040940c5030078075107041e602401041c0c02050640c013528010104598132030a1503611068001d82c0e035000c09103418141701e41803c0702024200c040d0303072a81041d0348040102e082103d000340046500010a260300402107481e82c0180703a402903025596604001c40040d000491034080c90199500c114000c180b030000b902c003074000404c9000b0503008488007008007107400004d4a03860402a105403040c00c41e0030410b02c2155034540200d80380940c0814840c18480e89841a02d9188602d1055203103001c0c1040a101d40c0c90040744580c241640503d400155500d1091000c084130708a200d4074000d071207c908200680301c16001c0c01e1180020b261800d00c0700c400c0d2040340c1480d40d070740001d008a02d02c031902d40c4a01800240e02c10140d400c91048030040e44038154544000c2d440303885046400105a81040a6410034002c003030322580400c00c2c07103001440904000700c1c031045075000c0c021030000001d542d454420b016100a41c001e040714016145006041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518753785 1250 518752535 518752547
    0xf08270c0102190b070810030b0915090703020a14120607091509050d230d0504050f0d0302120310030b01090c02060f011a07051204060c1b050f060711060a 68
    0x39000b40c0990300c49403110028295809140032010380880d407030070040740000b130094120581140e00510320001503526522100c12060054501d000654041c000f203031902d00c0350301a415008072455002d030814510b184c001900b146034034011181c04c10f00d02c0b007000314156207425590954003010420364086140c099805050100305100340e03100c02d14220705411010b441021010280e500c014008110b0f560a03444044541a03101a01f50707401541a0140d0107ca908220741951002c003036964070f646908280a00c00d000c0490701507203020348018201c8600298002c22008141002094070a449640c2d80150700440ca1540e407018040880fa58004502055103800051584c421902115100e40301c06140c41c1030782030240700304030605001265001c3c2c1c1105050052085901800440711501016945810554000d5200718007050403107808808119a08143d9483c10b00207c00341c04d0300c40d1811340880c01600340100b41d00d00c28240010700341c00b0480b0b0030b10b441c84078400141c1025101c404040c0058a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518755035 1250 518753785 518753803
    0x606090307030c0915050a0e070c1509050c04090308160e091e10030213020702010e040c080402090f070c030f1101050712060f05130507210f0c030207030f0827 70
    0x88541084401e50a007108118a5400c1b60b0001e0091003100b45000711003228160301400c010704018800356040007203251180d404500640303807000040d44d81d82c0c0745885490f2500e10101c070f071300940c1040c0c44900401d4202400940c0040701219000b45061448011038450104090752a031002d108400e01000001000716603032340484010440b6095140c00003250300e03604551000a41c088142d4291500103001a000307064018030604000040125440c0041c05495016040700005403c1c04100025413808200c0280c102c805050300c59258140b4500081204e4104000541407041c04da00300d2562700e105060300000c00025000030022803c041d640100021252040c00c26204e003008d601240254441041ca011180001c0600850600c0301001c0005886c000f09032405000c0350251048008410a8140d19003500c1c0d80c40000e504108842c4920850354405151402c0510600c03075003001030f8000080031205407982c20705840342e940b5212401c20429603480c05030b10205140070025044031001500c104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518756285 1250 518755035 518755049
    0x1b130603211b1704030b01090c0f050301061403192406050a080f04020301020f0313030306060908101d100212011a071704210620040e0606090307030c 66
    0x201414007401103030700141a003500d061a03103800200c000081c0001440303034900c444180702203050039034a0b02c42003a1117809901500549072039888004506a008900d040c41e031700181003981c2154100742c402803041980a002b807440c4400040400c0d91007051112204a0032148507040c0301840c0d092205500e145001c030781c0c4005000c490000450007500078010343e00b080d00b443c0d6510001d0381e034000100c1f40c00340300500241d8065600300540008111030030700440c41030182c6000302000d840189002002c5503143d5120104010b0080020b1240390400704040142405610f00030038a04000145850314540c0c401d40e5081711711841110000003503840d0041c0c904418020380c4d2040a07a640c1241c142e0364441000d418007504404c11000000a51951303c06034000510202241804d0700d54880b261a480d200420249401c101d002240070001c0e140990003141981d062620f4499040080343d50a6000d54002c010384400c0b9000040c081d9194003095070f214080050407034280a0345c90030041c403126101c1c080c0c24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518757535 1250 518756285 518756333
    0x30a0507211d010204080d0513030204060305030a08060a0e04060b03161e0b0a02060601051e0a110c03010e0c040c020c1005040e011205030f070203011805100e0a051b130603 76
    0x4140b19010700c2520110740e40c2d80054125003011200803540f42e848089070500002040c1400f1025032198885c06011f1031144004640d540302e5484042c01000005000030b105502080c0e00f071107007807402d41481d50015800900400c0c2c0a400000103420a0303a2040035208410701042d000410302800340f6200203415580c1c6a810445480d0107400072984200048807025078030290200f2100d51094005140030320a610b50b41c1400d140c140d040c252603a0144441000142c8072044c08443c5010500c551261007000b140200400c40140d5400d94640c4681d20140e0b01c25507072403102a401d24000d0008168141000303258410310349002401819a800c50300509907084001000455407091020340043c59039040002181000000c00b83e1486942c0032810480c0c06540b00c11424900c01109026910140e200d540580485954858041d044a9003000c4090440e030104c4040c0002c60808900c51903940124940600b800d840c100105900308414011040c0d01480c0800020a12a075840700082d9480781140304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518758785 1250 518757535 518757581
    0x606030b0301090f0308130507060f031b09091a0a15020105010510170403030e0316021315030206090604081204092315040f06090e0c04020f030a050721 67
    0x850300301e50aa00300244554907048004d400701e03001d03070307403a40e030005403002d40700e1201e4a1955154103050b816440000403c80c040c0f94800b905402d4024401d40364041c14120a001c015200f004004540c1e501ca07040905a941178003041c0329003010803c5006100240480305941e41c2d55030010401943d400750500103501c1c140000ca41441d006800e0305402840d40d6641400d00601e880b03403000401c01a00072014199100200c41000d0800c1c00641008000d14805d0b003030303404090041c05011644804403607125441c1200000d2941c11210100042d260142d0f103854450301ca0301c000c0350640c0720701e4010043c18800c040800342040e010b00000c00994501840900c03030400c4c01c41c00019010383c450a000c0c90401148006400b03840b000071000801c000c020030100702c9440702d442144c115030190300300340c1b0020b0b200c40758594003400802080d100c400c010f903001c41c42c201c0c40700800c00e00c40c04058030807a007480c0c071000030601fa5440741c00300c0c40002218000724042c101c00e041100c0000c0223106c40103907040c0642240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518760035 1250 518758785 518758789
    0xa0c23030a030e0f090c031006020d1b020609030601030c1701020a050d090c0b03070203040e0f25020111132606011205031c0501060216080a0b06040f0504060606030b 73
    0x144024000090010403003452103a41c02d590403244030f4241c0703030000c804088010a0740d07160b1402a014003003111026030340e401e2030310610602c440c20703800c100c0c155441a0709414405a12640161160724010510224810301e4400104207100340e401c802e5052141e00d002009200c452060101140c6568140c0d10403545181c0116090340546148040400c03000c0c000081b466445030060100144076210100b4501d480700f4200c1441d800c1642d15400680c4003103024084081307850092608190100e1070350f0128581411203247c0c517441005007904242d405441d90303040600035008a980705400e00140c82c1c031242c04070315952211005100d43d08116074440d030f464050654810719030812045601c0031b0070300d5a091410070400104404011107140c8010060203461000c3d52101603420318000d0300114013949490002460060440d080e00d10041800e6010802c8400000304098090b80c4103c50005590f1030400040040c0030071400d098440d07050a04101c10807030300d40c0c0900180c46981d00c0400152240c202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518761285 1250 518760035 518760089
    0x80105070801030201110c0406141008010e16211b0e090a0203091f09060c1422120302010509240c070819170a020711040f020c0a0c 58
    0x4402010071010401031000d548603a990300d408000d11400c41d400441c140c008242120001c0e4410604920000e813118014603040104104071003483c980400154102144403c401d40017900240d117607924980c4c2160300d20701410402d420924074603603c811481703c120a010140420401042c3c05200c0070004900041c000c12209514010150000301c05588186018000b540090f01d046010b00c40c1028108010b41c132080028698500c0342c0006c10844900c8c5000781c1502c184210904c1405010070346824042e6040e429568640040d655446005400303441149851039030f90032175028500441e50010500d501500311500031248102124200c100c039040324032000d05102d540d5900701095001003981840304001a003220b43c02104d519140041d0a080c2440702140074642501050000340c400d0480106510030650020080c40190700d4400160f88680003116410382052065684a05040c0c200180750306603012480301c0782c2100c440101908000188612511442c4140500000c01c00c6212030549 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518762535 1250 518761285 518761291
    0x201050109050112140f030a05120f090d03090618050d0f030b03071a12010305150601030c0806091e010b090a0b040f06082208090108060108010311060d1d010c09080105 74
    0x145911800346859030711045080d02112003445c05d8400c081c10440c1c031000520040c4600d1510303442d429950922000441410103000307080890084841c5c00b0040d034024041087c0c003030075240f4a8001101d01440c542040240105104106038514910071001000b1002813810290001c0e520342542c000c1020800314103841c10f658120360140c00100b410082820401c000e92024074608031418105004038440901d03802d4241e1040d5655400000f80140b4100f940003130700d4100ca420302e01800900d01c0302e50041d028010203040315000d110100c0c0020305547c0108525180c007030b9440b807600101e50b5900514926034000341c1c401031148440d10000145402c00a00f154210b5520049001ea00c0c0c0c0340c001f094440d590014509444280c4e0510380100c0380489005c29802e20f44204030607a240c0c0e120b0f8000400f00d20004100d9418400194010300c08240c0c40c000d22882c4000840300c8950700d03410b880d01b81d0041e1100902c64048800683c006221021040d00008211005681e4962180c0d645504250a0710016 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518763785 1250 518762535 518762549
    0x30e010b121e030405151b03042420010209010207050a23210a060f0203040c09050901020c0a05151614031e0a0501050406050f09221407030302010501090501 69
    0x2078200ba0140015441c0002c40c011034201a01c0c1050b585802042048032504001d9502003800180311400550204081501c0041c1d44000c60601f03080c05800700008241220076040000001d0341001800c0c8119100b0180c2c1e101130b1070901020500d40c010b81c0c040d400088509016000e803140100311820444c4204048401c91411802c3c0c0d000c401202d4021618000300700c8c0e410a00b03581901000c0e070320348000040082202001441d950519050030412100070080c0c2058460041007031101240500f0784400949200390b5000541e038464000860091046650b0112103008508110051150106099041404d005600020b0355074040103511000b504110f041e0120b17006030580010311142e0f40c05154404100c204421044825221200b08010102c4540300b009444d400180141c1c00c01e8002c040040805aa0b520300042002c0d0005040304801821102c090107800840701c8921a040c00341d02407160018803441070361038007000e0b982c0c803500c0c45d002c1500590308007000015421120301c1158101d88130 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518765035 1250 518763785 518763793
    0xa03030b090129031509090307170301050d15020d06081b090705030414031c0b010e0312090d020d020907020a1103070501140307020a0803070c140f0c09090a0b07030e010b12 76
    0x605500303110765404c040c011181060218030b42211644030084114042c0700601c0085499032080d1500303883d18041000c210880c10420b0004220640302c021464008550011035444001c281512160013802144940d8003034504242001401101c0814421440488002d4007045040000e05001c0031801c1aa01c00c00064401c03c00180410b4400d034101039400100c03c00d4030b1601064480001d00c1c201441020040e01d581c40c80000302960700911031000201003507000d4032a00a100e00726903c00d026115550b4000d03031101040305d045554a0218094180d401000103045081040c4000d603103200c03500e01142c513040f020310580c0880c03800081800486c0d5050359a4070683d14002c0142d900e03a0409407030441540304510207a0001030304107019620a400950340c00481c610f46041803061100d60b80a100d00c0d030303000150003000303034600400c1d9800c07411000d9551020079203400103864501101507101501091040c01400070311545034102c900c4a16403140248986030142d020480c901e194820f00c2e50250380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518766285 1250 518765035 518765099
    0xc030f0103200405070504210305180d140304030309060306081207080d0e1b220b0612150a080c0102210705012a080c0403030309140a03030b0901 64
    0xc0c20a03a001e81020812025200c04003402c02003015600161607090200700c1c0030030180085d5464944401d03078042c20183c410000c2400741c0f4080c01c3c3d480341525041841022460414440d210b9401740f0300500d03403200020301d004080403022900e0b5042402308070700280228500050151003402883c085c2ca0300f00c00509030b111071005400826601001084032002030500c0340c841822400c2c465400021225400740413007440d058420f82880d61460b4000344141103810780c00065203020841c11001d521200b10010f00b4203070a400081c524000c0489011442c200c41d001c100260390b9a200d0802c00007825a0182011511850f0365a103e014900030340c0c0c0160f00c00b4615006841580703d406050424207203c41d403405107e503c915085d104810341003001c080744013401c400d005400c0700d00003140010a14016243e4148481012018460381c8005020962160100401c4c00105514401440b1000e07003180e8416141e4030300034000c2c00d8402841392003054030f00000200714a0b81c0c00002d014030412010011620307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518767535 1250 518766285 518766293
    0x40c172103070c0602070507030c060c080d0b031603050d090f0303050702090a0e030d0e0606010e0a140a0f060e01031119050c101d0106050315070f020f03210c030f0103 74
    0x604001c0000b8100484001d00c038001ca200c0d440180794050040024103205801c40c00c0606031814203a21880030841900c1c0060041852401aa1505030801c000400d0302c1a084001a280c030302d803240007401d00880c1d0800007040020005080040034410345988980d540d03500c0400020144078030003c0d002c02c01c100410001440c1c84602a640904003000c00074100300011081451600110f48442070300756140c0c000343c0c083c0c03010048654402002d00c2c2c9240c55041d503202141c55030245100d00c0d4454101400c4421132036a456001c40081c24100007000040355a078240145a00d0501d02c840e0b012900d061a0841000045801c0310b18030071650041346501c04080320b085905e80c1c0080c07080b00365406140b013800680313086030184441065a918010b0798400c40c1e00701c043c0c2110203a910940c400da01030464040b01114031020141d20074494141003041a0070010141e05100500414541500001810b01e0145502200e0386124082d085003003143e40e505c0042ca02c1940c442640d40100c002e40b2140100000303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518768785 1250 518767535 518767537
    0x3120206040c091d0f0a0203070f1202090703091a0103021f0e0607020d0203030426031303060c1701060809101118030a08030a0f0c02031801030e07030506040c1721 72
    0x401c0001205213a04152080450b060801e0782c2d0071019103402940c04030040d0703e010449127003d0302440404509007454525843e41c81d50340e0440c02170141100c040043c0700c103800380e03000b4899560400c2140c05564004942d82c12241024041240300d01c000e2400c2c805028980c507400c4094031525203450955920310001c0000c40d0b00b0100c07049a0000344410103000585041c0054401009504140c0100b6040c02003400e0b82d150b0b00c40165680f41c4e10074001c40480f1140600d4100c1100e030400c0300010040481c090881e5041101c0c0001c99101d070540c0000101d01e544105000e20481c40c020503100303200528007000c4e007907030b11b508460402201e003803000310100c1e4003281010307600000050868240189030365540d40c8a400450390380440f10342c0c03001c20f6012101c80d4001c10030064000d10145103080602103020b0701850006491034109070b55050b6084a00d1400c01902005c0d54000301103e65518080c90300c0b0242c500c4038003640225184880800c035040f10002071000e008200058485d03140d00d05162a0055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518770035 1250 518768785 518768801
    0x90705070c1202120c13050910090602030a0606050a0912060b030d080405060901060f03020f0102150a0501030317010e0f0a110c0a0606152c130b1008070509040e010b060a0903120206040c09 83
    0x2305006800d510100701ba6644205403d441c8100009600c0b4a41410413801b02c034401c0d03012606101041003d19501603010348042d0a45043e60344c400c604190508010000302a581d060580611071031569098041d00304081d28403561040c81101c10b16a00c0410b0982070307032024410000141941c14047c001841d000d401e0403c1ca400610450f40014000b0000346100201039910401e019507610040c0305059220340900071401400e002e9082c1d9502d4071f040350070b00503001019601440c449001003135100c046078114802001010240b2030300c803a44407000b03903140c1030018001c4603594031b041e100045190301a000c0c0304403801c1585614401c0b11040d22400c1c91805262000e010703000210403144003c5c0e40b0351911001c5485110000106100d82509100d25600700c0c10400c001c0c40540c01c00c00200301d074490300f143e482c1c12007601d01264860660100601618801d902107910030740205525140c0d030341c407448500460340100301d2001c089096401c1a6103c400940d805411803401410901140d0850340120407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518771285 1250 518770035 518770051
    0x31603020910030e0f03070c0609050301050708060607031e03141027060305070b19080c0315120303070c05160b070f021f0f1101051005090705070c1202120c1305 71
    0x1d00c000c4603c5e410b810342c0d02c60001255868514032083c01030a0f031190201001c5c0000f40d0080016041615014040703040040c0380c94813500001031140101440b0b04003004030750f140c0d104410791694003000702401904011010011008420000801040320703180c41b001158528949140300120044d2990700e81c81c110700c0d10350320150301c03010000700003841081003200400031001d040d5180c40b43c084003440000001b0480c401049603400c00d1040c078501200881ea0400f0700e0310549018258050041040301e038461003444214040030081280258000c0219551584290240e940301d021503109418803040c20b01031108001c0040c01504002141c1a02c1c05118900007061144c8018881c110305105040582c00d01d0b0020703041c4000142c0682d0450307202d402c60150300000b84000c0c540588000d90710482441224441c0c0b04a40101e41041d026600b00e919181c3c0000b541d042090f200d0800400903041c00728224000d4164404c1000d0900000c1100103201100904044074502900ca24001419002c1c0c4210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518772535 1250 518771285 518771293
    0x80f19020d02270103021c0c060806040e12040f0e04050a08030a0f09140c0d020117070e0a3b0406051009140603010b01080c0409020c21031603020910030e 68
    0x207880120b55038540a1042004118041c3c0380d0305500c1070180314401104280303054071030a12031800081003071002d07400b5104e80f49083d160075a50800020082d0a40c0c041c003043d9406100c640400b09a40e200041055441c880415506155105031800700301d14101c0380a030032a00600183d20008036488002d5421114116022502480d8001b40400301c4072801c0c02103c04c0100842c001358666800d020043c3d0182c41101c040b41c2100094002070211401100c03910b4407504030340005045d032402034802d01c080b01c902420000041e034031140c0740c0c40043c070226140d40d03071609804422030070403618140c5c0b0100200b10318005135803522266205d0010b050080c0181010000004000c102d5413103510544a1440c245c0b1114806410620185821200c60070382441c100601c7d0340030010208600d03002c81c0d003162103601307006985a4201c025107080c0000c5440c40e804030015a0520721414001d40042c4d801550045d80c1c03c01c035010748200c154124481c039070740e498110f8414800ea0021501030b50101008480c40d405075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518773785 1250 518772535 518772559
    0x602040312020d090e07051b070306140106080903040506070311010f05100f0503030a05070f0321051509010f0510020a0c031412030906010306111210080f19020d02 72
    0x2564415010300031400060f0300c903100c035914203540300181a0080610120185081c104290010007030302c2070b1290000d004580010341d40c644a4208a10340c002c40c2c001008110b146043c01c644c18072a13900384103840000f06580003044c1c041602004039000c0300c00081c00c20745441c03103541d401d648050304000e40314400c0d581ea90788111005014040c09200d011002820080c007414021840400b00d001d40219000e58800d002091070036812008540c80d06802c00c403028004180d5150840715a41201d000260040e00e82e864001030000e641c100301d024803c1c680a81380742070340250520000717103401d2140383c000b4140c50708200b2190070141c003144031213081c0e803068940301201610303841d9440107150310449081a0355000a0690074081c820b8a1040080581040c9941040a80180d0359070303042c040503212030ba440b0101100010750408890710908004441e0300103241c1780da4104d00c600c0e0a8428500740c0c0c010302040d00104180440e5a10401c641e0103680c1441c142c07240c0174451030442ca450100d030811480904 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518775035 1250 518773785 518773793
    0x60a180f0c05040f06020102070506060105160606030803250f08100e04080c16060e041e05040302010c08011a12060109030f05010e100b030613060f29010f1b06020403 73
    0x907980e1108520b8581c1070f902e5241810f84403114056070711040443e403041c001d80300040e00124119400c02e0003440e046071206060115a004031088000c010b0419180c60400020862034001961090f81251566007c06629680e0390310406481e109200c00901882d0402c98018000d014840e08aa140d681e03400c00203481701402540440240c030f09850140010a507001e21003000c101c6c1c0081c3c0c070803640600700030f2071a098000d40700c02c0742c0d102120300c40ca40707a0140c52a80d01204284801d440089002400715051504020b4003c0c4822842c140004440400100760b80b01d80c11001441ca20100d51000e14180d0030300c100c0403030581d006d0030040c1040180c103c000086401e01c0c4035404418021000081c8140d01318803d24600b41079a14510a900c3c20103401c504656400315400341c0c041d000805000d1560154908070009081c0315240280700ca107001c01001c4012181c160200c54000b0400d14020000070a10064403804a000c41c1c420001d0001c5104007204c1c00200c28140c8100c1c443d520241c00d15480b595 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518776285 1250 518775035 518775041
    0x10b070f111009090501090c02100f020d050a200307020a02040203040c0e040804090c0c030c020609030a080f070620040302011107050d0303020a080a0911041d06010303080115020105060a180f 84
    0xb012030005291903018805500144152030051a2940c0100842074108202075240c0074040401c4048039070340c5452507034048154044030134518074030504100615007942c140009108404034600c1c90045240400780c00e40300c1508481c041d0510703030010102140c665007004003a500007001103410382e614803030024540203103880243c0a248622440c40c0c589040829400c110745080c0920000c04c069901a100842d40101035611029010b40340d980e034030400140840c0c07622100c0c00c00181194000a403101682d2001000740a6907845030360148441c521001401400c0e00380b00c00100003496080004200542c0039003240600d100f25142a5a03c50755500d00158403003005030707020740c0420340014002c454280e00c08a61030313000001800030000462561070301b00c1c1080e11100700da03001c0c60752089490710180703001201c001c03100e0003c0c080720103039030b1a8a001004e4090030310403d80c1072820050b112965034010b01559102c1c420180c01810b00383c2c81e01c0d010319104400312400510450340e40110010243c042c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518777535 1250 518776285 518776309
    0x108130c03080a020109120801030c060c082b0b0922020114030f0703050708100b0a0306030503160519080a12020d0c020f061008060a0e16060c031403010b070f11 71
    0x500000340c841c8142c01d00700c10307d0b1007600d902400c01000c040148002500d0240304004c3e10000d00d841140b54015181c012890302c201130f0791074000700b01c9901d03410300201c68803840031503010f2845044c480d5012850510400380400c0c0e401c2d4000c003a5145000804a1910403220b1f03100e801490402c0300c20303142c004038003000d03030059480305103000d00d000401007440d405004050300030301149810915454110703c12954242e081c01008401440083c030719a0f030300e10a0304054007441d04413081c5e075035420440c0f100801d403045c007001c11145400380c101e8401e0070081104040c08000d070841c00c0c1a29006640c98220f5001182680c286680d980c02d000600101d00c071442081c1640303816400516038009981416071404100903c0c8914004a024081c04405004940183c0003d000403010811103c5041030508122004004100198480500040d920b510600c01380906000f610303000030010b60911030790110700c400d0140e103642e010104100e90000b4400648012864007070b00b020034602c4a14800140c003040b100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518778785 1250 518777535 518777537
    0x38120105100203070213060e0c030c0307030b220212100602030f0a05162312070f020f040504080d0c18051c020a17250b0703021c1e020703020108130c03080a 69
    0x14045c02d001c2c2140300124650809c0001c1d02c030604500c0c1284070b603500d41c400101290300b01030f200c8105c040341d03031108422030b4908256640303107003040049101064001c0d00090a000400310b00170002c1100040702e9500b80050f0791180d4003440c90070400407000c8295502c80d024800401c00c1c100b1601164a001009901c00988240d020203ea140300d18502140440160100c1800d90007865002d224516128201c402e0103034440090040b4030344500000740381d0a50020b107203801c241840c040100f001801c0e4001c01d0b501c4081402003051860600d011106d5680c100050307401d154103104103101518054035046c03004842000d44025030802c03a07010500341145544034003005080710340d81040681c005e10050f195032201a0032800300821902001014410504c21218030b172800284660a251081c4840c80c2e9407038811008066100b00300c0001021038100e01c848442c003002624001d0301c0035101103100c004481d0140d503022040e4a901c0b140b41001c2046001c101c51b80000c0320000400160100c014000030344071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518780035 1250 518778785 518778791
    0x102070c0501120506090a0e0a02061b06070203090109090f020d090b0105012d0e030f0a030e09070c150518011104050103050c0412080a0938120105100203070213 71
    0x3a000003d40501c0c0410200010281014200700950300c0d0008030a034009030400010900300f0300041c07800d082001e0200080d41044000070310b103140546c01c61031400d8610120040751281e6a5800d0100d07207078041c140d88a4001801c2040411a43d90a50172808072009040c10042ca45211081c0b001d00f20340208408450740703101c0c00c004102035a0400c8000c0c0265401c0b0240c2d40e40e06a40708075619554101e409480140007080000b20010f4404000907094496440101d03483d00303546042c013420b04d5a400f40d10500c20701607040041d000c82d202d42000802031390b00a05442c81130071100e0071007010b000028443d2040e2004c883c11304290981c24055801c180420742d181580c0c80342013000041c15036900030716001c00e010041104001240c0305600ca0a806900813480940b42c8844120850380941381768002c41d0303449100350407143d82e00e021520281420450700542d103200003480c0e00102050055150204410082c08010402c9052204803c02c0e40180c5e8410340e0b282104940c00100300c4800c130401a062156 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518781285 1250 518780035 518780039
    0x14030c0a060f0204180f0b060c03070c140f0d0822140111100c0903060608060f0f010819080f03130c050a030f02190513090204051003230309030102070c 67
    0x20349204007107800030403400c25032405007014201d0141003001d0380040403d80d071ba002d4142c80c00e09640e21443c0c281c040100240d69a4080e5003c8650b260420881036a50303a1040c2070004101111950b800c503100006031196100441c804200b01a40316400c0d41681c1f400c03c100a03a4083d4602c0c20322403280041e10001030001c060400d0101ea05c140b8a108113141400703101c0c1c01c000302940740040c0d20304990140c0c1c080852180090b0100301c55103002c0c1d41c00280001e09088021404c83d401240844c45004c510f04212580c0d41c6908550154100038415014107400c0851000840c8086c6035440319891f0152070000e241c0480058544180c1d030003158a00460701e074545803107081142e15007005008040490303250044d80c4c00d54440301001c88d400e1800a20038204080f010030710707407139410031900104001070081c0c24400c6010740c2c040c081d2480e007000702d10076403500001815140d44100010292504240950002641180110f010b104004a0b24070244070902c10318060399024001000594810502651894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518782535 1250 518781285 518781293
    0x10e13140c0408031b07120305040608150901050607240506010f0504060e0103020306041401030804140d050c010c03050408011a040c1e0f11030d061e080607080414030c0a 75
    0x90040e1503014092010481080f01003000800d4455550128100c01ea80404540000b89804565440b400c42070203964800024507420801400480d1000e172a500e0301d66031035008005040f4802c400ca01d50103030070f11005000300c0c100240070300904c5105540b201c0b6124504c00f6214000e40c104020260703000d40302d40401c81c3c10359010082d8112500a0309182c2d00300740c142140504000c2c400d040c414101503010000030525aa180c0000d5921490701107041d910b56101c0c24029001c0c0c0c03203801070560140f103004008003181060703c0c405004075000301c0548803551103840112031a1108020a504025007840046004c0d10284075a841d41014020441107044c0c1031003d00098481030319104081c0045011003508203520034105c51f00300169894030f5556040b90388410b855001300480d4080d01480085444455010643d00c240700b9a5843c0c40101807074410049030b882c83c60824010341e00e4942219020441250207400960b810600c02c01c148007610f01403000b09813a540010403800100c0e440020031600380 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518783785 1250 518782535 518782571
    0x120a0203090c1206060f010e0907031d0c090a09061b0201060303030b090f15010224240d240c05030a0b0109060e01050705010209030607050d05012111010e13 69
    0xb09000b41d9070300c0740f4407041d056255191580107124500403072448122042680c800d800c80d8010490090450440341000300c4000d0040c62124007180300c011580070321041d5860000341a01d580340006001001543c1c4640ca003030043d040d01c1004440e0251106c180c01029502c1c0c00c14020300003000d5000052403031850400500341c0d00c0880400303000382d03002c2040c081d501208c001c8948c2d220100c41d01100c154a60300b0700407841d01d00780a4003118890301d906401056903001042031801110f11280580303041d450740c6054030002e0301c841c2040758454080403049000582031200c110780c2c06c10003d41406440e0403031081e102030b6030008201c040041c000000b01310030300703900e0311031495203410a2030f04480b440d0a00c8000f8041c0005c0120a9050240210710704081003025011116007400c0601502c806082100c00580203401c09490046500d05001c00815109900d140070380030400e80c240202ca824416441e0b09100e6240c10300083c2c100301180d03008a09580ba02c142c03241c6100e502c160005090515034480c0c0c041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518785035 1250 518783785 518783803
    0x9080a18060513051017091608011a1e040204090906140105010e1c020a0b1308030a050304030f03020d110301090c0801050f01050a170708180607021c020102120a020309 74
    0x180031061081e041801290f900030419680c00355540144082201c0c41610f00711426500c00301d80f07000100811591301c10220700001c5d140101e0b0140103400d0744902015007664852050341c0c445601c010011950381c0340140c80c0030305484440c81155140701420b00454140e9201c0c4c1c10202e1000c1d192000c250421000d84034400f4800c1c9007075086100c2c4d505080009002e103800a549074818034520060319074124a40c00d000000c19401442441400d9607444101c40c180c00ca0b03541901411700035a07000903d20004000c03200a006c541d42d4140c0b40d0790b6640e5003511240b0268040d5000c05609105850500a4078821003811f000e0125405480f50325100016040c3c4000421017420070000200400207910b44480c4900442000d003000c40e120000c2d403c4c1100e2107240b4120000c03a48100c00280040c05410a852900840340d501412031080003521640340d0710a402e980110041c1d000191045002a42c0900403a44181c5ca10025141c02d882d005041d10480d016111165102c1d400428400010010004080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518786285 1250 518785035 518785037
    0x3090304060801091e02030a0b040e0c100503040506271902100512010509060409020901090903020727110f041e08070b040e090712062903031c09080a1806 68
    0x2002c20540d1842c1d0107001100b00e1900e1178141c001c40800d001c411241c100c402d0302900a4402c1200a500c108603e6139183c1001100d40614031500117030b0620fa00c141c046274403d9030800c0051060751144590b01c45032100b0782c1405100a1109100303a2401c8500740680803a903603246240780040303032031030041040700040c1c00e41400c10706c2003c200049050008903016411608100d036947c00c15522072000c45c2c084c2c150764200942c800302100c0040351a00c19684000b005038041d50031103c5031a202c6008408001000408000140c03004541c021984142d4105034040c0385501545420300d0a030000d400d1803600107400155a034000415072800c0401ea0740210b20007403440000070003000c2d14101c50640c641c40359005051300743c180c8000044944038108002e0008100b54444080101d0040c20180010100d641c00100d821001400007554900041d03140c07d24824010080c0d0301d480d40a28100c441c5400d910f0710800c110382c480f03400350301085040014007003035419925000c409080418142c107180c0041d0300500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518787535 1250 518786285 518786291
    0x30303070210051302042301050a0b120703060e0108070501172701111315030504030806010e0307050a12120c03021207030e040603120212090d12140309030406080109 73
    0xc0a01540060040300751081c0c034000145a4071046a800303840b4440c00c1c0040e4126041c94105440c0c0380e0f00414001c1504141c0350a004c1c2c82c0d0302d9001300145051617205524151000b030101584200211400d10f8104906060000d40c941c2da80d401e444103c4000d030300c005010340104004219558010041e6015802044458501c0d4a880c2c100411208003086d0455400340b0b086080d0b45a6040951100d403424020700c4446031200240113200c00002e030b15001e440b81c2c0f1000c00c00c0405919000340240b5005542c075844c1c061166481c00011a018081408195410b1241d81c4001032103484418650010346282800c500200c5101d082c41c008011903000380108201c041041c03100460f0303010503020b040b0243c068503555121503034182100c4460b030480800303a01900d081000420003003030915210113804640c0030390f221244206007d000d140100042c4a8105284030151400119808007070305004ca0315050484054141503201100713600100c4210754940d00014007804881c0c2c000d0302d41030040840c0700040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518788785 1250 518787535 518787541
    0x30f060a1d07060507080f0f03101203020604021c06020304061d0a030206040b0403110f0106030507050102161701110705101109010507060c140c1b0a03083106020604030905030303 79
    0x707140e40700b9030ba20840007008804a0310304100210380707049032422080c0f80d88250300c1e480328080c600b00d81d9005861980c600d052024000501450540d804c1c80015095000343c846540c4070340074007211155402e039000d00c441c4071804200000701f4500c0034502540c0900c0c0c0000740307a0442ca982440d82c0080300a11000e070341c8403088000010f0382c009850b0f0b601941c410440c00142d00c4514098500710700404601d0b00300d00900c0b1100e030b507103e01540524100e0b8044c5048070b9803182d9410041e07803208190703851064510442201070104220341c004411101000c0800002c81148901d01c1d8200740e008528100d4040d00000c4bc942d064041074011801124107801130285001e8a80001070181d101c0e154000b02407980b140c0c0c400740064003490302c2e400051040058280e507000ca01000c00c2d21980d81041054010071a814180c02e1410942c141d001039070707400300b841407814182c031020303020103034125407009054400241a41d801101059112008000e250002d00547c206450041c003140920381100c0c1c0690b0041c020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518790035 1250 518788785 518788841
    0x408061f0f0902070f0623100b090f0d02041d070923100e01060c032309060c010908070c050906010212030711100c02060720030301051e030f060a 64
    0xc0301c01210115000183d40c1c2c1003d1802c54460300300742c10050301d500d2078410004002d4904000b06001040e100c5059002d60b0356580201e0900c280d580a944c2c0c0d030290074004000f00b4142090090303a9901d00404100c240799041c0e001400359104030403203401c80a1741e001103048020703040040c1d07006805184c6060203070f1400e0100022003440940100c2144030010808110280009440b040140507250780011045da180c1c840948031040507101100000c400004400382c140d085010518000200b140d25440c01c907403c410080b458100300b0030801295030310b04601002030700c501c0013400c00f984561008a501e41c6000c0c200512070b070707006214905640180b0360012410125604403540305003181410440c45415036002803409058803108406035103041458000107400003241441030300c1a5039441e00c01000d51040f00c284503085405015117600510060000d0324007201800040034078114012061083d000020389041c40456103005540c00202c20311000c0d01083c0102e0000c000c000040490396130740046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518791285 1250 518790035 518790059
    0x405030708160b010b0a0905090103020d0b0907080f070e01080a0f170c011104090608071508060d051b090a14010b0c150103030e010e270403030e030408061f 69
    0x5041c400c0000d80803030700c910108000b00b4816000003031103401e9a1602c1981c98907030710800210b000304195400010b450b01e0704100c180c2c143c80c0c2c00742030800581000c0e0380d05005a8005018102c04e8081d0000c04501c0e9201007100240c0e40c01d1035002061170900d0503884500c07492040e082a011500015440300110b091034800c0450194412140c002c40047d200d07408083e40203c144000e203035400d00740c0031810080200007510994115032000c20070706a0310520b84d55500c070140f0608039551224125180b00c00e004140e2158454000351460f40d0070750080d03850328141700001000b882008140da0124401d410913002c46680036101c4c1204100a0490008807105540144100c03d1844000240030301c10900900a45a0703842c0244075080803075860b0b1402a21481e203550720749000a0f14440ca002d01d6140410b801c0309140303550b180c1110361060040314a103980100410503010705445c2c0340c0456116004100400080c040540607001d0341c100b1070303980b00d84840300184241000b4500c101c11b0100605041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518792535 1250 518791285 518791297
    0x40305060c030f1e04031404120803040c060305160f0c02100819060b071407090204080a0314030709050906010905300a050601060819050c180a080c01050d061e03021008040503 77
    0x407c00c4035030310380310400c204107a219581100f0b18028140210408000200e00034501551103100c0131900c1d80e4561070210200c0780100c4500c54440001524080480d000390b28a516031102840c001104030401d40100354000d03151f404100014503001c08010406100e9426202004156081407216914290710a01540503000b40a4507031206ea080d00444071008009200040403108000d40d2502d41c0c4000c05a21420280700c20340210b113414001034002441103003242c1c400c1020b40c843c94501414103040c02403d0384002c007140d05101d0700e00c2011a1607902c2c0e03501a5401010b03000104110781c00c4110900b10180c0c803151880396a845039105d00005000407508905580e01803500000540d90344803000d50398646443c00c00d00c0c07140391000780001d041c0190018620748104c4c001105402510350140000b007003042c81510125086001c000440e076200b44003c2045084100d004200a40c503200c00e0341c040c510824000e01070340c40a001c10402c500b803142140440d250b0504250009203015140e041d168482c4c0307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518793785 1250 518792535 518792537
    0x18040b030c13150f08010c090806101206090512040f050603010b120c0409060306060302042a030b0f040608071410080f0408071b050f0607050307020603090102040305060c030f1e0403 80
    0x24022400500300310035410005001000d41201320550742c40c1d03054020210300c9034813000070b040d08a02150328480050280d02894201d40f2006c0307410718080442e500c0d240070803021100151a040300002080301000100d640c12121401c09984929041c401403007411241d100740d0003420140f00400ca00680780d070076500041c1c000003440d00c0e540d40300802c0404910942c0c2000010503c1e041000c41030000c41d50124042d60701c00c0c1c1d13041145c00716141c1d49400d0003401d84c00e40c010030a00c11010407649480383d00b10f80a000c40191940348405002c400043c19144540c0083d03200d071b80480c000304200610051210000b41c020b44030602e001c20441c5004000d08002080403035445140004501005441003c45a01e5a0030054118403807400005c00ca1002d101c1d441828070410007101403001500d00281110282c80e0720200841c5000d00d00c3c0d0034003489400060200c2183d550030f0200001081003445400e200303002d41986103a6030b117402c180f0050001ca001d131035140841170f40b000718600c404032005001d4105802d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518795035 1250 518793785 518793791
    0xe060705010b03071503050a294b010c030809030f03040b090f1f0902121f0509190b062803060f09020d03110a0818040b030c13 56
    0x860408602420b10000c400c0c0e01803041c0c40300029540014a850655500b0680e4140600c0d102d110f00d020943c2d51080d11401581759650307000c107018440c40102c0e11003107400340c40084146401c6a1902c0019441c0c180b08031291808150101c134400085060002c9a03800c01d0786001e485080c00000780b504d04101001014000c0740d2020070008030040003a2012440e840d01559035070301d1300d03280420800d41c0c140c429110034414468480160130740400ca48a440114180ca0382c003140788203022a000c3c10520200340e130000044200603d0204090140c0c41c0c95084030f4110034142003041745034104892004000306507075080440040c0b2103144003821580a00c1c1c000c00009101c4e100c840004a4090892940c105003ca0000410428541c00c182e101c00b00d80c00b500040081a00700d0035040d00351545464000e5100b011082403100180c002d45d0000c1845400100300c0701d10800581d00e110f00d50b4010b11769007510301800550040c03c0e1405005d000140c01064001d0a2044c43d1000455950409a8644201240c13 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518796285 1250 518795035 518795047
    0xa0f080d06090c050c3d09020604031412071e150f0c230316180e0612010212040b340906080f060105070602070b18010c020c010e06 58
    0x3406030005006020b40c02c0040001221074100980664421244034040c1e0040440024042170300001d0041c0350446030840c1100082d10884081d69070a030040e6600c40d40b035445038000d0140e100c1c0c07000b800c05184074141c1103814000380c02d0041d2800501d8040e90006c101d0400c111000200c040b98207211040d159000700c0700212191505074407010820496080303903880c01500082286058000c1c801000082c0c030307082607080d04032550000c6101201c1d040c1c005110100081003c02000701d100c605c3c2800c0920b008030148010100d000c0c0c01c50392640c04000840490010322140b45400120b008080300030034001c51030943c510031a2046408000d0028003131b00c0300100004c09104010fa0602c40810790403010700606070a20b01d00201510102501c034002440c0d01b000440c0050050980314050001207141c0c0165980c2c00e001140c81e030388060002c5410740e809220060016603184162400341c0c2002500014001704070509500311503800c1e01d07c100710341c07041c0300310b4940e031340c100c8070b10300806201340c4140d0b540311 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518797535 1250 518796285 518796307
    0x302040c0c150504030e01020a0c120212030c070f0f0518040305090a3c150507080d0504050d02011806231305150c092e020102070606080a0f08 63
    0x1c1244a002d00009403002005803491415071025200b01d119807511031401c440c0500490b510072080000402c4030b44094018031951040a46d0302e211203200400d0103103411030700c507049401c0d604102c82d041900d40c08120240488581e641c401800b510224514001c20b604d0030000031a001c038048031a001c0f200140c00401d0506203c0c00c12500581c0d8098090f045040e600c11501180302000c0040301d140049240d91185100d20b03c054072401c2c3c98200d400c0007029401e1640000301e4584041081d0140407041200a002901003000340020408411000926241c1401c007070342440b00007003a400840e45802c01e110311b00203101c0c40c040601a0040c2000a4003e82d090100c0f40041a602c11201380464020030443c2c9260801c2c030030800140724000b500c0442c16540d2200000d81d5065414200d6180c0a014000d20380c01c107071111013440076038141e407010640b038007908450380e8054403040c10340140d40000702c010502246000b07400081c038214000b400c9111068440c2800150102d0005048200c0000c0c016048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518798785 1250 518797535 518797547
    0x606221b09090b09042d0516030c090e0303070503191a0f0a030503030a022101080a1403030906061c060c08101d04080f0d150314150f0a1d160e07090302040c 69
    0x10741c00307c00c8402111903010311002412192000315035410a4080108d403504e914010224003040141c0254115142c409090310190401080c0101004010410003011005030051042140807010850f003a600c1060510801e010f50038001070042411200030800540000100c030340c4500c00c450016150050320207800502003000c40c108802001c03400000c1003200000c02c08001281c42581194020403148e00c0c41074803404211800e0503a03411210008183d4102580c101401d00c018506003220040c42c0e60300e500440e51080842c03800100c5141c00c20001ca03a03220589030181c42101a01201030401c0b2940e2649504010802061094082442940500008140c03020342e085c50f0702c180442c9924101c10580841180300035100c410740d003242c1e003080c0d99002c503600110403410300d0382e8070442d51860112032030381d4000342c1721491aaa07070307500c00140c100c1400400c0c00c080c6403880141098500204850488000c40d03049035004581c1391007803000081c3c10601d600708990381601c2c00300f03003685002400d80311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518800035 1250 518798785 518798873
    0x4031706060f0304061a03150402010f03090b070206070f0c110609030307050709021c0b0609040902150f090a1a160302121603030c020606221b09090b0904 68
    0x700c002000b408101701d51500718201108114070a0a21441003604060ba145030003440c05000e07003aa1000724000d035200b50800c104000c85810007150760700b2541d444a2403601d0407a9204c1c010b0300036500b44544c1a030b008400c941c1194807071a0a420708081c07500d40790070003074100d20003d1042100046113030340f90b1424801e580d00d0981281c1600c00c1d03107a4406401010b980300c16011614200403c0c10900b580c84a8070a181c80004085c2241d410309004409000048c03d0920701641c3c000e8490300c4048081a003c00104124440180e01c02e88030740a00c010b100452420341c00c0003821150040016020030b14400c15500d800f44e023980c80300b1482445050590403c2038228000c1c20044000031304610005010b03440d842507600c41c2c1c0e0100100040c915080784c80c5c41c0243da07050f0b40200561460300c16011241080079146030100ca002030300340040b1203110581e50149005c0e2011a100c00020040c010072032080829440090326000f070f00b464144c0d80d03603041d00e054512250780704842c40c044049409154910342c203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518801285 1250 518800035 518800057
    0x60106030b180915130b0c28030912030b1309080a0f05041a0304052e110d02040f051c080f0307021c05190908070e0606070f061d060403170606 63
    0x20003401e14607405c2d0007101042c0415194241890302264000b82d056049582c0380c00881780c40f00805001421a184440e40500d000040580340d459180115940288040181a007600d000501030707200000d01c091828205480074480c4d00d00740e80000030440c890201c41a000079490071111241c0090f00649240c0942d4001440080d0340c8840c1c68202c1c0044c070000d42c003503401801161000c40403030f0030215840e48228084510104504100e440303038080341d00a20360586200c5a250304140c42417a280c4100d07002503100c0d88900843c01400c01c214105542c07a0070710300210716040418035599444004003840b030b03c007a88000d85030020005410303034400e10580c02d40503036448440300c4142041c03500a00340d0f0030480001501c0c0b01241041c0300070314010514041240d4038131010781070040c6003441840400b14018550352b04201c003003040d8030018841101c2800c1c0705e071140341d000690815a280203a01025050b0f240c241961240d0240008250001c1505003000015441000ca82e03840b40c2c04a10103020b0350303050720 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518802535 1250 518801285 518801323
    0x3040518060a03050f061b0711240f03010512060f0c0d0f090b06010906020a030207360905011b051b0c03010f050405060c120f060a030c17060106030b1809 68
    0x1030110020410740e000c1d6800c0e1401210174604000702021038420010010b0a44440c28a44d0089092440381035184200c0b5940f0302e01020406041c101e4ac69010442c0c0103100280000140f0641ca042c409208032480200020503040c9081d0f0000c640d82400546113001040c008581c01501075004d4100b040d020130042d40c01d02284083c1d28000d940640103449503401306030a10310110341d4138400508070f01e505405a0040008a00d40301d07050f2641d061b0308110000e03444a003e0303603c08001c41c814000c1d0366004c4441c800038040c881da0500034211034403408003083d25280c0c2a1200d45007a03200c2c066580d03c11007800e59400c3c050740e0000582c0790018800415415500340351403c13202c81480e03404684110b005501741c5102c2e60342c0041c1030a20b4410710380500100080700300070039441c01c40791580c558001000782040da030841c0c0f66201e28801240315070009405040383c5645280c0c0103001d1020500400d100d0400340151104000060301c0f4a580c440c0010710080f660340054841103040000158602540c1208 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518803785 1250 518802535 518802553
    0x510150302120c091018090c0206040615060509010e01020a06110c16030b040813030b010b0403050114010602030d0b010e130605010801080c01020a02010e030c0a14011103040518060a0305 82
    0x180103500b010040e441c100c80d50000046100400c0b008a520b6244e000341301005443c600b11094440c06100b14614a108640341e402080400072841999806490703500140280d1805151940588a0007d003511044409070000c2001c1500039065428a010908160082c4c00407840100d00d007c20400000c0d00d400d0500d8981c4500d0001031008184201d1481d0903500c03801d2100501c14500da0340d40c0310041a14131b103500080c010030320210161a0004400780b020030320580d203843d000e0b40c0200a03003203014a10700009080041103401d02c10b01c400e1415100e4001415890158045c0d103d002d01d0010041c03407601c803000d102c05d680c0710b2003c03602a601c004000280405080441e50010031480c01031074041485807001003511a4002450b1140d1881640103001045c555801154a500d03004e000e82c2d0075109280c080d0b295545c0b00b401040c05845452a160780c3c1040300d0b000181261184586082d081e0410001400341c1d4030b0700c8240c42c1c510180c2588031203090b180c000100b800c0013a20b03440600603020710100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518805035 1250 518803785 518803787
    0x210506092a09010e07031b1e05030603100e0313080607091e0306020a0306180b10020601120f1a0a0f0b0612040b0903160b1506041203030e160807051c05030409051015 73
    0x400945e003c41d00c440546024071000d400c0d09c2901c005d81305d031581680020700f440507581e51504406e081c0150a810f0300c0c1000f4800388c600115aa1035080b40a07281c0040e010400c0180c1e00139030490080c8810100c2450b41d03601e4149003040305a050002400b5140c0002c2d6021903c1c1c0260001c0001304810001c142004094541440c0180704190640381f094801202085004e0306c0021054141c0390140048944c1c0380703103640c0c0c10780800c800c5141140c08186158500c04101c0115051510603004281d002ca580035220043c0c200700c4440b0145a4800c22060111406c03000742154804c1d402644000003031900d0300d0300f022843c51409280c10b506000300c420aa03a230100402101802d0242e14041d10102022040a0400180380030b40e029000c59003a0b82510714000c207100c3d0300000180200041500c0310402c1000000082c102190001015035000060401036030400b9100c1c1649804141034226484c03856944294480c41070f1700c2040c0c022601c600105d00340c0b9002d4403131100141034068401d400c1c0003103040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518806285 1250 518805035 518805047
    0xf01020c18040215031018060302040906051801060b120907050d0c0f120317190e0d09080d09050d08130e0f060d0c210506092a09010e07031b 62
    0x2404074000d502e11520700b094104c2c884140c900800040c9100d21402d4104030480c01043e402800e81d040310b5495030400005031b16117102d010300d11400b82c80c3c041010302c2c01c04a41c9805608041802d62260300d400402c001076501a4180e0f2000c6800030799110540e10b4041c18a80f40c01000d4010b290f102d1043d650400030070841e9003c1108aa01c2d1003803103400540d07180041c440e0041c0490700500420007406030f031291070f01601d6103d548446160456074002c010300c8655800c44840c038001c0303291503104684658555422884080082400d00001c144400d0203a02c0205401d03258171949000395102560390040003a0344040d40c803218800b2a0f40d036011070b526500070500d07080903248001c102411501180c054146a101e40842c103401c01e092108040c5040045481111203010b8010f1110354021110001101440181e00641c402c2004000c207807228a006401c9510002606c408581c0d250342541061302c0ea91034990450f400c1514021003981e6190042c0c011380010101d15210002c52130740e084116030405d1f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518807535 1250 518806285 518806291
    0x129130207120503041a15101e050a021203040c05041e020a17070e03070b09030f0102040e011d040f120c0605040f0b010f0b0f03041a07030606120501050f0f01020c18 73
    0x8003115212504941c00749114500a65403078802d607c8400304c00d000790801c643c0079840d11859140a10b4651041d40c8481e0700014599160000600002181440d0541c1044030281a04080c03440c1071841c01c107075807802160b01d054440e441c001d64441c00e8202c2d0340416148180448218100d040d540c4401301d00340200b4524403121000ba800c0c0d80080403039802071041e014000045400350080c0b05da07074104100507410307070441c142c5c1c1503041c414141c00912490782800980b0003010b01c40c2c40c0080319410728069007180c4016141082400c50742e1001c0001050a06c11001030041d0031031905c1c4100d84c03030084201c070303a001819006804182004140410044020010b42030f041c094034100001d640c8504103031760320075031500c101c00788294244043c0b400000e0b00310003140c00a2040c0b0016458510b443c4144c80c6520041302d1880c040ba0782d1380800c214190700030941c10302c011000d400030802d640c10b0a000076140700c0040101c030b015144041c00103807940d008012180d03111500510383c00b52171080301130200d0380f90303411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518808785 1250 518807535 518807543
    0x1e0d0c0509010906052107151701050102010c020a030e06071a10090509032209061706060607020105192a02040b0609011b03120c11012913020712050304 67
    0x10750000143c0d12160722645080d100014002d004200c401d00c0144d00ca2040003a80408500503803c000455807400984800050349035200e0208080c8010444840208141e01080c15a4144420013030310640c045a691261989404c0c001858420000414460301948000502103c080d22101c40d11603c6007680e24810341c01c0282440000b5100c0e00e420054a400790b401700b82c240e200340b10411a2050b401281030703181b00031540c00381650359160f40407030980720641c1c0b00760030114500001e441130607420300c100b0b64000c10648040e450300220b0f500007001c51140748c00c1e2140141d648020020b01070b204902c8403100c922075100400c801b940701c5c0201e210b0040702c520300324403c52620250b0041e0b400c002007a240008416150142044420b02c071403180806440e00490800c02030012800320f43c0020300c1000c082c1e9110780d6501071803c01490809084070000e0414a01400d1300786c0000004101c107102a80b082c7e00150303214507829080c580c00e8000f074020320ba401030900c132016070740014043d03129000d9403141d805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518810035 1250 518808785 518808799
    0x30408040b0d1b170612010b04020d090212070602060f070e1503070306090510170a0602070b01030b13050c06090316120c120c0311211005010b0405030304051e0d0c05 73
    0x301c1002500d8000c000c2400003016484c40001540906c0c1c442c0308000824190400400d1b2083e000d030010382241d002c10a1409010341d601307403000039030608416024114542d1401415101c0c10a032001e5a07500b8000c081e06d80503440e000010f070380d0b94030a40c00001400d10141004104140300800304040d50000c82e11074001a152600c0028500098051700d4000c0000d560602181c03070401242c21800d04440501d54842e102d82d40080d8009000391005011040c00b81100404550461520000551010f001403418140c01910440401c1c0d000c1500000c292086891130354404603040070034140a459a10720108161740000041c0820055260741c210b244142c040384802902d50071460707008114440b000d40029000700c414000598900480c1182040040c01c1418400e0b40c002c0034840248054180c000c00d8020141e2074a05111900945001d0062110a20300b840c2c28000400c1da6070083d80b050900c074480171003049c0201a13413021000c64402c00034100c0a03000140d400c040c0580c081c0f62007040e0203000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518811285 1250 518810035 518810081
    0x7080403080c0403021f0c08040e070e060a0e0909100f0e060c0c070311040207021f020615011d1206010b0c21180f04050915010905040f0305030408040b0d 68
    0x89108480c144c9a009152400e00340350103040da441040a565000c0c24004102248408180744202a000601c00c0d0922115980342025006120300710070800316010780d0b018445941360941245c080e07001b2010030b860841c040d69070032058030b2401c03a40d80c4148486915000c1c200000283d40d420810702d040a00301121180d455916100d0168860b02c49008031a0b0040c1c8010310000e001c1051030710408100601c01740c1802080d40002da80d41c0d0f080207070100394950511049140c542c05110b119800030603c82100d849280440000c5c04c0030381c3c0c00e254407807543c29504000c122540c6090341030450310008822a040d660319821400141c1c1d2100c0303400c0020380f1560b20404006070714484002000d100c411806402c00002c0840c40380d88005104290394008130914041040340c5851040e907124000c1c0800800b55030700c2c012842d1042d1001030b0841c807030032400d00003080b000c03c034640031490001e945803a01030366a944504000320b182c0140d810443c5064400038003044500800d400038104034203c5458841102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518812535 1250 518811285 518811301
    0x12090303180501051c020403060f0e0129010c0f05160503060a050c0f0307030b0d0606090e0622050709060b04150e010918021201121202030333090708040308 69
    0xc0c0e4a00c81c1ca80081c5040060311038a96041780d40013058013125001504042e125601c4409031190421801002a5290041e040c82802402070171038140000803040c0601c949078180c00341c50540114060f0502c24440140010049580301c880982604030702518402e00c1001140c01103c58288245ca01c284115004a111040341e88541b0b4001c10202c40d00b68074040010b1401101600000e1095003419610f59070101903440314006802c0491182c10006821340c101800f180448000200c0c1c2d001070f81c84402017000c0041c000c1048505408450b850000c9402286412441d0090302c0c5c211200303082c203000d000030b4004041c0026001391080c484d1800b40c1040b92100031501c5405620312140043c0b80390740100804000b03121692051358505401510f440000c0030103030145c08003a800081420b2400300c10310103000d11081d0000b0007500520145141d4100404d006142e04e03154484426603110100f2900d100b003150f01c2d801403010a0180880006190070100030b88440c0080fa402d46c003140c1d0040000f820a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518813785 1250 518812535 518812577
    0x8160203060601111b010507021201050708070c02060906160f060209030d050918061504170d0203040315050a1b02150a2304050c031f0608070e010308090d12090303 72
    0x122007100061581194044100c0d42c3c01d084428000c6c180131003000303010056102d50414060004604002080604096900801c07110005140720100107480e00070900694404048075105981280e0481c0c0301c1020a1158000c400400d03001451121000001400c001d1241c000e000c041c00e003141a581061100d080c16500c6100d11742a942d071100010302641950007245482c1600040e024040400200c4c025604141a40c026003188003401007180100070540410407603501c0041a42c805107080500e10303902d401000c00d940c12504d0b0020740326000603041c18400c1c0d0100400541c00c101c800c43c24000000e010351110013a030030a40300c411088000a00c101c25030f00810031014040030403c00d084840c110319500070100980211480d0003400c5e951091940c041181c1c2e0680341d119085400216288035400d402c842045e40140c00c1d98202c000c0420680002a2036141100c0c0c01a401c01c0e91010300d6000a1840e03808008020481c0d00c02d40401c1803c03640c4850700d4010f4034420385541d0302414411200c200c00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518815035 1250 518813785 518813807
    0x7090501170406020304050c040f062111060a020c0d0309061106070206070e01090e07050901170c0708071104141501171f1d16030b030d050f0708160203060601 70
    0x781d00034042400a0722550007180d102e409501a14040a007802c000303420b896281c1d403810b80311500c1d00010b002c00391000303080c8804540c081350320010302c80041d80c4d02e0340341c1031900c1d0f10544101c80c00f040350a65a80284000c0006082c0144840b007a0000c80c6405480340c0d0040c080c0d0b80015403503510821209a0014086000348015002043c155481f940201d40070310b0031005260410280150009031041c1950382e2030300030f00305600c27965151540940018040407003110ba42c40320380301c100180301817481e80a003195950358220400c60303694030782c8e070400c2c4901500300c414458202e450500b100320001d01403010a0701034000c0d42c0301d40ca11288400011600500420010034903190307000082a482c8856851014680444090707074070040f551110807051102c00504c480c0c080364141402c0000e00300440461a000d452242810055020210086035541c00345030080c8040c4000060541d8000351507805468001e5445052103a0742c60447c81e84551401d07000d0404c034080d12540b800b05465600038094241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518816285 1250 518815035 518815067
    0x90621030822051204030b0705131a0f130305010b0301060b04290a050c060105010f0206040f030207080304060306080c18040809011b0303020c070f0f18020c070e07090501 75
    0x200c1ea071030350100a0300304015412a01610300c03021549000280003486442e5414114904c055242c030325500345000c03070310001002c20701003100c00c00c80b080d14402c003020b0700c02c00d54800700703032392a14010305c65924481d074460040302400780403011070802d6a081412a0400a0343e1144000f80010701017107060509a03a40e0f4080c40a01040c144030034080c65903103035004c8050a41525111002d4078448048070443c3e480361180304000345c2c0004403000e40520410045004090a00c0d100907840007a0100079103503071000c0c0004105200910010b03003810b1013084404041d0145100b80d81d030311a0355807801f400620301c0348101c070002e002c1e40d000c46069240644240e00f4500c07074600c000041e0b0303075260b03995080c5501444005050006941d030315003292240c140c42800b05480384d2001642d850034058541e281c030a050340149031005410a00303200ba034403440c110504446000c10501d2032040b8201415019010314002d01c1081c1c8548180043d55154442465000b1012601c4070703100541c03590011103802c80d04500c0e640c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518817535 1250 518816285 518816297
    0x11011e05040515071a151c20100e0103061d01051210062c0403121d0d0504170c1c0503130f06090503150a090c090609062103 55
    0x6080514500182d003030800304813840d0a04507900d803051101d040580030a04040c4804001c07030354400480d42c011003002120403c0d80340c85141007002903644000c400030030b1030060390ba40011041c0001e100c80720a050003082d140e1626071864009103440480c2c001c0a0000e4201500060b81900c2400f0310b220000c40c03000b140c10541c0c01d000910007140c002003103079030030352044154650a400341845008082d00d00d003207410403e400d00f0072070342101b0101e0308200031802da0303107100f1b0200280d00803100750307da25030b545804954002900300d84c1d1810f0307500d400744a0840c040e2060a10001d507001c0001c00c10b6508260f0000d41c1d090401281680d9419000b00d401c1c2c00c418031840390581100020020211140f14100312031501c1801c91a44090001d15800411943c0032000c0503c4200d810034119400f034941070740107041142c03012150f81c04c44400588a0a4a41e58440907141402005008030001c1c025000d000e0068554608015009103803134401c03100d040c0a0034080c110703500001250912142c0e05a42c07a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518818785 1250 518817535 518817539
    0x50a0b0904051e03040b040b0301030204060501053f130605091609022b0902030d020d0c171b031e0c030a03050c04050a0f0f050103020405031c020307060911011e0504 73
    0x1c11103880d81e6204100f903440103010004000990b00020005010000216500c9502d548140800e5800541025040c0f10080c4903c10711b80007800240e008510050403034200c1c0340303071024410142c140f80c4100c06460600440400c006400d410031044250b40c81540c0400540c1d4603054034644440d0410843d11a440031080c0400c540143c58014002c06403102d00040480100c242d40c1c209800000b100c0c9880958507419000158a8140039122381c1c20341c20f002800d11840c44000040c00003004501c020240e91034420806000785150b020b070b4014100d400c1a0805821000b80116541d820956400c032210404030501200300a00c6021380d100203580c2c01c021410110a0136040e40134203402021050000c02c28080010103a45a402d000000c2c00340100440c0e11a0074a0128001d0005c103410041c103040c0100800c003c0340d1800500082c3c40f00e462a005c1c0759a00004800702c9c1988aa24406403103281071040240a001031100004403104c07003600c0d01000140d035130901110300e038114120f060100e0014001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518820035 1250 518818785 518818813
    0x2030d0f0201020909040539060d09080f030912040308030a0e010e061f0e060604121e120806100203180105040f06092904151b06050a0b090405 63
    0x1108054094500026007802c0948000c50041e8001b15829a00c0c2da010040e02003c2103421560544c01d80d080158401c40d00ca1480c3da50700a0444005c1118000c2c0800224000c01c1d0301030341d104141c1540d10401281e03440d122011980004d80040e1124111401400c030403209136410381040700c003181c0d44900ca190039a0f5510b02c52100600040800d50b040d55280ea07400d04050006010b00d40c46115440319030144a004881b0700d02c1040110b4000b12220240c180900c90642e80f100c040c0ca0485a4960b07a8190b40c0c0b203145820840c910600a410f0b00c002e0045041c5402c0012080d02007030034490070342c0c0346080d0750b490000f08806211030b2400034001d03801c00c01c6180c05600c1c0d00702861420b280c06040061409075114402224003003698009000a1120a810f0250342c090000a1300d001d041c281c0030424000110024a11601c2144555108200900502019180284020800790f00204100340e808850390500e040945070803500103a89901d48042242da6141c0841e1a034040d0341c200009080030791007150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 518821285 1250 518820035 518820047
    0x912040332070602030c0d020f06040f080f03070203040302040b01170a0c020705090411041127210c0901050a0e0c0702040b0607031d0a06021c0e0612060a080a02030d 73
    0x8484505500c000c008541c1e804080103100001c2201c2d030b00460f0b8800001c0d100750b091810141d1110115000100440c0a80c0d50014040d6002904100243d00b643e4480c60000d00520800d200a0786a01c400b00400160903004006841124025542800304e0022030004541105003000b00301184011100031950b020240d502c01d070b482070b00b280100e50b00c5503140d100003006400100d4080b2204c6940340c0d035504460a16020780d103074003c81800ea5038108a80200c052403001120012884e05100c0250540100c2c4e6400380700c00480c08040030000016035060300e5258990201c158001c1c0241b9071b4400019540c141504410f040b59620b404200030f6481d09903020040380d10900c020b9902a49981249072956900703c001c124a41c031903241c0f8040480c006000401d44c4101455551155000480030811160085036014049d840300413200e044c2e0403401e500761514000109083d401c03081c0400c911402c2c400001c074a0b40030303143c00c0b6014850681d450f581c0c980e40e80c0c0a000020740641080042d00b54a6001c0da0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 518822535 1250 518821285 518821343
    0x606071101050d090609020a0503060705310306022106100e0424030308010e24010207081605030f12190908060a051f1505090a0b03090609120403 64
    0x1152031450f2104280d51801a0b894000b02914100d030b0351505541149001e0310107900030903056001d0f01240c41c080d0340140081c014480e440718004019420700108412070130b0700700d4441e0940c1222442c5691241090402034120101000020400550724580d9801c541c40440c0310723510042c41d01e103012944c1c120860303081d105050400e0b0880d44070090000a500000ba007982d000a48001c40d4180903d5410001c007095410380c0600864071185091040301d105681c0c0030000c007078110072010406440040101e2410190350b02c98061400780244040f0b9204a00500c141110360490451f444840c0c0b00d401d0301c0d201c00d8001c0030410303042806c000074409030030510164102c820490a15000303655580310743c513042c04001c580003c203542d80c850070020010440b82030668414984100341c5207003801c180420a80402c0407507030106000000c61003005070794500032084042c0c031006c01c16030b4813030401002c410341e80d5006a481071494050758649503450100f80702990308503604080200c80c01014180f504803403030448 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 518823785 1250 518822535 518822537
    0x60907030f0e011d0d050304110f010c02040e0606041d0607030e0f0d08040c0e040209010311060c150106021509060a02090d02030a0c05040627020f090925080606071101 74
    0xd82d50781c2c40c030000c203105640c2c99200481c0303114409030004081c075040035511481c81c414404140b052001003285000510394a0070103550016030368800c40c0040e50140b803814002503100d030510095040c03d10010401c7c1d40922800d8505000005078010540246001310a80c40903591000d40040c0ba2103109800c50300c404c1c22040709848403c10b840071050b080940281740d01c8003060703103103041c402001342c0d4121142c01400c092a0403841414903500060f096001131001400301d143c10841700c01e071581e803001100c00c0d4900b45400c80720b5000302000400c07001d400910442015011b1682d1a51407421000031480c4210600c3d0060038440e5100000b42000b0740141001c19006001d454a403001a202003015613000b40c060b2100703064183c035000c10401a607005d40c012060b00c0c500c01c450120306045960340c0d40020802e9035005601c41546248842c2a405445040d0341c0c840050011302c00c00301402021080c030600d010900003810010504251030200f400c3d105690044001c118000203d600207280f00e44010701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 518825035 1250 518823785 518823791
    0x20a060b0d12030603110f0f040c090b070f0507060318030f20030306030d0306060f12020f0f1b19080307090b030106120b0a0b071e02031005070314060907030f 70
    0x2142c80d03103440d914004009201190f81c41c2014014081c1c1940c1e14040200d04954442d01c5501810110750f00604c00da04082c09151580407240300c460003400181c0240c280a480152111268200036020044200007512603005800001c2500b901c24003d010588008404010081d0070558088170206550349860007008290800d09494031014a210000e03200c80307000541d201d00b0200c04150402e1503260351807040c14603148081020b1904248590140c0303495042c4194035146031a0114064400ea83d0125910b5000040482c082030b01200a08031007610007900c08a1035015982c210380d540e20b40d012030703414005488451400146248000e41d405079171850915101c0d9910490f00360690002e82188000ca4807480e8401401d00c1e851288030154030080780c08c0f40348140b800e0102001441980000381000d00d0110680720309801c40e00c00014038503070140407076098000d0380c1d46000040c1003e80701c040000c0d080c0300041d004003442c0c1035064050b000c014404031450310350002c160b0081030355030300300005651 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 518826285 1250 518825035 518825059
    0x1080c0c0102041e0603230c160203070e01210503090f040237090312030207050f120307110105040201090509061311090102060c0a020a030c080702040504060615030c020a060b 77
    0x74882e00071100760b51130000c040303440c1c6041c01c1024080e0307100681c0d91800c03080b0398100c0156081419404940100404d050181d48540600c40c02510b17030140383d006500742c89000c0c3c001600115042c61241282c005403030010490261a074a0800841d000e0005132407980140f040c4e124078036000320340e031b501004010700040c0b0740002001204101403560418401c0e0b03502c40350760303514446c81c80700410145c5259454a1500c0c10300310b607688100c10b26a200d0502c00c059000c00c904003000300c10010714204801c200201c6e0f40001c0352510948965004840d5080041c0420040400c403d505000310340c082c07a816164002c1c11400d01d07060050044004008940c04102280c140c1da4030300c030a118601d9022080c0140d190382e0300c200303000607282c820003405981e8040706c01c0288100340d039400f00d1004030082e4145400800d08403c2d0811100c907006040f8040d42c03051400c002e200c04c0004940c040d004075410490100c0040c41c82010560445114410a20143e000005014009080c50f032008600c080000c01c1c8180040e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 518827535 1250 518826285 518826299
    0x302040510090c02030c19031103130f051e040c1b08120c0a0219030c1a0702010b030115050d0c1d07170c040303050c100f06090506040b01080c0c010204 67
    0x19016101924070020008081c452520300f80a8021411a28001103107854580401c440c0d69980d031114001d1210300ea4440f250400d445032904060000c152401c60307413038564044049210302594450131081d0f182e06a0002864240010503000003c0d001030100a501c00320420720028040c17441c1c8110800c20005c2c40c03400d41c0c02c41105129081400342c2c010316200c00001c0d1a4003c40c1c5400b030b001000a40c01032120824181d070005010902501c02c2c0e002513020815803809072000b00306c00d080107088041078800c880c0b82404448800d8407030b948660007407003009400d800b4903080b6604000d40300c4052801c20b00c00e22036030401040d8880343c0340c4151070820190740e40301c40c0340d00fa40139074000b55407603008001c040c0001c881c2d10144000c4100d2207010200242d091281c0240c01501c02e40c40020188840460000c81c60441403100c940d1900703244805000e215000000c0200629160240c6404180350102088007810300784a0801c0941042e151102181c8031815a0226a0400c20001100350f400b000003260750 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 518828785 1250 518827535 518827541
    0x30403050c0a120f18030506060d050a02100804031b0b160207090e01090318080318120f030408160b0403061d0a060501050916020c24040e0702010b030304030c0308030c04030204 78
    0x307500f40e40c0e4240c242048102c020f04032019101c592248843d801824808104041445500054101c9452090455924090f1704000c08064045e610800c409200c42d055038120408521841c480d60310300b40454841d00c040e00303030201c00d001c000e07206c1c0c0104400289074042d401030703614440e500f174011030f1744c0966280c6503001612014509500d10765100c168410405411107409441003040d810396070006402c0070451036980c0110f280603090107103814032000781d580f03500724100000f0341032101390741c0601c00900c019540ca50091292100a02c621840e040111819009840c2030310700b5040100c1c50186151504000f40520b401503181001190100300400b40302000311190551007004040760310340c940f608000071850002c00b43c0840e1052040d0081c0099404105250042c50407140804c0301c00d0010350061200c40e2401695075440c0000a01140080d803032020381e0b00c00d40d62507009004c041c408600b071540300d001d5444010400503e9400a00c0065100405981d00c08402c0c00b0650406030340390000747c16 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 518830035 1250 518828785 518828813
    0x51b0a0305030f040501030e12030f0a02090303030f160f090b0a02070f0e160309030f03050907080a03110714011b060f0f020a0315050a090b03120a050a081b030403050c0a 75
    0x3e2410001010056541c01d070260701202410300000e888601050f08080600c1d1000416407031021014200080c07980c0e220740d054528668025046036107a2601406c040e0314000280c5410000107400000050028800e6881d40c844906582e03d100d206840d0480c24030745a0000302c1ea0b401036010314a004188000078191040040041c50310540c041d00f040703c122400707803a5003111a410075007403403550740103c0d03040060b0700b0050149180005071a41c91081c25428601e041c2c012074a036000e21b1151300705066002c800d40400c0c8614400b5106036507a1503020b181096101d20801d40032130700319201c800d0040c074945544400240141000b00760030580903503410071035030300c1c0c049050f07a0382d4040340e040c00f04ca605200341d40111603c000c80b20780f0b80c0e05007000980460050320611000907258021200d0640307003840306c40040ba811074100780e240c0700610b201034415000703030440000155140b0001441c02d48001172032901520004207892031601c4548045885a204a01100d0103200b240c5940e0005001c0201c041e013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 518831285 1250 518830035 518830057
    0x8180a030c12030606091203171005040e0f0c060304080c010c09060206070e090c2b0623010c062309030d0e0604050d0e2d04050c07051b0a030503 64
    0x2220121841d2100281410281d8041011301d007403c280540d680180801c02070380c0250190750b0072420b10303103800c40d164070f001c1b642e211b45c9e42d0421b024000343c16068641303a000c0d20401c41d0107004041d081b4071380c955210300003000081d01d5446003020a0700c5040640003907070800c0c00303015603524020b4210101c6096503a080e90002c00030b03400c500c041003119030502c807481c3c21001b1803508420551910001070070200c005440d04604403000145109040140b08104070110801c04501100760b0401e000b00000b03107440e22170490454070000c040812903401c45690b15010310140c4500155848a40362130008000c40007031056140c40800c0701c0c10140c242c081c89144550f500e0300055035155000341c00f120559001c03541d1a00d03103510507420720001072404110b1800070f070168580040d0b00303911940000d00e520980120030fa4038175804d0500f800381c0d1100f207521843c03070035080e03400b03200c5520f0711007a8402e14800c415000d4115000700c0070201c10b020280c58807050710304004204800040d10b035201c10b825644000048a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 518832535 1250 518831285 518831297
    0x7030c060e06180a26070b09010e0f1c050d020405130e0d020c15030a0212070f3509030c030f070507140a030305030604110c0606130b1008180a03 64
    0x5401d10080aa200028010010384002c4d4520b035994008800003001c5e095203207100b0643d4040b40006101a641440c0e000041940c1c030f800c120107070b42c3c0200b0380c1c0c3c0c107100c4950103030981010600c0800101003000d11050001600200300320b10040b0f030150000c1c20286d10042c1c00300800034295581440841c881c00228078002455502c1a44041c50840d80c12407030390540d0481103070032080380e44c0c641d5401d851a13903803899550f41c0d980d08116100240302d81c00382c800b55015100c0130f110601e079014542c03014012564072007007440e1840690001d0081031207166071348a400115414071100340041110740e000350812081703a06003a14030181c0d50a507000200c4107500d0410100e030700c1041c44020003200f0010800c000d403000d20b600300315000c14528050b070302000d418400b0001c0030a031291034542c010b07240058104401c0ea01c880c8c15844203a1540c00903200203100302c602e2074040b00c07594442e2084003069a4010007800c1d00c014070381811f491446004154244d1191214203507043c01c441400014002c0e8806e0741c7d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 518833785 1250 518832535 518832541
    0x405010f0501050a08070b0310030f051f06120f03090f1211150306090411131b0f020309010c020103020909010906171504032d05091309020604030807030c060e06 71
    0x38100c40050380018841ca240c00d90401c0340c034001140b001c050382c3c102c0710001d80c0d0b075a90006101010615910007800c0c1d400045404044c440082001c0d014003840b0040c440001404052880030344001d4081e03159214110703004040010b500c9500c25030202d21904051860558580c0380080b060040e0b400446c0c140d895065a800b080a50035803c80011402c482c10321a8070342c408040003841c000201094001c0b601d01010500f0302aa5980c06071580900030101030b0b01c0c0005218000241c00041011444010020744003c500c80c020b044403180810142d0040d0700308021100111110360703041e4010f071b05041c0d01300088585e40d152406480c0c040e006d200f2021850611389040f100340300b611440031f20140c0e00b04a074250209002e000d0340c2c03508030380c051805d43c176440514a034500013019890b400e11500c050500c510701c2040e8102c0e01404214100311510b6035044000d83d410015a040c0300740080d8011000c010502c0001c2008000d042042e009142070000400c1e03540d10f01e0200e407161209401d10b0f904c40c00030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 518835035 1250 518833785 518833811
    0x60b030901110c06180f2a010f020c040c1803080a0e0306100b18190e160203190201110409050f060103020702030a030e130c09030512030c0409090201090905040501 72
    0x42e41440980a42c586141c42c0600701095100c4501400d05031100c15416000100c1034410400d81e5003034416101550b44081c1d1b03082d1201754002425403a40450f54150005800e07541c0648103c98800115030003401c2c1c0040c0075810480246116507542013400049417200c2d40c849c55040c40c44000d14454810207913540503900018041d14128010b0303510a9118030208000341d900921028100c0d02d0346444241c440590140724100c4181142c08070b40c0080300c0b4000d150b40a040728130800e04070b0703500510000b51901e601841c3d01c40402d0300b86200015a01c20000201c0c0003c04844000010640f440001040f0b140c1d1240d0b910b00c0d902c25800000f54507218401c1c8043c031403903420015000782c001d003000c42c034002159020a03241e0300c4010000c0c2c1070100f20f007000c1c084c2da112030012829000c0e61031000c0020b06a600005401003805010035913a51240810b808110300d9840c0c1102d00980442000c242071500d00344501000d0310344d0141c00c904225810070300085070075a034091180183d100d6000810801c0107020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 518836285 1250 518835035 518835041
    0x190b060909011b1d310509150907030b0f0106031109010c03032c010e06060f281d01050118051c0c0b1216080603151801060b030901 58
    0x21100300180d162440800360098a012607400000640c100b401d45002e204459164043d00c0c0d20b4a550017618209403c0c07140c5100518029400c0c141507035800c0b2507401c1c800403400300c9030b0884014155600036480501c0d400d0390760929030b9000b83c010041f2040540c403640c6151580d0700c11380f402d4261440c03040040c4a2942c160245440000c0411146804c201130407000800100341c07a04c0c0503040c1590740001d070740802c1c5502a40c550010003c2c441d50400d00e8902001802040e00a81e2408140181e0010482034075040e02c810005c2e150080010f0a001c01862899a6003503031000d00a0084404083c009807900101e0443d40f41d042155039420425894680007400048a01da1107503203018a01409200301d42e250100002c0c101c0d290808450502401e00d46a040400c8540040c03440d00300c0412a064820000040c680c49840c240440994541000e2000e03103490b00183d0301554590864a500034110703903200714095020046400e0b011001d26a121420b003101c0c459040a144c09400008008045000340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 518837535 1250 518836285 518836291
    0x801060e010801150e031c0908010510090b0a1a070204050108240703021b060105010f081504200706050612160b070c081f060e0126190b0609 62
    0x4100000940030040000301038802c1405014401c1e01020071040f081403140c00c6101903083c000d000c03a0742d01089000c034001512807406070400000c8000a01041c4d244040c0030700ea01031428000011426402e104a201c06480c0e0000c4080d042041054001800074081060302095035405048543c2c0d0039107801800306949058008280c0c650000005d9200c902220789181d0032001645c0e40c00120351100001103020380700c0d11700c011899003500f0015042081c5c010401504a920907240c0010b20b280f007682c25580301c0421142c046000d510702c4208280340c1400d4000040620120b40018402c10f2803100c101007c1e000703070805441c0242c0c0d9204010f00b5081c8100d14072402c401400040403100800190500801111700680000d42804140d0004000300121800058041034090740d6040c50410940c11411101d1010740103200e05003180040c4209101181d14181e40c0c95600780b0840812100e00f008103200101f44030b000038424031105a4a007004a000454210312810b08007529003030440c00c00070141009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 518838785 1250 518837535 518837537
    0x1817190e090a06080d080a061208030f070309030c0b07091701020306031b0a050d0804170f010c0f050a050307090b1902010e06090616090306020d0204050118050f010c0809030d02030307080106 84
    0x25400b440504d030000359220070250289080300083c0e95046000c0c0151200758001e00070760070f15050f11000c200d9400060340c403a1508802c8a2410340c0ca42c03004400b40c402c01e61001e00400c00c4801280702040c10f0f00c9000703501c10070b182884030516a581400400c420760490b2200c5c0c85950202c00d219052905000c0d1003d1402b0140e40c1c04115401180040c2c1003c10612420348200e04035080201040072960070369004040400e000c000c50410b061310036883d24070040c00030440c0d520b80143c00d02d5071809038110072446e010b40d58440c0e00308040c0c42000e0790542e0001c1c10360f03802d11106400015804c460391000f002079000713460001140e038900b40c0020307003541d120304445200c0360088802c10017003420014590750301010782c000200010440540541c0d420031030381c04c0986128000107032010540019001882111020390b20311405900716221900d004004e0300400d50b100a0340f0001c408558400c07030160f1005801407403d10f1800d0b40c003e00182c50404003502d9800540c001001300484550440e074128014101c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 518840035 1250 518838785 518838791
    0x20f1809060109181d01180512070305030403030c03090212010609060501080c0706050402010c05101b050c0c0915040e07050a0f060504030b071205040f020907031817190e090a 77
    0xa2010706010510f0f541128000140d48100001c00e45131403400f41c0381703043e40000c02040707083e00742c0303100d0611036030880016121482812044000008208200c07810303240c042da100f5086d515203641c00c602070110203c245007015110107880000d80c0c0c8140d2030a0132204010000980d03545013950520540c0d01c5a070015060011550800100c021041c04070b9280c540e210b200011250389520060328a1008100040c04621509410b480000c00c103070300c5040240c00765009107444802031034084985204402c2080010b400c0700305c0c11419030809454003500810360700341c40c140d00d01c40040480c00320380d000b42c003800480d408284108000e00b0045c2401c8050003006180202c0582070502c043c20318425480014052010600040c000358414020074082501c0da0405001d00d04050030400d200ca85011804da100d01c2201c0007042e0601c0c000d10614001c1504600e401171004129280c01e03010b40b6280f80c030150010400c0059200c405550048285555210348460085079032040a10600050090882800d24a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 518841285 1250 518840035 518840039
    0x207030302100b220905190515251205010b042d0e01150807020c0a06052a16140108040b090705151c05010b190201020f1809060109 58
    0x3501294002e0300c2004408003103260308200d0081465000e0120410b6030b219044080070018000680000303071014000c0d8100c3d02e4655607a0030440960340c1c0b03c5402400c5910050f841d9043c0d0284e803042035401000804080d48101c0201c0c0900002c01000c1882d00009440c9440102c40154612a942c00350403140c0c886030400382040107400170040c05005d82100603440060111b0b02c42450204200581014000b4122550b0340703c012010240000411802140740200010100c510018040d000c4004c014401d0300420310b840030507200356001d01c0440c600d440c40740c000d80c110304c1c04c10f0191580f0f40b03070603200914441504040d9200003022540145141201511107032980740c0e8454152501301c0d4120140205a407180d004903843c0040706d03444aa0420544040d410085140c40007501082180a07004141890401c990400f182d00900a04414080502c00765400103a55000784407190854000113142c01403e050100c100d8001458001c0c560841c0c1d81810b03404d0800200e215000102800c00007c0c441c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 518842535 1250 518841285 518841287
    0x11030d09050717030a110718020301090f0b03030a03020903160311150c0d0f1e030203060a09020304020d1707140a031202090a09150515070203060601090b03040f0201090e091c02070303 81
    0x2c42460800300401040012460130100c050201038006e001d2170480768004413a008c500d80103904244241c1070050715202409014408502a02d00401c100402075072805001d402e080c1d0080d041690703021b406102ea140039132031001180c0c1c1030001a60003083d503118180c2240e070800610001c1c0174218100414180310301400d032900029196601420340c02e01c0402101d0460080354500030107403030200c03140013150038800c0c4150545d00441c024102900c074510155280c428034002c1e8441501c00940003c10360f550040404c4180c51090b03c149043c1c1d281a1909a840d1105d0340d2541c0d080c41c00c100b01c1c1d0800d81020301010b40144004801c4083c0c1700c01941010348407000110050080e101d900c5204c1e40710b400e200f0001c1c010030701d00000b505008001104581100d55003500e203400281040780280310703d6020a0440d80241034190455209a03130503495550b4580e24408424a590300c12410301070310101c041101c044500c6503520032243c031070051010004140d0500d01c1d0026150b494000d40d0003100c0144082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 518843785 1250 518842535 518842537
    0xe0f0a0c2604031b1211070302150703050c100204080c090f13020123190801030f0609210e01030c0e03030d09050709020f0406020c0316090c11030d0905071703 70
    0x244007070303491104990703101e04081e6510f4201e00100012209001c080008001c0744603110031882c0041e0b620003003018181d901e560790f903490500001c2e601041c103400e4403250444035001441550710900e0464142190f00c0d0400c0c0c0303000da0800703503042c20b1a004030b401c1c020303c0c0040025207240081181c2556803814004403900315071001801040c9500c0c070282c2504c00f5a401051101485070750202c80303e0a1f4864644100c4068002c0040700c03003030041d409800c441503881450400d0680c0d81007040b030200a002907075418002e04100100315550950040d1418144c00740c500d0420f15850700761144504616620001011240105242c1c0140218030f84042c40a840000035101a11000900050781154508040c0d1500d59998084480d00d4000594400180c0c1d41a000e082240c0312034080b5904255001b00305601c0c1d641c0c03400c104034103052820040100f40f5007504140c00340034450809000e50820003084038103640c0b1001c03042c607206e901c4032091810800c0401408005281c0021090300103a464265180c403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 518845035 1250 518843785 518843837
    0x50307120521040f050304090605010e0907020304170a0c1d0f0c040612021905040f29090d0204050106031b0504120809031e1608010209030d030c05040e0f0a0c 70
    0x6103007120300c006001c2103112010704103a19045000c580d180d40c1d540e00e0234030240007140902c0b800201c400c00251054102400f14034000d1300550041d40c20581041c00d601d02001c12101407003e28820b09418001240003100890302800388081c0601900b140030030010154440074000d18280f4180c030081110f0400300a090301c0a40f0303001d00c1d003100d1840040300701101030301030700ca015003d0a00341c11040c60f02c1e5401030002d01c101c0c0c0f107130f80303440380070f82d0351881030320041a030000e52072002000c624109400002540010044482e006004001c12041c0350045401c40d81d00340c000d034003c00d90b141c5410103140761810841212050610300740e407510303040c8014124200c0c2d441100808045011840154603681400700c0d0600314806d1000c1800c000c5c8204d443d0307036910110701d00214680e03407080d4003203032444060085555064010b8014901d414081e82c1c12001049903103480c50420205110120304051140ca0160280c5208000c0000e5030421786134810444211510210a00c402c12a28441ba96031520f03072104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 518846285 1250 518845035 518845087
    0xa020a060b040e010f0b030c030610050d0609080c0c0a1202030c0910080303040b1006260a06090c0c060b0105120a0903030b0405041407050102060709170a0f0503071205 74
    0x35075101558081005002e50b0b80442d2044d508210384081c00d090198492680f11000b14101c0d9004c091540600d91140000c0d69500510410140c0600190900c0306414038018400c0800144209160b1075070b1075140c0001000881c15080b080d801c0902d842c04009210107429585000003181c0b07501c0d40000d6403000d01d480441c0c094403a42002941c49440315068400405450301682c0e40c0345131034500082c0f0050210b8082d001d10b03412800c0410014400c0f40748044030220890706040016003803609810346900241521001902d403800403c3d01141070051250b6101162103c015174034603890043c041c0d600c84103103107040040a10041a0b0809a80c940e56040840e032000080c0b4544503040440142180003200b0350400d05100c14041007000c504c40344043c01828a06643c090b64a50700126110b07841690711200182d0550b50038441c41020420742c81da030322411802c840406045a4a0001c00c08034014141c07202e40002c6044810710800c09020b5140a0381803414901c2c105c85244031100d142c1022070905 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 518847535 1250 518846285 518846291
    0x512031602120d090303120506061b010b030d0c020102280201230319050a140a1515021c0c030c0b04031206090501150c020a0e0c160305040905010b0a020a06 69
    0x42551925201e035410b03512400b043d50359000c1c4903240a020706040f88811800192aa1030f10203214881c0c1c1328103401102c006217800e1400b100c1e02050810405e402440b04015580c511354600c081c0d03010006e4455442082c0c46411242c0d182c0e0001a007091140c2031403240c01c4422401400d03000e5011884d100c0010340c2400c000a02c074254500d9045040340321032440391031200c00030520002c101c2640c072041d0a14000c1100740000d5a800602405860402c41d0f02001000c4d04804907070203e9068003c500c058a13207030603000783e85a5540f803e40001a038500c0320300c00768200c031804580720201c2c15601410304140d810300e40d1180040743d030011320200b40c0c80030242141c6c800c0d4001c101050320858511100b070404410901140c1e4540e2140c10051000388079100e20b50000c4840e54500900030580c41034030741d40041070501018649a0305400a020040148840d010108042015030540051703070030b030440c000c2d0b950940303803420011044200d480c180c2080c068004140048291039900140c042c0c000c0d80d001c5404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 518848785 1250 518847535 518847577
    0x3010c08180309210a0c0e16020f0c010302030603031c0c180e0408132606010f031a100506070303050f06010c080d0e030d0c0320040f06081b0403030f0207051203 71
    0x541000321006000b003022a4000b000200b051f40e80f01610b00411843e0007088054107004803d981c3c5d0007462450020541000142e00d51641c066400b46500440103420341e480d01c5180b0300780e59505040726a51000742d075a5100090300070340d031040f003403999050a4580900b0b15400c000031031269090042006159650020319a568804071603c034000405e0703804010190310140c0c0e209610b4a83d4181c4034030926104030b000000d00c0c1e42c00507206804a03030700300500044030400c0c644482e445950041041210304102800050b142c1c903844000c00c03256010b40d800055504110803000a0040040d22243c10490f0360420107000c03419002c200e64910800380000245d01620841c2e880c01c600130480e45d45886807504014910705901904001040041e1070400003840c041041100d03000d0103140107103050b05a64540034400700703025103012504010508c2400c4450840f0f480c800a80d644250011400145801c2d401416141c0400545000d02000c5403c0300e5012104120256030740280486800c0e1000041e041c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 518850035 1250 518848785 518848849
    0x5070f060c06050c121321020303040605150a0501030209180f0906100303050307051614010e07051504030b090a0206040f05031506010e2103030403020c091501120b0103020903010c08180309 83
    0x4c1d6101c3d1f020307a440a0211010f03010281d101e4204030703400c0c0d50407428480007802d1901c905085c81c4440318014088114541483c00440c001c0d044020000e070080501d1500000c0c204061a02500c2440a040030400d80c0c034001c0c080d10708011018100030b0907580c0c912420300000c0e40010580790300218901c0d000340c07251020100e6454a4500e0310740034040418459104c050410190040e03041002080103e81101e6035440c18400040c80c1c056019220403c00d2100b13200140e2a00562070b04029444220340c44001c03503800250702d640c000e42c060690701e003140030304001504007400107192403100c2c180210140c0c903080c000078101c2d03102c1d0011913108840301c0342502064190008124039445828003103075202d140070705e0085d66aa40120103240308800c04400942141c1c150508206803000680d6481a000b0801380400d020f881d50070000c40c1416003d02020886403000d00c1790504091075591501514248240200300c00c01e0500280c640d150010003081d607042d22181c0700c44402c4840101068030950221074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 518851285 1250 518850035 518850053
    0x91512050c0d0506060414061003091a1003110603071e05040b0d020c06090a03020d120f02070b0a0f02070215070305160302010c09051e0d05070f060c06050c1213 71
    0x940241c1c000c8032a0b5510040c00b80004519101d00310540d010441d420810700d13828480d6038201c0e82d15a00012110b40c582c40c0c0792003500002e403085e01c100c02a040ca0303c0441c414110700c41d07041b130380c442c00c03014014001c10601209000d00e0480c0402a1800c61950800420050040000401099000084440051065100360125001001161107844e15242040c00d0070002e98400401c034071a900c1002c1c04034540c1c0c0d0001c1003243c2c0d100c1c0c2c50b4005040c071800e1b41c101540c40c0e0006840070307110721b0340c0c0e200071580500070342c0003c00c00588540c0400480c0c0c6058801c001c215030540b80180300180c07051051100584980303600425145100d400d0540301c1080e80341c04c440c3c500c0f400c0c10b4003120301c111303007075050070182c05400c60946c0c07811985400040c1501c50b82800b40602e1440150321080840c80e0100041e4101101a0a00980640c05544c4ca040d00d64202d0f051000742c2c2d6000800088050340c55000f4040140300e02c90700020010303411880c002220040d80c60f40031019248060840191020004029840c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 518852535 1250 518851285 518851303
    0x1e0111030f220b0d05090a1202060a060f0605070209093306090c04060e0109031209170a05060601120b1c05061003050d0e01020102071709030709151205 67
    0x200031a80e4824a11141600d10b4216100702d20440703901c0710380d100000c5100c05440080d18000089142490000d008107005403501400160352400f0300d900b07031004100991101240c0e0301407900204424103054001030b080301d949910240e50131540b440140907003075002c0d04407a003294044400310310f640ca400550f14101100d00005400c188007104240d04640b0307109400d000c0301c080103400c41000c1c0d5104401c0c482144811582c000b0400c0b0b0800060000758011000c00ca5141010b01d010f1090380d80300d030740711820a0012100e003004034400800820620100107823100650101c00c01410700d0010903a622651242d0142a880c18000c110030360417002c0215500502039954000c0a4219041080c1d80c0d00440c034a1011042e946070051100149160000704c207840c0481e54410300920301140410422507481da4800002030441d502003214001040884100380c00e0071218510081c1c0c0c2d040003004040c0740070400d230f0014003a1030410550b2108070362050010b10840d907080c44116518021032800b942402600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 518853785 1250 518852535 518852567
    0x20c010f020f190b07090303090905150405042d2d0c0605070b060d020f04050c0f03041406011208030106030b180906220b0118180b0a0c0302091e01 65
    0x80035002c58816041c3c225182d4107401201c03041c140740c031041c20440306048107010240116210010422081140d41c0c02240c0c8100e0303801d02803804a0140e00003a050300d02c00e403002e81c0e400c9105404d115107009038805202005907641529040510180d49000e0f1480703d5038084c1611807000205461100c0401001030022030303000302e440d15625180c1c0409042c940000b02d041d03481c1d00f0300c88001085810305120040146400600076007aa00c1400c0c101710140500400c40c4141d076000380701b10b29070390368000080c5001ea4480c400202a51042d115414078001c0140c1c07101d100c0300e03444c40c400d601007481d580407203041d190703131f85401300d4584544004588111040c0100d84c2e00780c401e180408c8004040803400c2802604e601038862411403c00c000101c2d1586602000342401207079400402592030f0341c0c1400380c00c00007031100129100c0c1d500300c021144c400356208141c5813802c10350100315012840d0710856034002c1c2130b41821410480b07001c01045081a1a07400106c5494868680544036030089101300001c00350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 518855035 1250 518853785 518853793
    0xc08030c0304030314090105070f0204060518220c0e060d0b010b0d06060e0312090f030a05060a0b0306070f050903010e0d050904140c16060e1c080703050106020c010f020f 75
    0x200e0110641d42c1c0c0c420722041d0001032001d076203103190030705000c101c80444c181651100d0034440d00c1e45803c2d03540c0040d100d0480e8402d40e03c94000407141c42e50880341a800344800c2c2d0680392303442c06500012107040102ca0789180c10510040010001d0803c8081d001a1000d0054801c5282e80d4100810b2030208419406020030010f44000070303134103c08a0042c568081c049100f4028140c4e205030a0783c0c0340f12010046c69040d00304044c4001240d014801800740f007040101302c0055030f00c1a03c0460f003880c61150080c0c03040d400c41c80400588001a02514105e03841c20342c02010170b0318140724028a804260102c2c0d004014001907035011503542500902c55100d1044d090b80c034001d03078140000d8a0703079000c01c0c0c5a0f0b0040b41000e4981582c00c64460f4407a04c591701403400b680c90070f0048081c81402c0110346a0440b5041c3d036801003001040020020451b0850000c004018922900c2d40050002100244001e003050306000050101da039010a2402e4001c50070f0a0040f080c29030080140d05154001001c1d00307003886 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 518856285 1250 518855035 518855047
    0x9180c04021c0e060405061f030602130503190c0e090c0924030304031a040807060e010f0501080610060e03031210090c02060f16260a050127090c0803 66
    0x1030076401a011600c0340401c10083c45040c244081d0701c425084802804642009000660908040c0a0380005035418046071210613100d5440c82c0498206a465010751400d04100784690309040048001c050015140410540b55039500c0e803c0c0005140207566000180501040400404002e05002014000c203c401d691805808110588103085000350700c807049080a81c41c1ca05000c002c0303d0659400111089c0e103020035075a9014007030400713081202d2101c001c0006101080c3c1c180b00d0349903100c031450000b00e0228003940200056030410b8002c081c25030003600511042030240040f80d421181035090440c1d0719545a0002411802410038080c0700d400c0200c1000780355105210143c0503a0301c0408100a0a03003034030801ca0313488804403000b40010080b50041655085402c59a041034140d07440c01814450f90101d1071900c102c15a003c001d1019060360510250205600446004d0709110741c1c505a0b00074000490441442040c803011a020b941c0d002d07000a1101c480c014202410048045a580780 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 518857535 1250 518856285 518856307
    0xb0105160f02040609090f2003060114150405030d120b0a03080408120a21020d11032a0915160b0a0c080c0d0507111b010206100509180c0402 62
    0x6207070800ca12a134a40f2401080300300d020301c1010601ca40010041d02c00004582c0e83c0b400c3d0102c0175620280f07401c4d400d4121051075500b0402c0c03034043c180d110b2502003400c1d000024010004060594003501c02400d000901142e10006502c001c00c0d0b60500e080046841c130102842c0c020405403051580003c004d400120600070401d001b4411200088100c40720300d601d80c40417060a00581d2103403000500c02c0d291403500031030410080161201d40010040c90040c180164a0884030700c02c560048400e000b0042040e003021040580704039507106400c40704807180d10140e030b640c180300d01e5581c03906c00da803202000700540d500042611043e0100c0c0160b00d03a5000c2c3c038141b481c40040e040382c01c0c4011905107075060311410311482d0440d010b51202e0031501c0c141002541d840d8050000180344600300444030600e42c0a1000401444103210b008a80d400d07803543c000e000081c10024020925087d072141440100420f0700d580000547c00025100d94400170f9054031180c80c103082c000d9510690050010a58130304003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 518858785 1250 518857535 518857553
    0x151a03011a01092c070e03010203040c0311030d0906110a020a06020705150a0806010c030e0a030c230303070809150d0f0509190803310302010525030b010516 69
    0x40e51007602c6120201d513941d03100c0000c080200070007a1201076400400fa240400700480140c204d2000d0824a00484a44010a0880c0c10495060f5808290380c0010030611401c0e4441205201098016140c44072450780c0141088031903210780400c002c0b00240c64505000248a460b05495008254103001656a48025a1075a0328010103109a140d8810909030b80151000c641c0451070f15156611196107400043d19041480e9009a09001c0c00d44c000202941d200d032410340185100d071101c44851401c002c44500914030740701008000041440c0843d031140e034000700703554002d42d0080d0000d594900310300c041196102d0130135040c0c1e8110300200701c3e1412820035401411100c62442002c00050740c441c86556a6501190344024124200900100c0852071724402540c1c8086d4231a03401142d101c010180700030494603400c1e038960601c070306d00d03641c4205036080c01400d4001107140d03072080000001d510307810160b0000308108010705659580b040c042e17034041d405a502520b4056011105030a09090030090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 518860035 1250 518858785 518858831
    0xa030c0503060106051e09040b0d03020a1e030e2701060302030a1506080613060f0308030405010c1412090c060f0a2c12030c0613140703151a0301 64
    0x1003400b441c400401c5032880b41050b104a15100110141501e9030112900314a038003410350b05030000e48404e02d040081d103900342501c124600c00d40c0248461003036410800708080b84081c4245107610701c2c0c650328020036800910b000d810743d41142e00c110120310003001e60000c0d0344488103420350039100d8400014911380542c069480303001074000a024a1301d02c240062034041d0103000f01d10104003800042451410840d544007006d210220000800741e4030b6200500f61048103603c120740c240c1c400020801001400c0c0996901200282080001002c02c02e004005a00038403483c1ea4240e031820000032002c031801c008c500545071020307081c0340d90360f004642410601d9111100e4507010400300f50010301c0c0340341e840b01c0e00d010007030080740c515201201100070030680c80586001144584401d001c6080d100740180540343c012150300661001e45291071501200390710490100001d6500200c4c3e080000c5505507188101c000520100010000d40c100300314043d98410404c0c1c60741640c60412080041c0100040c0906 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 518861285 1250 518860035 518860039
    0x190e100e07080109090204060807121a040c0501110312160f1403060112140708040b090f0d080a090b01090507090509150105070f080304050309040c08040b010302150403020a030c05 79
    0x1a48644805030310a039224262452000070b001c0d600104030b81150b40d0b0081003103601c0104081015591640881d280000c11742051260f608802c04400410034800d00405410008030821899850706440b040d6001d05a4481c5505109650980c4c080c108030038001c075240c0700403485104c45107007841c000c0394040c840804528008181c90f283c50020302401344e52000300241000020500e950780d00c000441e00d0070480d00d1800441038607041c809400300003d021052054015580d404854a0305042061109130085d000b20600c6d00002c0306649200340200e142c3c2504407041c1412a2140c458607d0000144400e0001815100014002040000040c1c0050380152070070380c1c03a5998503448004011005400b1364813016803466100600c19594068800307464054080d500c803207110740712034840c800c0c9680201c8084555410000340045145420303c504a10200c8610300010382e441c040e903503a010035006001c064400d004c0c0360380340e680d00c950b02011070b805154003a128202c2e0558900d0b16007000d290070300031a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 518862535 1250 518861285 518861311
    0x15050d02150a080708060402030f01031707140d090e0c0403020d111002150a0c05031b1201080d140a08041704090f02040f0b0f12070207051e030601270b190e 69
    0x11b14510701802924003504090383c01002d01d9186584031007025400c042500b4080b0b000b071141c0e401090380a401d000c40341510201610164103d100024800c1c160341d08912840032000c41070080c40501e18040d10107803541036486040c008600d050002c01900140789032580007a540e1040202d680c0e002c103102d04a5011580d0400c99030312900c5454080e600d1200c294400070304244006a1786192600c109901c056144180a00d014102080000b03000030981028581d07522000358080403503484002001c101741c001074100e040892001000709070783d0019202628820a03a151010304110001c2102d0062012000801400030355001d0903002c0d402900c5080c6070544d6412000803058001c104454000c600c0c040c10303600d05041142410158a4040c25000851184210100d002e0302d4a90342074a00c1200c0c09003800d001c1d4281400c161a180050b001800d1075004094100440d0910307205030440e2114014002c5460004c00000c074070600344000000d02406d040d024006094004468001d0146040394581 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518863785 1250 518862535 518862541
    0x4110d0b0f0406081506120d11070605033706121103061b0a0309021c062f160609080405090f0f0f090c031f0e0115050d02150a080708 59
    0x40100c5a103489580b44c1900588008110100b180040c0c1d07501c04401098211100c13000645e0600e411001625100810144004c0fa000000100403c000030604da140903485e44c640100340d0203035074014001c0c0481c0c0c0d500925003000b4000e800460f4a43c44003032150100081596500a80c0700030854600c203036003992070b41760922078904020911610030200180c0d031620446032000c2d250f500340c6c40515070340101969962047d00503500d00310440c039144940035042421072840d05242080300d4401d00300409081036654000d450840d000c4d808581160000c20306601c0e0482000c0500000701800d20050500f4035245521003080100c1018005644007920300040c0c50b65011031902c0305850560354128002c15003030004103105080001e10b136000c05418203481012a07080c0202e4905212010040c00c00030442c4400c1041300307203600c52807c0f550704c0b18000748000780880405850003050360180e039006001401c0f400055441c6e1942c4482c0d880c11005c88507a03100f540d00c1d0300400e41407040e146000019140e5001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 518865035 1250 518863785 518863789
    0xd090509060a0608060d050708010914010b0904030305180a2a1805131208060f01020706050d1808131e08033405070f050102011e020904110d0b0f 64
    0x20144a0707500500b03079800c114208402683c0019004150300d5100018401e1000001c60a01061000705109000492401c80900c1e11580a044c0803114508076071621504203807035034458214030b8200350982030006094849800003041c0c41007030720403c401803040d14100c3c4100000f200d4542074504084d1441c0c04002e61030090158440b945200e0040e240e0b08a1400c900c2d54107ca500180d085403100e40042401001c0e6a10f10f2003003540201c058012940510400107107040c011040d400c1d0703420910107807440070300302440502240607020384d140103296641c070f80c01000850101e40a417200d4004103250307100c50404142c1d440310103442c007a8451210401c20500c1881d03805002c808103442d042c80c065410060031000c699844030f5407003110382180c00c01421820451800314110320791a80240301a010082c1001101d403441005540f1490440e890403c0401b0307040c9030014404040080300303802507640c107444030028000d440c40b42c50136110120300046460340c610b09a88049403600e0b081ea00c1114410200007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 518866285 1250 518865035 518865049
    0xc0509010b0a020304180f050f090c01110d0305040f05030310291b0705090109020c0c03030f0a0f0e030d03050601030b10051c020f070803190506011b05011b020d0905 73
    0x103180d00541e009005c1849000711130f04901c10405242800000d0904c14500c120303003a2007064a22100d0103524405001400d04180950031102100f802c3c040c40d0b490343d20320b1442d55000711074005010146c2d103c000c5020001d0603045038802c50307004402c982c0c80c0d0402180c2a001d06070310703214004044040415007207198802411554003500131801c0d460a0100c0540c0310001040240114852801488408107080e92010903881c06408400001600e400b10324540902d0b01d400442c04505c29030042c441031005006c1a003c0301c80c4c034a100e260003c14119a02002c2d64848442c00c180c0c3c0d03140c06126590f006036a0706611191280409903010700c00100410140a0000d03c50089a00001c00400c0103079400c0040100b04000c44d50720b0100180760000000c0940080c0d00300305000c80d40c62000005102c01c6150f4004e200600d054000b03005c0085040581c0081d00781c45a10801803000c441c000794034130901400703501c69001c1e41031513454403d0141c2070b240e00039141d0381e000c14154003150122a010a550038900c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 518867535 1250 518866285 518866297
    0x30a0624080d1e031d0304050423130311010504030e090f10031b1208070308071815260601140a09050616210e220510080a0c0509010b 59
    0xa12445030303007800e2501c00d11845803e22040c20500d9280c01c81821801d00000019032000c2c2104040d64a590a010411007aa581c2d245400d005944803841403200c00c1040070b10b0398014219100038501e001c820301c0d0a4901131601e01d00c0c2c401c135501e050304000c1810340120b0001c00d851011581c1e084035075211107028000c0d10707040d10301a40300f103204c901c140001054a601c420300103501c50030390300049607940c0107640b50000184089a103500f01190590130035030071040654200c3c00c1360800b0b0840d65198061071400032807600c201500d14480300407203000d081c0160201c01042d00301c400051038100f6860211070401800f0b54880d400505044108003800c4540340540301d06c442d1603503601d018646880100400c0d50403c40a0000000603c604200010242c0781d12400700440700803d81d9010903c00c0d0003030480d6040c07902e114010711311004070152584181004220508415a002413217031036070030900d250300c40c0300d410090091241007611020700c00040c40b10700c2101c00803248004103a881c1c0f80700d0180c90080c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 518868785 1250 518867535 518867537
    0x7020406061d09090c0a1e0e090a11010309060f0b0109050330040f0e090f01020f0a050a0c12020c040b040603171608030f07020f071a09030a0624080d 66
    0xc2d00e106450301c0c1911215800030195001c40300260144da00041100c030301c03a4801da1380615468141c0e8509080b0030380c0d035030050507844200d0340a880c01402803078031280d80c4100140490450210034005a001e07511800340746401000030800b082001e03158034010309a004041e8040703001d02130001010714000807407806001065420401c0d428201444074220310a80e540034010710810300000c9811424200c90000910041c20120481c2c14201465814400400030800071a40100810440c041c030b610b0868041040e145421551745406500489150030054030003490381c609113890b04a0143d000869001030380c800c81d0108014081041004100c84544c480180284980546144c000e0500c40150481968032043c803251104c0c965a00d5030b1543c0708840a40c980c040340c1060140455042040001d4040f0110050840300d00303041d4041c20200e106003684a04950000f103401e00764600b4007030210202da0250045c481c400da503403c450402c2e075000c80b000b50007400198002940400c0001d510b1005201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 518870035 1250 518868785 518868827
    0x5091309150903030204050312030117060103081801020a0c2912060d0218070201150e0f0606030601030e0f011a0315040b040204240612020a08150418080702040606 72
    0x10324000c10041c020000b42507003030550034840041c0a850900c030600206a41c038054550700c0d81440000c080000c0c0020300c0f10590343c400401400024012310032506074a45489406100c10680d43c0100c2ca02440c650b8020250000c0344400507150070000c40d000e403149128600703079451000c11448802c50b0701a20180c1850710b1007960100f2450b040418070552003a0002c1e00c40325800c12086040900804152583d0340180c1d95002c110b84000c0400d00a64060f1081e030b8950203107130800782e40f4400006806010b50307110394000004540182e00070b5116040c5031142c9010344082140565002e4024091603c4921001002c1c440d440c4261402007480500341c0242c2103c640143c0321a11140c1c503042000304126005031fa507070019561482240040100c480d4034880c140500c03810b0180041c1410f21807000100d02600511804410541003508540d01003d0400c0201410742400e000130050308460310000d1200110020940c00c0c03151980c0100141802641c040c4402c03940c81d0406c55074900612400c01003805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 518871285 1250 518870035 518870063
    0xf04020f0d080703021b2d0423070215130b18070e060301060b0705030403061113090209010f03020406023a0c030207050108010302090a0b0f0301020415180302090c1308060705091309 80
    0x684064504021000e4000104410385a400e01d00d1900c0101c0d0520318054070703c0070812b00a0b810446c64a45240301e114141d814107180d91803d1550b0070000004085a00290029000194948002a218400100300e0790825603a0740501e0140d5402e607031103030003542459804644132900d84200c4950301d40c040000c0d8501817a684074280209104106038824107001c101d011041000c40508001501c40d1610059549200000150024240e0700604091500500003000500e8020031118100110f00b010115100c49240b1780219444007500c070848030704050f108001d0721562144884007168070030303000c8560003034540b40156108c0b0400d10000f5484903d0304001041c50241e9003084040c40000361840307040310710344030000e42640c009400900000144130511941603602c851030710b0343c00c0c1400c9118002542185c011800c816001400246c0301040001e089007410602520341c0014038214003940d9031400c0c621402040399012a0321140309080c09406117003603c01c20710580b80c540381d200c540d01070100b13 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 518872535 1250 518871285 518871349
    0x501061d0c0a0c0503040b0901080f221e1103070e100b0706090204061404060b070f11030307121205070f020c192112080f04020f0d080703021b 63
    0x940030915000400400343e00da0400200c040014101520b021804182c0b200c1a03000014940d800040000081408600c1884615244011941d5418030507000c0400e0310b000c60700308008048440c844100c281020340601c10140020105998a402c03002c0301a00c01e9180d41d9446a030109034180e660034402107001d1400c00075805203000800e41c051144101045c00071071500042c2c01c80e8859803141e80307022540c0d10405060f1070144030746005004100b915508000050301d400c4190315944500a2458801e00300c00300c516230b8108295400c690b48405a40d040c0d01c904a0010320412402100980315402d180c081080e150180a4401c089044e82e030040000b180e00c0307004c00c490885800f00c440601040480c0106c1c1d604908000414108e90000b074030300c184a90b0f45050001104e0b005003010030080e05606000c00e8007405a8550340280d0111059400800303100c0005034503600e5010014555000000e98204068021a1030424003940300c1035620400180001d22401698803540182e15502e82110000e002c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 518873785 1250 518872535 518872537
    0xb0a0e04050709081509100905030d05060d0c0b0a0e06030106081303050c0717100b03070e04050111032409150108040813030318050319060906110a0c0501061d0c 71
    0x881e442c0c1c50300c60342c0b580d0741e409000d091103c884100342a000360300d4100400004100661604100c221800b002100300a40300c29499014044418040c00c1c3c90b280030543ca695220301194900d90406c4040c1d1025a5501d0010240c0d80680b403d000892154881c460240c90454141c0c0e0480700c060711900125507808940460340000c580d4210103205062003411810035040010138040c3c140d6440c000c0002c10b040022a2424001024464074181070441180c440e80700441d04a040325103038900540746407207e1420901511401281600349940401044840352240d03009200c04888008021401c2c0c841200344169014100c0e1020584164041d01b02015407048100d07503405406070140504010581301e0b00c0d212001181d00031303400285044007940242000d03d4079000280411401032401003024030300007100c0010790602403d42e40d6030380c0c11001802403503001008000c0012180950ba00d80405019204203000502560300c6d61070100041407440001d0050011420000e40e000c031160349003400c1d1262 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 518875035 1250 518873785 518873791
    0xf0915020d140907080c041a13020f0a030b011215061110090f05101404060915061e0b030c071b1a0a0e040c090b13031502030106090b0a0e0405 63
    0x1540d50758911500c14060b0403800c2900a00510010380310702c030b180251440c600040e00f90054460340c0b41001140451401c21381c1d1104182c03080d1450a0400e5102c80014000c2c0108034007080c0c40003000844079041c0e0340c15408401c424009890b01d180c683c81d00c42e41300003100e1115800b04140b58402d10b040c003003c0d0080300c140406250780c604403030b40004400200001d0b14030102d01112040300580410040000a0080700090580c0c0c21040007104030030000d00d81030f410b0141005d021140c1d80c1066109100b0320320f6200c17111075284036042c00101c0e60ac40318940b11103028103275100b804403801000b01f0300d0901c91048034014004600800d0400c01c89031964503880000c800c81ea24281030f04200084c0c095841031001a1401441b5880380e1600c1c80034002529000b42c4486040c1301d1403801c002e8100e910b411200c00410382d1642480b9640711540103d841100d81c00b0740c0c0000c0c116046801c800485035500340c000314183c95555594203503481c0d403203005400500540006e08003151098503001000c0c202688107a81c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 518876285 1250 518875035 518875057
    0x5010c030c0b1905182a060412170a0215060406080607080a11040617090f06040609021c0f0605070509030106080703050118020105030103260f0309011104120605060f1f030f091502 79
    0x246e4081403400082c159401540410080301c0c40300382100900c0b002c0c2411030007201503080b1039850402050703070082d1220b94010201d00340c65a8140030455503156988824082d0003180119281820080c0c0c003d000c14404954207901c3c181002d891043d0502e06d001920304644a07503c49110100345c4281d071b8403203880000d000f14242d11075841c04900744401002020701550207241c0028045030305005020a031100c41d05281a61285080080c1c001a0702003441c03850150401000070305c903112010102c9181c441c2c00c54159256003040d13400314511402143e044102c07031240c0d00802c21001701c1c07001c0d50b405800e510006404070700c0601c010004181c2c8a02c0112010300b5045640c02800c00615081d076564100007900101e055001c010072103142001d109089018990340800d070304151038403041285003090260024001a210390102d02e540d1160038001c100d80340b0041410f0f281c103465030005403d24114006910019040c03640c041c0d604041441003542c102d400c2094058140340d24004c1d80c2c080e511041d0190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 518877535 1250 518876285 518876353
    0x30a02031c0e0d080a0b150d0515030f030a23160c0302130207300e010e030601060309120f0519021e0c0f060c0705010c030c0b190518 59
    0x2c0308a400c1400320b103110340c0d140d0300c400c0340604101500b00119058249000d000d2040303140f00c205404084000d079083c0303000c0321a0104071a0340d40d0740046510b0281261881d09803290070104407007020044003910501c0882e5803008030260320000d40151608060900c1301c4245d074100f01584101001024003444036000c1c2c00c041c0c02ea1070340c3c0c0e804142c2080d81c040d40b2061580c0d02142c2c110802850300b40c1d14140e02c003c1e0350000c00c00c11a15a0b02001800c403640c5072001e00280080c4010b880e401000015154240141a0b8605680d50440680034014000085802540c540140100c00703018a040c4111000e440e0303142410302083e5001b4143c080042c4101d00c040d84035240041589881c1004106014105600940304c20140202800400350f80550254801c0c03005000440341d940b80040c2910448400b4a0408540125400d05030b82805140c14050401510501046842c07000c0c07078624074140310100c500304050f54800402a001100300342040445801c1602030f260040310504100b10f510020404407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 518878785 1250 518877535 518877551
    0xc12020d050d1d01051314040f09080304030906020d020604060c140a02010915140a020f090d0b1006080408070320030c01140f01030210051804090605060909030a02031c 74
    0x203160030300300300000300042d0212050100003c4a01c140c641007040c2801c2003410040f420364440c3d48045c5c1070003000002d60350601076606541c4d403a080241070382c0c1003030310070031480045052034465944201e509401181079440006500c901c00240c0880200e102c0e4003038600358966660301c4002e400c004600780e08000d02c04c2603040a558090f0002c1c800040c3c96000081e180307890386440d04008007220010f22044d403610035144580c1011840b03c95000b0900d210044c2d40b001013042d00c5074a070040702045038001d0036403c591010009020f482d28001c640745650301040903170f249401c07201c10301c040343c0080c0b14400900100740042d0041c0220207032021004100302904461450151031034000b1482688541e45903403203202100c11003d04250461703600c01c080d040642c15600400c00c041d9203211800100000041c00d0541400c40c0c00840780465002002800208030b1420a140035140030342d10345204d4201c01d00031078080800001150507800494010398285a103840030011701212940d40c4035031070390311a042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 518880035 1250 518878785 518878793
    0x150c0606030b090a05010c030b0303041e030503120108060901020306330a120e0c0a0b0309070b04030b04050c012f0a080703090f091413020105070f03081501030204030c12020d 77
    0xb140f0710803081c810007001040294145142503c201e05903c0c1e06240c503021030103655450110172142607921a0300c0083c4940358001c90101040d00c0351f8005012800080350341104c00c01d84618050481741c4140445803e5100d200381c5900302d1100360307407107640400d980c0d20076103410300380c228030504070007048000500c2503007406991740c030650040b41380e03500003003685404d40070307014540c410b00240307120690041811605150101c0e080440c81c0c0104007140e0004800552540e02c01c102d42c001908480d1212600c4654a26001648840580d000c8440f4001c2c03411300d02107948909030b080c80c800d40700011500c04000c01c4100312019522210101003901801c041038010401c0c400042100c40e210340d448240341c0d4a020000001a40c0c0341e00000e1405080c203002c4081d001c84807030380d00c0d0000c240c1200e00403000e2052005035002c0c42513400081105494505903400d054008400a10801c48000c3c1e0340c1e55a4a558011401c0f441a40002807100c03c082c0414800701c00700b014581201480a402d03840d040400e81c507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 518881285 1250 518880035 518880053
    0x3060913050a020909030913150b1c02180a15080610050d1a01090f0b070816140105040209060103021201170a0515090d0f0807030506040b060c06040b0907150c060603 73
    0x58030745c1c0b903600004900b1800d0410404c0341115502c403ca0400001d001000300310844200d074801c1e4140c4041c041000400d0702c05100e43c131041c000c0c0c903000c115a2107529542104070418510701a52040400c080002070440e015105420348544030b5135101180e40d244401c00941d4201e000550307040003018840301c41102e94921460900184079080c01d008402144001065003c071600040c00000c41c66404010004050080d109255480b4840302d071150740030399034096903a800c0c00cac0240c03140f0f8030200c03031196a204c10351010740110300039034013502c1030b0790f815006600383d200f51703140c0c1da04c4507410100410001441c000c20751040102c04080d203c4480c45501d4003031038001c5030201403001c007149205000d11345508100074400c0c46c1392070400e00c1c121080c801001e440c0b508002c000205240d100c0c030001c4d0b0a961164030500c24180c001f003c0680f500000f00509036103880c221401c5441101c200d0100b1a02c0381c00040c0b0208466101100000040c2034020487d0000c011110842e10380c0d444100200000314602c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 518882535 1250 518881285 518881291
    0xd030e030a110406080a051009050a1a0a05090f100f0b0405100e0604360c1403060907030f02010c1b0b030609070c0507150513080303100b03060913050a0209 69
    0xb030244000036140c00c01003280c071140d01c0801c1c2980445008000030340c002c01c0001c4c01012080340020300c0b8051381011800c0110703a4400605040102910b66154091201c00c0c0b4003501c4511401c1240d03541c0d42192503901c442e042d0503625240e0102d01030051040d000e1f00070070308080e1034000100b09002c60360045029100c06598000d28818400c070140010000c20400c2c0d540410100c406101050031000341100c40d004c0b00892080c02c0345e2041d42c01003164204052301c022150f0201c410750780b50f541e0742c030841c2114224400245c031034051a8045003881300002000360a898214420400c0003403207a005540e81190a802100e0116003400720b25415150301d00401c0c000e00d007203036283d40e4a02e8994200094564001e10440c1481440d20000011030400104202940c403500d2504034104045401640d2601494036103100c40200010042003d02000c006103002d46044210303603c0154a07245040014041200d9140d082050749001512000f520030869080c280a031003607568041e0030380c0106141c04412 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 518883785 1250 518882535 518882543
    0x1020405060309011b021b060306180a0609110405090130030c0c0b130509150405130506010b0c120f04080a0b0103140c030616022a090f01140d030e030a 67
    0x20110174803c0183d0003074000101c0f0341440a4503400d90f0101072215111034171100c0070f02a20b8003100080258850f00f1010740c03c2c9070b80080ca0503c528000c03200340c028120900030040040e04010700c070020b0070524416201540c50003440803c1f582e081804c9500c041e1043c502c18401ca122030b010070709804c01d0801d078480c20280a507485030080c0c03c2505050f551034242da8058142e410082148220b40101c1030000c205a132000c0f1a94409902e0303003e45981106ca54401c3c1d00e42c0146400148480a5501c110b03400786d00d0321810969031583c2c1c1c3c8101e2030714503000b89030210900d03401101000440c400c04c800200031080d810307140c2c00c0c10b03d80c45411086c58030700c04180413207000310001e006009120014400c0107185003100000c1102012180100b07440703060160001d040c0a14580a44403064000d006245001d1050844144001c5d0f04189030b04a510b412041c05010f500d860000c105d610040d105540c1c107076001d840b060b103501e00b1084140315440211b0710703060342003050ba0f6158040c5a58240049001c02d405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 518884892 1107 518883785 518883791
    0x9010312080f070512150a12061406011239030e1c12020c010507021c081b0702130608031e0304030206060111010f1103240a15020102040506030901 65
    0x701c46e4100343d010000303c9001c610314132400c2d0300c3c81849010b80c2060000c0c1403060380003822502d041d51814001050440081341e054807d4010000034004079420b802c180580500104038882c40e50003581c242d96080010005559040c01410000740004003d044102031005108031800309466094080c01540b02240c080002c0542c15940d405201e00002d015a280c1454001d4a5071840017203d401101071514a5001e6440b421170a07200744581110f0808103004005920001d410000f0100d9001c6000301112a20214a0003081c00421802d802540c84005400400322544001c00f60158098410300c200b00101c1d50018445400c0f8a081c2050385801c05040c1340749003d42905207594142c0750501c0040300b182400e0034002c521410121070701c9080100c802c1150404107140d40d20f501e900c02600c00d400c3c001000184110103044016000051601c3c0d07941c00410360640040351101c4403030355 = true := by decide +kernel

theorem cover : BRFrame.Cov 518705035 518884892 := by
  have h0 := BRFrame.cov_init 518705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 518705035 ≤ n) (h2 : n < 518884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
