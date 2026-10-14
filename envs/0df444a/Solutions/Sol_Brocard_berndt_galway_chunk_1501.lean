-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:17:00.299988+00:00
-- url     : https://prove2.me/submissions/ef533df8-0481-4c2a-aabc-a04f1fb2cf57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269784172 ≤ n < 269964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269785422 1250 269784172 269784191
    0x606090a030c06030213050f0306010303200601030b0411010c0302060a0f020c0a0c1e1202040f0b15040f1a030c0c1c0f03050109092f0d050106030515011404 69
    0x244058101e420107000c0c1c40d00400041078030b5816074000c001d144110314030440060351390410016004151350f50140c01d50411030041001a0041100180c00220300103402c5000d001124103a15040c0b00760b005450a000802c2070100340007000c10304181115003840d289007a0f50b0103072000396840002070025040b07545d440050030b003d440c2981c1901c0c1910712440640c3c21420b120700b8010b0710000203021f070b44d041409090403810ba450b4100802070848003106010901015560204001480380d50300103100c0a03195006070365240d0707400340740002c4580c2a0144688407401e00d400e030101e0710a1070b005069030300c0c00c65844a00c1001404c040da0b500010301c241540d40e905890b460365040240c00f24034400341d00358026104c0c1c0d400f90040351181d203c00460340e040119a903108085429925800000b4140c02070b40a554902c1090841454007011503005410366540b840c0d034049402d4043c0b0444c2911170381d6403a2420300030800c1c10321000c0040f11410180700d04a5050943e11a82441c00c8003540d403040b60b90b0040350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269786672 1250 269785422 269785429
    0xe090f06010225080601030c0518071409060d15080606010f05070210030605030601090c0f0c0f0605090c190e010911030f090a0c030b1009060f03020603040c0801111b03030f060609 79
    0x30f00a41414070a5030b070156900c0c600544001840c2c001c0c54420000941d13001c0f009150000303118884c80660761501c540030140803200801d6809184420b07046441049017042484660042d400400b00907030103041540d2800b8582810004082c0001741084180d0f0f00c20811207500070103407001940c040300d0301090344138291426401011190301844e0140110b5000081084490344a0359048241d6202c903d483e1291040c1290080010100209024502090000030031035a920483d0b00001510032030b09010540000101c80800c20500184241c2e000741d41804158075461207240106900302003480601600f0390485294000104880c07110a001e20000302081c03002c00c4002c0300140c1201906c03210365241d080c085851001120350406d0039001010014155104c0c1c8652401c98103046010724103641507a01704601d944c0060b1050701d2900d0096400314003903000384102c840400c003c5940c02d0f500c2680110034042c0c154000ca4041c12a0800c4c0200454003050441459100f902114155914071171072000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269787922 1250 269786672 269786743
    0x426030f1c02040510020604030e0f061605010e0313030303270b070306050405360d120207050106080a0302060c0306030309040b1309052805071e0305010504030e090f060102 76
    0x803548080e40d05c01c116121130f004640e4900850090303403040d86180b0100103020a540102145540020041103901036080840018000c0984501d0000c40c0e8140000b031090b107550020b14201c10312a00410042081507018840d40c0c4d491001109503250000e000c2c6042445d640c100100900940861800110070500c20391014026002c010000c01c07590429144507801600050907000b2031044106031030049249034a60010b4403a804d00043c04401d4408a040b102c2c441c502030784112540d021b01215000400a001c0c070805011540c0c010b101c3c895044c2030080c640900a4040c4480a004106106880d1000700440b1030848040c3c80200d86400b05101213150000c54020403080207141601d414104480030902412401403101215a22448110709503024002444020100d512180e402c110451070b000203e00b0031103c10302c0300c120b0107a4a885840c00d40310304680480005840007030f98070191800740c80607500000d04134a0024189002030010f561410307003802c0000c3d402c411007880a2203550f03505a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269789172 1250 269787922 269787929
    0x30d0b010c05061512010e1f15080d020724050f070b0901090507090b06070b09070509040606091107110d061803030b0312160b0702070b0426030f1c0204 67
    0x440b580ca01d081148184804c940c444407520030f2024090070850410140a010a98862000034008902059417035007004009005c2c2c0105130750f110701e141c41c15a0240f5000e8401046000003411501500704002410001d81350800c12260a50045011806c2c40c4c00c101545c022a05013000d0360b86480c411141440e5024a2200422040c0d020013005640201074000c0b40c4098441c1341228440303030b1a8401c450903503501c420442c0d01300c2020f0100502055a6201e1150003003004016200d40035180c201141c4004400c40d000c0d5500c6844800c01c00c10002148103130981d40c401c0151103828001240d503901c1c082120b841d442c61046008118000c28000300b6882002c0a142c51016100503014500e0003402814165025038483d0054008833a10480c1e01021100c21050039200142c541005030350329109010003501d01c004601c0361900c0840c42400a5005002401000c00030342061a07001c0c030841003000c4603a10101040d081400704134000e02005003907035420881000d0440e80750754080c228000a0003a0303403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269790422 1250 269789172 269789183
    0x2040906080a020a050306060112090f08031f060c0305180a0f14090a0608071a0d05010608151e010e030307050a0303060302012303060405130609030905041d030d0b010c 74
    0x1600000c85040c00100d144400703101351024800c15546900f0152143c1003151020301060f03003440c815007081415444000800c2c42841040c07600f0620f03450340d610503002210200d100c0c0a091000090543c2d80b011500018055440c0000c070740301c0745560081040c09040c40398140c0e00d0004070000d00a40d00c607203401d40a801c070075100050b140c3e920a41d0a82e49a44100c03114060072441c80072800c488014040c5400b80c0b00c06000400b056480d00300c4002c000e0380c01d9100448441018001001465061301800f0700810642d40c43e0246030411060120b96001d1000455111300480081c00364070b24032419481c2d4071800e0900b0080780c0640f00001281c1148110803000b000da01540b540c14041503010360104003541d000b07a840c5801c001c041c0c0c1c284038891304456a1050300200038070000d849440d0503009a0344c000c0c01a4070410300c0700b42030b0352030b84291100c1d56811000f02d0324442c2c09100320306213845025041100300c03051024082c582d03c0216240d200324000e000f0425166000c20750241d0082c400e14035003d9000e03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269791672 1250 269790422 269790431
    0x50304052407030c08060a15090b070f03120203040201020d14130b0c01050105010908120703030e01021306030b04060e01170307080a0906120e030a080910090b0a050f0c070312020409 80
    0x24401803807041d1084400401092509001c0407249103d55251880741c1d6000e0081918030b401d02c02d80515136030ba5004080b04022a030366002c41c0d1619040c019280c4107114043c3e03204210f4842c03501900d010681d424903070400d40b05104000c00342c1c1e030000e070640200d12a8106040810f01d40c10300040b9510440c01c900400401d1080e0015031a07a0700d8008104109000b0020003659807035000441d00382045201d00c1c805a40100300140e0842c0c1c030a00101140740c440c0c1000120b00342034000803400d9030458002c12003d0290000304100840d0540a0032040f1241210108042400d000c1034140020381030084110340300107400213030300c264000c00840300c050741c01034130f0291215540b8800600211040c001c180c00104541921161f1000d50301680c07011203c420003460400c02c82c210203c583e40720040040340f40b4440c2e1041d92078202054402d2041e04e6000e40c1c05040a450085201d00c20fa903009801e800c841d903080c104000c100c13059101074400003070341483c0c0000b681c5050003240002c2e006640040680c2445c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269792922 1250 269791672 269791723
    0x117090319020f010525030e160603050406050a0b0d0f06020d06080601031401060e0f0907180b09090703020f06030c04091404020301050703060b0405040b010507080d061a0405010f05030405 83
    0x80050740541c0745402401700c0d03958455141500c039042008012800c6003541c03500a040e020750072a885550b418801c0b0756500fa40d141e00e015071364440b41e0145000c42e42d42d00912040c000c1500940c1d500043e9001e041c000322450101040c0381c034800000240400c4410003c0400704605901100c401140e80201805106d07151080303a43c4686086c0307c00c6601040b10b40503054007e2060107140d003104c1110404045940d1020b4514800840090020085026071540800c03415420410f0090500c00d0f41000038500d0320490910000c00c2d0302410035010313a4400c00d020001641d0300000441d00d10400d070354442e105d444512020586002d40e411100c011800d241601c2400840582030610540c0200c0c002d0203c0d0312064815000c031081d031300922030340032410041880359040640094441d0703181894414a0400320392101803060b0800d4451800d525200c0100b0854004e081144250856006980d50b142516100003c0c14806421100030180500800090148101031045506101400801031454440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269794172 1250 269792922 269792927
    0x30f06010207080606030309011416060b01020c0102120414012114060d0215031009020d1d030c07090f11160302070602070e1801020c0a0501140a09020117090319 71
    0x4465040c014071a29070300060b0180b0000340310340034401c040c0c05107160080207070044901030a030b541419007030281042040b812030580841c00c000c4901944000072100158000241841ca402038414110740c84082520405007260017200e0807200000c0310344030002640001030f41e0034940c1c080341000e1000e1010356444101081d406c01c208288541690520720303610341c420090310408000010307400150180d031280050004500841d00f0100080607240c150755a04100002d07613010100a07991587c449a20707039900c0000035114005445030b0b00180d42801c40d0511002c0e81e4500b140315640f1780035114030b500700c40d09241ea88110079082c0c8081c2610b6a4802c8140d841200c00c25000c4100c00621400800240151021501005407184a10b1030042c94803400010481e00c0207440500b503465500700501c0c9010b51040000741101c0c1d10401c000b08000340c00024041c1e40c0800145180341c240e00382200800141e0703106400800030820708495151540724260309134a180142811407007a80e402071445030803141c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269795422 1250 269794172 269794201
    0x30c010e011812080a0f06081606050403030203251a060a09021801051c090f05010c1e050705150a06140414060607141207060b0d0302190c0b03 63
    0x80d140000d000312001ca1040c032245415240c00a000b0746104074201000500c03442945401041059001c40d031038503c5803489046501d640d100c40300c554002d0135950119520810b40400414040c103040f07040904d9510302948030b01c00d240541c2040d0b11603c00c48141c0da0320040d502e1407203070341080ba2081c0340c203d00b807003040c5504420b5598520a541c10017000840007254001c403515003d484403038440b1407040c2c0340107440070303044024150800c003030305203401c00709008070710590040c2402221840203507a400d081c541d00311443c0b806144200320040e6800d20350100f040600c8004194186045507650b241c50800a080181010184410344040c0c1e050010764800b80c0c0050781170741c0344640c0e003040401030041000220340401c16148420325150700001c1d124600213000c2c15155000d40604824140201c013402e0800c014101c51010380a400300d210350034071056209020100d801500c44030007480c5240c030040d542d803007407000d40094581440700b84020021140054001002d511440941340d003400d00c5441c81c9030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269796672 1250 269795422 269795441
    0x20a05010f1d0a11040f0207171b0105010f0312020f0601080106080d081306022b09150b010c060e070b0d020705160b0f0702040608030c16060521100503030c01 70
    0x4641e004100740403120086030082285a202803111340014001c018080038000031481a81519402d02000020a5039401a162034961090709550340741c1e002502802220302d819100241070707140000500c01d2000c08074498068a030403a86051849180d041e0803841c1140c1280c0302e1516000704800028a52015002407040d91300d42da040c0c1d1880038152908a5006a0481d5004d020240c60f0032102e002c0f5030b0603401040400c0c402c1002002009040c411100c40322402c0c2000080d0b0b03641c9090b00b006000c078140045507000900e480c144003140362540000c1640400c91400317420a561404240d080307500c1007100f50000d00c6156240c40d00e610354104114003d4001e00380c141c13203901a0b806c8440b0606490071405094270a80b242d5a4284050042c000180f500903060481c6c00c03582c1d50201041411003003018040b042c078a40c00410201018100046490400750b02c03030b0040c448107010440e84004458040702413204200400c0810396a05c00300c1e0440301d0b840342e000d543c241c00000340c000c1e01c400c1c0640014140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269797922 1250 269796672 269796701
    0xc0f0105010e010909050c1509100e0406090204050f010809010b2806020f0304180b1c0c051c0339060605090408040b0705070e09030a02070816060f020a05010f 70
    0x180c4ea5150180305407031040e40c00078900d42162419021502d42034440320407180b0a15100360800c01014081010000303174a0014011441480007030100340f0340341c001d4502500c482e00040d801c088c40d00001c1498408000e00d0141803003032040c00500410ba0035401011201e0000b801e9000889031f40d450010b00d0039105d02c800d940c0100d20300011405900024440400e000400300a510702882e21102600401c40400b244501c60b490300e80b006601c1da201d0005076402060886010071803c0b1514000a890080c1d138451030242c140c0c901d07001c10070100c2c074072040d40c400c0d09401d084400c101c10310b20b840c0700d1020150100c180d02814040440c1d8151205a600391414410b031420000e050300d9800f000702c0c4240448000702002802c200500c180c60041e0003070070700360f88110102e90b5815100c69264454690840b0020760301d0380007050205088d5030401c102c800600c111009084085050b070f8103540b00480600402041c00410b02145406c2c0e4800c000d07000300c0f41c0c0c028008018104210210401420016a49141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269799172 1250 269797922 269797949
    0x1e0d0506191b02060f0415060902190306050307120c05031e060f04050304030807081603020102180604140d0302120310061403090a060507030204080109080304020108010f032004020c0f010501 84
    0x1140302e445442540c4031109900200311030341d00da0307000c1048040002c01c111440d038202c0721125443c0c1d0643c0289400b42c03105070380158a5903500c45a0f224a4912645103904040c10100b003048a82c5002c108501513038000b00112268000c6030500b02010b060a60101c1d40502c02c6091715a0100c1a4203136800400880105030307582034948058508030b0140985001d0f00c01d400800c010000505400024800180700e20307501c9080101ca103807441d0000c103100c141903000d030b5000203400240030310174803850000e08000c49049080c07a04000ca00301c0c1400d2041e1445009079101e031302c40814107000300107480503001c5d10b0a030180c1d40d140c900b64000c14060507224084c04103608000c0706c1410400c050943c2e2092003140000c08030503041d40c6411020f010702134011070505d5802c010210f41d0641c20300501d07043c14000d22241d55281020700c0014969003050380000c40d03000005000344000368081cbe41228600382055045a100305c44003000034000c2c405c1e04c80d411142d104814a420900358107421103412900c81c01101e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269800422 1250 269799172 269799191
    0x4030309120c120204090209070e040f060614090301020c0a03030b130204060c0210090f06020a0b100b04180b09150f0f0f09180607081f051e0d050619 66
    0x1d20520480203110102640050048060410074810f0740390008001141070307420354000c6040202e0543c1e0f12400254088071242c0e450030540203030700181440100400c5424a05034000301300f844840020f1000803c0001c0c41800c1d0b035401d4042d103a140110700b0640d512002c00349406130041225a0505000e12040c03001c01001c110030f4030a80741110081d4440e2030390988190b0030810303091001d0f0030007428000ea2940106401b440700c01c14a0140206400507c4c80c5d90303e80c102695641d200500410040c480610180141e03109841502c0481e18504424410600c641521202800222200c1500450810100a03000346581c201c0c008101041d40c1f15403148002006000300480c0850f0000c1e002401418100b88905084100c0d41c2e00c000343d001151312245401c1a01401e004082d1803200001c1c074800107002810307400c3c00200c2d40031410544d00500c01440c02c4040b40007456039905000492050300d1008601e80c03110310070020752a900805640ca00c0c58030146c0b2440c0009082d460f05138103494450b148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269801672 1250 269800422 269800439
    0x6060f120c09110a110114010b0a090e010506091306120303060e090a0804050d0201030b090c1209070e0a0f09051015091401050d032606100c150b0f1504030309 70
    0x1d003a000e042d030041524042003010255645003170003071400e0603590f903a61010307030040c0c0403104e00e8081c14030315100da996141c424400812402564101d44400ca0000d0300403c007540e54001103485030034041d91544d03841844030410000602040d1301c03810308050b41c250003000300f41d0b040d80303c4c0d0140c411001050545442e00306920b540c0d01d07a010320007082c0b910700b007005026600c0d044482e1013049105160100b070000700da0010559070242954403080042010039201c4480e800e4042d996480200d50004000c80761a0130f805060401300a424692816500c0101c070088190907007100310b965070844101e4032045503200c6154014036034138601c003486040c0c03000f0114020106018044207407141c1c408a80442c1d0030401008142c0140d108100c082c08a20f004100b8100a07042c085109c4040c1d07070800041c6883c1c80310034003070312450640e208000c2081e2408048002201d05901c294020703d918000116246404049280700203440c1035282c0c0102c06401d0b07500c0c00c03285100203000762032180e618280740690302c9401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269802922 1250 269801672 269801681
    0x90307050f0304150f0f0e04060503070b030a060509040803070516230118020a1716090c140a30090c08010c0306081510170a020411190c06060f120c09 66
    0x2131100003041c01109008441c4a07c080c3c00300c0c0d02c0014000600265910300191810110b544030302180c8102004020043c00c0f140702e0107005007400d81c0e024500345400e07070300c0d007425100040140b001e001c4003280d40e1000d0300b045012004c61a520540350300c444c0110314007081c04540142c00ca10019800c0c01464034825951101c540003055004d042884050b0414483c1c40000c0429501d00c1403038403a508414481d05620500840141001c48001800b40c0030a203006120006400c98101422004c12604011941c85004035501ea49070310b002d140d0003a90030840c40c07041002c102a0600e0781c7e00300007140d000e110041007200121074002000300a0203030311810a4040c0d8940c2d100340e220603003180240301d42c240c500d88070441d4406081c22400790020340300c45c4006085440340030009001c1e4407500000003141090b10035100a46107400704682400402e44518115902000307408041240081c800340800c12590030070005414601100c0700700e1502c4500c8140600754240f01034403010b44140e000030381110207114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269804172 1250 269802922 269802947
    0x8041d0601020d0c0303110c0d12050c092b02040c021b0f060f030a0609060f090b01081b090f0418050607080906010905090a060606020c01030605040b060909090307050f030415 77
    0x76070a00078810ba8030203600419164820687d8100d040001818040082c440030b0403152494460024500c881740001048a034010b0031040306030010804204603035180300c2002e40700254040600d15241e183c1e40c078805d0f5828010f10094025040c0344036000c40c150040754500c5480b081c4241c0305082c000702410048a107a0400c003460b000784c0108000301840300d15000441d840321a00001050302684c030310405003100c1503540040000740755a02e0600c81c92180380a0956410024030b0f00c0c94607400d000d9984120350a1502c03080280d044005168215525401c2c21000044002001044105500d50381500c808403200c0046030240250b00c00241d0070340c0120381403401016010001c1640d682020740510060401034110000b1f880340d80c0c070340700024546025a00181905a0181105806080000d000c0c0d8440b504141d20503402c0039012590350311888155000003a0480b1001d08a45908071150b0841c4101c1c10050301c0e0313015040801c4402c442c000000e104031a88009480085010001e003281e00610303904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269805422 1250 269804172 269804177
    0x191d0f060402070c030816110f01020c0f010c060e0307030e22150b071101120905060a02030c1c0207230d0807050f1803010c0206070c140a08041d0601020d 68
    0x40200300d15080541c064500648942280380095840781c6030300710250080410140581d04e0164054100000c9803040349a68005541e10b01110460b0300010b5140c0188002441c003a840d2140c4501c4960310a0a10441c550f80180042280303800e07682d001a201d5105050a90102da158001515582003040744551003000200605440c000c000055401408000600b00120494800e010600014040007010003e100700d500303400490000c400544504411000c841d80c40d45015080d801003000400c159502c0b0142982c0140d803661195840181400f4520362620b5012030742e03890854503002a4010402c1900601600580182c081440741c1d80708810719414005030041c0c0340b0940722034016170801e60029918100710b410f0242a0403000c8598102580107004d00081c26101c4000e401c1c03c0c03045210750741883c40a004686400d0001401c8e041d0032010050054418400300404a036040c02101001070f40100f107550341c0c41c6e481c403203481c600107807002040c0604e980401054203907000080c100c02c102c07881d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269806672 1250 269805422 269805451
    0x603050f0706120203070918050609010f06020a030509060c01060f140916030b040b12010c1b231f090b100303020601050609010e12030316080f1b09191d 67
    0x4010f01c00203034201a05850a00c5030441d804650440c8140203e44903540c0c0460003d06480e001e0100b003109501a404402c40f017401d00d0060180a502140c0c203400300343c0505240360354156880118125200d80001c22625500c0c00700017084c40c4a00d0198041201d11409207110090300c10010414040d400b91460300026400032000710f1414040d07005802c0c40000104009010b440d10780200d900c04441c0c40725005a650b540b04202e61083e0040c4101e004801c4402c019a02d4500a41c1c5114074680c20b102115901400381f86e0200c01c2400402036691008a54110150308803600c1c901a0060b0904800c115070f2191400d0020301582840e2030b084046a030160b004141c203074070300001c3c840140e006400d11030400c90b110340c2c0803125403500e5101c21807006141c801940d407407621600c3c20780b6108000741520100040ca00c14401d00c44246650782d5002a020701c403415100594102041141c41114002e5800070000b12410905521341400e5500303e450359220600803030082d9000203c4408110348545562250 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269807922 1250 269806672 269806697
    0x81602030f04140409170d14040203070e06130204030501021e12060105031503160305150f0402061308250b041208160c030501020c1509101a130603050f0706 69
    0x405802c165036101c0600009000c184c0c0d520340c20f0b0001c0c4481143c0c6d100c0200018003a514402611801e410104480c041c201c0c00e040c9540000e40740c003283d129405401607500040751070307a695551010755618044c901156070755900d1411a01075040140b81c01d070000814003030141924400012103c414040981185080d51074030015502c82d0000341c20032948007107500c0600b103561010003061182071600d9150b50070b000e181d8034010780740102403040c5002d42c40c821414424078403100f01130303280c00c00d9040700c5079500c03154129904c0b841099968044990340c800e404c0b10403102103510740c456a4100c0e1820140094944400b810303112840f40c2e120706140c02c0711114400340070408680c00f40c401c3c0184c200c0e0707030b480c1c40c00035444825143c00242c00981d2903940c0003840210000041103281d8044401420605003882e0801c0310320b4481e1542406000102d031646a0300724400109003515021280040082515003040080300c001007001e0301003201c1600c10b404107040601c3d0005a204203e554555a00000010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269809172 1250 269807922 269807939
    0x60804150e0f07030b040c090e03030a020c01091509020a17031c0204030209070f090e010e18070321090911070807030903080d0b030d111015050d03081602030f04 71
    0x541154a142078041d88840b01c1d02c0038000e101c4000298090041d03002941098108900c9801d00340d400284220300c3c240708800d24240c00300503284d000d903d030b42c001a141d640500340c3c43d015104002009091076404015001c2ca49829808940e54a00a4403a94691510713030108800c584001c540915035580180205040c48920031580d4000804040740581032550701c0c0c0c08540f281d103041c1e40c00408203140d01c0c24507010540c868074103c010280409031401d103525003560b24000b03802c042c288900036001c00c03140c0c50412600300000c100840e40003030041c0704481c2400c00990754140c28400240051102e0b000000d8843e4603019800b0b00f101c0ca64100c03031401c1c41039600c010050b80b001d00c0860a200301c20034000046060800500038070114070744041100001d0f00101803c004504443d481403200602d0700034101c050004083d045601a12800504c403821495991044030315a40050750001e0400014003c050b4040401340c0180400c0361030b04801c003400001a070322401a485a0180c00e402844100301050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269810422 1250 269809172 269809181
    0x4060f050f0706110c0613051e0c09180f1204140d05060106032712051606060f03120c0b01090b0d020d140d0f0e190801051303020c03010920040b0603040c090606080415 74
    0x803840048542c070285600104bd131582c2d00321400c1e00020110320307600965000c00d10400410072016806480c1c031004402c00389076107000d280100301003900b80d109441180e449440c4000c0070281c04c10100c0301e180d03a40c0d910041c00740644120300d40b0001241ca400c6c4000d18440a0355104241c0e200e040f00d07481500084040b0390503004040c0f000e8200113084080070100d2482c1c400c0d04050b1862104451805042d820208641d05600003240200b212644148c00410840808141500c0c05045c0200b41c1801000014400344d4405202951010384400b11300c0401c03c0307e03130205da0007044000a07584080703101d0384140c4061881010450206a0f500c60401c2240f4240000c1031801d840400c0c2011040d80303422a65003100c908586a2443c0412641c1c14024581c04001441031010124024070100040344d41e41d40406071080c0c00400b041c4001c0c014150f9581d526000007249100161400752a071130b03d07040201c001e501d02c1c4510312459141c080003056036032103842428810707500084c4a403a0030044401d41c10017407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269811672 1250 269810422 269810473
    0x7031101210504050a1e02011e0516050106051017010f0305120a1b08090909030a021e0f030a1d040b011704030c1b030506090304060f050f0706110c061305 68
    0x24011007605e1030000707180d44101c1c01d0a240c2d4a007a040303492503034800580240c1c0d5217580e060794084407562140c000d941c04012120304a4640504400909291408a02500c540e40181c0c1e0300c18200d2806408807a4844c0340c020003010105907650190340ea400a032007001c0c2c854003020b001500b240a80201021145004202d2502240780074187e056414000c100300d0321880204869030600062003171010324000d00001e82003401007000c1c51620101040181d030700c3c20404000c0b9184446100c0119222030203100c8420008440703c143d960700e0100d0340c1d0013011100c564403000c6401c074800000d46100e0a0510440032110010b031541c0b07a4400f13030000b0a07111040000d1080b02007100313004440340001c007c440d5103400c10040c05030081d0700c0b60461a04a0901400070314500071070303009000820003140e20100e005100360050070010350723803d50341c0074140c924854110701400803400d10032080e0030503c00000a0800c0c0414000742c42c229120388550800d0a0340400300a4641c4c0c1c800300000c008440064068181c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269812922 1250 269811672 269811683
    0x10b040b04020906041e03020a0308091002010621080c01140601110106031505130f060b040606110d2105091c02010b012106120507030209060a030b0c03060d02040e07031101210504 79
    0x106031f03281e00103a03004501d82c0086a601202241040080c20441002904643c90b40000e124113402c2440c140b4035041d44404034104614841e01440c1800940412240e07030604442c0207002448541881e62014a001da900600054900e401881072403070610982058a5100030010812030301280300c04041c010251801c141c0b1500a2281ca0028411409040145104a60119101070081c081008903082c5034001c2c42400b040e5422808202c001040c060022001c1d8100b10f000704d0305440c8010070740c2181401503503580d450803080c45504800010709500c007211109a2545481c11500c0807400e9030f5a1214923808107458060b900c00035038002c058600144480e50000a03140d40d0b40300005252845080159002c0e0003a240a20031b601305909200d81c07000701901d155540610303554542c0e1505100a204848400d008070204280c0d642d80106226429001401400385483c5030005c0d40e01c4024134807044402d041c074252609120350181c0c420100b40140311903030310000d45042c2c00d6800907100061040300c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269814172 1250 269812922 269812979
    0x7030203040305160f03270b03101205060105030d030209091816171501030312020a0e060c16090e0d030509072610020f0a0c02011103030108010b040b0402090604 71
    0x302d004d1141440c295450003440040b10b01c01190070083c3c41200000150032012200350310880518280b00026803c80d400900904d40d203a4640741d881e004500d1640098042c0c8101c59840400d0100000340c207070603510202c054407041250a6000c2d422440f80c504540c2c2c00201e02c00010b0600c100c06232580c40e40000b1941075030018200000c03070500a0340c90703411441045c44c000c0356040480034100312800c003824414204000c0c0754110340b40645413407100000701c1103064001424504141c89008198070100001d44410340f518503540010b0307244c54400702c251071150085903000841c2c03541c0380a040e0300b50400704050100903019000482c00307464020b0180240e8458540d0001c0d030b0136802110a0240c50642c0d1010301002d0008501909242c1d109034440d07d4903005010000c0e0141d0040201e030004151340c03c06000510071440180d9100311254000260740c0004400080e07076060641108202c2c0d00111810020000d00204200c128003030105000d030800c205010500140040300c01c8298030b86001c0100b41c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269815422 1250 269814172 269814187
    0x112140f030a0908010f020a020a170403050304030308040b0615040b0a210b1c0201121a090a060512150109240b120c090d020f040e0307061b11030307030203040305 72
    0x9186070711518202c000200c40500811030204203200344007240804a009518140074480000c1d034801c40f034180505601d91085580307088920800840e0300030356000f810f40b030b02d907680d0f820050203461045900303440030121040050f81a181954104042020440e6032a0415003000c03403040350354010a402405200c43d50540381c4a170b4203441002c28904484100104101500c1e00601030340115070000c0314001b8240c0c0110740010703a0005802c004001260000007040c07401207414044025005400503000106103080c024242c03800e805c60004d5860035101817880a020b01086680c9191808101107940111401400340b03040540040d42101c080300b00084010f2000403c00c00c941c0203551200741520400500c00c50034083d4481c00355441410804410b05014011012888000312070074003d114502e2501e000d8181d65403940000180b12014089079240c606a1810b8001841e0150450f01c40c1c1d0200f400c0c10650303520a203580000d040e070900c003440c15038540030020f50280d0000791044050200c14850072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269816672 1250 269815422 269815453
    0x31317010b1503040201030e06010b091e040f0608010c020f1c0314130606050603010302130509031b07030b090d0f320d050105060a050901180e04050321011214 70
    0x50b100500001c89a0703980341094800036086454107070384403001d60026001001855503520036902420020794250320f2846120000001c00107024440c00c1c1d01900c1c01c5c9035140580340b00d6104100ba034000000810040c0b0008401341d82c0c651f90400b0a146e2548800303c00a0038001c0c1c803210041e00d2019044c00b06150590549201c8244021601c4191028200e174140c0e05000d124040e81001b040c080e524507185504603000700b8104850712000d40e0714192104007140c503000003041103403031441d5025030b2400c44100800a0039194601c620007503035110040e8005c1400d000e13000c039406458180c1a1503202444a0307464040e9400e5000c5d054000c060b104644074503128160011420142a0440c441e25645118945c41901100c0040e0400c130300840060004031800c9810408841000c2001d0801c3d0101c06a520102c0000d00f040d50010820b0627901414081004000009050008040030f401100140c076104980d840700340901c2049401410f0040350f86c04a986450f20303c84403021002610520500351503071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269817922 1250 269816672 269816689
    0x612080c060703060f0b0711041b270e0a0612031e0c0201140d1b050901120e060103060504020f030d0914060408030d020c0f070605031008031317010b 66
    0x1510841000200d4091034842841501e0b8410102d0030704100c2c02d0b00300401d100000f0300c50302038040e0007100000e00e1f00038050581c80c4d1204400c002442409032a03903013010314030803c00c9028114080b40030500c9107001c903650803000c0d10030311032408503104030f0a240c000c080740101c6002c0e0940540c6692040e000c141107144088150500d8002c2d281e2a00b80951840402d4000f050141c0d00020007500300d03103100044c0c3e446215010180c05111005481b080d402c11180020204a80001d011a58200140d146940c0003406440c5141017600d400100895030b000f010181e0781c41c0805018117422100040c00011002d41c0015045400600703892400c1049a010170300d444103801c81013000c00c092100401c0000200b08202c0079009007641c03041d04107403030004515503070700500c03034892403550300401d80e900980c1c401c002400340c107080c0501b217450b56651100064120343c4150364117142058684804241403074008211411071100c500840401803901e1410200b513004840c4004682d500c4000a54080c0e03a507444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269819172 1250 269817922 269817959
    0x1081009021318020a090b0315060f0a2411101815200a05030406050402030f060403050a030f0b010e0d030909020a030e0c0111150403180608040213110906090406 71
    0x6201c083c0d60b14010011014156030181c48000c0c2000201001a140864100101d08040d42104000d45071007002501a143c8649001e030050a495800610801d414080205251b00400c1d05040740e2020281191552030f65500b501c0164480b40341520a4425030f800b05030b8008603080c0c15618140c240d62001e21000d59143d4408400307031541c50780213501042c4c08120030740300701c0c0c01d011a140140c0440058018040200f000c1c0c07070301d555200040c3c15910188000502034400c03505480c10791a251901400c50703002400140c0001e480c00b000c4c50003c40452103810031110b016190002082c501d1340c204002c40390403000c02c80811a00b41c500190364180c1c0d00250200039040d803804529a040040e0180ca0036002c403208a0401001d031900a03500300c03000c2007102c50020040403a4080d40d844d810140c401c1c282c101fa984a83c5100c0c0340b80005c6a039031120016014510840d070303600c505004403c41405888007810400780343e10301005210041d15150000301303001d070409840400c14956902c0341c190400c0d41d0f540c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 269820422 1250 269819172 269819201
    0xc080d060324050709120203010f020304080c0d0f05040308090f040608010606030b2403090a0b010e010e07020a050d050a0c14030403020a08150c0a0c0501110c0114010810090213 78
    0x104001a0100c01c0c00c029942d08114050030069494131640c01400341c055449120210250340301050107544080d040481e010988402c25940c81c2030a00d021001c40d84101501d40084c0954100c3c9190140704084007074502d81141d8410341003a08507140e000980c0e0240e000180c1c881002c042e095141e4566015600050505d4000001c00c40d10f0020302400307840c41051541e118a154001c01202908040b800303101382151724a10341c0e226a600b02d0114130b4505001c0c005002c64044900014031140c0220707465041c0c0710070289020494036000380c1aa07907092140c00042007900420005120301c2e1007000070300f03e00701b0149414401c421301034650481c0c0714032241421a41e50070000d410f00c203504182c000d242c01040800020007840040300100700d40b07071101800f0790383c2800c00012a09411403150944421907034110000b0052500b907861826001e0384040c070003071119401d10f80003460414104040d10304072100c100107041e41211000d4640010200080100e91200c5003048a901c02d000c40e1080400c061480c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 269821672 1250 269820422 269820443
    0x102011401081e0102090a0311061608031005060a020d08060f09010305030c06070f0503060f27010614090d140703051009150e0c01120605060d0207150903050a0c080d0603 75
    0xc4460b400a0740d030220b05100c83e0fa004000c49038954031400f01050450b178100020030008044140001c44c54410000940c90312002007280005005007000254041d070300401444c1d140b15598800e0103550b009a00240000d81c100458140708a40a40c8040d91b00a1004114031800c04501000032441131013a042528603a2020460642c181c13000c20000d504090b40341131074a80f804d1782a000821510009240f1800342d019004996001d8a840d89000c44081102a120840e6142080403103a00c0c00240301e07250002e01d040448010844a2004a0340380d81c40c080c25040320000706450b1a9032103808180d094110784038240340000402c000744840324501482e078070041071004080c103080c8040c6007081d8071803140a15001c0b442480d02c5001405030220482070811548000c2480280e000802e02c5920454020f41d00007140c041403130440c1d00a108651003210240c0400002802050803515810b03c01000304104000d002d1079180a0042415024402c80d130740da280807960030303520094a40c10742c070440b2030b030411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 269822922 1250 269821672 269821693
    0x1e06041d0f010e010b011b061802061c110906041205030c0303091605030d120e0c0a1512053102030d1e1404090903230304050f0a0308060609010201140108 68
    0xa004d01c17546038809117410411a622500b03011620320411303000030711302c079540c0307a4081060b0840000c102e00103400802c0742d0b455030901c0d154005100081c0c0310b0803400e203107801400160813140d030090396092040a001d55082500700031074454008020380007601c581c80140311f054840801000250321030445003001c1d00c03030465039181105902c8030b41c1c0c006600c2608803000f245084d81d846609404e00004c5400e01052480c1d201980601f400c040181c03560b041800c3c40c1003c1903180e4101348000030b61181d41d6030a507154a00640d1241210011f0321041e49462040031a01850200110000f615456420144c5895900707580004c3c030340108600d0020100b030500300700154841280761100c01d16042410b0210050064508105051240e4054030080681da2842c0005043c400c030075058035904084a0321240f0050045c0c2d0318aa600202c400700d4052080369811121001d0200310b0381003140e07041d10741c642a41c031b8040c1005003c0d00500ca810781199a10f10b204110304074440031403030080c010100506848440d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 269824172 1250 269822922 269822951
    0x1021b0a150c0509091e0901050916050f060a1202040608070806030c01080f10031a0a1508030307210c080a05010501111903022a091e06041d0f01 64
    0x14410600c96024580107964942e10740000c12181200c80c00c542480041c0d540d050954641105031643d1003c580c1503030204142e401c4154003160080c14000122140032041e0132111000403158001c4682110804100d20490700b0508050100c00540d801c10074038401d40510200200c2c4c0141e030080c0c0000d44170038180941c003038105481c1a040322045d000303003201c0f095000010385881005401c111100402d000059240c41c0c80c204114044d641c003456448541c1084406400c00d05025a001144540b4041c0101c01141201591800700e900b100040c60440c0d0343d545040d11075140d0861455807050300c1019000304050180b16244140c00d00c0e032242505400c1200e417003011100160442c074180a07015480380402c1000103030154950b1f84042481050003114942241440c5c0351124810015001c918141c1100260780001c900b0b031802903030005126071b20340e5010900010700709011141000f051002c900d00d402d254000c8c1070500309603a6170100880d040700300d6914004140c0701c04082ca0350b48141c80c250100c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 269825422 1250 269824172 269824193
    0x18031f1a0a080c010e0f0301090f02150a1b03051903020304030e10020c04090f0b0115080a1b11010605060f0d0e07030506060603070311070309060f1d011101021b0a 72
    0x82503400744031442c1015101566a00105800740c180700c5d07403410342c1d211581c4d203582030310f00f500d0080d0003480200034502d02000c2c4081c134160106e01c900b0802800c0702c5649050019201d054401d55184590010301141448903500600829410814104100c00b414a248064410001204c0d81c0050f524034040c100144892226811188142d010302c1c0103600032940081e0542e00c4000440e400101d000c014900405d00c1c03503034207100500440c2c001c03000003402101d0305400c0e045000b050311344034295614250910210b56242c24002d54a441e088000c111040c0f007a9501020041414000541507840d1400a01c40f13400c20758031800665800540465101c0c0c290003803800816400c0014117026080d45e03101501c401c802860540035410100001d82c85e14841e40020400000280300b1658445060800800c4074040f8010140802d000c0d0070301010719441000c141005090300000b21921811003c011903071000b48aa280ca1199000c0c806542c01911029010b04902c0e0f6100040214110710314055400a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 269826672 1250 269825422 269825471
    0x3080c070c0e010512070e0a1d060915090309010c030e011106090f012007060b131112150a0e071106090a05010e0a0b010e0c0706090303050402030f07030818031f 71
    0x80e04881313000c0018040115243c1c8d0040d0126501184e03401440c0816414040404428100b5110320000e0007045403002c907120030041c650f030420404c5652000c0030340ea0f881c401c07510014001001045110082403258202c0340044105140c0310b0b801c10490300d07900f8a040740580d03500245401c015454480d0711000d100704513031078601c86401c10340c8a0246190310340d503003d101c00207000c058071410755800c40d0303843c86540b0940060000f03081020980d00584650f0580100c43d00f40b84500001010441c01c11240005141c00c1000030910303880c0f0b6041c00d84440280001408003000e104a82c400112064002d02a907482240b0407001440d0f10b5003039060407030960300d0400d0b1107081600051010781c0490780c2070614506441c100308034034020340c956042680043c8a085e002030f00310f0f031070701882a0400d0fa040d0032890041307008030111842c881440b00441e444141a110041c15024100100b54640c50403450b14601d00500609031080180b01c1c003034030821071801d00d44490141d907540719660303150b46106c201107048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 269827922 1250 269826672 269826709
    0x30608101a0409020a0b070326130201111e0303090709020415050a1e030e0c040c05090405180303010f030512040303121802120c0103050a051303080c070c0e0105 71
    0x2944001c0c5004007401c0050010a00a42d1100c910078150345551003030a0007040314a02c450382da400c81d410003c1c0340248034072600f070030340d851011000a00740d28000030a0007036490034441180d89480d41d0064070f0075000c1c241030424a001d030103600daa036042403101840001c824440603541d00d01d4941302850510600d03400c0b282d04640305120912041d21310044104084034107040240e07403180c02450641350440b00074182d8a00c803001c807410098660b81600003509003082c00e03088500c002e41c0c001c1080291003072498010b00284043c00089c03000d190a401840e000048030800c070503c00c206103000c03070135644240c20080304180040010010030500b013100b45540003985142506060459a00610020440c08403400490310b8400c424070011004c0311074a4000d600616801d2103c10312450720f5100d1524054107400b1901c0e000010354220413a0281511640f2402c00490b521406554160b692041c0600011110300b0280510000155051001000f0b0160196800c074190301d400b04100c807455540c03e00300c12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 269829172 1250 269827922 269827931
    0x2030606030325060e060a020702040c020d080a0207060b0315040212070f0b1c0c0909060603090812130f06050105040c0c03020d05030a0b1801090c090803040b0a1e03060810 76
    0x30f012070480000c40b070043c502600e00d42d010054144000036054106016090f40206030500010007107660080003170510942c0e0510805294040c2030741c555142c2040000421110000501c1100b0954010b05925104040020b1b220703440c030022924100044207602c048417041d03810b0005529212400c82c0038a105c150007040e101c1d041c11401d2134003110a03c030b8016051004102440501d8000c1004e032000001681300700400400310200034044503082c07081c1d0003818039100c404540640701e4003035a00c034141c00081861605107190f17910701340341c1c80081a17400070701a10159240054401c00d0603400117030065401040c154144802c10044440035080c140070b104281c828800042c2c4c000c942c0000b100d00c6414019143c1da103150882001d000d680701100c1c0e0003d9214101c440c040d944041c214142c0b10071440401492400c01c2003956207040034026105680d00c11f0100304149101c01d8001d144400891511040040c0d81c00c0d501c1c1203081900715444048be85803e0140704c00001001751180389200000180b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 269830422 1250 269829172 269829187
    0x5040b0c0a091706100b07150f020c06040b060a150e0d060b1c05060f060913060b0d080d060506040302060f071a0109020a0206160f0e030c09070807080a090305040506180a12020306060303 82
    0x8e900f4484020920056241d07001c003101010740c5c1d07045c3d80014403802d054a040f880d0078540740540c198200e0700c0b14820000d0680124514104075074511a405840d2101c81c561114241040000c14440e201103941a8031208921126160403145100c03141c0e00700e142452800c5949400c6003407400080c5082c4800d00b2071410011552348940714650440111090070452070002d007440300144c41021019500014001100e008010156008110503103c0e4441007041da9228000c00c4424880c03848042d5101c141800308120040e07401c80209000d9114001e031103000c006140c141c118249003607000d283d90580c0402e00100154061122030341c0409404005403007000b0103040a4080b0010080c0d110130004200b60100356602e040103031000440c1c00a009400c1450205c00041254500b15500740c00259503e011031400100c1d40200000346900d0344450f800c003410602800a19048001c140705902405080d06400707031900303c8100060004128011450b11305c034014140341c4000909414002d9100b0043c50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 269831672 1250 269830422 269830433
    0x60e03040f0b0a0801030204021c1a0f1008010509151903110901030321020c0f07080d0207050a180f060303050a020c09011d1b04090501061205040b0c0a091706100b07 73
    0x19042d00c0c7d04640050701d40c46244000c4248055003120804100c0ca46142000c01c4000d2480b0700c002d040f81120311169506810061000717040f080780444003c18140b034018401480d10704280d6074019841410064040c00e600f002030001203ca5144d4085502d02c00c000384144400c080a291a0000583d55600c5039455076030300501002108000400404616002e2b0b68441c0340d0360125400b110a400854544c2010b0300c5001e070300c030701962041c40c80c2889070181000d040350001c2031400465100901c441030b010300d000000c410360075070380104d0707070b02903039078000250307000085d803082001070340c042d59802c0d4949081c900007030318018402d40f0044c41488404010002d6450444040645580241460300c070390301d990340c42c49a020040354650b81e02c0440454007050700451540b125040382c000b80d844c040d910031085401c50451341c0699020b8800300490000407080c207440001403a601c60a45004040280e40c0d00d000c1e9184030200a014110303400c0300d402d100b500284141800058080c0c1d4000c00e103010101d0717451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 269832922 1250 269831672 269831687
    0xe0405010b090a1a070507090203060f030a080d0903091e0801060819110621090c060a27080a06021201051923090106020604021008070c020111030403060e03040f0b0a 73
    0x4131060312840600c0118544059415541010f510804440d030042d01c408110b0081c4d0000c4418600030000c201200030240380c0000d00042854020004ca0324042040208402400c9012001d80a004440e50b000600704007040e00c455031060900e00003181541407030002801d44031280c0c00005a030340041106507902c013003401c05071f4000350700101408090f00801c01241c034602400c11b841003e140708170002c02c800c80081c28100e11501041003039031410b1140000300302e0540682203203000001c403404030496800729003049681d0f48404200140a20581c1c40001c14980103c401003221800e40104080c8e1480074031a1499024000c110b8400341c50075620390304200341c071041d4801d48140f400690b001c0c5036400700100915804039005081c2d0394056840350000f0390350b0041514100c0c00354446070155044140301b065a28012910f59584c07505440c2107400454880149104610440c0000c00001001500d24032411880c108004003841c1c4492400890881003a4568058000da00b010441d510340725921000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 269834172 1250 269832922 269832929
    0xa0b180c0a0c1103062818080901090e130b0603030405012709061d0708101205011b0c12050301350105190e070b070609210e0405010b090a 61
    0x1d140c01c031030340c641c1020740d4025000c0e114144c050103107809000590005170460750b0b007a648001c8140c010807211000c001120014200c0036a0410019a00400a0782000040400100524100340d0f41c54981d00c582c1614841952401040a0100701351000c000c140c0d090290f02100403000740d400c00c0c1c50240003a09505820300008185016407902002101d0072480a030b0107080c01d039a0400005448101603041602001981c0da8010b150400140c1800e2040c03004901c15039505100b4404949040401c0301c00c0100f110b8200d500c1d540301c860380031a015a6100458050446a0314500c0700d41150408804016100c1002c10030400d0400c0180038a15920320080b02c0c0060031211109035030013052090340054201c080c4002154200403c1c021403003008070000c209011411070400041d480c40e104195610303072612451a550740140000300200d4950f0b400110316501440100c01c0f98512003240ea110702c80c41400d050040713400c0c0a54920142001d00c540c901400a0f80e00c0c2038a0000309400007200c0e04440e10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 269835422 1250 269834172 269834177
    0x13031101021f020c10061d1b0304060c030b0d020109030821100f060f1b02010c050312090c0105070203120703030213240827070f0b0d0e03131202060405090a0b180c0a 73
    0x5002c96001c142544000100303c0c01e0701c8c2d00c01d48909142c80c00d4009040d00b1259500044c1c1000790841e25890031201c2804a568140c4400c8685480e41d0fa0310881c0350408040305c50071106030111070f001c403002040c10034410a40c0640040082d824403440d04d00200c126000603041141c1140030340c00040d000044800c4c80045042c85e41d114044038070040707070034010b100002401c50001040c1d094004000c4018a809010344030305450b40382104c600111000d000e003c001035810350000d85410545506000240100350103403401628050810324203c0000031294419041c0301c0714052401d040000e4046c2011000d0720a280603072503800c0c0812403440028800d40e8407910a0400501011610001c00c03241e002400800e03403032140d942d6160745041e0603410902c0d0905100341021400d0300007003404130131103124822004001098905002800044091a01c001c0743c0043d402c110224582e43d64140c1213100e10f54a0101065005004083c86460452081c0c41c0252000000c18050402918003d56101584a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 269836672 1250 269835422 269835479
    0x507210504060204030210020a02041d120306031014090c0402160b1e012c0103051c03090b01030b07030e06010302011d040207060c0f080c13031101021f020c1006 71
    0x42c14040000d12460348000c2d80069038403030307000e20660080b4015500c0383c0201d800300920741d82d44980c0100d10111407019403c682100b8034a2800c140600091900b1440150803940d81d000f0018284c011a00d00384084028200d644040240401e001c10030421100c4091701c0950820070081d049013081000410020881c1c000300000810003e0748000e0021035a800000c490550359580074420000000306205400f407804074102040a05014402c1c54101c907170000c024405a07084070200d800c1801c070040100c1c1010b0300c9008003000300e1720401174107010b140100340c441c5072800e040310050b0031a00500308522581d0808001000944e8020900003280c14851b00e18036032502c42a400680240300b40d070001080c440c50070358000001544082044003000c0644c17281030300f03a1540c1c0d05001301401099100f1400c0307505040c040c800a000142002000d0506004030b46040802c41624091200c4002c14901e1940e804240000c01e03101c10015842c0f9010030321010002c150401761001c0e2040d443c990442c0b40c18510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 269837922 1250 269836672 269836681
    0x2120915120411150705070603090302210318150406020d0207080310140915060d0609051311010f05030103020d02150705031c1b120e03040b090405072105 68
    0x2950101c500080c0e41004108a80c5064500450b0401c10b825565000700d80700c032440c0700801000d10483e08102d03040f6008004292070f100c822030241150510440c1103010322005c02c41e00354044c40c441d01c40d2001e05e9020355100d182040a805070040402c8000b10b1942c0550800c44041c6007000030300313401c640c004d0f1002d070380c0d401d440f541c4101920400b24010711055001003005451130a0007a0079003a50045400358201b0f00b0010b04001016038103179201c00f000503901c01041002d00d80b100003030003211405e0b80c000c00d20b01c0e912065042191000c1390040303020001c3c026141c003000001004151240d02c2420800500590b0100007482400140070007030050142031540411765840603900445542804040c1307640741404c0c60704503184e0700440070001040d5110003490060003903e00075844910f1f03a4400d8040010a4040c0c200d4030103035200c000105665a80b5802c3c005a081840100054010306800c6030781c6403400800e00c02101c00c000e10117000c1002c9032030550031031280554403e100c202807802c0410b4a071074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 269839172 1250 269837922 269837959
    0x30b0417040f0308071205040305060f1902120f0105012105090102040e041b12320f0705090a11030144060a0905060c0703030b03061312021209 63
    0x302e40011a02000c51003000040141d5003000744502d13886840c064061040b130803410f44250041d0b010003409038001c0c400080d210f00304036070f10643c007410526168106c0c1a4a1021a04907407150005104145480080080c00b50701002d42600600c003c1c0303401c032281400d80f034082007102c186500100c1082d4403080030800c9041c094054401500c2c40c0300404101d07040625202c01d803114818100d50302c0c407600d0700300000c5118400c08840005908050050160110700000381501c1200c850240064030749440c1d119140b50080009081c2c0f10200d100601d84c25050500b00000c0a0004042454150921050340328964100d13050f2811940300c0011000300c020503400c10220603448442101110910b41c2030b4110529080b6240d10500203600c05947e22921040294029a240c245010f849548010041607041d02c07100b000f06a80b90091500103008550107000078140754081c0c0c0c6442110480079152800c2c8150004000c4004106000030260340c04501e007020700134081c1c9200644100c0c0e007000904610310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 269840422 1250 269839172 269839177
    0x41e12030b0f1509150c0304060c02180403210203161404030501020d0603060b10091a09062106011805090c120a0c0e040b0906040506030703050a0506060405060a030b0417 75
    0x91005106508080f01d8150480e21a00304100c0c8520415480d14000c280314820b030202c8011540c044c02071032800f41050404e40b08059520002c0b40c1180d02c182c0110920484030440d40d00940c030a64a070ba000b20510031040d10460a410240c180d600c0c410030600c0752519800007180143c4d20390341810f03405040816554080390040340e2024000c2e5000203034041e0035064941c042d805407803142c0700400c00c1001d060140681401648454400710b1100a81072101c2e000c18083c044006000c44146442c2012000c0414915008119402c03400548090b01a0036021902c1005038400000e18001c9400b00a42000c210401118421103004840301030100301c90000510843e5684100304c0b00d452102c1c1021004100188103102d0880c0000e045d41c504102249814001ea59140200600303180060302c9050800c00105005080c00e40e061280d0440000000d030107019540140780618003600c0e0604d407400a000135231b08000c0989104c0c0305085400e10000c0c4800a803940c1143e0011485080b60300c62490a0b141031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 269841672 1250 269840422 269840449
    0x70c020901060e1008012d0b0414130903050f0c0109140a020405070f020a060b0402121927080705070e0c1819030b07030902090f041e12030b 62
    0x580a000030402d41e40002c0440030420003520110010b80d202c90085403800c4080c052081072130021600c1c0c00804110203111050389030744445200784240c0e14101107800e0303072103544220344d21107542010800c2413408040b0780343c0441e0900e00c28401620565001041c81c0b05441c4039078039500d00412a021108402d601c12004030742c0c055500e030600070859510300e0362510400d504900c1070307007003c0010b800301d4420482116455966001000c40c0c041c9a500c04c80688030150455800a5092120b035031180c1d040e0002c50f000f500b103401421003a001c180000c0043c0e503003803450100f130340080304c60341400b0003500f4850443c02074100c03241985400c21881c4c00b60904c40903078414401c0d02e04c07040034031100f004c3d054003d182e100392003d80c0c40c224006103003d03c003c16500c0d0318500310840c10110108040303400041c0c1039038800054500052422141d60002d0b402c130000b620000958038400c02040100810746c2a181405080741010b52a44001995072644600b04901e44030101911031320219101d0310340705809800d070b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 269842922 1250 269841672 269841679
    0xb240403022d010207030b0621010c030b010f05070519110a0314070503010b10140f04080d0e0118031209080f0102090910150813020303070b0603010606140909070c02 73
    0x6160448050b11500380000310041590001d6480700302e40c00010310f50100ca03807085841e200780d92100b003041081600b21603c00300d00c8014007011036418100381324400c03451146031400074032403110307000040c00001001101400e0100400c044000700d080056803038035412a29110380d69400392490030b410400b0012910b1501b08402c8503001c0108240410b008510390882411207615039039030010142642c0c038040c40d075034000c25203095112485c3c3c0700305c201188418100d04554a8640c8000500841d940305900c50380c015001289111030250380020200b00361031007460f02c41520a04000c10340d042064034440240b50095010110b00054082d0641c02c0081040105036219000c1207200d040c041e5105200003481104520700060719004040b646005407500c0d607a66040310f14207944c00340c84440f80034052042030307940c01e0742800040ea020801424400d104d245d0500c0182815000d060940350180c200c24107000785059100480c0510700203031200004112400304850b00d6005003507a03501d2007044040d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 269844172 1250 269842922 269842939
    0x9270c0201050f090c06040b0a03021201060905090f0903031f0f1e05060a020318010c020a03060903030f0204050d0f021c0f05061e07030b01171503060603010b24040302 74
    0x20054042d8405889100c3c24840708500c0e9452154031500c03060409170b81ca92001d820704c018032401070303c070003e002015814100140340800012390411404c009038005070014042103000d0181d03041140b805c54101090650502160038010030203512400010701c4007100e600d449c2c80c1c40c1103c0c800004407a00418100c00119046511083c0c10944a882c41549404658184000181a0a2036000c07602ca8030ba5907400f96040008901d29031501c2c14030000301604001d00884008090307500c05140c0002103110f0310b00045d466046260203400e0724180c00940c2c034003500c140f101304080c2e2a042081402954829202d0154810f180700041c0f110040d580a80c001c403034040041410400110f100c1f405480c001c6081395015603d03402070201103e81d510440c604d402407403001ca581180a60091200001c05042010b00140c0e607901220000c0350031207040c4458007107000120140c2c10f0034805a50000015070003440340000c44404205500101a42c25011400107404500c00c232911100380c5000c1c650061203140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 269845422 1250 269844172 269844191
    0x90b01060f090b040b030619050a170c0306010311150d1125020117070302072109080a020d1103030c01061202040609050f0a0f090c080615010f0927 65
    0x384007509036980c10300441c4141002140380304a0708103131421103210700816482c540d1510140f100c1c080103000b00c80306000300000013080642d22805000040c0144141403414020040f0f03081e0b10346010401098000d82041e00140045140c69000070b00451040d60285800442040c04079400e00c82c8418050017185481149841c0d04049402002021050241d64001c1c4050040020201985900090100340c10303010803000c041b000c002141c0e0110150030010b0400640f902e6008203402820b4440004803d10108514031030f4210038a00c1c0640b40940c0141080b44040c1e0104411b0f41d0348050281001281c001c41048580d800c1040f5066001444001c0c03142c2c0c0e0b42d034008105c8804254604921503420500081081c114a02ca4244204c80b40450030381980c94141c1443e005040b1802c944203195256481d2101041111211b0340041078a100104220700d0103900c08041e18240a00d050b041040c40e51040101a034040d078144c0588000c00900c002c90b000352a9010300b4400d034440031081480c249681c19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 269846672 1250 269845422 269845427
    0x40302060a020a020c1906030509070609141203072607110d0519050604110409050c0f0f060c070504060602191212050412020c0f0105120a14040b0405010f09021e0103090b0106 77
    0x6d404a403211b880c01d1100340c903400c0b031b150b48600041c02140300094880c1d200308030400302c06002280802004c4c0031a0096a4200b20b000e007180e000a02c00e6460410002c1e034681c0c1c82c07001d510b103200d00d96076402880d401c0448070707070340c10000c01d0840710703818480c000c0510710b2410b0040c1403000f01821040a4082e0000341c03014074100342c07105002c442c2610000b145403a0380b03074141002d002d62342419511078082e00c10410310030104820709200b14806500700704d2100102c55181c0710807000741314070244000204111440d01c000c11050303034100e0700034004640283d07200c1151a0b40c901c0c000c1c0d6006610200d001c1c210312420314103d40300d0a00801d00038160303007843d045c4014021440703100c2e12000055030984628075421424800d454840305003c41c0001c5003081a048480414500c0765004883e040011443c4520510240d03d10034041e202500c030300d055201400b081100912a02c0034514078280144444503907900095200b808441d00c1c0070001c59404005555030b031103903000141d6250b0000c644ae00550315040d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 269847922 1250 269846672 269846719
    0x50106020a03020f0714010c031101021309230c03070c0501050c04061d21120d14150a14040f051005120127080c030c0c010e09040302060a020a020c 65
    0xa4001d4092441001d080c85130100f42c000c1074900c07a8041c0d4514141c1d4800440f00d10301c00701d400350100f221006490400030006e000411a0442340c260a1260754200000c0c1004c80b10341c28403608030512007451070421040b40030002c03a8413240c10880c031522640c07200000d1b900205103030b000a15651a02c0c00b08940f1240050191060b5142681c40e245c440001109490f01c1d240781003911030748041d03030b18000b50141195410309094203d11106a40510310950306400240c1c01002031039071751a48500c80720007100300098515602150500400e0240b1044601141c0200054001d00314071000602001d813403900c840d000100320707a14040b8204024034041d41190318000c95800340c0b81c81040c000886248090050042e040c00c03100000d40c3e26444411040d1008041c030312008102c4a4a90501140b044020f090000d05108030002020700300c080002c0000501e4080c00407120782c40b8140000900010a5001444581c000d000140060f59007135048800e80c07412071060105644024103460030840700c50300151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 269849172 1250 269847922 269847943
    0x111608040f05090603060a0b041e05071e0507021003060320040e0c09010e04020d0b0a050619061707050d1e0c05160305030705120c091014070303020f0c0105010602 72
    0x2403074101d5456100f04103541d00301344c41c610740c9680240d010485070015075101c04981c0d04000c2002403e404149824507030f001ca6021a40043e41d038030400c11007540d07000f5a02c4140c00b4080310904407841c40890b409400343c014184042e0055980c0a080d05505009510034800307150443d002403615560703500281444d4800b041018000d6040c4480d212030040001003560109e0710040005085a08044400c40480f13401001a680502107030203600205540341c4480380500d00c0030f4408201850420180600007001d0003000302d250100680030011f0a50004440495018840b468811900c4462040b2500c2c080c0c100b16030115483c04e8800300c13111500350403190b409040300d40140880c2e0b01021003a10039000d00f0407000c41d4030b51040d8240000070f2041c0b000703692101c901c0c203009060044040250414220803140d001180200145141c1c041c03030603041903120540e0620303011036680d000b000c1089943c010008000c00b4190045501140300505e0400e85202c0802d05008000640c1d540c4002503450b400d408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 269850422 1250 269849172 269849189
    0xd0504320106050a050112020d0f090c0807050d0305040b0a0e1504050a0f0f0e04080c0105100302120a0c090f1407050912070b0421050a080c0706020c031011160804 72
    0x80c0009182c01d04c88500d904480050310f455160351f580c00030074806940000e0310580d02d151340e64910800440244680c1d0071550281c0075981030142003000707407071401846820103446031150070710708400254820203d41c20b841c0c0d000300c016159800b8100940d40c64101514482c0d0004100544600c1d00003090068401c4803800c41ea401001c55680c02c1000304621300d401421080c0b074225409114480198004540040c801c0340214034000310400c11508483c0d0a42c0d400c402e601c1181010010740c5826551405007007600005070a8203150b40d503075a111102d0350311500c04440d8565048400b0003d059006181c103400d50f40c040505131400ca6001010307640010700300752240207a00361000c04081e0004007070064403108401246000c0c200748040505c3e10b141000340051102c86c2541d6000120140044100b16109042c81900c541e50081d40c41d0405005400000455010f0114564160f5000074a400030300e100e048005204406400705074450b1041e50424440c000b0101380c92420000030034001c0080782c0080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 269851672 1250 269850422 269850431
    0x501020a030b01080411040c121103010306060806240a05040906050f0c0f030105090402060409020a0f080901181202011508070501090902120403030e030c0d1d010f050d05043201 78
    0x4900541d0b04e0201524050014130800c5807030750b01400c1c650b2081a00e40c42c0b5003400303941a400d154020003950345115101c10844c0010004004006a40c0105800f4010b100080c1c0800d00e450904070b500e090740da84200e94010088281d0720344c83d44070035103507401601d80500140141181420900003510050f107103081580042000104d2407060712090707901102e40207461500d564a0401001140d40740030b04281ea01c02e03010040011140068402000940e415840f8112680e06120000c0c1000300000d280000d2a4180020084d83c5c41250710f00c0d490099200880c0d100e041e03e0404201e0060120847c041944008400d0214822a001031110f0465201366200415107407512040b60590191012000c54001c41c0380200c1c0c0000d0181d0010f08962010501300c81c101303a0034140007407800011003201d40c08181101c40440c48903840c0b00020604440a003803000100e004601b0041c4140b1a1084100d1400d40d00c4020400700140d494203c500e5489403000030503900c4126541291540030f410150b040740d0300c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 269852922 1250 269851672 269851691
    0x1f020102070b060f0919060f08010f0518030703030504060f020406180821090d080f090f04020f07120909050414010c020c0a051c020d1a07090305060726040501020a03 73
    0x10095201134084c1c06240e464880d80c5010070300403060480f00010a403100c03804074014444441784001440713039a0002c1200c032038455a03007048a802071b260b4400b8142032840c565a000c0e00000702c5030f14590500d0001a1640d8a00b440320041850034254011207000060005425500c04031001c00d00240e4410301855070740d01c01080d80c0d01e60150f03059001001c0901c5a00a00b078a280c03025010102000d070803100e040b0307965520301489078070a000110a401e008144000766040c400f51981605c607060f038045191480d2240c000203203002d1107c0080c01042202c0d183c85005110340b1121300100b031400005c2c0554280340c0f07004030104002c9000542c00d90320740028156440c1c400141c1c4c0304007200203407081d28450300f080140030803096001c3c450042c1d000800f0403400141c58a02000500c58010075501400d8620001545401580a00908100a803194041c00490000708034940c1140450070141044070a2002882200d01d445800780481e005800030402800019001000c500e005070741c1c20040e5901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 269854172 1250 269852922 269852929
    0xc090a0902130303030b0f0909060709080703051203070c06021204020f031c1107030c090515010203071104022802010e1606020c04020309070509090d020c01030c05181f020102070b06 80
    0x200c2d0082840442c816a00304042402940107017000c0304080c110303078082c0302d4440110782c9981045c3d64000320b0343e0003081040060780d404001400606001000342203480e01d140c4907143c1d15040c0000001d030b55500000444d0300c1c10702480a01244e03507070021042d5100c6040030952050100202c405074094031410301802d6892070046a050b07420b00e19145022003038800e0f00c004a5080300f404020701414800d00d5004030125a00e203007550000c08440a01107841e10f881809111005855007030b4a041d58014820000014881c00382c0c0c030b0308080c040d200180c480d0310851603112030440e05000700e40301c2495205951540b96040d0000350709040c2e488103c51001d20799100311201c0500070301c94900107801115a04030036150540085030050303640c2c0d00f06d40402d03886d0000144194000c0c0c421f0343c880e900802c200244250103100200302c40c1800d003020017408400c02c401800c03038401e00481030004490941d408181d80d0b80c18000d0001d800900d2542c5a04888040003c3e0003076000c420243c2d0210300c4040003843d54039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 269855422 1250 269854172 269854177
    0x10e040209130c030b030a050105100506030103030801150504030602030106020312011703120c04080d08010810140103020420031302040605090c121e040609060b0301093302030c090a0902 82
    0x300500349000e422642d0340010020659003126004042c1c54804131007050360f042040c0603941d401a00002800d042003800e4000400007544814040c12080c8010400310350003a081e5030444bc5034031550300c200380c0392201c02c07142e070701c60303a00300070040341c404400850303010350005c082d20203146408005801e030307600c500c8044952140780070303c5d48582c0d104002c40101c1e12542e01c982c1c0c1e0000d0580309003a060a4490301c0d200c0c10280c94000d000c0020300c042d4010000200c0404c1380c81c002d40c50040f0308010003d00401c0b4400c02510500000c3d01460b03c50052054100c2d190000004620100360795689034240307204451700b000741c00c00007640714904195000c501da29107050924040c941d1094440e1a0404a0402e807162000003031220000fa10114500c1c8051540913138040c3c891882240d000518808034900f4904641c8200001c40c00f0340c0c5020700010000308070161010032400d04d0003082885c00f00348050356034210840c0011400a84c000300c00c1c0100384000c00054031060070112070181001761502c507050201d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 269856672 1250 269855422 269855437
    0xc0f07030206031906030c120203100522020315010f05040b011701120212062701050405120d0f02270114071e080714010c0e0a0b030a060314030306010e0402 69
    0x1441c00c1000c1840c292614103050b00304018200c4c007042e416904d0300c8031010480564000c042c2c600035521030604504c3c0621614a80c6410040c0810050800182030103001c11198502343c801e80c0b42a1484040d95070412441c00700e106001d1a5404070360312201e40400110329441081c1c02142011400d89203507001d640a580d416400716050041030b0710f8620100f90b601241542031360041c110300710041c00030b4028886039200c0d80105481d01e9900b1140b41011144040841c0501456450300d000c0c0800554007180242c2d40081c10940140c0741c9800d118910004d000984074012124400921102c11041d000e0a04019600a03120318440340c41b07000064504074030411041c50300c030004100c400300003544001d844500d00c00b810400da100c01d11507910341c01d03039510041d410340d44019098203464410030b09004030210380c00f591030070310b001004010218a60302035601030000c150b58048009003290b00140d2010000310780000f9184d0600400d10402522a84140c0f142800100c50450309803060070940201c0c0c00c407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 269857922 1250 269856672 269856679
    0x102120703080c030a09020a0308130f03030e150c1b0a060512070c0f0807200f0d02041805190b090303130f240f0509010903090e09120f0c0f070302 65
    0x256200083e140c11944000c0c603010000d17540310344c40303800b42e11415540c40282d44034040d01035852280ea444076000400d2540003900842c2d6504042c40000e07842121035040130310583d80300c1a80241e6406840303503401400302d145414031420f0010040321450066260002000796840c8139440e860b08021510b601c1400307403189401d0000000704007002d105d02e40c1040c445024221241414180399144407446d80041c0095941c0f2503084001510f43c203000404248840c4220340d0a0504012a030204d080c443c286080644100d981d840301c11500b000100c501e61010394008250788846241e0000201045500001a02c070400742074002003062000200700d9010b08000c4c440101c01c00419500c0c40b424507100441194000d4000002880c116036440c0030200c01c4114007804201d0f00107461000088907001041c03000c15030b043c90046c3d8007094006180c8001c3c0d8501c403031150101c0d41e411500070b1620040504c0e00e0a040c0000614000c00d5000c0c801910704010b81e48156407146004003143c0d981c1c8d0b0042d0001952 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 269859172 1250 269857922 269857937
    0x306080607020318041a1203070506161209110409020d050304081f050402030c060d0e010c0306080c0603010b0d051003080304080a080c1201141c06020702040501061e0e010512150102120703 83
    0x1d0f9850112094107d0a082c1310850b494506a65a0b2506203a42611802c80489500c42c040c143c45810924445541c00b080004001c001c5032501d43e030201003400312103640941c0e680c13280c0900790b44070b0000300b450454002046a58560f50760303000d143e8585415034101c0294a0020003990b40c070f4442c3c003505000f1703a00100104518181a002c101c000d03401a02100e040581e02c07001c202c40d1613800e01503103c0011380341c2c034000368030f03890700585504080001069900c18502080180f00b100ba103d016580c2c101d0080b02d0029241d40d400c3c50350703200d1320043e8001400c4448040100020442800d0003007112440c1a80c50030090f071148020755906000e0096490166500100144420506a1a40800402c0007020562258140c4656801c90701c0203a0b010b4811a4000030f403101035003440c0c040c85004041c0c51510054000c1006031407440c030140365040c40108012040301c286282c3c410341c240c8030441013520b0340c0101c80c03c04000740f000340300b045101140980180c46000099a4419040c1c80a0a406032280c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 269860422 1250 269859172 269859221
    0x80c190803070215040909051e0d02120d060b040b13050d03022a1c12050f16020310020f0a080f070207050d0507030b04080a120624030608060702031804 67
    0x202c113080105504101c26030a210020700031a82d0b010780b0f20400d00070000340c5200c105812244009000481e60504140d000744400219181e001035050000711500a1164889190070b10120140604d90710a03800c0010104010030782c00040802041d0090b071b41c0b403412203883d60301c6040c414680e011030809005600b02000c0c400c4c0d00d840120340b480c00d05009996207200d68503d280040d21992001e90007074202c07401c211207642005514000d52038000c2c1d031818020306101103004a070050303101c1c0150b040c205c0b5254020748001c5487c100026040880d155030190b4a40c4c92000c0000b115410001c0403000080161020038440c4261032041360141c42e2a901034003106082c601848038008044104540c248618180000490380d241c40460050348261922a9508004075000b0800c484407070800200c035181030742c2004000c015410309030000030111540070112402c043c0990040c2042d60090006014580c02c000c1110350200041c40c41d01040420380d43e9007200c103c00c1c80115491111501c508200c0304a248 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 269861672 1250 269860422 269860429
    0x1b0f03020d090203060a09020f0306330a2315041a09030a1b060923030f0a0303020301090f02120604051b0406170117120f040f080c1908030702 63
    0x10082520401c1c1d02040c216443c1e40072a261460488412404654542180341189032250102c0000d24080740249403900701942c0a074445918000010443c80030488481c607200c1c031f4020301001e00e0000420ba460300c140d40701d0b0074a0781c2c9090101c095148c0000c200840c130403031418042d100084803540c0c80e00ea06060801c0c145041c201800a00b0010348501808808260b580c10000808400d04c0340080080612070020030350302d00185030700007005229140405100d581c444003503808101ca410b10b8051040d003c0800070034117080845840001602603490520145070301f5400031070403070b61968400c100500d50000c0303200403402881c03003102c846072009021840514168110603046006d1020b240200450990f5009540e8000d901030390120b000d40c80b100b14041c51201c205401844040d45002804409116007501c89902c02c0d00107021040200d000682254200107840240005284c80410070740c90380d07070182e500c47c0704a42d142d10402e84c1c52007000514120101400480700042c005505010031b543c00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 269862922 1250 269861672 269861677
    0x103060602150c0a050f040906140d050c040504030e101d06040810090c05180403090e09030306010c08041e091119031109100c061508070506090414090f011b0f0302 72
    0x3c802084414406c007485120b9210050004050311940001c040e480d2400f81d8040e199001d00252043c0c443c40e0710703400499004103c0311080f60089400060a543d645000d5483ea610400003a400c020303040c8800515903007201e0030018890180c0c840c6040b040115040041c244070f9801110403d800411184a8042d80c98000c116010310a03000c0740800340e11000414523680d80140709401c80c003215800d1005150701710040202418403d04807600b01d2034021990b43da2440301402083c10450b5a005030b00a21000c5802d0b20b01400024034464000c81801c640e1403600b0a00380160418185044402e03940e445103002150310401010380c030443c2c030441d02074040d0001c0110250401742c03440c0030010b2940036076841d400560043c009460328169400103091502c00c403401d00000f1304090801c100240304201c00080c10008880003200c00c680d58241c5040401d000e031103024104c0115805010038442c641c813001c40e20f8180c00800000030400115000011880e41210400081c041620044603d0800344207800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 269864172 1250 269862922 269862937
    0xf010e0c1509030604030c0605070c11120106350307050d14070501090c0602160b0f0a021504060e0d0302030c03010501032304050706090905010b0301050d0f0f08090103060602150c 79
    0x10241014160b0012a00b0718008941c110b0018000c070b400038041002c18851903030014290302e480070001009075242e485412458001604c0f5030b0580c1074501c0421003d404c81e0780036004410518024510640700c0540b034031590b04548540100180010080c1003001041d90007035500800200f1903c0c035012000d40704c884202c4035840040c1c0c410461440405c10901848854920400f110401d46150050080c10006a10021303614802002010017140700c1c081c05a42050b0004c4000d281da51041d448240e16154910780b0744240c00914a08100900449030300004003000f01c030003a02c400c407004040c11000ca01c0200c03204034040e03000b0300045c0802c0d44a0351000101003544400c2c8600c2e40045905031114400c101c601320b80031340c030480041c0191766001550b03070020716000009007e5941050103e11460105014041c003420068103010300f4002a200c820b0101d50f000303501201007d015042540b550361240118501080c02c040c00001d00d01d2001411b10304100241513a6407a90b2101d607194692a4403050307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 269865422 1250 269864172 269864209
    0xd06090302120f040e060303091e0303040e040c05031c0203030411010509030312070e01050c0309040f0b0d05030301030b07091410140c030304020315070507030e03030d09030305090f010e0c 83
    0x24000c2440030624001803001d8640609419111340c54030501c40d10001004150034043d40050003804800d032188c1d000392800f0144040388008600f40d0070046451406664440c15248060400740300070b01101e1124041030303483c05d500b0364000b0300c0311610011516600b414041c00507402003001501180d0321840f655004407051401c940703440740c9100041d00c0c42e0841041c0c10803440c901402c0c0f0142c540c200300c12048616082c20b03d0f40c10501d0410040c0e44030f001e0401240d00070b07030326884000c014070120f5210044092009000b400b803483d460410320342c2c071b80090100300d805d0041c01c40440c030740e0303406a441a42260511450030440003070314018010b2140d22140520103101501c03000094075541c00d409000f040321000020b5803a0b2400e40101403400c4100105c2d141000c91800501000d240d11408807442a40c05040c00700f180b01c820030103c0c0c030790300c0f030280f05c401503500c3c0101c508201a8180c200e18041c540201c2100c2507141110400ca08072110303161500300c99401510802d1850a000b040320000c40d0222 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 269866672 1250 269865422 269865433
    0x80c07031209110307060801082802060a0f021002030411120c0405090c0108160f051617041e050619020c1503090f03040501052b110c010f02090d06090302 68
    0xd00c103050507240d80c150115000c502d0f60050b42420306080203c400140b0181c03500343c0c040c0d4980045a510b41100070369950340204130107149442c0c07045620462081690190000380d44403c440e000500031160500313118018052661201c40d20000c500940c0c0c0100c1d000546005105a01d00410003071802040d455072803400741c0d40700f844140c0c2d41c0e40704161040041901800d02102c50100041a408c802440c0340e02880310904030b41052a0b001d5118481e00307640c0c4c2001e81e41ea802079400b00000c080303142c0004001011220480000b051000d001d401240d07168120b8000d02020120000d10000300f6014044e00900244440b211410030b03421405900d80e50760059131400100d0f86d02003071103101c04268200c1224000014005229000c00c4085e04c81c122482c081c41c00c2c1810000001e103184610340420030112441e204070940c001d40b007500000040c1140c141001189221000d000260300320850500055207000c80780c03013030070500d0700854a092000034a07040000a180c0e642c0e00091800c0781080e021807156 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 269867922 1250 269866672 269866697
    0x70206040e2211100203030f01030f0305070f150b180c030a09060f0b1504080a0803070306090c020105150a06050d090c12050a060609060513052814010803070201080c0703 75
    0x803004050b80c20b400340050035140051041844502501c104a007011944200204988040152200c07415a60320030888000340d20981021549030040c0203015010b010100c05103010060500f205915500b4068001d021018105041042a00b0682003d100400c01080020402000540150b03409546104005094003081e202c13030301100c10020f14540400d035100c455100900d041d16850010b1840ea441607440c0c10708102c8856103072080d003c00141f0856020020a00c0345000e45c2040015160303140041140038080c00c0003d01030201541c00000032190402c1c400c0e054280486010243e403600e85980385440d84519982008203181001514240000070740810f000d090160203144150042006004802007820b14800b240c0c9180e0041c00203601c0e2001c00c12071601c4485080900a12894001903290744518a171000056810f29a084a0701f48420310780c0f14150a0340300441d02d40f14070181c16896a00e0310041d940c0c0744a40036010340482e81c1c580004035081c4000006003c0c0c2442841c0941138000c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 269869172 1250 269867922 269867971
    0xa0b060c010e030c060112020a0e07020c0607030c0b010503160e040501060f030b07110c0a060309030207080105100e0108060603190309091e05250f020a0c06081b070206040e 76
    0x180d002c102c802e400014a24240090820805014210111610040080316400200b02c0041441600c50b00c0c2080070018400318000c1c003030140c220001a004960760300c52464001e1030940042d004035400d40c0c168002154a050008182c0c89414051040c04689800c000481403400001001150a907484180114483d00742e5a0203200030b500c90b405080315800c00c004c1c05812400d50045e003406940c02160030032000d680c2c005420044807003509001500b445030b81422030524040d034200b0040340d820002800100b10704210380a044810300459500c0590702c8160070364503180c040c0c1e4559031540c04071111180c00380506d8801500c40d840703410710701755060340d611419043e143e5428000c01d0407045826241840500c030f01800d81d000101112000b9820b241844100540010246032001c001034114090010b50080024056507a080140c800300349a036540f0081600d4401c641010344e03025404548c001202d01e0380240c4071001c0e40140700c00e0415042071405480440010055003000151001c0351403141c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 269870422 1250 269869172 269869181
    0x50703050d020c0102070801020a090513180b1e1311010c05120301060908060f1b0903030c0c01091d0604090c1205100b01020c0d0f0c030206030a0c180303080a0b060c01 74
    0x2071a0041c00a00f9032000c00a810001c0310b5028005913401003200c0794265501c01840d0060b660304444180007518000d98201c020000042c8000c000050064200705102c00141228411500c0b010380b80700d02c0b541d01280040c80342c01644c0f8800510200d0002c0d400042658100c802048810701d0b112104028a80b00c0514050100000d1001c03035500000612140743e02c00009400390100e04010100e034140070084251a4800a04510001c2901303030810f41c4981d00c3c403040700c0710350308000e089075102d41c0448680b54a40c40744411060201e8982c0c0e0000440720080500c6846d82500c480301ca220306e03074134802880040c04601008a500d00c00303205012510035480008a58198020030080900100b074206640c1140d0048010505641c4007020610241d9135010f110701400c4d900ca255411100c64515103220000d0007500b00a501c04808030030402500f441c0e600c00c002400d083c2e502c0b101260f000455070035180480e40070140010b0074010000d40d4200558200724001c0102514071490486400000c60844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 269871672 1250 269870422 269870443
    0x1106090118120c1a12070315080304090b0312070609050c040e060a0507090803040b0d150b180105040302060d0228020d0215010617041b0306020d0c1701090905070305 73
    0x240042c4451005000210f00c034070015100040c10512400c4010211003101e0241c07080c4241c0049103040040c082c184250041c003080305201d040c01800a44401040341c80e60405d0040b81e0009180c0400c4075181d10300015405a440503103001c884c60005203448410240c200e5403000e40b010320a0100d1201c580d02c0c0c40c0700703101d00c900d0f40070054440b03402d04007000015644003900321030401c688171209001901c4080200c034201c80101c00060380e1075041c8802d000c00b500c2200c072070400b01c4405100000c0c0188400e8020302c0c4816a441c1c80d40209441d090043d1000e01540c00069000802888991905074445e40244804440c0c0e17421500c03001000180301000e140d5000400c2e006070071540c412003c00d50108082600d600003051411607541c102800202102d0303981020000410b001000314013802400115881c046094a00c6a503031680c5a040000195100c1c900300041180341143c850f0550f80b09044405c801403a862000c921646445107400240480010a071410300a810000000400c2001003040c0c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 269872922 1250 269871672 269871689
    0x1a07120f11030328090309050d061112040201022802120109060c05091305130b1f061e0f08041202010b040911030106050102030c03040b03071b030c021504031106090118 74
    0x7811013400f58800070140c040c03101d1811820890303600e00080e000003000d0103880040e40c0c81001c600c16420150b014000d0f41010b0b203140007001030301c250311741518030005100728000e80854500000c00d18540c2d00105044004080c80720307200011200501d811004203905ca804880003103219140f40c0c0b05e40c000c4410010302d041c0401d02c0020060180d00304a4000055141e2048041100b0302d894105c02d000c06510700401008043c200b4006115a6210009110024007000d000307941581c4581014160107681c410011700d0180401c08a6480c0340324030b10300c201020550303031600c20759100c50384c03210070504000c40d03010709554030380c06000350b19190352160a8510b80507940c45c2441280407030515086820700e070803d40c1150020050880c007110000101c2d01240c0c07299154960b644d8a641044136402d040d4412408081689100b43e0149940f2205141c0c5540c001c45400e80103910104241b0814401d5110040c041500c000d000c40d290314204007d00202901030400b05c00e10360300724070010a909459048a80b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269874172 1250 269872922 269872951
    0x4090c02072103090923010303020c0118150c0203010b040f0518010b010203370201020307090e06150c01020d0501030803010f050d020f091902030a061a07120f110303 73
    0x800ca0075040c941020404a40d5010201007150310000e04d10002d0303020ba0a001910b502d0340c21b079070702c0071000300003010310b0348550381c00741e40d6102c2c0750003500e400701c041c0c4d21800101c079007140000700a5002d0044089a0b070380c1000f4400c1040e0100d050780e1085611000742d0b815542d5000720403185c4c6441c0a0b441a0910b00c030070014051400c0b0700c10156400951665240503898001000b146d40d0300001101d100740d65035407070f141e200705070350111002030507240d445841410041a1145130f0716405402960051095484441e4502c0e00c421001e03901c108100d80c07039a8880c1002404140c3c0c0c89044004180c0818048009031070240d0903040c42c0d00f80d84081c0c0c02200c0c2018000010406590340a4903000031f004111011a221381c11a000070348070508403140c4500c074240180c0031440100d03509031040c0709051050b009545034030f02680c000004001d98454292203080161902c0042e01441c0708560701d0680c489542c10031401e078000111140d00f1007400e644184449414000c0315a0000c2001c1d600c0742c4044640d800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 269875422 1250 269874172 269874179
    0x10e0106080f12090d02120f0a11042d02071509030f08010603050705030c0c0309040f1a060c06010e103f0b07030203130803090105040209011a0a03020f04090c0207 72
    0x3890b0003520f00b2010402581449910a5551041c946080403501158040c42c40240340c84454140840c8044070000c1c0e104860901041007c0c0c00c00341020000111010405070071800c801081d04100420143d61003441d1400f90001404198080c010303103806898a481c1d0504015542402c44a2030303c0190086031f80005496056640308608030301510043c0313002d00c43d6090580000e0f09600000e8252240c111000c100000220710800c191000000001c10512000c4166039040004180c914040194400c1b16045081c080c04c081c42180e01304c0880200400941c0e103000c0c501c0300911005419002212640180001c00c5080303000701000582115109084030144048100500000103e803984040c6442407031f0004102d042c5003a5602142a00700580e80b59100c0105a50001601c100201254404410300030382d2401548424421442900c440e002c5903200c210400800029000d4042c0c01ca00c100880c1449a00c00d40250898045086203641402d032241100820359100390316070b00c010380c450807040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 269876672 1250 269875422 269875453
    0x1003020412082a0c1c020402030a140709080a120309140601060806120309010c1e051b0306250912030f0e040b13020906090d0c061413050f03010e010608 67
    0x94919405210320719200b5590750005601c07420980d030128400c0c444a0601c90440041710705110840741e009000f15071f645410200340c001000311242c001c0420034480c0004024034001d80c180d00541e4120b80041507903141c19541c1c0c40c0c14054500000701090740b284494400903041e5480201114140c41c040c100715810030500901e10b1600400c103611480c40d0703100c1c40003882008000c98131082c03000c0c41d00340182e01c81820160000301c54101c50029085000086806001b40801e00f00501c584001c5214803078920002095910317032064504451607420000d41c24403480040301d00c0004142c85080446203140e9424041000801661054000c59250140000035590012520003103503021a410440e0b40350000200d00c4403500060400d802c00e60000d0a100981e947d082a40e40c4c080000780011603c1708149055401e0788014071543c00458194014081403503200c1342030380c44402c1c0424005c0c0f00640f82c1000c000c8154040c0e081a0f815569407600608400c0f000c0c0210310141c4400300003000a8441c4a088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 269877922 1250 269876672 269876707
    0xc010624020a080403060504031701120b01140f1012110903010e0a12120605060d090b01290711190f0902030c04062001060807030c15020c100302041208 67
    0x360011504400364550010b040e07001075070190303900050001542e0740c0d18030b01a180700c0c1c80424900c9540305040000941c0001c10070b1140c0c2140c0c441c501d105080c0c1d0340c9100441c83d0303001541100e40d004185c0104550740d0305040d4801d2010003542c1c03800e240c00299514441044511050401d8129100010b10000a003801d0090700121a512402013009002d117032100118000d4100550302080748100e2000f5180d510740c0c00c80c00262600805081c0c0c0c82d6000401700c0010a250701049505074113000001804580b003100b002851001d000c99034500ca03407200c55130506a801984101c881640160151680392146460426141d4885d46c50855160a002040002110320303030100b100c080c0100100f00462200f441580d08542ca903007015540c003d031820b80003c4031a049120320115600e80400010116400502d0a0490307024007640d2406503286e600510320004141e41c0740d0b003d680402c1014003241008501c1d182000c40600e401414151a204c6282c81080c40600945044601050143d250400c0400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 269879172 1250 269877922 269877989
    0x10609181407120807021518040510080312010306050f01030c0302060d020714060a0b04270804180615050a050a0e1903050303040b0606090d1115030c180102030f040902030c0c0106 79
    0x52135401c2c80804034030341b403012354a481251b008986420120318020a442e4524024003111001d6949032500c00c2075800301c2803024170059030b6007414038011490420355001000e058030380040032441301b5411a02030100b036902481103510203650800c41d4501150301003d1081030b80c00580003401103410070b4a54001030f149880b6499110301e03c0d101c01101c81d0013082d181105209082d0f4803131041c1041a08240c10540aa5032051003505100b0b01250709624441e400201071364a00032ba055240a000f0780111400c1c0681060000840c1702001404d00c564000c41d020504000028540c1d07042a030380c4000c64070025280d40c0304640c40c2e1b002006100c00c201203051510b82c024400c1d074049081090103800241560503851010344140c01c00b0f11030f41200e4840c0350390417002d0303000c01003520750700e00307222550440903841080241010142c08031244869031011084441c260300c98007a581c200789c01d000002000350302c0a4408841c801c1e0400650300303c140d003801058000c0c800580030780b0000b0030304102480000b14082 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 269880422 1250 269879172 269879209
    0x309030708010c0e040b0f04110310080304150e0409050304060504180209060712260402031501230103090501062c130305090301091b050301060918140712080702 71
    0x102030f0b084041c3d11101500781c2050407540400c6028824011940c181d41d40b602064001d424041c8a40785950000000c50040300c00c038259411043c1d503a41c01649901850007800c940749c07001058264403505c00c8000b04c401000081000403411003541e2940d1950b441a400000459000300c0c2c2040301304110a800440600246030941c03620a01400090140c0f00302940180000340b40440a08424882c0c00c80500410781c0441038441400811039007480ca00044034100e21901c40c0042011000807527050260482c0c80c1410202c0c034440940c11140020380c43c1920550405907180e8040d0041402409454020400954003040c0b000d0589101c10002101c0c00703203c0c102d070f1204003d020100303501499107084950180b51007a255541c0d000044d000d052149030140c070311500b80040b41d42c009041e9004c2011a00214000c0205650301d00ca060152120360b0005030074042c2c0c1115000200b0344030702c61502a075040a0548503415100c2c140800842010744040c1c60088000c60a01e04504107a0000503003c007010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 269881672 1250 269880422 269880431
    0x807060203131502100e031801020a031707050d0609200403080307052803060509130201021b010c1202010c140f031f0503070303050d0606080c0a03020a09090608030903070801 77
    0x31640b81a11440d485480f90400b69120141c1100780f09000220188100d0310083c4003082603052440d54030780060306c07403410100302e9071400c50039907000061300454998540c9860107800d10070418810030100013001c11060140c00c006400300507079284a10b0005c0c00042800060040d08010500c01d003240050040000c80010082400400c14600549a100344640380403946d0320024100546d0103070700804c65152460f00280800d0465415401600540e5019203000405694203500d071204007c1c40440640582c1084900e2144424011000d003c000c01c103040101601c801c0f0340e2170944040b008209a00140d5407444805c0303110350710070b4282003410a213404e00d07401c1081e4802c0f01d10291101401c02030403d440d20342c140480f008000d12142c000e00e002400d84003915983e080240070741d4008e0000c2d4004078540381001c6021402103d803903002c4c003109402175060958505054000b94000542c0b4418002c851000045010040c002d88014203101d20246031a8018001403500d000c41d00d03000141c80381d041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 269882922 1250 269881672 269881687
    0x5070b07210f02060115120204030b1918030302090402090a06080702070b25020d060e0d09120308010308180d030917010e120a050c010f021e120c03060f09010e010807060203 76
    0x80d44c181942c0010211814540400106584042e46d01e80002c0440380081000410b0041804001d40f08180c81081c0381521807201c0c40c10000c5a20039004507030503c1041e141c0001191080e80079000043c0013400c01440c0c0070002c0009003500c1300c039900020005401a040000440e414000080103105020685050810007491140c2003c8820100d0031402898a40c2c07400351b507202d080604183d9040703241000b00e5040c202e8070545a1410035607500215629030030010b440c10070300310002c1060790941e0707614810381d00f1039480d031031654480782c0c0b1010742c08080b44100100c1c2e59003c0400a80500c6615413001c100e15022000c07003200c80444031007600f030f40f4281c0b900b8038208021980610421103d1002c07560b0349100e401c1620b8500400140903182d61a00d14450b0784001d56900412081a085007108200c2e40241500c20007841005108108825914041502080200065600242c0003400c0342c0032a11300c5002b040304145c0c240c0c014082d00102300d004000b40c690501c4400054000c505c0910f2034140c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 269884172 1250 269882922 269882927
    0x3190c0302071a070f0c1e1409060a09050f041205130b0a0528030b030703050a17040504050901050709090b09130c1502010b18060d06050405070b07210f 67
    0x80c03003a06100e94001d803080203a100d80f082118010b0341e02c40c110081d108244d0501d41c08400d0b00f4066031001e24180740c1350280040c4203500304c1302103407815122105400401800d01040040141480c1d13089a03090b14042410031940c0101407052040d681407039818a4141801814956140102414010104034200c01e40f09414984016104002d2845a4800b01c084040780d90380704200ca034801d5502003a1130104141034121b1030002070750713007a034050102d011904105522100030703100c001c080360300001913480025a14070155100142100d45071303043c5699500850240c0303d0440d01506280d544408100c8096009142c1d0809064241d404001e400c0746a4081000f001303000e0504420300d5488110700c81080307014201500541030716020580b1280c2d000102034041d11900668a10600c2c0003e10041d140e1741068600384210801000a2403001c1280c680e40010031020b4030541d814080e81b030003c905225501300501090717100b1800c00b01d50030f1b40341c0c14240503c3c2c00108c401040100480072804441d0b0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 269885422 1250 269884172 269884183
    0x50d020d021c050105041203021309050a0623122a04180308010905150a0501030f06030b1e09010e1f060503070b07050c04060503190204060504060803190c0302 70
    0x6905a0300010051010300010303034041040d000310300092008000c02c404100041d005540503603ca00344081425108071002d900f60702a00759103141f001200902040595113039044590400c0c141c200000d1420740301d41d06055401461036074a84d440f0400440e1521508048411107880b92412000d404000c02c912107820700c0103454080d86c6280c144400c11443c1594541d4000c943c1450990042c140d0010103240243c41c107002441440e110780d2030000098100c5a0b0790b1040312140c01d004004500d81800c0500540050101038030f4411b0305503031080080002001d41c408940a21a005d0017110301c0b54482e0560307591000020b0049025904000d114540c000000801480b840311110901d80728004a82030f881c02004281e0046515200305400007450101c1400100006401601510003880c043d0007400180d030450320444d034159200340300741c0340e481c5078a090103d221440100007041d1581da6400040070b9075a41d80054800da000003500d181d0344040280841c41c840303800d0400307000700301c0c072500d019441e003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 269886672 1250 269885422 269885449
    0x80c100210020906130906030b0c0310060807020a150b030c060705030426010c05090913030206041518050102040603150612020d0f0e010608010e211803072c0105 71
    0x150b401003441040c0780e42d1802519881440310320813030364065943d0145400340825100a90b8101a820042124401c0490803203206900300c501030462580b03005821260b84500401c003c0442c00f45503129800104009100c961442014402003100da046034101820410004606486440200301d0440001e001000b51011140e00c2c1070000b0b0b903c030413494040003400c58409283d8555103410741030258690000301030141044240c1c0d0342c5815640d0403c840050001d00380020300540d03c000005000103100031b0310150a003104000100f15003410340d81044d250695070300115030594010609101d081e5061181c00d20f1305d00f020091840e514035250340a05800c007070440ca944402d03000600210140d800f50040c03403001c10000700802c4480050b014090082029001d0413229508023450b901100704000707031100c4515009682c01865001071005580c1d00d85c041d48503080105500740a01c44e581c2d8003804804010444502404882c1100011502d5041d01032455901112803c100601141c0c80751006000c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 269887922 1250 269886672 269886703
    0x90f1006030c1202030a0e0f010507120e06130809030d093f0501060e0406050402040c1d121c0c11011d0405060d060218010207050603040803062103040609080c1002 72
    0x40761039140c800b04c003030003201fa2114514840c003140c13003840780030551006115013510b40d12012007100061321030060300c0c200010700c2420740c469404140b1460a0759941c0c920f8500c25002140703400e0010021900f0424042c14100110784000070821241e03010034000406990041d0340c13841c20003c044c269208504625061807107000d9007410301d00c2000825170240b0701800d0b2050101c4490320340b62034008081c14045030b04074043c40c2059280302c003050207203440740103041124601d8411000d40741d060102010703400408030498480c90448600034180c030b0640070020041542c48070840c0da1503081c45a1180c0b10044c921b41005401c0c02da106503144458140448000125404202512000d000581d043c50711107018000c270b403001811640204c01d1610f01091103000380c003503e28040d9280c003000350714082150f02419640f000c10010f2071700c0ca041240300803841c4240004030302c01001c501c0b4507441e641140e042a004104d4030038040c05960b004000164001c8812078218219000390071000752142c1c441d1480080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 269889172 1250 269887922 269887927
    0x13020a1203411210140108040b070e030c060d0203060a1205060a0e0f12040501020d26040f14070e060f0315100909080d050705030f04021c02090f1006030c1202 70
    0x40704800b1080f90040000d003000154607043ca040c01102d440d000344034241c591355120500c40001e5020740021417145404c011030800e240c1d5070f02c00c10344841c00301645407940340c0100d08281590713a90b400007500c8207204040c00141c03685400c0c410301512540c10340040e1400c0304036089400001ea400100154004121f26000c106101d0001c9003a14100411004409030301505c10065441242240980201e5809a00312403280041101c159010614440081035180c030860502c8003010040d021150041d100e4660305008015903117400142c00035400384000d490704600020001c10885414164000302c0498000040000b600c2c00207a407001e8401c640d101c0c615035000040c100304903030301c02d200040c16483c2c0e0600803d020f901d40b15080342e000c550141c0c1e40504e8440400d100138420000d6034800c01001c1c0c0500341c1c41d251602008101407180a101c90b641070701c0c01a800045c1c4039220040c1c0650b00ba600b6028903810018a202c1c620210364000d01308041ca440c02203030034294003000142c0c041c00807000059 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 269890422 1250 269889172 269889287
    0x30803041101090806040f02030709020405060708071a040b040b01090203090c04150b0703030f0e010e030a0302090406050a030b070201050705090f01210c0f02010501050f09010303030513020a1203 86
    0xf41e800200758403100140c041c0d0400c10050203080d00032a00003510071020317a64050348820250b822400741d070150542003d0148a14000a06108024240c1c03601032200600b00100d082030084840c1c00c00c0340d0480b0100040c1003444100225181503e0251090460550840c5860b000c0640c2d00c5041c2800c0d18801c9494006001070b07001c51601c8003016020141035030740d591005003000b4000c0c080558002e66002d20303000d4445031000c0f06110318030445402801451424031a07010880294001e9401342d54817903a0f42900048642c0c0d030381410401103220ba12002c0c814a00b0301d030b005c0d084600c020b0260003440b108202180d2240d860080c0240d0380d10090030a0070f40b0341c0c0b20790042002c8050351040ca2050920301100c00c44820340110720700314610400d6009002582e00c0d10184072000540034074140d0044842c50060000074020b40006900020f002c51170a9a00d10b5600001c1c0000d510b94018003003040452101d40505900441142ca90700c21039a10341c06400c40020300c1600414000c442c10514000030701d40c403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 269891672 1250 269890422 269890427
    0x80a0e0d020a0602030c0c0904030c020904210906030f05071b0f1202210906030c030601030f2406030e1903200601150206101406160809040501080304030803041101 72
    0x140803294000e40a16282c0b911404042d41d01d03400740600c0c42440c0701c0c2945008091420344901442543e0603629446a0b05041d400c0c0400c42078040c0003141d1001c070046441419803003443c000c9612200300e070364240c070b2035150500c084c0031545004010341c049410582040b0b807090300906c50b01085601c46040d40b1144545040441d006c0c025150001c0140340a1107001ea401a800108010340391408039203620f10011002d08842103108028a064100c030090000407410b64280f400355910103010b04000c04c01c001142d41710001c07160041c0342941c01d041c2c41400041150303500a40a40501713080e050800a00c071241410542d5400a03c1c410150b0300141001d03501094801c00a0302c040403400b10001200e10034248800f81c40e0b0009000f43d080009a501c0c108420310710025900b8006d10880d644d13100d04038140032940c031001448940c05a08080100a004100040c0e40c407103000e141e00440c0196191039840c001c000c04e441c01a0f0000030039030b2043c070003440402c011004880d0095800f020507642e0000340d40c010b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 269892922 1250 269891672 269891689
    0x6090801020a0801060e2805100908060402060a0c1a09010c0207030507050f030c090f071d060a030e031e19030e07180b0909010f0f1a060912030a091a0304080a0e 71
    0x11f0000c8040c4041f800078030b90714009420819904222003000c20904c00b00d004848484c1117200701c9110340d0005000c01c0c0541054801090409a24640143c10201c42d0701c6030329030300488500403003548000c4820084c0312031082c8160b10b0071401600c05040135510b56200d03255107800c070340101c1d442000403d00c00d032020b030b03410000e10a400ca000b03000d40c481440c0c001030b400c10504044890b0008900500b026200b441203643c010005607100401241c1030460710b182c03c0b00103007100c407594001844204814030741b400340c03428038040002003103000782d41e580d04900b5206042200400402c1c20f040c281581803003900d5010900400f903641240840061807000042c504c090240590b103107410040c400248500c012064000090903c800c500900c031141c2c0030010807003169085004c0c0082e8245031f02500a0f1803a00500400026100401079082040300481103811640a8400700f0f011940b4440f0070040e24800c1449000c4204407440d03000d042d807604d604c80003082c0c45090700000c20440e154200050316a1400003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 269894172 1250 269892922 269892949
    0x6090c01180e1017031608030a0b0301021602041a0105071b0f09091e020a090b030c090a0b1801060e0607020102010e0a0302060105011103041206020306061b0706090801020a0801060e 80
    0x2c0d00b0795420030070807040b0500305a00840b10541e0448410304031502c40003080b65040c1112028039459610030341c982c0d12a44e000500808070741038941451b490310b503500b4000b0303002c0000c800300030103582d00131841040204c802051a030310030000814015644c0381c0e0040b00f519580d40d0000004815480c040b0303044500d0311810703000a510313034148030000300e030b414640c1e800381c80039600c258401d0700754800080594580c14142c40740254040c207404814040a08141c002441d00b14000d0102d07902d244c145e00c005a03046804a980940d4255260002821440e01003203140c0015032450b0051099410108024881030403009594081c10001078000216407003540b1401807c10410b00381e50340b80d1440d04e0000e480d11000e10905000840c501c92a40c3c58200100c1110103d83d1309450030301581c8220350b20307503019410080c0f41652000c814003100003202c3d01402d4015081402202420016052904c050a02262034101101c142c1c4140942100260000205410f581090504500c61440c010014051116466 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 269895422 1250 269894172 269894189
    0x10207080a030306060f182106110309060601050f03130f0501020a08070320270d1202011104050904031808150411010c02010909020c07030602030708040302060906090c0118 76
    0x24110000c0c980e1660080082e82ca0aaa810400c0010a503046a50300c200360751300c40c00064002400c1151a01c01c60f40d0490760443d810f40865403a00d07a86a09c1c007140c4120301d207002002e50000c03c0084644042c000e10b0341c000000d0030001d0030108103009400c8a0300005005020610341c1c200c100c02800a1182484492076008000399039540020200604040d400d039810f9010038200100c989072030f1503c503000803010589451050402120388802100300c200c0c0345003c0700b20b500b44e120103141c50300c400c4140c0d1012401891900072403042d22030300a00f190302039801d001090509020501880e50b039440d00305d800c150145040740070100303880b041c50304140c4180c1c00b011840c07180301c03d414080720f00d00220b5485207029840c80e0661180b80320054403802c41c24040203002640407a02480100d4107035001c0c02e007140ba400e044030501e54581da503030000c0742c2c400c0c0c1300100030a4030b607030810003010317410002c0070341c021207080c081c1c55207080c9010020781d1140c1c0c40030f15505008071442440c0d02610340e0140d01d0014404c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 269896672 1250 269895422 269895433
    0x30c0b0d11070f110303040b070b060607050f06040c12080306090601023306030105011406070f0c060518031b04180507030b01052409060d09051005010f14030a060b01020708 76
    0xf40740511048906500c21503140003403680c04180e51501200307940071903040c018800c2c64004c10b039071800181c0c8001021103912130014401c44002c5001007080c1105460003000408540c1400d08182e0301c1035946900881000f001302c2c09100008070701c8025240c002e002541c0000f010b03214400141c1c18024400b10510860b10314002d095501c815074101c03050700a000140b83d8156444800c00c1c035080e03034004d0050684083d6841c1c034074503503400c00340e004004060240390400c2c000081d544d25885c00c20350560043c00041e4005c10310b80d002520106400340240310450080c4046070460b0f80c244000424200700c240f180d941c41101010300300e0000c40c0404000d80c000150740c1e805444e8500317020207003000c2c06031900174041b030201901080e490850070320030032001861060030845c460080240d903a22a00303000d04c00949901b500800108100102092412b003010b02103455030510761a18254001a44402c41055940002009039180411100400390f001000400e0a81150006174902403050744240c8039480768 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 269897922 1250 269896672 269896687
    0xc0918170310090209060304030f020f2e0921030e0f031e03010f030b070507050d02010507020d030c170405010b060d0f0b010801150807020c0316051801030c0b0d11 72
    0x5403004512460208000d44451a112400c4000300e000d00c80403183c0100b820400b00c0c01080c01400c402c48800c985104603207502482091031402d200b90403907030344118240b0700c0c6c03000d41002c122846d80c01c29007008001000b0600040d16280440c81c0c110502e441403c2103000c0c1943c0c20791013908008030a0f4082000c492480f000185590342d40d600c10301072140c082d400202d50400406112080364100c484140140180508607141c94035031107405803140c1c01788402040b00134000381003403008076850701d2150000900d91a05400c003906251802003680101403500c2085946290090121001ca100701424200f441e039039898064010000c900c1416407000c004518068a240c0304e40003120340791400c0c0014819416540015a14408280603240c60b0360481c0081c180740354031885125a010b10648100c442d04003200d00400c0c00d06c0b00c40d10040c000c1101d8494144118101142003a10042200b0180c200941c55915680003c80c124000e004e81c940000275041340c47e4600f40c000581e44034004050660380d064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 269899172 1250 269897922 269897963
    0x151107050c0f0603090a08090d140d02060f010b040e0612031c060906060806130b0901060504091401060f05071103010c050711030601081b010908060a0618090c0918 72
    0x1000101c1500c54a000a240840742c20140c0690703001d078070710314001d04526400d071740d40d401d00303400282410390001c500b010044042041c1c49141450007011501601380130400800080c00c2c100010b1000802002100041000c0c1d5424012a0304880021103000c1d8103803101c0c8006890701c044400b0040c001d00c004500c02915002c0c94113004e54000e400c08081144950f160002e83c03d5485500c28000401c44a10000e074a504110341c89204201480c0030009540c0320940000b00400f5081c0c00080004c3e001040500c030103030061040c40040c031140005440c1640c0740103402060030410408000c03c020000c1011b40411540324005159081d000b07000f80401c1c01e00078802001c94011010568049904c150034041900300442c0d9a03040c0d0700703500e0241c109020070200c0c100c1c00308a0041c2c19070400079076940004a0710030030300c502d41c02007188000104085c1e241907018403809858481864140f480d103601040061b4443d040842104d11800340465403002d01c40e101c0150001c9480081c0200c038100380c3d901c20600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269900422 1250 269899172 269899183
    0x201050c1509060108070e161709010b031612020d080403120c0c05040207030c06050603070314010b090609010e04020108041109090706081e060f04061701020a0e09070c15110705 78
    0x80350040f00c0940e030b030b0b41c589903550303021910580c84103842000109203003107031001469203400b0040c07d0005078100e11712030214424204544a1320165034801e45544030b0301c1c0038001c030f424806034011080a0340d410440b1501d141c07000c9080c003c0c804e00a51408504000c01241907074000e5403c000718902424a21001030044506860200c41241007041d02080904e07081c8240d03013005030159180b0542c0003d603640c040003880040d0000b58544680c9500100003400310201e0320318840030000100d1291400f0050000d00f40024000314442c00458006000d60b00421201c41d038803540900e00a200da0721030307080140c00304035814402c0c0c0c2c002060008000c070050340081c0310f004a914070384ea414121399845c211131a00c0c044003089041c103a1469004501c061400021548110000420004117180c1d112a003004810907120f8501d11030b50049403540381b10360884080d0720101e409407201545864031031001010310341105002002180c40c039030b10404520b50740c4d1050369030810300303030160f03584480d82c3c1809569036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269901672 1250 269900422 269900431
    0x702040b0303070605060f2209050309151213080a0806180408070302120315040218040c1701092a020115180e01020c0a08030a0209150406030c0c020310090201050c15 73
    0xaa020800c400442d007000803001c8c40f400020140d111400d0784040840c030113000e00b100d06032841c1c1f0081c0715442a0303990300410806861640e2900c980d0703510380d0301c803d0510301d8401801805102d51849816010484500883e00300750903a14110b00785540b07920024411708500c0d07141d80c0103506480200802c201083c0b00070041c01c4c2c042d40880e000b0341c0c40700c100180c59100440c0c20002a080360714480b10641001d4002d02004241c0c40c0302c41d812100e20101280c1103920a50070b0100007a58600500003041c1c02d0322515003d4404007a060000c50120f070700c00d102c046654840d1096012690a1030340d0028030030b41c0040031002c608a40c90780001c0e41d0b0074400c4c1641e22403006506450745040190058000c051003121030106500c00540000b0a8a4a54042c1c9070001041e0005641d000c01040d0300555034184010491065908029165820f00c54014202e80c0c81900080500c610700781d00c440541d900140e5034058118646002c6420702080c8012940c500560503220928070130504c072100c0b92210740c1620b9104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269902922 1250 269901672 269901679
    0x1b0615060e03161505040305120910050901080103081803010c030b190302211005010b0d180b0406020a050f0705010504050d0f09090507090506070b01051003060b09060702040b030307060506 83
    0x1e680c41403003055112541150060070401c64507404022080107460f164500c1d12040c00c00e1030130719650b0f1b11810f040c2451014001d00700100001c01040625113061080034401480c60410b0401880c040003030402d10060001414200001c9410403545a20303c02031050010b0203002401099400940580603007140c46140340701d10310f003418407191413403050000004c8030b400500345c0c02d0000c4441d813120107c0c590303004808485c1c000c1c0000060034890b58040c4070700070224400400c0d80c3d240390800000803504007498144459503c0c6141c07201203500344401c150042d80001c0c1c010b076504a0800283c0d568400c11001c103241c42000301e502802c0c8201940400e100394043c000359100401024005c503401501b0004080108007601002d00c81c0c0c0700075901c020762000150400d0990640c440000918503008400b0481e0640d0304000140280c0c10304420301c2400c04100c1c01c040c0031040c02c261105007140241c00d111030155a0100360602590340d103802120501901809480c1d6880ca9801c1440191100f260441d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269904172 1250 269902922 269902937
    0x91e060506040c140f04050312040509180a060b060d0f0e0c0d031407050c0d0f1b080703020108060a03140f0f060709120f061a01090b0f030103031b061506 68
    0x401d810640a0002d802d24950340c2e4050b9980c1070099140d41750050b1080301d8044105000108840e102001180e03101d0500412007616685000d0070080440c000611107803080221599070003020740c0c001071640400e0ba11601c045a040901001b050350341c010416110700c0241012526074100d4101e43c03000b00b1030725004060f1025400500c0034031051900908000300000d04d41e01b4101540140d2001510540e4801e00a4a002c0c08071100011408100c01c08150765044090440300308005207001c000810107168140503c06e18a0b102c461604d5184511001c1d0500a410b0f001400c139685e150a0a409103030300409005807150f8140405036501090080d0410605c204042c02c0b010f00707800500944101882da0355150018205a01810000307981d83c400c46400380540e2080300064150700507800b00014800c680307070000b03400c08001400404107500200e90808100700316041040244222410750360581445640605081c28884144005100141049103040100171502d0fa080d1001021a9415902c140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269905422 1250 269904172 269904181
    0x100c0507110a0e0606030a020c01090605060f04090503030c0c120c0f070b04030c0302101e020606040c0c080406050a050403201512040b090312102c06010e04091e0605 73
    0x554000c6008500814080400041c1c8610348030004551191a804002d4100410030700e9160941d030001c2f0045a0040c0c4030010082d06043c40d80050380910002c603018007a9001d0b13529240c0e22480040c0440c4c51b090000103031402d0b00ca43c01c1010036100134910320f21319030b20380b2084407107074640c0c5900c1040c0c1c2c0c0c503018950001404c0c217044410780d4140d0707400a42c40c0c06410319550070000307180c1c0090084010b00100800164070200c0001c40c41308100c0d800d8014115510740001000210341e040c5100d0420f11000f4214034021501da1401d5909030740060614965800540209a8150046900040100c1c045144510007610364070034010741c510059903aa0803450040e0f020002500802828042c00e0580000040104401448541d04504000d00303803850b02501c01c80c1110215812951600a04900c1c40b08000032140303428001d1541032489801a011031245140c0c5510880c064050390400c103200146010039075442d845903103038590100c202c100d4003c54440e118602d03140c982060710458649030016 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269906672 1250 269905422 269905429
    0x3060307051e0108010f0e1603060308030406062c0a0b010c02090106050c01050c03090c01030903030605190e01150f210516141303150f02072a051c05100c050711 71
    0x3e20a03035001407a03080310b540c1e07000c0301c3c1c000ba441c100320708c01d08043d140d92b00000400c1d85400110300507802000085565800c0018041441043d401e10a07004000342070824103c8c2944058241c000c2e03041c03d00031a44006280040720032103490480694404c03050400028083e802038014402410750030000e0250303540300d440c4040720340012100d088064000801290196200c0c1d4858440030384030f410001a401c0e110760118201e8003152680d141c1641011009104414001c1b84586c010940202403807000c08003140020b202505c40c3c0c000005000f80000d00503130301c17040d0350322885e01444c2a55003004549001201001200724100001012404000e00466050324a104840c20074403407100c00c1030050324595540c103080054015854401b81c0d40d006e0680180340c180010300c0303810702074000c013000202c1d41d61000e603c4c041050720032040c0d0800d442080040c0c1d01c0300612022105c1d8400503042c144d04403810b11600300003001c01035001030f80c58840754030b07606a0024040c0c54824007c500700380002e0020342c20b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269907922 1250 269906672 269906699
    0x105040206091011030417010b030615060a0215070917071a09060f04030803060312120a0207290106020c0105030c1902280201120506010e0603060307051e010801 71
    0x81d401c86000c01240d0316a08201100048800c07441c90403074030180d201007005080d500286c2004c4440702d1549000e50401909004407144620218040c00309410445128000c3e1150140950b00035070011500201d018028012800054000f6520030124904660024a00c1ca41c3d40680940309680480b1141c8104001400302c054034203101044010036035981140148c0d030080798510394807010400011402c2d0712480301800083d8454880c0988074100401054108040c51043d000e142c2c0b0140203038401005800d0703405820070050100140c2e10309190038029460012103c491003a503125016600f00c4024650109040300c611b5425500e14501c410011900351000b502d6100a124050250506882807840b81890071001801140c0451005130400703000b0004001104134034110141d200402c1d03507000500c40c071041d060307210104114504040080c0052000c0051103018060100004000e0388080203140d02800c4000c08229030406030b003081e000b000204510550004110800025035012040314 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269909172 1250 269907922 269907931
    0x414100e010e1f0317071217071107030c0314010c020604110103180605130611090906190e07030219030905060a09290610020f19150c02010b010f0f0504140301060b0412050f0105 78
    0x12300c0d005a140ca10741214a0702c901807242c09540204e990010000c0d401c0002540258840c007001840c80c90001d24079405c684180301c4080035908260100000a10a0803036202840740901b0000756080c44100d6410360754642000c0202613514040900030034030250000451100c0c400e01c82030040c6002c408a00026004560090760004807510204e1980c0c0b9181c07030f519844c0c40f511510940b2240e50b880001049140c1960302e000405e600042d00c1003000702c010300e41e0130800202e003818400104140e665580e40c00c030017084031b03c940d40d071040300100704000e0051040e2110003102203a034140740c6e038041c42d682e00710b0180c07071032403091840b102c055080034008281041500103a03800f6010480b981d0280c642c15500c01c403004c4900c5c6074610b04851481d142e074401c510020925600010310540b4500c000342c0b0702c60f040c06450080c001d280446950740c80d884012034054a03803900c0e140a80e880001d01081c00342020303400c0035450720004200401c842c4210140b94802e02c0c09a81103e40081100e10114201d038001d44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269910422 1250 269909172 269909207
    0xa03080a02251410022521110f03040f0b0a120f1e090203060408030703020c0307060e060f0103051015080a120909020a0e0609010e0414100e010e1f03170712 69
    0x3d0079503003140c080c43c050025442c001c0130303641a502c81d42403485184c016847c2c10318001c51074442140e610303030104024015400043c00f004510b001d0405160b03610b200000c0c42091403244000602d450542e1155160701410f0b00004e030140300ca00e200b4400440a4081c041c281d01101c007682001d203420f000103010b5418580d401401030902500e40d0b071903610710307980010306140915800b0000d010301310000b0001032440c2c40c0111000120b8901c60340902d403c24801914145d815442c05005101180020039007000c4071061246c0040c40324200100d001100101c2d40c840413440c01210401010310014400c3d990080442d5500e000400d502c80d00315804902070310100d680010708000d8540d80d90b00b00354000780b54850301410701d60210342503800040c061b41c543c2c1044070450500282401241c0c5440c104d520b0141802c0c4107800c586605101c0441200310004100d00389044515800303020003002021803002440d00700d040700d2500480101000c0180d4010042110343c6c4a4040250140c3c91003005541d41020181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269911672 1250 269910422 269910457
    0x20106180207170301030501050f010e040c3008040503010608030a02030a050a09090518010c0c030e060304081909140604030b1302130c11060601020a03080a0225141002 74
    0x1101240d000b900300389000c40d640d800b43c41d81c034103050460b64040c50007540b050f40045590328040c10300016891042e84506036a00d01c480610000403a03100f14003040e104039144110448252050310b8001000d0180c40640d00800146c242060100c0c1c0c4004000b03540c0e041d0000c0c007003c0d07550a0b000c0c1e0b4910443d0070203030060300144080301202d0303c2103004003000c0146280c607a0100fa103c1072840102c034410b072100260000c02c0703c00d02c40050b400380600f06c0e1000550904080140c6140c030090304441030507490b148113450000020301041404c4042d00d101c42c0c294001241401513445020303000760380a01803c2c00b03440c1d40c4031030b44c456803400070100c40c20b03240e1040c080c035815104c822036084070305580b4400320303031148492058440004003482030840c1030300c90355201c11040d0752520f0354500707043c8090100e40c115040000d03103001007900046185d421004000005039260b5104848103000c2c00f110609400d400305030f42c076410174042c00c110b003058046130f80e00549962000c5019954102c2c400c101c012800c00d0b505 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269912922 1250 269911672 269911709
    0xc0c0a050d110607140604030905010509060d0504050a05060106080411060723120c030a08090606010c1b051804030f2c03070b0a080f01271a0901170d020106 69
    0x10100000010b100141c55941000b8807544c41d000700186160000749151301c000100018503900140280003490203081241c40e11124401240191050811441c1c0301c0d900c6901050030043d007088018112508201580c04558440500601c1680184d41c265013845c3e107000c007007403940f401c03200f100c00c4250310403520b03540310310078544e41d9001050419a000d11801094007032201d04c1c400070014210758403100b02031f556135440d030038015050040103000001d05600040c20020180d80080d515102c00d908241604502001c0083c088000c4040360050340d0803014040040c8900160199103d005611076202d0300283c24161100300c44030070843c02100034010700d0402c3e040210102c0f0303800100002000d130595035400e85403408100a58440400340b0001059041080003050620611718050160221848070f004142050300f51406009448480802d958020311000c00040e00c003895030500001d80340200c55a516041c00c0e55828854181440f1400703000c295000c1e0600c10301c140e00564a04510070304183c00c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269914172 1250 269912922 269912933
    0x606061e080112020303133002030d030519020a020303180c0d030f050408031201030c290f09100e0405070c02060f0c07050303030405070510031a0f0a0513020c0c0a050d 74
    0x14002c02c10385e0180800c008081250740d100d081c0401401c041440441d45c00605210307043c0700305005c80d14241c29142c40f1101001a030300400e048200354410300d40400c4a46076910540c11201a41200350252407002071810203064010010f14841d42d000c0f00625035012410112940ba41101407119500850204540c000240501d2021078480850710b0010308141d00c03001002e181da40207036005e1010b00d955a004100300030406840201071710b01c052000001001e9403030300d083c42521210070f140d004280400c8080c2e00015107026079201440080a261020616080190080c911407000724000c034201000145254020502210740b03e82c042c107480c0c03614020502002c0140c0041c0306031010303400f03440300000c0d46517010000355010720f00601c0506034042c07900040002c41500003050380c09150510019621134880a80490309401081d903140e05008460b00c00200809041c2c0c00c001d80c07002007290351041c0c07072f01e5680c040c0403081d400350122030104c0d440c5400c12002000780d1003200d03840102018800001030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269915422 1250 269914172 269914199
    0x5100510090608070903020303030f0a0f02072006130e040f0f0b0708012c091516020105100b04170111040b040509090604050c0607051f051504050402061909030f0606061e0801 77
    0xc007020400079144401b2007000068fe03011490988041c3c1c3c1c403012028000d9035040e01c6661074801150b0442c0741076064005449240e1540c4281c2038050640d000150511820828012509500440c2800c59001741d280c51041200280c6020000030040b2001103030340da00c43c1c40c50045810340c403c5640d10300400728483c079014210040c051300da10300441406100c41100d00f85101c0c003a040082810440c40002e601c000e085a40040c0340700800144901c04105080c1030300b0445080d5580d001c400c1824200c80341034580036052810030304500440000b000901c00d06080c0203401070310b00071600350410f80c0351510340c15507403401500c01516a411140c25031001d0300d080801403420900c11820303207207040ca0070100da00000c0044140c5c0842e040d128010018100404800b246002c181103a0401881c1481c6e00492140d00031ba2030b03107226598030a40e44210090061308503c0c000c3d82c0c8450104c00c0790708246821409030045105040201e06511260183c40c020481360918000f02c1e40c0e40e42103244e20348204560703801c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269916672 1250 269915422 269915431
    0x819030518390d03020a050d0c0c0b03060105120c2713150b030f1005040e1c030209030303040c0e09120706020a050f1201080f0703050a0605100510090608070903020303030f 76
    0x600c1d41c420042e44a0f2aa811800001d50181c2c002d0003031001103050290404860700743c10401c016107420340e40c4c0002c248812400544000724051070302c0f0b544690043c0c070035202e41c20209624100310010442c1e100051802072007408034880494226054020500030001c0c0a072030465400390305150402098801540800486102d50b844009220703559072078000d02e9442510915804035844040007621102820484010b0105607030420150000b003044986a80340074039110388106040c00b034813503564800d4042c1c036500b0000805590341da045c185000c0035002c03064804d0318644111540003410b03c0d030000c60018000c403c898403943c135002c0543e840400035407041c4d8451050103814455144d440c22000060001c0c0048005807800039410100b0982c904400308000800d80c4d4401e6105100084c0c4c04224040c4469210b08042526111510a80b2001103203401040d041003e00d11401e8803030b0b6100d800042211529124000f41c2c0d190148200c0c3c0d11915408013030b406601c2000800c3c03481c2034a04806510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269917922 1250 269916672 269916763
    0x1e08120606040314010c0318030c12020705030111120c12181011030402030106050a05151605030309070e010e070e131103010f0801050a0e060609040819030518 70
    0x241603c0c1d9840c600382d031001e409407046584d503a4007080c401035058440d4608100120340f40c244000050354004000c0200c00c2001890340d42c40360340f041c0300380d8001c100c40c10140000234000d00588075007112800054010b42020308846510101003406000e60000300d40b19011003100801382c42e510500c1d4101d100040c1c0031404144d118001e00c10144041c2031151544581d201c19840d5a03d0406004160035030b4440e401080c0300d803003401e034100515581c1d90825000c00344003070005500e07a01e2480d211070160f14a000050840d02000040190444010905170103036a005411580e01c3d076250a95200c0f80c480484aa5010510f8021401698a045421184601e0b00e003c0042100700c405070881503541c20a900c80f034030b08820403d05008100082c064107520400060b0f0411403003849070329180d40c2c0d45d030140c00d4a00800203032020030188081e0074110b51405862010f800c01c0005c603200003c0042030101c0d0403821980c03044400041c0007001003441600c1d80701c00203440e200b103000700c6202c61310007207440d010070315 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269919172 1250 269917922 269917927
    0x20d0c1712011409010f1e0e1f090507050d0e0c0a03150605040b150a1b0305040302041107021003022209060807051903150e10091e08120606 62
    0x168400e144006121814510011030099403400c0445407000109001203441480c00c0401403148040803801300084030042c00c920b00303e401d40e500f4424150780280c2c120498a1032124100102ea00c47c036508100c40b170980c609107129442d9035220400803124262200b4002170000c0250100080254002e4640002940240d65241c0100300000c4c1c1410700544c4111007510003108514002540752040c10024a000e030340900c07000c8440c0e8000b41c412a040c0e0006000c01c1008201e2607580b0f0302c00d0b0100b68000c0c00c0c039901600e516056050141c01900907104c224861828002090101c4c80c041c000d91300b0860303002d446103802c074030000c0e003d602079008400310342400000c110032180816040007a210003803815040c000b0f11700e0b08000c000341c1802244d4011502902d24071200b01812050b403625581200d40150002040b2002122144080c103011000890144114110710040100c142c2c072805c1203e20070116411003021035420702e500d07840045405864548248a410002402190b4256100500600c03203403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269920422 1250 269919172 269919203
    0x100b1e03040221060709061d100c0804060804060c03020423041b0309061b050a080c0403080414010807020105091e07030f050303070e0105040311060702040603080f2701020d0c 77
    0x1124400f049903400c02c154405070a000c8000d0b044510400034004c9481c0482c0741c0000711018400c0c0019800095004614001e4007100f228072a08880201603440100259140c1d661000145480029502a500586040100c02c80719000f48200c0e07088801007100310480c140d604401d540c50710340c1c2c00741060300039403100c1901054078808040c10740b035100d00d51000181c030705c0b03142000400c07500c1c0c0c0b810600d14040704294041840b0307009410b850202056140c3345a8503500d0300c0340596180180d0380014118000400c010510911540702484460b07800c0e610038400d550b03101c4040b42654016107000099801c000c013a0703100b103568001d0300d041900341d403000c9400d402c2d6a5502c848119180342c10039200340d0004001d01140c642e002851900110382440d20030b00381825510b03141c0030300ca00c0354800c9201d41c074001007010840d01e0302e0b000b182c021504110090380340d02043c001841c151344030201ca80036481c00e2400d1200401e400710007c0c051002e0682c010854600819400d40d11084290001e8940b80070070764420 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269921672 1250 269920422 269920459
    0x6120914072607051c0507090c030209011101140a0c021e0102071e05060a0e0c0406091e140105010e011701061e081b030c0408060f100b1e030402 64
    0x2280180009619003014086a007662512421825102c01a81d040b00340304001c9035072001030821010110030aa0103800c0d6aa1508518014107588580c8400b4104180403241365015406000d080b1000e0302c9200c450304000e4480c2d4221600c150018100e10302c00b2011030171081d15a4811249c90540d401215014480b620504841c2c1d0708211854540d40e4000071141c00308914a84450403100c100741210b111405190343d0ec503251440100000720b03060b80e8050021000c18100001e00780e40402a008100e515103440c4420058101e0700400ea203031000d4000c03040e400c0c200c01d2140ca229440344005c4101180d081c00011180901105490341c108030030b08022402e0842003001c064020f00ba10b81b0303a0308030070710000e41d894030009080c1162002d0000c180208054424400c40007200b403242919503a03a00e5813001000e007050b0040340c05c612000d100300741c00c0bc040180003c03103142c00307010008004660141d07190750084142c406c2034400801510455074840d0650340d0b260203550040e01c000c1c505403496404203041d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269922922 1250 269921672 269921683
    0xf0a05070207140102070801050c0705070e01060215061c030f0e06090a03141f0603060b0f03031204020105040f17100902030a08070204020d0c08070e0105030610081e1303031506120914 81
    0xaca0611080014190080080410405005065401001c00107601d80903010b5201c0009800050500d04200c00080701036a600f5204401a03c40120b00c200340b03803290034000c2408446d01030820210309804440e40e40e900e40102540ea1040c8020001d00d100c40c210340c0c4402c05050030407903040440c455403410240c50506600401d0341c01c1001c0700000790b0903180d81022001d513112807402c7e501407464520410060344000c01100c507181000180d4615581f2640300403680e0f8820341d844001c004400c800c000c6400d524000d50085016141c90440e03509914044010342142c0303200c00000e6060303202215801c0003d254901400e503841c00100b006051083c103041a1050320102108640028504420000703115080f82042103000e400f86001030661a1240200c2c0f0040180c0c0114810b004959000400c0310503032207801a6480c0710b000d007200e40742c20302c440f60b0a10140c1e00001100420306256410b5600c98014039050201c1d495a03840414482c1165a0a4000c1211540540700d280107035020f1850386108108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269924172 1250 269922922 269922931
    0x506010e01080d180e13260403080c152e060c150e030d090501050f0f060609040902030f0d17090303060904050f06160e12030a030b010c06140f0a0507020714010207080105 75
    0x8490343c6ca00040c2c60401c1c1c03c1e0200203070021f0018007201c0c55100c1888503c06550540342d114055540d40d42403000110310300448002040314941a600810400d50942da0b100181108500c102c02c80c00032818440070190240f5018007000559429030300c034003098124034040083c05401500192a0b00c41551850440d40981c0705440a45c0d12041e41800f000024865690b0110740304d0058580b600340281e00400030700015181d584503030b101184110003a03a85610141350154028120354219450b807003001d4499080400e441c000c81c4138020540c42465142c41058807603a041c0026515550745c1302e0070000d0300c0c0401f400a036114402d04c1c0c0f0400c40b1001c2081000e00514040c207681644100c11400100070320350722480180242c2c8105240c100310900003083e61a801541c5c00e000c5180b8a400004961b071044245024203128141a0001c4030083c00307410f8a8055040030852103469a0b400c2c86040644074180d43c0d03400180d009403010410741c2000f8002e540482c4d8148196030a03956180161400c0d12405d54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269925422 1250 269924172 269924191
    0x71b0302010510080307020109060f031d0a0507050612061e22293105040308060402070f0b1b042312060403050f0d060e040506010e01080d180e 63
    0x1c09002c1c220b40000b0f8040e0003401c4280c019445c0152943c002010442203128038800c0c4844031401b581c1890203600140903400c1400042150b1403070071408030351380d1a4a50415280341c01100d00102d43c0e804c10380201c607109404046802d85a4070744409003c00c0090000c420389030211200100d10003555280e1001498454034a44000754140c545100811159070b03000d032044461204501d00b80030f000035141090b20f03160440d410320403400d1404080c803045030f59810340c0102808415200e800c13207411f41c0c40300340558003d07510750404c0d685200c280000c80c42032080c090001e0800003041400a20700700e90107a4000b0801240c0d54034041605100801e42c2c200390000118240180341440c03401d81422121400c1d40d00849a0144c2001d00c004070390f07100c1d4009880941000320000e10701c042401001f088945410050754204040c03951019808200c0300305640440d058018400000344101100326200e06844900014001d0114240c0007a64030504c901c4642005039041000050169502c40403944110a0309 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269926672 1250 269925422 269925431
    0x1505060a0501051623120a08070315140d050d020106030515010b04062d03021810020d050d0b0d1a0a1407030207053d091208071b030201 60
    0x800024038055000310741007010520102c0780300085140e00c081c031980c00000d0928045004548403100c1041d498176100103108903489600c0301c040101c0109004406503072001a2034039241011801e03620b01450070380070311065a00030700602c0c0266040b15402c1c00000c00000c1e07903c24a0741c806e418403c0107040b040250355201e40030418408103012003c0c00750203100c8201d401d0341c141444030074a4081d42c060701042040c480003120700310343c088030f0904001001984590744403d0900005020354081c3d419801a0140000032030040d0810903820f1000e28000d4000d4070b4017920812007140e841c0c1040b444c180c1c055840d455018100e4480c0150700700140d024507034106952a100c21040805d06c0c0c041d0070840e5080c0b8240c41e40c0008403a00350300a8004100b4500560b951040f814460314003141480b11900c5414000044461840c1c880d82689403200c0e8003101c0308480c615151585c0403620b03032020160050000c0c44440c64540e1080004507484000d905000130300d140403224010f640030280e141140503030b556 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269927922 1250 269926672 269926681
    0x4060506030f0f070e0603030706021c0b010c0c050f04060b030109020417030c0a0305070309030515150a0e01090b040905190201090909030516031b031205060d03050304080703020a1505 81
    0x70300c038030a0700141440041c40c02c2e0fa609081d8039624038042c842c14286008007404a0f40d2681c00b44122408582c2000301075449901c3c610f001c84c0780381d10403040740c11928a00203680d8060350080000f100d01980044411501e1880d01d001d004c0200307a40a240342e4425a0b0b036002250450083c4003850280800d03000040c2c65509200c200ba011003000175040030203500c01d004600e542072000941d40c203515454030308140ca47d40b0030b18050703d48d01c0054200400c0c500032281e0305500c1c2604207001501c00d101d1380c41400070706601d0005101c0540702d54000c1c42d41030781203100188801041a00080903a28001c2e200041e0303400700703440c0c0c1d13402e1100311000002c103075104140e13100070f540e44150380c40b0240141240420040005550140062045404014088850b5044131040c90700405031306011400c61810b02204440e6441c0043c81c10300c004041d0002545040040307000d5003881f10380c80700038a43c0b41e182d440c9962a41d80b0703400d02c02e4201000440451180c9803821000844900084080e60418070000c555800e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269929172 1250 269927922 269927929
    0x10609020a051e04030510090203032818080c1c050102070c0303030e01060e0403030c020a140309030111040803090d080706150e090d141e0304031707110c01080601120504060506 78
    0x3c0300303888054000301440140085800410554251950590001080780c45440481e085002d05151101505d07101c9201003d180741c140f1006002840c10780d5084000051101d003c070403d61703940200c0916500c0302080101030300300308007284079040d030104000e000c10b540742d501c503804e80c0d01c0310310100c07a44080301c40100100740d0140a07038488984050f00034801d030750500009036000500100041c040503201c680340500d5a00a12642499030780103410401d92090f006036065881d0b106408250196180c00c82c010000c004220695043d5032054002e14038188030a01000003960340303c201030390012010440c03400065820300c6000b401c00c8000802c042c074036191990106d14448020714054103604010300001a15a102c0c400c00c0522149481881c1c41c0c8149003040002620503076078600c000b9000105200601d0381003900020400c0d01e40d41150010f80e5004000c45840d05e04085890441d401000003600e158042ca080940c02101854440d00c50700c181c2080100740c070300594003500c60964444c28070005d0304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269930422 1250 269929172 269929207
    0x905030f01020408030313020613080c0f0612010519080f0604061404030e041a120f0f0f030403030804170d0e0706050a080a0b010e130f060e0403050318010609020a05 73
    0x500e10000314105890013840315202d10000b005200b07002c000c09601411036584500f5110105000085026002d480d4001141c2d20210016201e116050080041131249003420443d0410685400494400e0340380c40184006402582c0c0c955003081562800420072042c10800440d07910142401801541070901300181110346490032404000740800800c401f00390801802881c0c644181c800040d0143c08010100c2801c3c0110041c507482101c24800f00305103800020003041c8841c400003510b0201500030741c55035070394802112509058100b84020030100340a01e100b568400c0c040d021404030280152807054040d80828854000d59a990006150002d0308010180150408d8140f02d0314042d01e2142c003402c0c0540c010b1001603443c2d200e0303c080c03009074440c21036940d2080c0003905200914070740100c40341c003401c07004e80d010003140e25100c0700040c00c1d1019054a4011509502c40c00c0c034644038072040d0303540d5900030002034070340759260040000e08200742d1000300300c0e02c000c658a030307a1541c2e8904961000c08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269931672 1250 269930422 269930443
    0x803070306031112030a110106120c1d0603070603020a02030d061e060302040602100213030206030f010e0f1b0307110f10060f0503030f0d1503080405010e01020a260403020a0303090503 81
    0x145141350010444040000403240c80c2c086034208507070907150b040071550241600d900049000001c0d050a202045029180d880548008042196040100a1040441c0c1200b1580f541c5c1c168407100341004214040d0340100707034840c02e42c41960300c1c08171603080039802d480e09540302a0640712000c08000b6880014105e2102400c901c1c03a065203401e281140080d9901c4400e844800c03020390000f1644607028107032a03d00300840d806801a602c03450308840550714804240700d01c0f03420b00b5040001604001c2c11882075841b030031411040d2211023070380c0f016400054100521003c140080c41c1c50003040c5450400c0507808448208006199000550a1090030b0f00c0e030036403186001da109910180210341d40401034400c0b480c903400029403568002110b68000d0b05c601d009500308510f960001009000200000340140c603000e0b01d9108120301560012a90b40d00c008201501c0d80f00d1500d003030882d00b50200e04007201c6a807c04203107030805441c0d40016908000942c41180454040c1e8400c1006040900c03401005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269932922 1250 269931672 269931679
    0x1609050609060f12030705010606081f0602030d111314010e120a081c0204060201060608091b06030a0b120a020306090d020d0e012006010e1003020a03140a08030703060311 75
    0x1c50501e0000b1400740c014525079144240131001e40004011000c1040d02d102c40d81040007403014981d40d110203001d0302c9003501d4420444a510740c1504c50723180e041004104580441d4000c0d450400c0344801a0018621000d030f1880114040010034001c468444401026180701d2501600404030312001400650051900c0c90041101401060a11401040f25414142c2200380c4540e41c0d83e10000b018111007121054600407480450041281c0ba415803100d0259142c2c0e4886100a48410310066540c0d00c011102d1300d03086924020194082c01d141d00515080501c80101250038400030000aa401042e10301f503c4c899809000040c0a502d4100002a00008004043c081a1844480083d241d07840c89200a05000c000480e00c50a82d106015480e01200d0b40303401e010440c005614041d4850340203106050078411075038003062101a0440002d011264000c1003c4803603032941e81e0b004000320510347c003441e150060214800100e01b400000754410700b421303500001c0c51030651a1088214810708416800f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269934172 1250 269932922 269932939
    0x702040c270e0a0e01021603020703050717060a0f060503030403110a1706150f0a0b07050105010603020c030417150408070b0915040b040215040605091f05030705030a090516090506 79
    0x1003000301d029680e00291042c2011130310726441c4030428007a01c200c80b51403440b400903c603d40d05240c0d0200d05001580e20920a4912070f40d03494260710002c001c2c40a400c1010341180f4040f50b41e1500650001d100c00100c1c00011a0256440c000030341507400aa005682c691074031640b0a8091804d49000005800c04a40034400403415644083d0f403001c00070407850310b08000700600d030440d9480310750b101c20340c020081980491940741d1400c010607401281017200d00750b00304800815018042d00941d4004030360036000f0b504061502d1500342e040120709090780c0b400d015a04400380501c1d210080070307100c1c1e07004641e4607641d900189485244120018810095a045290f4100880901111241e0407a80041740608140c989000003461001e00300c41803000e03041c00007400680b154001014089241084404560400808011020288070262000300150003003000800a074001d0f006550011003a540001e14070446590781c52810200e01460b0b144007040b1034081200130450700460713600c1b80040c1d481c0e00c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269935422 1250 269934172 269934179
    0x50111030103110d05030717070203010e071a0d240e0123090a33060908060c0c0f0f0c09011e0501200601030b04020312070305030a020304080702040c27 67
    0x40d5001e08140010341310b0040e180c004014003504005441d9100d4208a40400c1c400f108480c1e100c5592003010100d00070350800c184040708070000b1640200711021015101119400700040c0192a40000d4100700754540d071340381102c6d00c00702105111130a040440444aa402c0c1409080218680142d119031080c1100280ca200e40d4801042c50030702503c0140c80304c502a450346d40e40c41d4081c0c40c000d02c0c5900b291941c1005c4c04294045100070465440f01c4c030000e25002c82e1944002c407041d42d824000c040c8035602c010041000894203100805022020314140d90040502002550410580c1014044281e2141c03c01003405d10300503401d00d00411010070100d8012491000120002d08244101414406020816510007040c00014681c2000001c06d8a180e5038480c603042d001c0c1d44054400f40e0281c424144400d42003099030080700c49423a0107845d4541182c3d51034001300d0103540000c0c401c03140c242d4180300703500040c0c496000d04401e02c4000c0d121510301c0e41a108050201110144084400d43c64028040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269936672 1250 269935422 269935433
    0x9050a1b0803030c19031103071806020a08090f2404140901060c0204050603120c0708060c0703171f09020c0609030a0e090a0207050f07031202160608180118050111030103 75
    0x417040819100b100b03002d20b050000c0246c2c001d10804d0200504140d001040100403544110a1240301958032101580c49445000480e5180d4600340001d044600402c500780180c54408017405100d000149030b48414920030008040001c3c07100c00d0700303407110ba000c03800780140300e022511261a80401c3d44c05c0545c5601d490802004c81c6500740c0d020b402151390b140447c01544050212021000704003665a5852598406860b5500203e22403040c46010b044042402e01e031792031080368906074140d6910113070540c02c1c91012180d54000f03041d03109000c00b910103441c10403562200300f10080a40c6000140c448240c0e4103d035003402d100401c45412a0800c1019802d042d4000c403005400d607900751005541d958a07141c1c004000d1042e120301074014070030f18240608c0000300041c075000741c034424940a001c800307004070143c0c0e132500d41002560320041c400d07505100d42d030708c141401540075089a0122001d0b9803d00c03281800c584d0031880c48082d0384c440c000464240a82409200d194011600c901465585581c0380c0c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269937922 1250 269936672 269936677
    0x1401050403061505100e040e0a0c170304030204140106031a03060c090102030c070306020919050d020111031210440a12021609140105100309050a1b0803030c 69
    0x1054281c2c0d844441c1c0c0c000c1c0350080701c0d0000d4840a848045d001d07903400301c09402d0420301c5402030322643c2000070704d01e100320020a89001082d440368845a00324200f810309620003140c94101001440180800000740e601d40c0250421f0741c12810700030900303505150005090380c02401c102c0c21542d070301641d800d885880001355103070b0180c0d8641c60a91680303102c00041f400c62040c480b107105c182c07150035401b005000056000b050310131801c48091080d08a000c4280342c40c24240c2c8a40c42d4011800e03810b260165024000310308034110800d040d41d24103080c4641c03c051144050b42d6900c5072025941d402d102c4010340d440144201e420079481e58100c10000d1103032210040e4107103044c0100d40100041016540f10801041c00343d980d01caa28450304040498009588003039840031001e2441010b038001426901c03520401c0c0d0080101141e0868980c28502406440709207003081c5000c142c3d840d15900041203003405441718003403062402041c2c4000c0d0590108031100141c006013001c0d04200188203840c13212108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269939172 1250 269937922 269937929
    0x327040e1c030b01110f01020a0e010c080d11040905041407060315030210140403030302030f1501020a0f030504050d0305030402150a0f0c0201090306020a0f020f121605070b0a0807080114010504 85
    0x40c0843c00075115001201c03c0214130aa04641d4444e00000d00b81c1100306401502e10003581e0703a148814010850011030b1301540349003011b042586d080115030316103040c5401245007160400451403038582d49420050449a04039020f8a2050342000d64505070f100a0080b0401021540340610030150414400e0800c00e6030340c03000a100c0d2a00315149101c031030140f4044c0c40d042c0d090382c03505900d85a0b2410054061340c400c4903004040c803485000a045e08046500c460150380c81a030080c900303501c107641c0d840b680b072200c004140d049c03000c14013000500b07599026001852520a940d401d48a0903e03205100d00700e5002c80205444c10030901c4014009130740021150007040003032030700115075402400142c070406601e070000b81c04240001080b8040e140c1003001c09103600129421204a440314401e09501c0d605400b40c16002070508100c0300b0300300317180d01c280b60a006000d1015544410390780c138107504442e48000112004030b0281d004200d07030180c01c030380d055005190025260702904c00042c0000d000d84031310700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269940422 1250 269939172 269939177
    0x60c040b04180e0d050c07060f05030a05090703121805040e031e0c01021b0c010306260c040204080c090c070203060106141908101a0d0e0327040e1c 65
    0x40480074444580010560a1400080d1001c0344c510402c01007040c0d00040240e5018401c0e550001207061042902c00250005a0f940d01e09540b103560f10305002e004040c02500c842c1c403034200d010001c5021000078070a6181183c0780e600341035121041205031907140d544039034407403490000000b00c6460301200315041c41808038003072102e2041207006e1500b11301501e14000103e610115526518100c041d14241a06900400b203079910883d19004509444c01409580049060884807402c1020501054403401e041102651040e1185a012400700d810540c0300c0003141d449075603000001d0074507904847d0000514048076162a001d81c0200703903502c4040c072450003007010303100203000c0d00050b0b607007900e40411580302e01400d0840e89160040603548240c0f0060920040c1c3d15000901c02160b40c4d84d00d40c9505000d52490800540c00280002007002066034040783c00104150003259088400c40e083c1200c0013000040e000c41e455050004580c0d252152000ca54000700e40328240d0301c80e0424404103074000c2d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269941672 1250 269940422 269940449
    0x1b071a04150204090c110a2604030212010b0f01020703080301051528020d030b01020a0b181606030f060302031b031e060a0e121204111c0302060c040b04 67
    0x189450121000101c0d45140751030700c0801c0c0401d030035110360442511220b155031138000c2810b04030070b015240e201280e001854088c1c00c801220160007007003403240c415010400643d080c10390383c0c0c005c1607062880300001241a50344460019042c91300c100920f00e002e10a200030b01c521801c5a440c040d4038031042c00340502c0346615424213104005444221142d909610a09009142001d060790210354804811500903005003e417010550340319110780007090005a00802079044181c40f42e1030020805803000058500c50324900c0c80402e0b0811140400070f400c0418020381602e4510000c04a0b01c101038035003210b504140d005c10250b580083d296044140d141607040078462b081c0d0000b0301e03104505040c4514554114982c0102200226401d40711701420542030259042d5107840c11b0b2944a007808034964110107200d0201041070300c00d28560302c14800c410480c141076400b40000e21081d000c40c6003000303490741c4518030020554180629a084030b182c3d41c045040c01c4c144921015140118001c015110500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269942922 1250 269941672 269941681
    0x40e070810090219090b031902070807052407030501060f080619091e090209041e0c32030c010c0c12030305060907080601050307030c030905070e1b071a 67
    0x1403201d004014041d42d40e04540c0c961840b015a0000c018000d0030501007914828001003001c0c2800490303200c2d81d8101c020b81c201c40003285603100203420a0b04e040c1c0703a1441c180001c500180d401c100282100300c0364400c0826805800c0680705c01040d0080c064400c06040a00400000c0c0d04810084a00c2030b0034241311801e0b40c1c526001c10004680d95071201000c1d5074100001940a2150744240401486101c44e404c80c801c010469805a82d040d20300250000324840004001c6110103235850003200030308800c202840c0880d1621b4000d610b40340c015046440b00003203140908000800024002a80d8072481c411450306540080d0300d0b10501c8036854140f1061301e0120017004010301e401000b400d01d00781d9042500e101c82c20020001c000031100140542050b0002c109410300503075502e445640160748140c40e40d43d58800441c064440350088009040d01e40303e200c000644140000b02c041c01600080d52081c0c50720107028030b0001c0e85000f8124111100b0002c00010800d43c0411120502c02c601d10740d400c5454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269944172 1250 269942922 269942941
    0x702010e0609130203060406050a0e0105062110231e03010905071403010c180302010507110301050f0a0506010c0c0b0c07150c02031204060e2e021005010b040e0708 72
    0x2400c5072141d401082c00d143c0d1150001243d0146010303070025a42040202e0b21a0103004100e505802001d0f2003c8601c0010889440c0034001000d000700750600c0c0d07003104802c085814902a006a802c501c04280c00d250501000070320040703071031880b1010429601300d05403110202d202544101d01401469518294078001c64900350821140d40f9882411284480da80d09554210b0020038040b462095003480511030b020f91240c10350610459600054031780b8507255500664040d800050101c8805101c0300791001150703400c2c07241c82c0c417900d100e90464865140441039201221002058241071000300360410003c5090400c0f02000d0719440700106585052032500d40e0301c2c00030507900c40051000c15072842402140d03c5561001510310a80880783d5202020502421074090342c05403d0028842d001c03092641c2c6040c500011520340456a0b1807040746426406080310726005020401503845005000a2081e26114180c01060540781081c246420310144244a400290244c4104070b440702c0820802c2c02c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269945422 1250 269944172 269944177
    0xa0804140709140109060605040b0309070b0c06040b09191b050409210509010e22020310140612041209080604150c031104060c06150905190905030702010e06 69
    0x40004100d5624603902c0ca50400a003c02a0b6102d03420001c201c0001600e8416002e85003e54204e601d6440c103160030100142020f80004004a40e0741c032030840006070f903e00400003095000381000180c030092a01d42803094401d4400b0b881c09411364802104054500011440da001d81540f07c01e0300111408808004280301e441d80d08100d034480e2810700e10030100103109110206c1070b020350b078480081c200300080940320343c0507000c02e00340480c2d0290035014107403038641c9010f034001d60041d89011040d900c004040301242c0048035103004081300080e0511041c01400b14040b102c6078102c0e04a0300e0b15000541c591200c910140000b0035000301c020034040ca40d402003800c14040c0200703038101e40346c529080c10006009480140c00640d031600e03040711800701c03e00c20301682403c6182c0c414441c1c075040c0741010495512080450594030340c0c0c3d403100b0b040c4030742100842240c0140100c3d600841c0034104504580c40c050700c104002903c0e0745c07408071039000141c00841621062078090030541c00755000a004a1a5032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269946672 1250 269945422 269945453
    0x10c0f1e0507060e01020307080f0412050304030216090e010e010204080a0308040807120c1e02030604150b090103060e0f0307113706020f0a05150702011503240b060a0804 75
    0x207410300710300d6094904e05602440c440c00160341c900090380c65051054a1f010340030394000c3c04c052512104000010300800c01190020300c00e1048a42e8a600c525006106040b59040309405a8580d601c1200c900b00034091041d03603006030002146080c2c501242943e4551012000400340a0074000142c10700c0b4900095a161a40012039812280c3e40104020806d1a014008550461041c0d800c00300700c01c0e03903107151141298080c00a00541d203458541003004200c0c8154180390b661200d010320321a49808001900840c81880045841160340122a007440200e02c0f402159500070310980f03000c16039422050564010036100f203200307224030040c0031400c00700d6403104d10904000481499020f520038030380a411198598282c2e0740321160350000b1903c4910300320002d407031680603170030500c260201000e03041d8112506000009408000807072440040c0c01940c0241d91030300d50003402c04601c400408406101c445452403c0240c1c40010001680d10301802c50160100142040003a0400881d121041480c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269947922 1250 269946672 269946683
    0x281809021203070b1003030507060b0f1806100525020301061a070c0b2703070f06090f1a120702010b04050a0c030f0218011103130314010c0f1e0507 65
    0x1c1d021011035990340d82c8074440442d96000c2c5180040c594141008a01041c0c9038141d07600c0f4038284882e02c035900078240b400211a03203ca2900690800d55540500b1b46038110314806400e5200e14040080001034540d01c4440d10a00404200c40441000754007142c4030960305038103451000404900106e401080941c008141e40300340a02a4000000300c0405820070a1190070302150340351310b40590703035117500031503c50070720141e00f40900541c600712104c499018020040c0031a203250b40e0740d500c0c0030103950303e5074800004617070724440034004030000802070704c0540320205201d02c05990302c0d041b0502d18424101d41044000c82c10000c44d40552013900b01d08140c0500500074405405c000300920300602c4900d82940110b80b0b4124029540300340740c025220300101c0443c81f000c0003880c00c3c2c01541c007503040007880da00f81c0c002042054103a25420444501860050076503a0810700613113025402c651200484c0d0701882650350400c1d00d00b503441822407814200c205014030071450200402e407418083d51500511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269949172 1250 269947922 269947939
    0xf02040f03050d030b1516050607050c06090609030702090702010b1005090f19051005041e0f05061911070801060b0a17040809090606090d05060628180902 68
    0x30018251012001a02e0041c0c0545801c0380c08160107400b22040040b101d500440c0319840b0203a1030071004040e044400725a0382d02c24101695903141824050110344030808504046640050882d0810003c0e0713008482e20020841030a20355a681c0d074a0144000084c800c042120000707036814800c0d0004070a500001d4880304500315008030103001500014003c9004548a1090b15503505d00a5181040d110923410034000503401c1c0814014a4021140103c00344082048001560b0481c00c81c0b042d400c10b500381d0b84800803400e05961b1484842c066000e140f04078403c0c040080c03080c02540a0504100e2203080203145400d12084890400c983d81e80005900e510300f92001071002c45640040a160b5400d5540340c0650450000075000004152006842c10b1424000c8007000c2c00d00200640e00010003c00c05424103c00f0400120030039040c2c041104c039900300d02c06101c100c0c1022803484440440c0804549100000c05020401410f031074402c1800341e0300c41c40801041600154400301c503003034024003200c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269950422 1250 269949172 269949179
    0xb060418030e040e0c151b0706120b04050402130b0301180b0f0a0c09060e130e01021b010b0310110405060310080706051219151401020606040c0f0c060f0204 69
    0x208029025052030f40194102264450300100120300d0100008004188803202c0c80c060350303480e084da00911280100c0205104d00140d1301c1504000000091143d0740c0d03082c00b500c0d9000c403d101524020000e0130301684c105800c1c000140c2d241c00300c4c1f04442c44101c000056900f6030b440043e02400c02108600da60481c442814024007100308052842410094020304a5413101c4440c80120b0b8940f54154000500c00d480501909201d1a0000c1c1e1010b0002c00380700c1c1c042d62001c506000c4400614040c04a6980055045410038201d010708942e11103001c001c1142d80125000700743c644a0405125404071307070b980c40b101c100508c0c0320203640262002400b01d503142e02d4084650448031059018032581803150104c002070861054044031011a803c00324564591150043e01c1083c910344268180403640310400030b8111908012104001d10004080000f4005002d0000e0309011000c0c11081c004c60400c0032811003150400030781c03c500106032904518090041c01d20a0041042d5103180305035500028001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269951672 1250 269950422 269950427
    0x906081005060312040308070302011104150813020109051c052d060108031902100903030b01090b0c061515040e0f06040e0606040b060d290603040f0b06041803 70
    0x3a0003490914410045900c48104141d600c210103e199040350364100011300c0000d10b000058114117201c2c1c00042520451032450592541080c2c100c400d103010007884440c0c03619440000c2d1034000080b500c0310000200e0702e07000200145054041c5034000d1a00880c80c0102e802c408004d0052181c2120a80310394442d4410025801080c10110480c080c01880e100d482d07040c0085840da04076000c40009600c2c218000e12020060088004c00300158001c00104254144080c0581440340c0e100740d80001c5c45651480c005440c1103415044441400b1080c4056183d00000140d1203030040c0040940720790304001000000c940d032031800d4507049003c0011900280203202540700c58001d0340b6003240f0720708590300ca905020850b00c2014101c030007584180b000c1015410241c0c402c06100784090b00c018500030201e502e190640e5420300d020310a6043e005050051001200f11000103208100d0340c0c05e2450074107846141000d150300c20050300c40810440802c2d22aaa107501607a00e46c500f4035580b200203141c1c5d0501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269952922 1250 269951672 269951683
    0xc150109090c0515090112090506072703030c0803090313030503040504232a1209010e0a15020a0507020904050c030c0108091e030d060b031506040506071407090608 72
    0x2140c0c071000007400800c83d8582800b1291190788040503030713810301d840c00c80112140c940e600340703445109648107016000300d4000d10016200d0411512803841c800c4005c10000d64004d40001a502400c4d00043e0600019a00682d0030718040d402804040d12612004c201c10f086101702e1100003e5115228800810858088050012035504480410440c01c0d422100707100800142103440148041400081d541c0c03801102440c48400840341180c56030f0f00c0b1040783c640d181c0c0580640340c1541020750070841c06400c02d00500c0d40b21001303000a0000150b060380c0e07091003250b41d940c00c40e1856401150709640148220151458180c00504a0155042509040e501c03020b00c540b9640c000e001c0c2d4660f52142d035004503045402684d801008081c3c0c2c4002d02d4070b85400c0071500885042d140420805104410514014503014001841f000307a40c2e810f001700c4480f503921901c3c011900840c81444104017698550040d98009074010308188240380004894034180016a00031802d554507200000c1540d40c40042c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269954172 1250 269952922 269952941
    0x50607031d06130306020703020c03010e031b0a050604150f110406170408030705091216080601231011010c0815030c1309020310051e0a0b030c060c150109 68
    0x40590703040c1c22842403000c0743c81840070b00d100c20262200100b0001d140380e801401010b010388180e07141e50f00c0c0b0000080c01d45201900e1001c05038400f0820381040800a07514400601c0340c10010164000e040d69440c0d15010010300280c12040ea4403854418900e894000030010b040d105010480380d0000103141da402d400c1405081d000a9050745004004691444128012a0411512800e65a0701401140c0642c01424095002424042c18160341d03076003088603d582186001c204418541845e070031520b0100143c0c0a16164100707103100406840303440e0395001041405a0f0780003165a06804c0903107900703011510302c074100d40c43d10314880c4481d42e0058006029001049025a451161000301551100004151640501080a410303002050380d0302c4002d41c3c40c40941907929201030f59405004590302180c0c030f002c80c1c01c1e06803000200195201c0b900d592042c86c4110802207070981b5000300380d071031105140c01c9000717010000d0600081c05040040e005803403002072124503150307160300024010305803810b0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269955422 1250 269954172 269954207
    0x306030b0a1d070605190509031b03010f050901061a0307081f0e1602010510030302060f06040912020c090709080a1103070906080f0709180602030c040b0304061d010b06071b05060703 80
    0x1046c42c40941d2003081168000c03600140103209c003480c074441100904c022030711040c0d81503607107084445006a0b40d010b014402d41050f00000344c402c4c685426070b2840b2070450171003940c03100c0410402c50b1054002d40102c0d001fa1041e40401d00c034081d14000d055006a20741c0040003000314600805c0700021900c000883c1a07080f6030700a00c5180c461002c041c15450040c00000c016801074070000300c149801030758035680110300610100d015541a10341d02036680100c1250030058000c111003441605180c000d4a0300840345d494807407031031b42c90072401a40b6044600ba008040360044210701c0c0d07035550100421405460f03417032410401c0746e9940880703660340c0c8204940100e16024070072000030328031b4051260301c800e0400116a844500c240c2c1c0d071184000d50008182e004040828000450b20202110285200d03d120750720020706501e1038861903032820504042e40c440303a030400a554815071560800d843d20154032420340c51500c8003d540c0101c1700c0f8450b410a6404c4480810301c1400d0591000c82d8040440d40c00d0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269956672 1250 269955422 269955457
    0xc0909040f0f08072303190825020a05160b1204061103070201061d0108030a0c060212040b010504050a0e0c1207050405090c12010b06091507020a09050603010c0306030b0a1d070605 79
    0x703034a21a101d0187e0340020504080c08291640d005001e0f28010307612000ba42c01010030341a24000d0103801d17941c002c80c42c500590003600440e00708401040340003c4d5100c4030032078190301880d1203c41000361242c00c0f60180032900c020003007010003070940c010700c0d411442c0600c0142c07130b40350000d8000c2c02441d02c0e210b44072794003503410a40110314a06681c0c42d4166005140a1440c0500c03040d42aa580c0c012003c080300c50781d90030000d4861315441c908140307019901c6950010030b6545044200000e685c0701801d40c10003e407030320054407008040055408101c0300203560000100d1080700c0c8042c1031255070303440a03405c203082c1000c02094100100349400031b100101d58000128141c0c2d01a00d00302d074105000c0e80d8022030200004a034900e8003101d4a800b4800c10203003d45091000d9010480c05502a0b10200d0059125002d1120030303c0c0a0240c0c0d04c4110581c40c0401004c1d186494006220760301629181d65182c2c1e035400c1002c01e0001d0000c00701070400030002c0700d01650340c1e40001000e0b0b0b48040e0100c14202000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269957922 1250 269956672 269956733
    0x81b1c03050405060708040c080307061407030b0d060f02040801050a05090607050a020d0509041d010b0a0b0f16140a0b06010806010f0509091008010606020309090c0909040f0f0807 79
    0x1a101e02070055030400000e12103a0f07210181502c1d00d59014206880d26900c030b51001450303100410052198030321030400441c5010206242000005c0040c0c2030105140c21303d03150285544541030b0122001d500800301040400c08902e01600a00c540e400907203195082030200f140d10169900600d0003004a070003140c00550b47e500084070315015400c514401030300030040301240b0f28030403000707000413046c020400900300346841d07038800e0422074011302211140d46034005003401d0315040c03006400800300f44004500c2c140848510152512070240c000010a0190030110140000001c141d003542c1018000c5403061850350500821441c0200c507114009072550001500d59403050881103003a58840d183c050500104508001c80c64200034036040003500d15a4000511650074003c050040c039054001d541c1e55901d01041c45010311004041e060b44110070051464035494030f0329400c0d801608424414500e12591404510740303403d604c0d01405680d0040340302c0742800300c10860718080d808100d4001000018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269959172 1250 269957922 269957927
    0x9030706050c07090923060603102016050102030f04060612020105190c02040606050a031a010c02010f020109080a0504050415151b140d02120322081b1c 67
    0x4080a040c82d0342c01c0540204a1004190024090a442080c0b140d04c03040d0941e11080000000c00340d0480c07664405000d00c515404c041c01801c41009000000f44100e840c80848569581441010102c8262000507481095918400c402900c0d982c014020340d07480c1400d2440b51241c400544040d0399092805000041e20101d448041d5840da90607110320341461340b40d0239201d00f50b0150a00c81c1d000d0220000700100142c2e180c4c0300e10806404e498031565111030000c00d000701210784604450304910384401c1d801010340c0c0c00c8222080301541c24a04643c041c2d202c804101d02415512800038500305010552080054000d0050804c0e214191004c01c5254141010503011451341d00c43d50346401100490515054441c540010300112006100704000b5055a00c60100c201040381203803213034001c807506103d2a0350500481007000300c0080000e0842c24540d140c00581600009650025040100201d04000141e025150300d440300600308030011065001854481019034000d080ea61011814610902d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269960422 1250 269959172 269959177
    0x9040b01150e0d08030c1207050a020d39140102041502060f010b090406050604030b04020406050901080319110d02011b0c03080414120f07030305100b030a0b12010c03020903070605 79
    0xd0002d00c42c1c61041030607120b40b4420b40c005001b6460b41031081001b80340c4910301e15150780c01a01c1d1076840366600e0140c61002400d008410000004002c0ca5107211251000344010f200b91441040c49048080c40301440ba0b001040340140d0020080c4500060400883d1410740c003a00c110f4680822030390900b8002c900898440b0012200003041903403580040c45810350130f90141064a10140000030303455181c0000460340d400a0b4402c94010000000f04403c50a240c0500300040409888180c0c4950409490072346a000c0d1800115032088035280318a5424441c0c01e88603003034280780f03041d80d0f08031001040003030180c00340c60321203982c80c441d00030380c600814410041e000c5003e13090b83c6c4012403500d03036681c1d04443e000480d226602c07511400224450500c2c11a0052218250560582c3d035138100c0c4d890040c0988000600404826005074400c02c030401d5080f0490347d00181c1c5e0980041d02c4d800c0714000802a4140c0c0c24480115880c0c080c0d60a1010303096801814214800c81c1245c1086580701811185031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269961672 1250 269960422 269960447
    0xf071509020a0e0115110313080c1e030601090203040c0f120302012904020f1201230102030403110105160507090f0605030304210f0213020403020f03011413030e09040b0115 76
    0x141001724840c40e00ca201c0c01c44da100300001403094901c0c0810165581c1c111442036001408190041c0c1030b00495841d1203500d2003814940085039401810380400045c0e100e440511811a00c1e030340000000c0c080041403130101014051680440760404d8450000b506500d00082e0210090b44c44d10840381c822207428030303140328280c204500d4000043c0d44442800041c0d00890321440c1101010f0005145022070500c8140c0600341c01e105a16014002141c10049680340c03c8803281990000c11003071002c20103c01d80402114021f080082d964140d11009241c1e45841c490044c0980c0203809010504d0b10355604400b202400c1c4800600203181ca950425450740308910400c15a0034210200c0101d41c969250290100d0703020342ca000c8000e01d003540104004490b0071100b400b00540c0054184110320b003a00701061a104184c00811030100003090108207888040c0c03164400c079800a40c2030f1304240c4101116031802c440a0310b190b0650030640303400701c1d0409081c0580d0b0505038400e240304120b14825000030688 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269962922 1250 269961672 269961689
    0xf0219021b030c190806070804021804030207051e0315070314160c0c120804030204050f070c33050109050105031219140a020c03060109140a020f071509020a0e01 71
    0x404000e804020081d400d0741510f261070403c01030700044034401400424820003198039001009d00d894030410a403c000e24001c401e611035007100340400700b82c1c000f8041c401e82c3c000b915851009803a00100d1440156141c0b500f613810310912003c0b00703810035464100350103141980c030207001c100c20000f0900c0d03206030200c4029407c08811403d01440701d2064034000040703400344a01d9800182c0741c036030369402c00d00c0c030380b9081e60f000c00001000c00031410a0b00c9090341c020101d04854001d070815840060000301100c80140c9100342c168681808078a00c80d12003482c0f0018000101c0b4806a0b40400d100602070920440540b90f1a20000140e107080c08a0010140d6284003165842c191014800d8200c2010209003070b0204a041d004096142428000518070002c1d01c0c0c004159481040c0100761601d0b505800c18030040d8182107068205180408a04e5008210000090f8880e07003604082d81c1c00c2d00030441d005d4441000e403422050341002c29400342d91168000d03074103030490a440307400510740d020080c0306034031030f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269964028 1106 269962922 269962933
    0x703051b0f120c0d140906040311100309080a03050a06030b07021f1a010e04090204021303050c060a0905041806020d0c200a0206030a0f0219021b03 65
    0xb407078000940200d10300040200042c2c2c03039119540f42c000a00c400044980d050038008403e03a520729a01824507a00c880d50390402d12000a81070b501c16000e02645900f441c044e910a0003641e8900e9002882d080c54000700070002ca0003000e0082c01100300075501c60000c00040c04212240b409400564010038003c55501e40a40642070542c240e0025030740b0380180d041c00e070602c4078185420f240302400c0c06660030100601007030240124040095020748001008100d185031941840260b074000d03030480d40c6100c1d41c0e000b4000729205550200d400308120001c1007000c1d01d020b420100d5010304040070400962015601d09003a0b070401140354a0b83c41d107400b82000d07104d601c00c051114501100614200340c4c001d052070306c1d440310030116010f4015600080001c0d400e81c01600700c2c0f0164041e00e1000c5540c0d0000313000e09103000c41e040c91664018024511185004141d421a10030f10b584010050035 = true := by decide +kernel

theorem cover : BRFrame.Cov 269784172 269964028 := by
  have h0 := BRFrame.cov_init 269784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269784172 ≤ n) (h2 : n < 269964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
