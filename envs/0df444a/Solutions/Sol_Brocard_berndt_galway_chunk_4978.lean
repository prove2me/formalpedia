-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4978
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:20:44.496839+00:00
-- url     : https://prove2.me/submissions/12a32b39-10ac-4176-a1bc-437fde2eb620

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 895143884 ≤ n < 895323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 895145134 1250 895143884 895143913
    0x10806030c1215011e051e030d110706230a05040e010320010c051005040507050607030c20030a03050a090e01090912030b0102070536090d0e0108130f06021b 69
    0x104005800c603400b21728284148020701c0d1051403d810b100001e080907114a4a4000007400c0119620020002c1680b8114900c82483d003840024000c1c2628201508070f40c1803494000d280b842c3c51034088030350040019200305228011015240038000200814080390f031649040107081a810b550483c2030050340790107005a621032007510700c456074480c000d03002c0c10b000c60700e4200107008080e10455081c021030001196944883c80505255402036854055941440c2080d5149100e50366068002994503000018141c0780010b00340307001a494501340369601d031043d5048840ca034841e000090f2074500c0400000c0c034004030f6000f910f030f03a50280030503441c500c008480039003c13291085030087c056009101c041042d0710301f4450001141030809104503260b610280ca80d410b41200c7e66622000c11003010900040710001c1006074540c82c1c83c0d06150904011140020301180401003162588003020400d980c10050b07414034200a01c3d170301620a43d01c454020759a5804105070080021091141018421104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 895146384 1250 895145134 895145159
    0x1060602030d0b04091211070305010e1f0516050310080d090e09060f15030a02060d05010f0f030b04060f1d0c0f04061401031d030a0306050906090f06010806030c121501 74
    0x943d01181c20044004071b00d40940300340d8180310300d10341d0341d01485200001051082c0100d10000003890050010912610051030b4910049010524050326103810004070a00f0701101d009002240e00308035449694490608040c4522500034a01600401d0f062b1101950009260400d49060740080c0d2015035440717218035500d00089a4041c0201c1c912400300d1100c1090300050300d20604054140c5080c03079120b401264641c0c0c40345203039445590303a81300100100000c0702c84480107059100b8030a803c01f841e5884070100303420003420244c08503613150034180806543c0d0b84203a00301040011304440c040150f000e015102d080c8192400e028101c960540b0801c1d140511032142500d59220141c2d144030100740045005211000110400044909121043c10420009030140131f05507a0302240d51403c202c148016020301800d0f607405443c00c281409850950611301e585d0140080ca005055607840d100002d180080e14680250007000d40c41d070204801c8400708036002074410181900d013450f6a00c1410b940f5a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 895147634 1250 895146384 895146401
    0xd053306030606040c12051806070908151312020d08060604080316020f0a08070603060b0705100c09050607060605040509160303081b1606290d0f0501060602030d0b04 73
    0x160072000000f40185465070007021003080d64500032410040c6114190202e45040c0c2e80240c0000c544101a03900f50420408180e1064203440c200d00228500311069550381c0e006104501e4150004001900c822a500190b805d00c41d0800810103140c112454003039101d5800c11159400100da9900003141810880c040790200c07401c5000851500c001c035031a12170060030b0f803501203a21110b402d07405c03585c40d510800c0c5c1c00042c3c2000000b40680c64540034003e000c452aa03030040782e000805003d00f4012410128115040c40c8281101240c5501c1c1c04034101c42c0e02d0300e140c01283d400000450000203010403a800034060301e500b95002c10854440c1341141d80d42e10700f45c80d503650042540102c1480000d1040ca0200c0e00642001460b6203201c006030b010942d103401030b01d040e200e007105010541e400c3c0561401109402c0313100000c4074015080485925000c01b0b00070242900640110310401c0410099040c1c1201c0503400000810000741c4400f4001d4070380c0d01c00201001c14908283c030b440040c1c54940320f005003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 895148884 1250 895147634 895147639
    0x11070305031e13081308070305150a090803010308070303090b090f0601080708071a0405060f0a030c031a0105070f0501051602061b090907110f1e0102040e0c090d053306 74
    0x901050310b071381c0c07071000b507200000139140100b8504000030301030001c11519001d9441030b8042c060b8500801983c802c9094028000c040d120300704040c0394049030281044a0650790080007042d6a484c540c1000e41c0501601000140011040700400c24021004114408040c1014040c1c420b80c1c2d0b42d41c00420b503140214003c0c9200c58105810410443c0c00302c0d81e0700c0c44c080741049800d508150760b032800100c0c40d03001010504281c0760300084043c0295854800c0e080c011010f1b0900300501904209607c0d85042d038010654180040001e9981c1401920000c1120842c0d01c40024001c0d8603115000c0b4412a5417682c0e07440140c465100411421114200344003107090700e1484030390070401c017003007000380d455400380c801c0040c00072041c51000000000e01002480c001240c3c003e201007001c40081966658a0808001142e44180014000702d00a034010540003074000000d10784909110000484078024180002d10a1040c0020410074031052222a00ca108182c0080d4420700c501d50784200407250122102603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 895150134 1250 895148884 895148911
    0x50105090f120f4c05060d0c150813111017070e010818030906211008010b0406030302061602100204090615020a2411070305031e 57
    0xc815052404404081d05050000c403402d40c000c00310414203119038004108049440c141c4010b00313010b91104546103200b0810b1400e926841c01c0da4000c003800001002048000e5191004601d40b03039105a04100c0741500031105440300c80c0e44e6030115000301800003500c400700b000d48000030a030300b490f005052030141d0054050401c480c1c00c1c008108000da0f00d000b0038814404180480d010b080140817009120f507040307803540c030341014140c8005842c0c0c0d0710003004800000e03403900184048a001005980070b14909075409600c85070380c1007003046251840315000607000189001c000e045545848488101c0700d43d44004c12000c40611300f0301055400701e010190142e4040b9010400100101202e890280d909105482d45c3c050800c07610f00903688160b000050f00ea841310001c1c084404400b0018004134040d000820070700605035a03482c0d140441e40400c12058041000f503880c0d46100340c10030784400081c3c4d02515520302d81c0303240140254009542041102001514104000b00007031341c040d004000486004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 895151384 1250 895150134 895150159
    0xb0901090b0c100e06091e070915090207081206091501080402040f0e0d020f0d08070804060212011d06030f2a040c08042a05271f05010509 61
    0x941030340c44078420420b01d12414006101041d4288100601ca82818002d4102402c01d00100351521428940003010500140b1070341c080c3c801e001910400f12100f030030f0085224038140e022110030502075845240c02d64000105101003089500080861121030341210003207846036070510802d1402224000f1030502d0315683c1e00415805100b03035581c8584020004203071b02d54a2480b40043e240e00303010f204034a82c003122a10780340c66014080c4051a201140c01444e854082c243c004280703c40203424402484107450208080c80900e03011102002e1185414500c10350351fa070040904002c0c007540001080c414040070455a00d03001c00c404900c0701d0103000a0040300c1e440d11019842100b000014041032a03d50780c104142d40392406004030f8814075803112682840c003414641080603000050390741103104801440e5042031450500025500e043d00c6c1c50740c405400c0c0525480ca5061400b00d42d04003101c440406c5003801c02003056044080540b064003800907a04d42c01911207000313249600d0360113900c3d001c58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 895152634 1250 895151384 895151399
    0x1b1103040302040207023001060b070c03060504020a23130b01081f030501050a020c12040f1802040330020309010e09220b070314130b1803180a0b090109 67
    0x98051180028070401c62880d07800b030740d4680b0b108400f021241e10003203500503007c128428461080108200d9500a00e8040c1d0b607641c26001a005010040107280c0e80c10204083d5115a444000134101e888040944201c290030881004814030042504c14404090310b071040707142c1c500684150246c1a140c10301182c45d0840203066803101c0c5c400060104403410000800306109011701c60003102d84940050340d034180d1050403410281c028007e000c07034100c108020410b0f612941110005c0b55111004074000c036041c180d5001c080c1c85940c1c0090710340c0d4190403c6020494059640b0341c04403540f16160210700440306010f2b622070064056190108181c0c81c10700200d800c0a1800303980c400c00d0758000c0c6c541203290080c20350202400050980324000c15a082201c010740520858005c09076100d111011071600c00c3e04110b540340303d001d00815032041c0300003046085049007a9103d80d9503442c01030725203031550480740d00d011212000c0c40f1407042030403c41c0010036144040440329640c43c180d4400c02286c0c18041c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 895153884 1250 895152634 895152637
    0x140601150f1d0607062313140c120c010801050a0b160c05220b041406040b03150c0703022104120503070b0103030503092a040b010908030307031b11030403020402 71
    0x101981c0c00d00448201e00e80d02c1c00001e04c107051140c00700040c41040f100b00d1468100302c64203428940f04c400300900003003401200c0b000c0002c503804514018211340c0c20701b00a0410300b42e84c0144d03800c16818002c200c4c4298010031040300c600c0b000c1ea01c03015507a9940c020000c541405104d010f881540410011620711040000b010249020b01503941ea140d58402c0841c0e001413202c00c1e031940d1034440300c1c10a0340e2802c00f07010b12040c1140c12201400444a84003490200c0500a0420340c840c0d95101d0780e00c08a500e05101d210f2480800130348240107444c1a0200e15950b60280e50120b006004003840c0120440f00d40c1403121406000424043c10319042000c040e8080f00102016941d07071109010440018030030209180c043c61282c1d0381c280d00c0c3d06001303000c5454103820220003030161800c0c02c500c480d1100d00000f1078929003400c4130042410168503005883c8211582c00c22040342c0400000c000569402d504040d805803100042c0580d811408401260941030032555400300f41c008100030009403600b40c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 895155134 1250 895153884 895153907
    0x150f1a010c03090810021b0c030606060715050f2e050906013c020a0b07030f06050a0902070c0503070e07080c04050d060e0c0303090913060e0a140601150f 68
    0x4001c94000d89604a1030b25208101c5c0340d03071240e95000280f10841d008140f58060040c00710100812155020500282d164400140b0260041c1c06c0860384d5010b010744440c0703c00001078414810002c0d400d040c8440ca40600c2d00300c0d0120384001100408009030291050f201da250128041c00c803545900340400c104400310040c02d060704104000c1c80515583d080000315400c40304200c0300040c0e0b110404030460300c400394010401011340d005800c660002c80c4203403070102e134007250700c2c500000d1280b0002002c038010070140d0402a081010540c0c0452100a607600801c44617005400444005645008240c0d89025030f0050060031441080440c220600442d0b6054000203501001400c1c0b07038644010540c04c030340c150b105540345510783c00315a541c4101030001c822a100d09401640c60300541c80089022901c0240c25a2441c0e43c2d0f040041040c082c1940c040c000480c00e4a0544906981030b0034580d00c0c000101507990000e029404c0005080306480100804200044d110707811300309103440044d1042e80e4101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 895156384 1250 895155134 895155137
    0x7080d18050706020c01020706090e1314030c030702090c03010302060a11010204090c2007271803051804092d05030307110111090a0b070309090603150f1a010c03 71
    0x30104000080e078140030100c003500f650790041c546030a08070002803802c141039019500307000e2615414002d400d001c2d0b80f076070390041a103003811250314a10b00d407001e001030600400d14403d000115078101806000300060036a40e000b10380008260300d411165049610082c40000c0d0700a1040050700f002d40e000d481100d441d081e00030001428140d4864122055900d01d00d401700c000341c070188020400d016a18040c12101c0345450080c25110300300344050455001c100d41d000800081d0902c2d20366a50f445030821103504504452520b00050a450702422640000c00c0c6407071007541044070b2010a040520440013456002020701110342901c181d0400b201c403010700e0398404802c0741040c04001c40c104000841c003440003690742030714843d810610b040c04c66035a854010140e6208105020003070341c0b0740180a003556080384031280e40d0b210905c0d0a03100b100103036000008103410507500200340006011041051b628103803080c44880c2c0102c0d01c04d0704071060001100050001a188200c09503c80d04440002900c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 895157634 1250 895156384 895156421
    0xb010c0f03111006060f0e0a350a0c0611120d090f030e0a05040603080328091104060803210613091101030b0a0b120c070f030309050c0607080d 63
    0x64480b8100f65041d0343c07989080e034407010100801540130b000e1a40d4050a403a02d1a0b801c02c078070000503200d24951184004002030020080c10b031040722000a052a112681c17070000300c0d2800c8840781e8550722888819601c1030300c050300c00140c0074025844002d408021001500000b040119400500d40040c9001e1091554406200000954905a10005602940720b11244410740005c0023450812900054011410440c0420010308804c050760340003802e4100c100030101407151844490607107070440750301c12414405440e0501824485170501c848060b28241321050b101c022a60703030303803151400711010f8041c6038401e00010460381d061903801c00c0d0000e18240c0d502c001c51041c14281c0e00d2100061303070540f00d990b80000300c0d0745c0c1501c03030704103241c1094038450161450480042114040c025410300300781c4181002600d07440c1c0d030304103d580c0d09078400d0f076a4411f90fa15040c010000d0406003400c031280d104510150f49945000020b48581961000781103152000480034880a41032a04d0800f0340c0011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 895158884 1250 895157634 895157657
    0x30d0e04151502070e010f0e0a0f14130b1b1b0735070b030406090c0b0c03031503010219030908040b04080d1421060f090a0b12010b010c0f03 62
    0x211124546018640ca50080c182c02e820129103140000c1c046c1d07c0f0411182e844d5070208480a120740041d64010300100340090b20000000425002e011000205200c00e50b54400f0005600056400c1d0804503010b050321381079640d0b0f01801c0610011620821100841003030140035418240700407d190040b110703000703403520140ea40000c15031a842042c01210030013541e44050034150380c01200d0020030500280249031a42c0390047c1c1041e148006040545000d4031889400c0074468100041c400414034104100d5840c0340125144e40c0701c0d0400e5690945c400891b40380d90000e8a03050003910400034070600948a017903280c2d03d080d0002e040b0100102c99003c414030000071340f0b0310342c14041d2004003120005080c0e40144040700521210040400c541c1c4400180400c1220034501140300320365800c1c0d810141c1c51501c1c2c0d4000102414402190703140c1c40950780d000c1100b40c0c0304c2600800021001a2010840c08080214250a840d0200b04440c001140542c1a40114071810010f40141d8081d04084000f0035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 895160134 1250 895158884 895158899
    0x1d04050703170406020c15040611070b18030f120f07030905030a060e07060305043c0303020d060605030f0705031b16030815030601030206090f06030f0411030d0e0415 73
    0x10b402c264810030b01c6002c50204200b640621580100b01c030100c0310a4069502c041c04c010795030199000358420071910254420f0401c3c000c00602014020030490203440d140840d01c0b002d410350b01c01c4201c03070081c06a400c40082c400d00021300c0e601004450316510f0704054031482c0303c55440d00b040c041078080002c0c00c0740016940c0c42c01d000c1040154080c40c00401c1007102032504510f01102d079808030701010728100c1000003182c004420031149080b00c50fa9a1080d441d007203803014001c94008072509949909403940c1c400c154069000700000605c2d110240007441d030300d0b00159042c0c0011a0840045000c0f1000199024410801507a0000201d42010070345411070146814603000000e6003081d12480c0380090040c0341c3c110500c0307944919840485d40c440241c0d900400e460300410b10000b400307206d01013003e40c82943c402c40504800800a0202074480c5802000d00038007220071359041d90004000348000b09039080104203407031042915121010b164400e00144001005425a85c0400882c0c00c0c40125119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 895161384 1250 895160134 895160153
    0x2106010201240501020105011d070516061a040b0427020a0803040b04080c0603162a06090b16080f0606090a0801020307080106050a0c020d0f0506041514011d04050703 73
    0x104070b400d5180c00681c14140064211403040e0030181442c08280040d084102c0d181041c954404102d180c0240c803000039031181e007c4010b801000038030751414200c809001123410310640d404001d00310307011f000d02c045071740c1400111003c0607a00d42410010b001e611040e02c4144401051003031001e130001541da9543c00a413070450f00950409004124005000c004000c1c040150191745201100d4031451740c2003500080b02e44c40001031101040c0f116482c040750070364580c0e01d003800340340d071444520340344540f51490504024441e0039070403225105a08007203130080807082c00f90110300d965034407240720702c0e212440055a039180003003915900000401c010b40c503988803010340b24010040f120015849007481c60340a00f0861058008108000c02407200001e00d41d404070b510b00c03100c0d03015960b08450003990b040852040d035107080301030228030644042c0410002d005824118107113110380304100f00480f0700c0d0084407581c1c082c0f11701c0e420074007041481034250301da07d1040d036080342c461811100450340c0c942d18071142 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 895162634 1250 895161384 895161431
    0x40902060c06040b040309060905010801090507030f18020102060109180b04140111040501110f07230a1d250f0203091806010e0603090706051b0628022106010201 71
    0x13000b0700307074050004241c1c001d26983c1c0a001b490526400c410309101c0000c01c04c0005201c0c640d5560f48450205d12414002d0707004454148140e0001d000c61005880d03d203040341d102c0c04080b40180704103000010b4031071a91054101c01800e0404000049029854009941c40d0143c4240d0b4244c0b41d2511f800149a800d1081c06115207811402c2900c451400b8005017600601c19004856a0030180c44114111b0340450030030f007610f02950761540301c1042c40c0c5e00300c042c940b8507811040d0460380858000c1042c0454103800d1602c01d42007210200580c1d95a1400d500404020540401c40b51211000c001002e0240040e200100c00520440f4106214a000248400e54880070703070354820745c8a402d10903d540c2c402030729100300a061750b0341813035401c0c0303022010317641d41207441980d04024000c9081510b950581e20a0340080300400226065420300b2203035442050244a174681c08440d1194154002005e50b000395000e41000c2200b03021640074200b21000b1181005110904555942c00508000d41f052111b0224 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 895163884 1250 895162634 895162643
    0x1103070915261f111804022a060f060a06090302060d0f140412170f04050304120602040e0a0b0d020d03050f07050c03010c031812030609060b07151a040902060c0604 72
    0x9100b101480e81108032081d01348840d0b400102001800f800c10009580d00005400a4400607500c520381c0100840c1540800700440c800b0102c0207075441d006000003151400b9980c032950608094a4013030404c00030f00100d110341c50101e1034454041000d450030b04090001743c0d0090901040550903078060304101d80c01d440300c44240c41c5064080c0030600c0b003010740c2c1e03003106a030b141803407030800a1600100204110091003003840c00404000601045814000d9800a000c84004038001100614150002c0d40140c001c00e0203111242c00050907054803401004810140502231001d292495003c1c48070300e41d03008100740c0c00e012040143c0a010082e00c0010403500380201d0142608405442c00c01d400d507200c103440360781003505200714040e229031240d030096921580502e40540114080034103030040c1045a0142000380d14100c070002d0f602e40303400c0040c080140704e4490002c18180503c030541c11208a042c110211a00034a124030240c01c051744107020b01030006000034101910540207901d1300d10101c03400c59 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 895165134 1250 895163884 895163923
    0xe011b0c1202060123040b030f100509120409051f060e130501140603220b0114010c03091203030209060d0605120111030c07060b030a110307091526 65
    0x101881045110718a0003185440500000c0d49051044c60201107205040c250044036410609643d640d00d0f17000040b007200c06410364620a15a001407903e03035441c000e282181c0c600381030002c0ea00ea200421009c03001080c41c24407506081c09d02c0c030480003c042c01004090051509c003102d10b000744c1c00f0080314008102c1070307440459a01c07850052004e03512804070003460f21030030000140401c0b88522100d00e1603210580e04603859548528010304002000025042051240702d1444103001c1503544060683e02c0610111900e0074040004682d40c108448000d4001501315605000040700004010901406440c001d4180055800041c0d1039a01c040d11400c40640d40e0002003115003003804480180781c904400070070040d0824101c00c0100d00c402007038541403240005454081080c260300400d42c260340941162450032451900b42521200c0141c038510038850100005002283da0141d2440800c00e0401940100e150100404160380c103c1000c60101500f01075205e1b078004208a22240702680c0c1e061032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 895166384 1250 895165134 895165157
    0x40b16020d140f010b0603010b0909060a0e10051f0f11100203010f05010906050708070b040201030f0e070315020412150905030a02010623030312060a0504020d0e0d1b03030e011b 78
    0x444c2190000944d06001d008188010094004a201941e00c015000d450707000e2170369038001c00607896440715007181a050b0503500174010300b140004001810740350182d41d4188040700494054a400416055090000360b1212008000602c5080c0383c0d08070b8602d0008644510303022611001c182e80090704010300c2c0c819100c404211940c3d11121030b41c010881ea0034903924110042c3c88100311071050250280c08403402101050440e4803075880f0390344030b501c0d07150100010b0500c400c0254803071031144010794648190140e0007502000c00d2080301e003250100305000103948250341e0f40c2c0c1c5160744070b8105501c2d01980c801c41040400c0d410300040101c2c0d60305600003d015401c3c07400d12120b41002c41d00c84154038066034082c05840c0c4000084841034040c4290341850b40d5680c20002d0b8039507440390031194000d4008906070000790520381007489804a8001907481401d0016402c5a100903c3c2210701013006001140340042070290b032003c601500e00c035001040000c0c1c9032141c0001c140415038441d00042c24130002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 895167634 1250 895166384 895166413
    0x1d1509070f0602060703020a050d06060809100b030a032102120f01080a11280605120f0402061c060e01030321060f050402090102010902270c040b16020d14 68
    0x1032000d85400d014003000c0905210000303554070302c000c146005044d80003681000f850300a905880000b121003030244001c50700c8502c020300d098003c4d42c00c501144140c058a01c10501140103c4405000180082603545402d840480d4840d108500200382d0101c3c01c040802c42003e80c5c00104880b41c1c41e080180d21f1428500c58140b1000c40581c00705080f6040041900c0c0060107101c02c00601c18021034403040c4007801050010341400f07901e00c91001810faa024001196a041005451940f141c2840030766241d841d240301c1c5035112802c59000b54007020804ca01c3e01031030107905550515402e41c080000d0183d4498203045402c05081c2c0055010484244045002d10307113505004c182504030a40502c141858110801014450350190600c56900460701c1c01150340b0075442012025001025204803420502098518054803040c0305c1070b1101d060b0005000308409002c40c0d00719040480c0c0280b4102c8540c0920341d600681d9038040364800c0980b90b07114042031038400d0001684801c0c1d4007506103c04040d54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 895168884 1250 895167634 895167643
    0x6052d07230c0609041e0912200a0f0305070803100e0c0a080105060d110d0203010503010b030d0504030209040c0b0a0e0108010609080a0204050702150408090a090204050d02041d1509 80
    0x1000c500662000007440c20680f1140e0503610051010354010504400e0703004100c2d408441e2056032080e0a1401c60312406001c100f05a040345440305884501541c2d40a021a21001c0d840e11002541944070308080000610700e40c1407810040d000349401d0707041c420300d031b03940084647c400c1d40c0c2110442c444e50b206205040c04100103507008203180d10554078060684034060820b0302c0502c152482800042081044001c0360780080c4040214600c04598862103659441e009410a0003043e01940c68a85c01001c28200002d11442e6001140c65003410a440c40d4200440328600034801c40b07902c0f0b01c2c0d0400240c1184803d000d0000f401c0300742c450282010311130000618109050b0301c0f80041100360070301040342450124500d89140d4054401003070365504d0840907868801a12001103444100c48104800e01c0328104c098036001e030003194520780c01540c0d071000b039041e40680d024099010034902c00304001803600f50701601c103000e103a5650448642d007854580e410306410798410100041c00601300a060041880b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 895170134 1250 895168884 895168943
    0x70c1707060e0f01210c021c0c05060112110418060b090105210a170301060801060509211204090f18030203030613090c0b0a0e0a06052d07 61
    0x1d400d801040b50700002501c0c1c3c00910a03440e06000d0909010041a0725035164014078113401041401905500b403002592072805001c80c18003d21b446422035040c5110b41000e840440c0c0000c010719140c1d080072081640e000a03140103c0707101078005030341030a03921180101c1e02d0205440780341102d09812400c005007942c0c009a802c51081c120000107101a9030b903101262501030382d44010007128588422100e1910b441840d02400700b080b0340d4151109502060000c606036150f40e5a20782d060b999410b816140c030b00400d507005500c510701000500700409055412101521140100e1b0300c3d4451180c81981290b00c190810b1890380c0d103406400040c1c41e580d004540444803840c0c160707103088440b514001d4480c000904218812203002c4c040340c0c29007880b50030041011b50415030207a00c1650f02c21140c269984070046127400716150b400b0340300040c40e04060705811100151529403404c00c46e0703d556040d103035840150210401040e450311451007901c0014003040f910610354050b0302c8030448291030f607a203210f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 895171384 1250 895170134 895170137
    0x3010c0801140a06120903050c01020706050417120c070203150a050603011103060307050637080106020d08040201030c090f03050a0c05100e0904111e0a0f03081e070c170706 76
    0x420f007009520b0744242c5014501e00403030400900c006072803500b26428407274500c8030040d960002c10400305001c1c441c1d020500883c40744100d60f0703080000c0080020503010b503240850f441044030340044c3e0641c42d0300e0001c1c11400d01c001c0a944990250000c10311446100790f4101020036991000c101c240c0c282485141500064800807e0540c9012030000317170364144501170b560162001050b080f4010401f041c00180c3ca40400b001c0ca004804c0c41d00889130744204000c8064005001750f0000074205001103503588641e01c1542c0d0354201e90303a8580042d005000d00a068004010294500041544941a80402851041024004000407030070712600280603500118803032001031490411154110103104c8503040252003440680d99a170410f06450300c02002d1190304049070f4082044009081c102e40901d03020200c5040c400140c44604404003048540001400000c0421804000c5803000809040441e010a0720350310388405e45d90341602584c1141d000300c001050a042003c0c40150078484400640285e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 895172634 1250 895171384 895171399
    0x7031b020a0816050f06090a06140f0a1e06030305070510020f0a030b04060b1b060c09010219020a0b070b071704020a0e070905041d1203040201080103140c03010c080114 74
    0x3141c4984440f88220048140e08a268580800801406005003866401d01c001519102e1401c600e0b80b43d2100911481203968501c2d040d4810310000112600746c0c000c400949000f02641d40e4401181300a1a1824001648800b4081620440d485034050311024610030360b5651b40391031880c0340c0140f6001d40404a940c000c2d006020031614480600250f418110301440c000c01d40310400c10208005080507007004242c0d4200040000613003900c0442c24004c44030a004685040d0b941505200c01ca00640054034010381110000e0482402e101403d05c0590780014500ca000503628806e0701103550124208481c010408420402c050360131140d004c40c80d900c4003254040624065001030b0040c4904c0c003130103a10022810200b003915104012080140802030010456100c22000c410210008042c91541c58805d0501140426107100152401240d040e1240d0140782d0955480c0c01d0040109091444180301d54609409259005d004580300f41041e07458101c0c66505007035030308421404540c00c0e42d000f800c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 895173884 1250 895172634 895172653
    0x6020a0b0c18150c0d09150f08071d0306070e1002010902030a1203020c0105012423030c0d051603050f1b0f0702031212100f1a0904020307031b02 64
    0x2502d03035000b0881c50031581e40307a9490412103100031a010751407012010f8440c40940000c0c1680000c40303401914800e482e503050100451008035541d804049150300000c0240b00880c610300d000c2c5d0340e00f019100c00c5000d040700300588032010a142450888890b000503036805095482070510216560381d08196100074444c038805034020a41d0346856a400030f20000035032410601942c8690f060b10750760071140c0021b1245594500a0a41c4c4000c1e500402a0070031102103800c000c103016081c1000300c507540b506c00e00490b92032000d042c2c0306900000c00c82c10200e00d080214018165052260511408102e802201d1900d05140000c08039040100b080100101c00390600507150b00601440c2004030300c00c2c0000355510700c0d00d92410388038004e8020094251042c1a08590f04140c1c0f20060304e44200d00743e42d5031645580c2c1e0304a10200b01850310464021602c5880c3c01c2c0300824040420f08443c0c116108500d140540b00404201245c1c01203a00d0340000f992004e845849802c0081010175a441d41e1004142500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 895175134 1250 895173884 895173907
    0x9040e0a03020c01210c080609160804021011070b130e150d02032401150320090f120c010206160f0e0a0305070e070936090c06020a0b0c 60
    0x20f83c2da007414188a4141d20480b0100403c0a01064041203a841407001c0c04848201400f40303141564840d00c1491181c3c0010441030000c003804050403000e6640600d551120340a10030910f001400002c100594560040305960040150340002c0c5910035401e591004a01c1090030004001d40250941a03104000e00203007103074200c00320110300c10440c0c041e07103c10344500c006071038006542d590310804c1e01840303070340c3e4912072043c00c81504031107001c110003022409608040b02140c0500c41c007640207245031034a032a43e0441e05001380088400103400301c1c942ca10b640f0006014011456080c00c0703558841d8502100b1540c0c14044a80c10001034034030b0400c00600780001911000010310351004005a81e458080039699107504040251782200558440039160741000712042c000300c0c0c0b01360205e03100280000c2d01034946101040104403920041d80009280f40010007400c8001828444040d06e03484c1002c0461105110440249030b00e400400b1000a0ba140141360707a0801072a4099401007030244c00d00c0382 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 895176384 1250 895175134 895175143
    0xd060f03031e0c150902030d020d0314010f23040f020d0f140118020f071110080903030c030a2d18020907140c0a1a09010507090603051012060209040e0a0302 69
    0x60b0740c0451a00d0a1041c1304110100502040ba00a1340c14031074031818000715a00441c03482100000e82d5020700002800c0d1540541c9290b0078403c2d0b1308000d000800400c00c60a4180c200c0316020040840d61a44d0108e040005056400c1c40f41340021459001038040314030f141504c10b0003180280f074a01800070541409100300c669105110324103500c1c0501e0051308020402d60f040f50b40b00c0c2c0341404401d4542440e414591841a10328900d0380c0684800800030400501400040384924040300042d451076031001c01d658816000640031102c81030315070340d03039000300010030014003481103800030b40e008031030790780f20441d01a924914046614045000c140d080940c40d14a2079551054260800e5a40c001c91005010f05601c5009080f070b03e94041c9695010401a8540c0801d80662000314080c915840305945036089460030350344c0c2800b0429881017048500d01076040150b00c90302c0019144201e0381e80322510301202c040200c1c00c035541d5900080c102568500340c410040d14403941401442c0c0f034461940c001e07544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 895177634 1250 895176384 895176407
    0xd090c0f0603050930031014090121140328030e1c200f070504051e07120c1e0c0c0b030c070f15050903090d15020d060f03031e 56
    0x409202c0031918401074000c1e0040340301702c40fa641d100c0e91724a000128000401c00d07d02400b02808400c403030005c1c980c540540c890381640c8039004082da42c0c40703000a00c4100f45007216421150020080024492442c1c02d00c0035240b082d001e001d01d2400100d40d00880402c407070240508000f89071034404956900180054054401d440d0010728190113840c0c00d50603552029190ba540885100d00d414a0341070220100300446000006e0003207442d00d589403420407055440888100c4d001d02c00401c1c030b003040c2e01703920105142c1000160620760314110440d100350701628402418100441d420104640390b105159031a03004861407480d00d91403c000d10350b140e01c00c508913407003440709145000c404580100c0b4100222003c240c1d02000b0390a510700c9d503243c2842002c451010016400d4940000503c803000040100e680c0700000400c0c0d150b050359555a0b800c4405011940032415a900f40f0900020340210b10505c40074207503031403481041900c0d505d0000c0a10700e510035a04403410308950000c20b17281d00010725520 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 895178884 1250 895177634 895177663
    0x902220f1d030d150801020406021005090304050f30030702010905102010090609120c0b060d030c0c030b0115050c03030105010c02061c0c09050d020f090702030d090c0f06030509 78
    0x42c951444000c0b900a1340f1142c01c254002c0d40b001500160780c1c0e400043da01c02061142c80c00740310303664916001c01c1d1680200c3c85026040341000d4241c81c000d1524332035035424019082c0761802c441c543c5a40d161104480c140b03071100d5640c0001080003d540e00138580800503c0122482c41d206c241d6030000a00c541c41c410013440445d140c282c4290038545082c4803000e1550340d83c1d807080160a4050900c1d4000d881c0f051015102c00c044011108000d83c8201700030b0032041d0b04640c42d400e480c0c54070802d20840b03001c02c105c19010800810369101c00a9122910b640042d8041c00c840307802541020703c000014450403400a042c40b00400500020354408070940c0d046a2090821303500540c80b50011400700d06c1406050305402284040f0502801101d52005031840c80d0350351802c624076114030074800c40c1c090341200a54000b01c8820320500134a800c1011692202161045d0703400c0c040009826025104111011240000404030034046082c00d41002c000920031403a080c499418006003003070b25014000c02011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895180134 1250 895178884 895178891
    0x14010507022205040605060f0307170a060e030309010507080708011203140c0105150301021201151701180c0e010c0f03050f1b01180201020304090902220f1d030d 71
    0xc259614499605040607001e1000e80340d1510840b000e100414084904480381c518200c01700381941090b2543c03a014950290090030b401c2c0c245001d4281458007640c10704000c2c4a0140000d00091180c003984d80041da514000b503450f8100000c100c1e080d80c800034858410000701c6010080c0c001c2e4450a03403030446107070915054211000313003400c640320802c1700a110010300c070005011302e0070035055102c58429154030304030751100c0001808050a0f0303c90007040340d0040001c81c005000d5020384540c00c2a500315a803e00c0742c1440c002d61150240d00c0000d900c8180e1140080000102140300c500400c1c910402610700601d141c52844000b07071180b01450b1016000080c03050700001014042e100726403480c402045c040c0d4640101c3c1120200040390561800300a50800ca0a081100307640d00100490075416009141401d040508042c0141517030314090341e1107031403520340c0c824102001c1c103441c40e42c10148a0129503498001140d0058600c01e902040f18410141c41c5540044000302c241d03100f016070305031b012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895181384 1250 895180134 895180147
    0x40312020304090203090d0e0f030a0308250206040606050103021213030c050304260d141309290f09011806030c06020706020d050405060f0a05190801090e07140105 72
    0x224a5070160f9000003001c03600c00014440a1400010f070560045400d58420030305180345018040400224455217070581c2c400200c40b80080d024059450f4814500801e4400590226101c64195200c1c3c8034000050b800c48000d00c01401031034000c40c1d000d42820300b801c1d441d0022921b03064810000040c03828441c400c0b52540b40c0c00309486128041412604141100e4032151100c160382c0221100081030180216410b81c010300d8001c0100d00ea2508110030b0300c0708d4484902c0c3d0040f107091030344030343c985a01201a41e00d02265100c0320b441440100320080c51034210004585004505c1c211501c0c01c4548030b004074800c00101a580c0701002419240801c0d0445102034144048601810306908010424017507081e010030101d500040800803100164200c84944030342000c1a00d6920803405480c0c0c0004042160030610500d500080060300ca19140c500d141c50503080041c046072030100c40e6500000d8803d001080003181e24020740001080c5840504015850305d41d1750042c0140e5095190b040c8240030410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895182634 1250 895181384 895181387
    0x705010e0d0c0308030108100b1008060a0e0103080a030c020a261629070c11060f0c0c01020d030c09032a083319060519050f0f06040312 60
    0x811449038001c40402c00c2d01d80300d01c1c1c440025013003402408168441c02c2c80510321240750b8000d6040412024080c0700e0085507401003143c8502c0002c4c521a0000d0340300c03070005400c2e00440801b60086015010190b140d4108810080c151000040345004652250f0842c80c0464800508403d150014410fa0140c0c4641d40d03030b01d034046000c1e105425044181c00d00d909002d10117130b903610582c4040c0f0118200110601d4000540d0010350a03220b030701c00a0038400c1901d000644500c40000e450b20000c0102d8104944019420415401151101d0680e00a0000c4020958041001e241d1094a60800b030217225194440105040e10030f00c000703821a2084203d44c6c50a141e0a1404880e0b80f40c0340e00d541400170303111540c03c0d96400780250708070000c5d811003540b0b501c0100c101e00c2010b03010760700b0b82c4045801e4441c0c1c01d01d01451950318111a044565503c0d001032507503981c0800010021042c80001c403054980000c11803826440000c0387d003e8108200500020703550b01089800b0341350700943c83e9680071245c510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895183884 1250 895182634 895182649
    0x906030d0819020c0307150e0a0f050a0c15300f141f081203070c020a08161706010e0c0d02090301060b070b09010c051804150312120902030705010e 65
    0x222034005403002030030008120b4003100528000b1f0183d444440042c215201c3e200c125280c0790310042d00c2c1d410400218001070b10313048000c004640980c0c122140c0b170f2042c3d02c0d03441d4441b050b0341c010b401c01e00d0214442030810345c20045a00b24020114851801510862006102e203800894007880155a80071509103041d02540011380040140503100481e1504a40305060f54008250901c903030040740b0400203100303100040110603070303980340309a84c21502d03043c405407200304040404a9202e110014017241d04642000b031825a03004200440304400c0c503080700072480d014180805031040c4c01000045c02829002110760f90000031a428082e034900141072504020b000b90002240d15500744000016680c0c0e00308003404a0600402c0306404544807000164201c86500c00d091011440a2051444441280204460070341e80070b400414041711184120014000300d0300100d0f103440c0702524100109502602c0e001200040210070030455001e03400080c1e4400d0780c1c0c0700d0541003094903c40015a6111040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895185134 1250 895183884 895183921
    0x30602030705040f09020a050f090103020706090602090f0307140603060102071502070515190e0315040b09070602210319182a09050a0e06090703020307050906030d08 73
    0x54085450303003403041c0001c0480d0300070b02c41d00c03500460603400410020070a100300c50300700b105900d956240071001ca10000b0f00b038004500750390515600f448150041001030080c200018420f001c0140e495104c3c40411403038207541c60700c050090b408000c041c420054040300250404100711041502d81d620000103d02e0802107030806491044200d01c0f80c1a00c07900014460140c9804403036500d0015584000b403145400783c81d40c00c01401071340030302013111503006800000303806001030240c8030700307010907070302e4103070403c4240c901700d40ca1000c01d002c00506400501503100500180d2014241601142c0d60390360510000003540200d090001002c5400100d981303041d445200c8485406000c4020354001216188035601c0d41034a050307104001c2c11201e0b407101c40a082c204048000d030101064103019144004100050100c2c2e4455504c6680000c1503c04210300d40c41000c2890041800508610605046c22403641c0301901031028031090000c16980440d03002e5089246103084052a9190903081d80d011070f001d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895186384 1250 895185134 895185143
    0x130e01090c080d090527040201021c05030411030c0102070902030907090e0f060c03010f120f0209271b010f210c03060b0301030f020909032a0606041116080403 70
    0x800060540c1000c201c110b600101c0d03440b60752800f035a900a10840d18581d81a00351006000f40e000002218021b0005400c03a0061041300c0400c3c0d20001180050604256100041000401040708010100090032048801074019180c80d07503d004c0040e588003654010f0800494001c0006034414a04020b81c2c801458140011f0104405404020fa1039510b0300444021a010342c0000135100071041d01103078100c601060001e0842458000c1862041c090302904541240111031071002694484081502441c00040c02c1004a0803080c44100e018100a150f0903964108030681c240042901c0c0303112412700800e0034004402c0256400459840d8000a01c810680a82007a0717040c601405501c840f9a80760035460801240b038461001000074002440001d00d644c14054680c0010305104140581004041003100d0038000350410041c0c5107402d89481c0c10105445400c8400c10304810081d03541c10600c291007c100c411414000041c00784a03c2180800c00a9070295441c02c20a000d0101c030000c6810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895187634 1250 895186384 895186403
    0xf0f08030106020c090108070b07151a0a0918030c1b0806060f030601080309040c020f01050c180d020d020405060a0305011b0807080c041e050d06060306110405130e0109 74
    0x1515141155800c02e0007000300501c80c03074181880c0b030705000b0302c02c0d4141c6460500502c001454100d1584960788202012908203540c40700707207000180d6500a100d10103044001607507a0040340010f0109510095104180050034000001c1e40b1800b0011250b0740c2c1a01864507400072096410502c121019840c1c412074260322011000407003800116146000340c0d01110300c050341c030424004060741d6030000e009408441d0800c010704515443d09070302050044c461801903a0030050a54030007400c4901c201c404114503030340040c41c4e04424240300400001502c0c225900300e0000103075004075001440c9004000d000399030307550100d0615610400641c0003191300c031009004800d6108800001907040100c0c1101083e03070b42000c603090601582c0f0280c41a403829000701c1c06c25203810140c40da804c078003082144040d00d034440d02003640d803203507041201050f000e0320340403800c41d10f18079014003180e052035410500c001c4d040c4018425940c52001c0131194490b000d03004503200500601090050151100c0140300804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895188884 1250 895187634 895187663
    0x1905090a06051302090112240f0626071103130303182108032502031903050c070b04020a17100c0c0b060d0f0b092503050a0f0f 56
    0x200703802410580300d040c2c1c0e61850220008940034103a0041c2251a4042002c1d890440c009004681c000e1400350001001c0401034048108090070703005882c1c005031000d03414040280a010b401c100102038800c1c00c096161031207030f07454032a640e942e08041c0c581e00810005840e1644c1001040007520360b218048400c0d940c89a9807454050030340d02a100c04980e950203024400a5030701804a1807803c1e0304103d484402007c4a81d44d16660140d00081104003e0403043c1c00780c204141020342c0b5081c00214a800559403003100c109030020a1189811020426003001c04200103502d03a502525035940d80010342c60fa05444a01c00680e041c40e1581085c0004410300b01ca85101003400141e004481c5c004007410442d0061901044401011020024000402e420003152045c1002c400c420a040d000d41100300504c011a0703202e81d03082500340c40021456206045125256505072052a07010003841982041213183d42e030399544030030030324030090500d0200462034424061004041c1c009541d028402449615 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895190134 1250 895188884 895188901
    0x30f030509012309010e090c07030c06020c0d0c0203010b03060c0d0c2102120705030106170c09030d1101060b03100e1906180612020f0411251e0809190509 68
    0x3c0000e0310b030500007802c6c441c03545c8450901200550184070600080c1d440c3c0f90041d2001e6551200301c0e00100d8890fa0308008a0b0b07204901442030780000840c3d42e80d004861403007030041600390b0b124400780610940088003400120020541100d0814038400c502190340e17808031034192005000c2509140810303e0b42900912051510307030041c07078a80809050740c0c10681340e03070070200d0300c50000b4080c82000c10f0000d80c4107110600052103c0e6440601700a4840c5000c0c152400b00e81440d00c2001c01102080051004080040007801510098088034489508610340704981690598951007100c1e01c3d1000e8a012500c5e11000000070030080c1e4481ca01480101e03501c001000f5890122606d2040b0146491404610440804d04a0105070f03002400d82c1c3c09000c000003000b00800da000007000c4a90804c2202d40c0d18000c143d03040d6000202224551101100c1504207103c0d03021a03800c0d2680140700100c8840300159601c1c043d513803004001e07228595290304c501c0180700c0807511500203c0c0d0024407030b4104044107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895191384 1250 895190134 895190137
    0x180106210218070c0f020a03020d0b090111072a0806090a1106160332040906090203070206041115030108030a020709020a0f0819181b030f0305090123 66
    0xd01c2a80c000798000107030a0911581d100070b9684500050101814102050754803500e4258180020402000640d0700d40c0054920541c14600b2a281c1c0c41c103504001d42038500784511202c20f0010201c4520340130450341c8004501c0311000c1203501d20010100c403000706080382001040a00204800c860840c00c00104c0c1903528207a9000c02c5070000c068440700442420400c0a41b03640e0341c100c800d02d02c41d0910664082e111651740c00709043d000b40c44840352403c0c05108000401402191180c84c540d1503080c8440d01c1c040c0c6419800c002c101d24010024000b50550014642da0300caa041400c40903500d60b610001a201c0e100e0f00091844e80501000200b1014804401040700c1d071065002c407180c82d5a00d580d0304080c0e002d1a806d840c00700e10001c1503081c035180a90f100950044450114200a1000b5442c800442d80e8910035244003035028800c217810401f08580303404807545e412034a04031262443d501c80c1c6a0050a50006040000204411490764010341e01c0208002382090540840440b40d646802903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895192634 1250 895191384 895191449
    0x10207020a120519080403030503040312152414030c0702130b01110706140d060b1801120504051009030531090e21040f06020313150206180106 63
    0x158029003c0c01c0e040000d4544540f800943e2101c0300f903003000c0c1f82d07031416206500018016414030060f214880b0b003804140c481c041024512803007140695091005904c1d0101485241070381008007042c0301d0000b076030056101001c04c0c8502e42c0c3c40c1d81c2c07680c0d480c0100000e80034010b4003d401448026261070882050f030000d0405103404e84c1c4186010200d00c06d40e0303669038014881c00c00401c0f808403000c0c841c800214010801a0340030200402c995903034100030002030344000340d0765031410b40030400d0910031b60744000715444410442605022508040d01d031961500450f210044140c0c0d51070000c1c07820140100c054803a184551740300e0f0072920002c440b2110041265440781c07848030359202c0c000316403d46148100c140245170a401000003403015a000110540b442444aa1070101400000b80c031641c40030100340a020298007542d121403022500f203040404540000105103c442000d244069001544590104880101da00e01310682c1000500400c25904000c0e011a0800d124140014265046110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895193884 1250 895192634 895192643
    0x5090f0f0a180b101722021309060e0f030d09061e050a0b010c0804050d02030a02031f06060c050c0d020112060e01170609120309031c0504110a050a0e09010207020a12 73
    0x10a421813140846004802c400034021003404a00415074070780e02d10801501010b800403809140c60103d80020f1240c0a4081844a8450b11400d115040001e2030040304c2d503400d44c41004041d058080d110080d00ca000e484d510680c01c1e513459070b41c00700344100b5800c160f12011820464183c041c105243c448007414003211035489c4641000c489821551040080c60005030300140e1040c1410309000c100142c0d180e90104c04e07a41880f0345800000545ea061040d07040c160001d00f03111540f40340b1102c0300000d842e031a0f801102409002002d94012170404941701c40104c004480389000e65805e4801a90100c3e11658404241c03883c040021599100100f0303001c1c1a44d001050100d4811035140a00384d072100b0441d038111154000081c080c810964800155400c40000415642007072404130b0702442d0000380c8901000c002c0e03251b50500c42130080705507000c40c1503002541d80c846424108800700d072106040744189910305001900040d64020294145d50f115075004051882c580c0c0d544840c1200c8903c1e0001c02d45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895195134 1250 895193884 895193899
    0x623120c091e0a120203010b090f181603060213030519021809070608040f082a0d020c0d08041205160b040303080601050706020c072405090f0f0a180b 66
    0x600005102d51048401d503002020b2040341414003000300078106003008200e816640300e010001080d0b0780c00703418a1154440381102c01461602401d0500300d00c070b1408240500e80c202030060840b01041070b04900030344e5000f01d409a035a00400e015801d034404d040d80040c11314000d0000b188807480b0010207080303120b0700840e5440c50103100031880c5045104160340c4040c05038003508042052500451000350312038080c22040865040da40c462820135400505803034044902c90501105181185c26114070000f1001c0003412500b40c110400f95580e1801e4043c1c2c0d20801c4800303c4141008005400ca5000d0000c0003584e51005040b450701c540c4d81d44042c210707007030003000c0c441d40070840c00a440151000caa403d503640c00f44a881e00f41c010341c0c0b07075400080103603035030ba8081014044601e41000400d006185440070303294000540b001c40750802c00001c3d40c0e0170411000301f04956044e41c41c0e0180d183d0a0790b007241d284100c4248800040c02110841d4010f502c44590044a2050300d0302d242d0142e04070840030741d40c4c0c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895196384 1250 895195134 895195159
    0x417030301120b09031e090a06110a021c050a080307031116110a0909030f020d050406140a1e052203050d08060406050a090b0a0e010623120c09 63
    0x161a80424001c1081401c441a0003078041100241d849421180100c1528500842400902c000c0010030481d02000180090801e00c02d040c81601c800041c5079034070b48506003120010040351903408842c0060722030441489460080268107441052144d4820100c580069051410041d03035042101c65801080c9002c06000c0c40900400440e000d512724002036000e0030f06940d55030690504006e800d590031101d001008035200c0164440c204e02c66000ba140e1751260045504000d1405d600d201d2078004102060104202e0550050902012200c02c1d1085030703110b52002104036400949424bd401283c03010f0501500204c1c2c2081c01000c5a4010313159400200943c40140116000d0740d00c00141603500042105940920413240c0f141c2002008101040e92540c40d00003c1d00c09180c0c1e0813920555680d0a03403a02607183c020800780080aa140b4905119854004060000e56040310109200101500010025403104040741d91000004e148a1b1103030800c4a00c640458200c900340d140038400b069540c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895197634 1250 895196384 895196429
    0x509130b12250f23150309010b0f0609041e1d0c09070f180b0406030f0f140f1306050c03040210080921040b030403030b101b0f140a060204 61
    0x2a5040e54405006003d00c280741c02c001c441e0009041d0010004414001c8807403c0d00e60361200140d92102080040b1030f101e05208844a08540071100903500c1a078111a10a12a407190000e6a983c5542140c00150506142c6100440301c80160400e580d02442c00300b600700a880364080c00d401c445804000c5580b88101c0d60180414a00142d50103000714140e500001a41c0d44a00f10130504204030f0f107004402c5e10f07951000e030881a04a600030340082a195034000c840c2062902c90021080c000d11010f0050b2411068425602314001d8040442e00000c1d038001221000c042d01c07040030684c0d0000040107140b030104010051a0000c3e10100d1007524291850b19400e44074001190145242c0800303402d04000c1c180381022656032884250340c00c00c0052200144020141c80550721840c000d403808219820058104003000201d4004203061105d9408500300c038038510f81412128503840740c4507244c071108905015000c940e500d0b80701e0404d441451800d0b8100f21480d005001120700c2100e540000300d403103030308 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895198884 1250 895197634 895197703
    0x1a070b010e0708270f01020406020f070f0e10030506010b03041e11060306040914101104060801050402031b071101021b13050a060b040308040e06040207030509130b12 73
    0x5100d0300081c0c903100490f04011000465900030b8030900008a804d110901d10300c1d0a100c5c0003a40040d950354042801c120842c2c0511015074003c01000152070031500342085440000c10500075208441300d00f00018140c10181c0c50308402854205088075901d60b542d0b00d11841e039500444044481d040c114003022000214030060006d4562300c6002c0e0000c0b540c44500788126a0002408254060f0b141c28011003c600083d01c03034850195541c002d400c082c001c3d9818503064401c220110390b00c240040004200b031035840380e48181500d408540141e900d85070705400c0903843c50060008203c01030006100800c201a10028520010f003e03002c0c0c680410041d403240380a1001040196000905a216442004c1099119a52103081000000360090702e80f004819160440e40041702c0040b0005001d10851030100400741d07010070300b150300350700d0042960b030018058040c001c120b03401404651200b0800a80c150040b503000d00f40681504c0d0340d10510328020350b0b280001a295032072441c09651088a1419071070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895200134 1250 895198884 895198891
    0xa051c090509130213020a09080c0d080301091523011713021c05011d0f0c0a170c0402030c09090606090102030703051608030f0702150613090204061a070b010e 70
    0xb06468855950001010011480828100d070300009041c1c0b03c1c40c0080192015161165107a5603941401e802d1050541c940b80c880300045100e0345110001c00d00103149002128156070702c09030045085800c40e0145907070303812260024401d4494802200c422000b0b011409082c641c0240c0e07511869120001d14045c200768250744c0c0207449890396a002e800b600f03103100f0f000358100c444000c140101e403654541c81d084501c10a148184008003c410020683c5c04025649020741c0c0400503004101c6031800262400e88188030303804107000f0900800c2c0c90440b0901099110140240084d91760389000701d2803080c2d0798098000c0f18810058500441c10303608001e8180d900c8400c1c10f800031441e2043d20703103007034070b56401c854444208820a0810000010710b124051401003020040b8032259041c1840007a0409407080c0006035152511303401c200c00b40c0c0d2039402d14080080c44c020001211811400401c0151115800c1002c40c0c0c6a003006c41105c02035203200402e840d6002c0d80380e100c9240d0300c07018143c90016058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895201384 1250 895200134 895200139
    0x1206010f0c0b01142706150906160317090a0b0717090c0a0906080705011416050a110f030a0b0c2a0f06040c0b090103090f06060602070501050703050f090102010209030a051c0905 78
    0x1d00003481401c0a407c42100000f002c401d1034140080f00002a21607404010343d04144140000306008254003d0900c0c1c862140f121800d0035103103480304000d5a52651a0400303030482c4040c50110b03803101d01403015810700c806852298480d501d4540100c9689130104c2c03002c41d020780d10034500010b081c20a4130400d03058500c00c0700a0130196242100458000c4607004140e030100e1343c20441c40c00801a0300b4044101c1d0b500c94000b51043c1041c80c01c0c10301884113168031690242180e810442440d503400705205009550001c8269220f031145541c00c40140184400403240300e03850007100c6840b0080d0680da407118440b084c119440707803c0c1c11000548031802074900030404640500e0500580707400c0d0b0054000c0300c406240001d20315100307403500602c050030300720151401a9654400c2c02001e605014620240500703080091a0a4841c1e400a28902c119070810321603203c0451130301d02580c400c3d0101e407070203000101200e4080c0d02605000c1c0d00c0380700100040003c044610a5511650b0041c1655411200e00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895202634 1250 895201384 895201459
    0x305160f091206020f0301082506120c0e030a0320030405010f0507020d0807140606030c010c080334030608071d090114100512031206010f0c0b0114 65
    0x8102c810101c02c0200401240c0c00394090002c22030804540c40514020500c420003400d0601030303640203040c1d140307018010080d0300e64200000d00480e90003159001c230400d406400000c5030150040e0131900300410501c42941030040708001c1040c036500c1480c40189020030880021144a10380701c00b5500e1080340b250a01142404112412044c0618054102e55002401d4414907206da1f0ba1600c000764403c0d8021110f400da008540c40800d039082106a138020b4054005100207002a00081c10764180d21134010080030f40040024401000101a031118a41c52001c0c0e039014070748000c02d24400e40c0f603c1c142c03078006403900710001982c400010307124003218110404c502640460391820a41d4043c000c00021a07503480310103402c072101c0301344501d40c855401d075420080d0090520b0104680a11401401145039009002d50030440c5940300d04560402c0b801d080020111180b2001940c802040f01c2e001342c00c000d2008000503400030030007a05425200100c4290024443e00700361581801001c7d0001000040d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895203884 1250 895202634 895202639
    0x303101d070c1b1a03041b06121a10020d12091a07021c0908010f05102715210f082a0a060612110405180105070305160f09 54
    0x90071103403144150901c00d62191034403140041e680001404804141343d400004010500000081000c480155100c014a6041c50045c0041440d0700100f1812001031b62030241512140341440e40351341c01800030b0300c0401c0c48503038800081d44549c0308210b4000420403c0030b508044030013901c81c20b00302ea0307401100d203130b00030a0900031001202d100610150641c4282070311030806c001039aa0706488aa40b41e40e4000f421030030416158250740b9440c894842e032a007844244040e00e0b1170311007084103070b80920342074842220f445080103201030f4400d0420031b5898901508101050f0410302c0b4a003e403107002c1c680c04100050410030300040004440c01410340c4100c8080d10002403a801300070412403c156400c0020200490034003c505968035450f03c865a00406443d401c1011500034100140042c0d154402c0341e90300c0d9240d84c0342c50062108010300c41c69031080090003c198024072110780c8010381e40200058501080c2c0a8000c0600b070300d1060115103100e1030001200d00c1620014440b81c10741c1c1d00c0406140c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895205134 1250 895203884 895203893
    0x503060403050706091a160f024c1b0807020c040c0908030a1205221103031606021e271804050607030f020909130f050303101d070c 58
    0x2940101140e0455203094100c1c041c40286d58038a01601c0da0742c040ba40c800126200180c10090f03504000c0056401942203041e611000b409410283d5601c0c10b01203414401044c44108840344910703034140d8820b64464440410001540000000d4415070403030040030415002c20386074800e084a440300184d1010090a8007400d142c0c009850100c4541411000c0340c0c0c94082d07003400e503080301a8407070004110300302d014102003950040c2d0381c108080101d40b60a940899001204d0511580750280c0b4440d0a44560203c0740c0302001110208078034500c0d103450314012860004084c0d4054104000c51020381c80c00200a05454070480311030b51114105140040304402104101802d0300100b43c4d4170280040c51076001305180f000c5648141d22845c090122490f0507c0d01504540b071900742d42071402d10501130101262241e02030a600702c001d0a030b07009102c01040c60060007041610000514602000c070501800d6441c01031084181ca83d0054030403c031300350700e0500d040c050750122030510004031002440300108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895206384 1250 895205134 895205141
    0xf010f06031106130315231314070f090e0607080c0d150302040504061b080903030411032109130e06010317070c080615090f060918070b0304030305010503060403050706 74
    0x1d8010381c010004e050350701e032038001d91a141200c0010f0ba094503003800a08868240d00c07031300310928003140403010505180e40d031124111031500c40102012070300c641e10015480c0070028a401030215042040d4455111400c5901504c41760f507040d6024821000407a0045008058840c031403070440c031407542008410800c9901514030100000c20380c8918070b101001684030380c02914030440c0a0310010071a82c07205100303403071041d20030340c00031040003070354024440110b50103c12a030b0041d4200110415089c40140001d040c000e1090600d03903401c0001003503a12481410001d8512803000704e0b04003441032080d81d030880544102c01c0c80404150064070050000034000680d55801000c14140a420030a050703031898000702a940100100b68418000c01107440241c520102c034518080c0d804400c42c6c00c01e080c030400d030b200c00582442c0c411321103640020102080010000442c600602c100e881c0f8640e00d02d6000740940c001d4900343c00182c2002e0001c80d07141000900c560080789e06030f0b203003440c2040b5601d5140c000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895207634 1250 895206384 895206397
    0xb0d0204060e011a03010315020703110313060206060a030f061a0d110906040b09060409021c0311010e0f030a03020f04030218070206070e010212070602040b03090f010f06031106 78
    0x401101451140940c69500c1031101405001080416650400c541001c00070200006803c81a0041006000040603101081290b041c46000980c4402192a09441a00341804801507520002c00d004d590300790149a40000c42c0c000340c086c0c8015403118001d106e034044481c0405803802031480800c0001491a500c08070300d8031100c26441c2255803640000400e1a103000c00151640d01c0d98410300170706864031030b21542d0020803c031410000301504402040c02c2d0314000700700700d125582d241380101c195141c080c0c034030b08040d215030720311003940100d407030050100402d00322601d05640c40d003004c180c1c2c0d04c1800203192039180c1c607181c003d41c100268810114040d500401c0014040e0388103000020058940c2445442c24120140e0f13102114544050700914001004003280c082101c1c00c000080240d8020622000210081e21001d580d80414184400648600d9118000015001040086180c00803c0040c5005c0411009200f143c1c51140344906130703101030101401c1140043d5160001d498050000c061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895208884 1250 895207634 895207639
    0xe0915090c040506210c03060d080a0e060d0906110406050403120e0604090903031415040903022a0a0b0408060f0a0b09090c010e090c04030b0709030f030c1403120a0b 73
    0x281c0b030340b20000b00b80150052103001d55000c58481115203550240340707036a5030000c0c8080d596030030b611b40791001a22800c0103d41c0030b8502800080c118a210344958400310303400e400908116640c0340c4404d5140000d1070b2144050780c2c3c141c170b45584d41c110010003004440031a02a81d8600b4107250540d1a0a13440351100300e00350080c0328002c0100030040d05d92801510080440c0380c2c0c009005040c0d40cc000d800e55032000140e03040007042e40104008104007451070140302e88151030000e103004c41464144e140006020f8000c000385000001e48845408501301207444c460196600c620007a42c811040031140101e001d013881c1a0415400140d02c4155003044c16441644258007260a200200c003086040006030752070b044540040500484550f088144251010340c10b031171100c00c0d458031204c402e8490240d400010000114500481e40c41845907552a010310f41124a0035040161460f0240c401071603034101700c41d51a407641e81510000380c00b106a92250013440480b47d080d0340c9202400c0b001340b03914250750340e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895210134 1250 895208884 895208887
    0xc0306030809280b070b010b0c1e0102041e050a0608070815060d1e050c090603010308031302090a05010e0c070b070807090f120203070e01210807021806010e0915090c 73
    0x140404190800000601c4d1828460b65910741c1806e002c941c0c804148c1024215540801601c064080700082101c03100c0c038400035141c280000070b1102806442140c3c0200a030852020040325804843c268010440e801140c43c1001503a480c5c0090343d4040c0100c803800c0219203100009085010303280310182e00f241000b4401440c0c200650184000c40b541c8042400c0c0700c071090342141c00305200a100f110303003256400184c981006c0031040055020b200500000f042104048041481c0f0241214034822440d4010b10203081d900d00001610010503091054044000541d4046403e081090f000c03160401d4000c0d441100c65501d50506a59480000d0071390000c01040c41c0c1d00050602d181c081044c0900540064508040010b004052030b2070070b6a00010610301c425801040b088d06030918059614007103145d02460000389040c0400b04e8050f10f2000b9410950113810119028011071001380724403003d0300d80c1d1a0081a110510070406421920140660807a401d9060703146802c1059a500c0001c048855 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895211384 1250 895210134 895210189
    0xb042414030c0909040f0c060e060409020c10020703080406110414010c0201120615020f030a1b110405040b18070f090b0303090315040c09020f04060c11040908030a0c0306030809 78
    0x8031448801c4809071b03603a0140402c1c050421101c60800d2000b030026144c9030604281d0600055000d10440c0700d0a20306950000c3e003429040024840d0003a8008042d40441d01c800712820701518030305c400c4804403034152404014230541000c0708195829103005000c13800c020010500195011079401000f41c0c1800840e00c0d103200c440c1c2031802900080e02c07010952510607000314402900d404880441800d10380c2041c482140e080d944080340e1003080211418443c1080c0d00c80c00c0c05503500b801c01c202c071078101c4d052908210500006503800c81c0220186000300c500380582e22403550b154a41d42c02000990100004100400115500500151b0030b000302501d18007042c5000103480d00403000c5d0b1500031017521404010a008150f214003004200d164410b602e41032492030102c08520aa0040b0303001d1080e0a0f01c04414010707408810fa48811000d8010420306003203082c008010740085a03c64a114100610902000d10a000f041c1c120b030760215000741004003100801401201c803000484142d802407550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895212634 1250 895211384 895211389
    0x601051204050708010c0206090606012607080f06030a02010c02101206080a112b060e060f090d0e0a0e09032a0105060a120b070201020d02040b042414030c09 69
    0x340141c0c0b2820040240b680307400145820b5603982c907049000c0d504034104106901704046196039110001340f80050400c25032040c4002a260150140303021015060108041250040f800358021100e21611064550b03500041660701d80400700000c0c00510b100c0c41120042c18821f20107442c2d90307424203141f054200751803c19012501158000d081a5000300c50010a0141c07080094001d00401d44028400724810813044510101d440e11120101030705d60b000d141030000c2030b80300c1c040a412600aa81e514140541500d08004095580019078090003183e250003501501c40b01a903160040c000b0300c000ea2800e413804102207801064406a80000c01c5030b00241c010005141940341784003c0c41c4039420030350100d0325084a8005040c28002c03c21283d09000c008440501c190409910219030f4416544255080340039000b400c2500213260300104001c039a42c1030b076002600a0300c11034104400f00b4646040940c6600c1071400b401008a600446841c480100000c001c2d40e105c0d1461501d02d00d8964028003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895213884 1250 895212634 895212667
    0x6020a060e0c13200f1b0a1a0403140a1416080f0703120908071b09181b060806010513030c03030302120a05040b0c0a0e03070303180b1c05060105 64
    0xb8024096a590703056070031360288078a80e40e000b10004009410a2129145c80509118400d00c5480c440712900c4040c0c11003174104440075001d0f03481100310280352240c0e0340c10b2071448001d031002c401103400072480688615090041c1d03800004541d4900d144510348001c01290755000e0328848840441801d42d0344003142a003c0144170388025004803695548650500401c0d0740420030340300c20b40300d0030b00c00070b000881c0804041c0c0741183d401c40d000d6001000714040c010800b90b01907104801d403600b00f8910314400c90038406034114107801511109540d4141c04401c0381420014011305002c1a60800030413215403007000545103402e040507004501d2501d989540740380030101d03442100000d40001e0081d601d11112240300c0e403c1001d01c0020700587c1416a01c800303c581300104a00040340d00400e150011522401e8408418880501520307603070340d16418010168826075840b80112412401d00007611051001140c107a1070194090701d601800d000f402c0400750201a244c103042000600c41c19084220000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895215134 1250 895213884 895213909
    0x20406060e150405130b04020c060f010627120c270e0105060d080c01020d050a0b030d02071401141b0a03080603030918091c0306050306010f06020a060e0c 68
    0x31944101107880030104400180001e00b40c4040d03450500c002c00442d00d584440d000c50142c0c4035000305100d0034079000324000b4000c2800100c1240311b440140020f1081543c1030605955043c3c1e9504101219481d03400000310310300e0140703400c00d4603c0100300320702c6002c22040417840c6c0c401c400b03500c4040c0d80d400c032090a58007440c04107803403150300305008020741e00180f19a810080503c0000c2c0700e05c0c5003600009442100c00080600540b500050204c1600400e41c1160f071810128407040000c0d0400e00b40000c020329035040a18028410380e00320350000380c0002840812240b908503038a4200307e2600044078004081040c4034004402031007442c00f407000f0f40410300b0329403244d04002d001545250800a01020b80504814000d41040115040940300c01000d5030100100c2c02d01100c0344c0e183c0614092501c00340c0001c0101014400c45240f92060303041c3c0082046400c11070895045988408503070b640640301e03106400259000a003144e00041030750b040300b00080012020390300401c1a40001c10300344005032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895216384 1250 895215134 895215137
    0xc0c010e0f011a0a03051504030e06040f050a08060f1303120c02030309010f0b010e0d020d0503070c1a09280506040612110403020a1806030f0c0602060609160c05030702040606 77
    0x31540d52410f03410000301c0003107560080300c90b250014a0742e15155105c1c940c12598000394444400010103160041d401302000030b001400b0195190b5482400001700821030180d14071035042040001100040061200c1c058021641400816255840107048d680d15911044051041003c800300b610025485203001661454014503a2032510440142c01c4900000890881d81d10704a042c80301369903c2208a8031546c005c0d524a41c0410050001034610301c0407100040a62000240101c1000350f400311404c1100c40c01100075074882542c502e4420140541008a074001015040c00a01d1413040c95805480c01140c2402194654892010a01c1c0798001d40001c004508440c03d05007095542c0d1140411044480012078203040c11a030004a9001851083c03640d55a902e0707a03c010485035503440340300115400300c4c1d010206401850182d0031171441d84600805406800d00144890411043d410701c03804810039041040040a00191900e40242c0000e9810b84400c4c082d000058407140300c3d04020b44421b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895217634 1250 895216384 895216391
    0x130906020412060f0c0801120503070b0a020715020301031e021305090c0f03120d0c051224011d062b020924040b0f09060a0e090c040803030c0c010e0f01 67
    0xa0704002007074404070b1401d00d50480c50f2030f00207800300d03912001039412340b01d4014500701c0494440c24024a10301484401410b9601903000348901e450a0303a005211031403050451100689022100c3d02c100c2c0001d01c07000c2e101d0b1942540c40000504034001c043c0c03586200070100d042120620800000b1030700c045800700c0c0103912524600c42c05140c0015001d03070030003046004203890125843d41c8040c4c2e012b034404000c05561240302400e4801e001e101511800e07103040381c4c0702c0380a18090b500345804204425904d020f0740302601e90300d602940f00305240c628060000c2d000401040502d41440038542c00421400a44048543d005001d8000020fa9032480484103001580701c142c003008000c1e2291511103101100034210305c002010304c1015050361304440c3c43c058803544070340404905ca40c151203081c0045a1240c000a002c04050303801000c070488009050b1180f4659a03100f440c402600e10681c010004541e00c14800219407255400c020503404416500104140c0302e244c1c2c1103803421501c01d5034000103945 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895218884 1250 895217634 895217669
    0x405060604060902070218062b1a070203070f06060b04030f0b0603030702100f2604050c09011202060c010f05010e1b07030f03050411030f010b0a090b06091309060204 73
    0x18540911005003a0300f410440c0b80800c268001254150040d070f0110840e50510001070316640c40500310001c07000c03920310201400007034466060380703e14101021500d0034074080f2003101640740200c0d0244980c0c000d40055107049059100c11041806952007111540e8403003801241614241c4003400085200305043c042c111102c2c86c0c070350641400203000500036031040c4075100141c0da0710f000602507070308182040c00c02c610311b00c801192503040c02c13000c55032050030740d0038010700c1e0519604103a889a0300910584492107030040410074081c0003807040c118801d080a0500e805441c02c10005c02120110306c0c00000c071610711020402c141e07030090f800b803180e9001c2c16040069862407100007000015503640300a240c04c4250380c0c050b00c000c1c01e030000e0700c0400d580e03a000181003044403220001c40c407030b006080355000641201d01c50302070060318800da8040d00050740000b40741d00c0e45000c1c07041e0a2000800705409e04503000288000c20040700c1e00b48061903184c26890010405501c01000503007445078442c0e06011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895220134 1250 895218884 895218889
    0x120a0306080c010215130b18011803050910050415020706020d05030106140a0509031f0b011b0b06030a0c0b030f13120e06070c080d08011208041404021204050606 71
    0x5646a0003519103401074208440305030780c045003580715422102004031a5450300c00c03020488286c0000014510300800040c0111300300440180001902c0d604002e01c5200034441c032604014a15000c02004260b0a0140188924000301200020340403843c0040c1055540d000c014039041d4480d80c00000341c2c101030340a004442e1b0512880c1120030482c02c0c01071079035140c14401442d01059056105240d80d0105004111034800c0040341c107241030040072580c89e072000500140300b1440c4011040071316860841c90242c07a50148003114964080f2010200c01b8826646401000b03130b200030142d5915001e0032824000050300d0f21014000f41001c5850f05e901e9240901000c2c2040c24040c00c00a580c1100040150002c2c3d0080100b400c030f00b8480c41c003c0500c2c0f02c1a00425168000c10710b0080169070410404114107034001003401c11000702c1d564030780e0305903aa0181c41d0710144801c003015107108420130045c028880f242240300c02c007142c081d00c010b00e0128850b0039404480c00a03941140d080c2c20903414040c0a2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895221384 1250 895220134 895220141
    0x140117070b120402040c0311120109050a0c020c09041b060f0e2d0406180902040518071a0d09051b0102070f051e040e060109052202060d0e120a03 64
    0x1403040d40c0500d07140500b00c2c00d00800b4800010002807150392101020300303c581c400d0300030044046101e0901900c404501c10b01848404090198070038007403506e400210002242d010b01820017082e0303000f6042d00702140c01401404e600041064035415240005001c003d15034611510080c40641d4038070342900c0c400f031001400307a120b014179644540740c0e01110711170050808110700030705c07071134000d1505484401305c01040141c140e43e84040030b6800b14100312010712110360808040d0501c22141046642e03034408102c0810b40284802e61200da10210007801040b80c0505510303064814003120714105003502d03000a003590b40c6400c04176990f81202c40c001003031450080444250000900240000720b00b0485000e81c0c10415114a0340304100900510600741c42c0d44901100b203540c094414413025810441183d6500c100b8812603590910b800c0002d1050101040d0041400303080740d424100d2180c045e020007042d90000e000a001c469070310002d94020210030050382c0341c0c0260016a868580f603500c140503084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895222634 1250 895221384 895221389
    0x3040b0a1b0b01180608030309030903010501080a08040b03180a0602192c04060305071205100509060403111006031103100e07050409170d020d0b0d0f03030c020114011707 75
    0x6100d00d06200000160652500c03415a03c2400c6005001004a130010000d00455031000009000010610031501000300080000c5903003500244082d999441c800342e519101d000340900000020302c014040413000000031a00940240d082403403840f0140065402c1070840082250034540c0040c101ba0b18400c0d009840407800031604200d29440f00d403c603440140b0030180c02c00c6103a0125646c01c040030f07980325030109001d540c00c01c04807080300b520b03901003103803078007240e41c09480d140300b0003040307280040c075a004140c1f0400307004025101c2600c43d55030581d0194034030540003d403800b5480c0c4c45169000c852203282c00650058607aa485400c00000b45400d0090700d01d41038043ca8205180300501000000742e441c00c4030002e41c0c0008440030340c0c0c20024504506142007001008000500040a4901e074001c5c001a040c580350801c0021405420480c5c00406240002e180036003034192840464081d40c4420105c107518000800c0c01c0c01181c2d03c1c0c04c0c0c040401d8000d0b94010103a11281c240740b40040104401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895223884 1250 895222634 895222667
    0x170a05130b0913020c07080a05060106020f060405070312210b1c0201020a020925180501030c12201303061b0c11040213150e09060a090f02090303040b0a 67
    0x42c150501020600071000d80079202803c1e90009030502400e60208801001428006c080e10403007201c0d85021034498000b8130880e0014071809510600c40310021034080d0050364000020400c0c2451a0790f481c400e80c005071102014480800d8000036682007000140484e01c84e84800014890800420040f11a541c58461b11480c010300380d480005076000101d41080c1501260f200710700396554070200e800010310601c2888480601d078400c0d00440e80024040003031102d260029090551501700441c125015441200002000d0420580903041c0650081c06000036501240402281c1820701e43c00c1c50340b04541280e81c2100442c404c10a0000d180f0540a1541c0c00288e65500062000380083c08400c8a40c00070b0015507003c2010040c40d03442e80d0480d03d1162081030b5000d40242e4400320821440b000e89040f1011a022414848042ca445051540700b00001414030240c00e040c2940c05006158036444113004a6007000303400c100d641c01b04042c3c402007050049060391000407400091800102100c1400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895225134 1250 895223884 895223887
    0x8060105130e03091f02010b150304031d031603052812110601121109041205071a09330106030f090c030503130e090c0607170a05130b 59
    0x881030352040c0c01101d40e40c0d081c40c0042080d030100501181540b1801908981c08007240e4100110281c40085c580360185854000308181d00203c3c081c4042e816445982c0c0050400400008000a02689803120131103104900e0001e1a00000f02003031604000505a14560f9040b080c10001c000c0308101589508008101d02410078048c1d007000840c28110181c02041e66014440d040e40051003140c120241d078459104660165a69104406490701d500702c2c1510320f040c56080403811810104505400fa83e8080100340b003040384800e089541e90041c03a01218a440d00b0f2001e07400610895902600580303543e8094aa40c031000544035010688000341c2500341d61207102c0b062609202e0702a01811900c4900f804204004a40120b00080010b00c070006c020f08031002010060040000107801c42c02d103086581c260554a03565030001c5808101e515112a5001000320682401e215024018691003a0080d018082904101302055001481d00c0030005070301103070920628031040c0090f4028249a240e80703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895226384 1250 895225134 895225139
    0x60c1e060a1104031e26070309050306160e0102100e0f0f070b0301030f020d061e050702030c071a1c0c0f08040201020604030815030a0602030609070206090d08070306090c0e030601080601 82
    0x40c0400d4417080117982078800c0d071801e807405200c10549090700042c032040c442407022054a44480e81c9400c0020260300041903180d0224a90034002425401408104150201c10707415480464010110119150460054200c10a840315203401000c51007240310019000ca024118165440e1140c419810719259000348030030000540c02104503415260800b036082c1081d84680086442010010303402000300d45031502003610805007143d2042d211200070000d100c2a250301208a80d1380c01860407122160304214420041c40d005508620003500040031854140040c071090400218040401d0b8600252143c10744e03403640317501c00750411561030f0a051900f05030030240c0002b5035400000344001e00b44aa224046000c2e1b40d00940c00c44070b806070007802c40c0c0d04000c0c1c07032500501a4205892450151b0903080c0420141400490103d04c07440302c7e10001c1100f401a588112051400030300100c051507660700d00441c0b4049103028191202c0c8180d01d403030820f0441e1105040c07402e10140d000303540581000005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895227634 1250 895226384 895226393
    0x100f030f090f3801142e050702060c0c03010507030e0c0d060902040603230a030503010618050907030c2307020607110406150f0305150607081303030801050307060206090a02060c1e060a110403 84
    0x4c03181b0b00d0003e010004003590072031011b4600f8451083e029500c903101040c102c07009800000c003031850680a80c02031040d619100c00580c15500031f8500c14289800c029000d01040c100013091310340581c0149400320f49060b080d0082400c5400ca500140c40c85a481c18808215180c0c0304032500000d2820301c01801c0401d45a20010600c0c0010b000c0c030800c10015401c29000c1c0260f8004800280c40c0040c5800c2850400000c0a0000c04412510501041c20031521500c08040c00b044414662032107400e8500d840f101d54200609a40301003421030341040380305482c0d0300c10703140c500c940c1d00903200d44a006c00180016140241c107c54540c0030500416040804200c000d056440e0000c3c0c0c50038082d50a0390301d8041c07510340383d0f600b400743c5002c0c0c00b01c400300010700005066104098034100d1344198181c6110303641380d80c01261160710494010010f5400b0020300e1005003000c200500b0380c014a031056032000790302096072030461b10301054081816032010040c4030105a80b0312a90040d00700719940765150520756942d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895228884 1250 895227634 895227679
    0x12070f020c010e030f0f1b0a030f1e0803070207061403040218100b0c060106030c050336060403031a031b12010b100f030f090f380114 59
    0x1d060401c07078901d41c46203c41d10100080c1031070141401c00e40d85d0040003a11481d40d1030411401041401c51202100d1111342490240078003034a800540c0ba2000c909151a00106a0642210b0500406030b07648010086045840918010f54036640503184070384c47d00744000e0580e03402c5404140c040c51308100b840016958800c01070f044281840401c1c00300e035519011442e403a04941e0144c910904000340c81c03d0a0b41011030b002d41614560345082000c83e50202c4121a140001c40700801c2d20108010b4a07500155180030321003908841c0d000e404551010000301d941044800c0d80c048002c60349810102c90b0400d054460301d10038110070b400600818160424007480016442c52042c000d50128900c030320040829007102d1000340018020020035840702400804e0b0500081152000a260020034034401f040d03401021800c942100d030140e0000c03c1a222550000f01100030032040c00c1100001c0c0d103400d040895200040c0500001e8104a90314000408182c15024498980709403041d40d0101d182001e000c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895230134 1250 895228884 895228903
    0xe0f040201030b0103020d0f0b190f36020a230714030c0d0918060b03060613080d050d0506030c1503180316052b0c0c0504050a0212070f02 61
    0x1030080f8140a0000060b8000e100b0440103819450404440124103c0550015020071f5402d0b00d00b01586e071100d10078014110103500a0031038941030400200010550800c0d070400c0942a60034140f8600804021522003803c943e0545082c140c010078480c00c0710782c00c400d500040e0361404001000111041c40f00741028440c0800051400d0900c1058020f40e1504005031030042070303008211041c03a194910050400700762482012004d50712086559080c100e94003418048800c03001c5400c0c11500c2d04000c2100f9504900d03043c50406c4041c0100142c000030030042c03012840b07401c0e211560740d440300142c4c0a00303554009041034001d60002183e21703403944401c0e02e9058100b80d010080da4894980c0400c1d441d540c041c0c011420507030b00c40030a05000610a1004504a1900c03071400c4400c4010f007142443c055002d00c10024070642c2482403010340d642e01412400c40c01c2031241d903000001c81d80380e01c00207044810a0321404841540800c10f00c081d2030641050a80011081c1410842c1d1103244070002d55403800780 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895231384 1250 895230134 895230137
    0x30b0f060f04180603230634031a04020f030408070c1205060703060602060f04200d050d0201060f14060703030204051c020a0b0702130510080d0e030105010e0f040201 73
    0x100e0603001c0d8a05020754025100c2107558542c212241640d80d40035005030b020646500808010400c40146101c13110b42c4030301c00840c0580556a10300c0522440c10900c1003a50740e4041040051901c0103120300d109400225035524001904040009120004c610032400c190141348100901c0406200e400306581d402544414019581c103414036000030400d220780d10940e500f40f00d101c10380c400c105000c10700605c52180340c3d400304110359913841d040381d4814041d0b440e0b002c1c400500020038045256502c290f030349034000c3d420640700b420000001c0307074194915038000c0c0c90a0304441c4a00f28010b0782030003450004c01902000c0c100302d030b0814034070404583c80100344a02c101c82c0043c1030000c02d400b039015a070003440300230200c1e400b440c12a03d82c0400f01c1c82c0c0e44000c0740b18102126010a860751404240c2d500c0036000782c54001e0180d01c0182c45e500505000e0250f8150542d204030015a0800c104204e2044815580d20898210100010305d401e4441c1a00301520b420041d400300300300c0408041300158080d409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895232634 1250 895231384 895231387
    0x30109110f06070c030308071704020f0d140a0c031403030f0a0b190303050d0e1903201212070c03051615150302031903201c0e040b01030b0f06 63
    0xc0c03400030300907202e2003c00401201c040c100000a05812925152082c015a1202c019202804d0b5065070460000c4800960000b0018031160590419826150845110f19440d00761600b10903000c5241c25041001110940c5280c40f050080001c1e803d401e542a0103080021415800e120328407001e845001440c000415540745008101035485181d40c0300307401c2001c11815081a201e050051059120702c45120180c1c1c1450500c00d1941d0001606402e50800340c0c0c1340403c42c0e200d82e50101c561404202c01102c402c400c103050382940c00070038071500b0f1503541d448bc2d00d55602c0740f840c03001242604000f0310a4003403000407d0f01001181d0404116401020f50264146146c0300501c2d0003102c0e005d00c00c00b0380c1149480e01c40d00000c2e400900e00e0000c00e8170700840c200d03980c00828509100904041a200400213000d51f1684011811219203600e100d07143d420641d40420702e0030b40c107031400884140240001800b0b240300380040e03041502c00c40c40c01080130f10b000d100101604c0042124405415032031401603c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895233884 1250 895232634 895232659
    0x1d01080f0a020f1b15190b0f09010803190f0c0f390b03011d0711030c16141005030a020f0c0703060c051204080315191403010911 57
    0x7072035044800b218800d01d071040d116100380380c5070815407042c614140805e2040e05291048034540080d00751141000381d407540300307402102c05000c000e0060b8845c11a08800d6075401e00b086031b501c101603540602090b100458660400000300b4180e940368000340c5040c000b259400810145c3c0c801c080000c0c1319001303140320000447e10310380050820250200d1700c84003881900070b07444001d601c079020107011040c5042454a140c0f40d0804034490310003032042404100c0d441c00c00090b0b000c54441401c0d4440168100384220001c01c0350800c1c116409000140015004101500c0c01700c08010030318000303019091100401410000d002c81d0758070360094000703018884044001099414150101e580c5010ac807485035403101900c0c404a983c1e00440c2c0402c961640c142a55041c00358403d105564103000b0302800340d619074032145c540c4141b607880540171100d04514100c4107040c80e1144501c01075003201d040010500c01d807400d00c90b90b80da50141c803982d501c40d0341080c85d40c0003c90300391100f041c4904022180620f0036403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895235134 1250 895233884 895233901
    0xa090315140c04180203040c0905040b09010e0106050a03060e070f030609020a060c032c03030a03020301180b150306031509031308010e0727051603180b04080706090219061d01080f 79
    0x180720351080b189c143c20039040104204c0e003145528041c4660b60002d0040380171031100b203400c0c0c038054040c454124600340010400702e550742d004105450384c040d081d2006240c0b5040041c640b01899041950400d484404810071030a00460301c00081c0000c2c9000c0745c10111f030350f078001d0000c44a5604000340c00d1009800403205002039200e900c071010010102e0350344030198000035000c0d4000344114120246890300071813546205000f11804074000402c806447ca1201c10717800700d2900045c005a4141c864440c1d100d4140800c01da03964007883d030707540c021900c580d02140d1401c4558500d400854481e41070500c40c0340300b0000090404c0950300b007566907414139079102d000405080e00700610003070560f0805045c0200881c00105030004140c1c1030f90700340210401c02813010070031030f4104c1e8000c0404038038100007408580820050554107102d10f0b40410686000e40000f00051294500038807118000401004555009041c0c4820401101d01001100d20014000307030990400810140c03801401800046d0740c2c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895236384 1250 895235134 895235153
    0x216030c05070b1b06061801030b1005030724030c0e060705010f051303020d0e0d06110d0c09060905041e020a05070c08011505030f0705060a090315140c0418020304 72
    0x1010002000c0d43c07a81441c020401c00e0f070720b04c05401e400d18003454001c6046414800300a41c81200da0903000800f41c0d1039a503804404850080c04440ca500a40350041503998083c09484000c01c044202c010041384c2d1508904441216440d42c0300905203041614071089070084122006094111019900c03442103080042c00752101d40c4c0121450f03031500d0b042204064001909e6400c03036010368200d4620788024042942c10101e80c002070755020440101c110006000f981141003003030000042c40342005003000504090b2100000f039200400d10082041c031916601607100700040101b02e8040c4008091141281d41c0c421007100d25902c1540c0001d4131461031809a02105c405c980d100d00440d402c19583c841050013001c141020b5501c241d9080790000b520310340003416500b452500c41c080c0000700d03d000c082200c2540b210020fa0180056403078004080354002c001010850300750500030490420644801603076003030051408036152420704c005c4c8607655210001c07000e4141d105500594984450612401c3d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895237634 1250 895236384 895236389
    0x9180601081605160c090b01020303090c0d030905090f041b0506310b03150d02030c040b1f032c0312060112090f0b060405011406280908100216030c0507 67
    0x703008a1a0130f500410505400741012107984e071030100403001e07090b4012a10780c481500e080810f80d0001200148a28001116a02c558801d081400155a88901040981301c040b50100c1c0d600305800204418800b4a2100c07901406613000390740c00540c18071001907124000c107440f0821a07929511405030108210f24008245500c10340c410110365070364550401c1560046030310b621a80903001c031142e0030b42402c4000d01c1002d507009000e45901400300042c40000c10012119a5100709503110900866440f0041008003400a660200752402c50705210900020343c0b42c035840c02d407960f4074510650301e58040191061502403205000040d00c808004039603041f084140071541c50316094031201000801c1800c070360054886d4001c1507490351070030100811a2024406c042000034011449841840c02038010030300d02049084000800601c0d40210603408903c10030705010424400b03092080340c0781001405800d10841324194a4a03208180045068507848001814895810001d900700074083c03010401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895238884 1250 895237634 895237657
    0x50f0115050f2206030e030703050301031b05120d11070b030106051e190f0c120c0201020f1005091002040f090506040e1c120207020d0f051504050309180601081605 72
    0x100485403100c00280703e440c414200420314000500c4d105100c04001ea401854240d1109402c2d6840d40e1900c0d034841d0a40041181035206042020a0b02c0c1d45580300484e2850020004105144040314060030310002d2100b250b10703076404003504000f00b5145100f2a41540c402d8680252100709440c403003951503044642d03030403052101103540c000d01c04850801e0b2203070350304640e1000c00e4807890305015900700d580804d015088040c10764040440c1800390b0b8104e00300034810300c126039003c00c0f0300500c81c0c1407000c540d00c90000e0079100e00c20b000404004104030b5405c0d001100f02145410f241c025a03c2019442e485807a0030345d920f4400240143c3c4d2681d01003020404860309581881088070940ca04000c84910010003007070f040f0400c070314110110300c240d500389503001d49854070340f9126455404540c002001c003111644074090f03800f5980039021010074003032481a0b0086454901100402c10328001c10260704210b2040e81041190350703a40f145426400181d407035001e0001c0307205800101c23045d1185403050103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895240134 1250 895238884 895238917
    0xb03070e0c1c0509070e07170907030506071b02040b0a12141b010c110a05060d0204080c0105180d02151803160b030711070504090803070201050f0115050f 68
    0x28294460001400303030003103240703100b010340e040010101d04440c400d0702c0000740303030b401400d0034080380c46c0c000400c5402038428209003800c00042c01d0000b01d43c1000300d0f40380406820510342041041800c003d010b400a8090401c403007865050000c1c45000d1341e45400192040e82c80340c14407407145e10344111032030141414001c0c0882130103c500b08880000841041281c55100d8170100c1d007517240107254440d4500c0c0059513003100580141e00d0310001100392150895125000090006040ea0340e04000e01c07103e90848405a190380c5419540c034102070342c0404131410310004014a41c5020302da4a00040c3c2800f048907000e14134510703400440c041c20600841a41c00d0340000441c03032a500031180c094040840128101c800b07800d6601d00218440c2000e10458115500030700c0403840a900031405014120108422154a540d5582c0001c065400900e010b4611190000601003055820f010303003607001c094607510100030351511b155503000c0c9070091b03c840300b084008a080281d420b484004c944070401d490790380300c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895241384 1250 895240134 895240141
    0xa0b0d030503040302062d1b0a020a05010605041e02031e0108071707210f05030f070b0f15120102040321021b010507030311070516090b010503040f060b03070e 70
    0x79025610a44041e8090b11415002801c0079101480004405403006004001c190814039070345d00040c03002c0e196090360007240c0d01c2102e600b00c0c90000380c80c50f00810f9006100442240c03c00d5405c42d4030940249005a0a00c8803c08011840381003502041030502c2c0016545e5907a0700340a40c210009200c1504102e20701c0d000010712000000301e480544000007d0072200b42541d065650344c8150910403030100050405004401501c906800608240166070012217020300d540c0b5142903600445421324000c10210b00d41c8203215548407025408610700c08518542c0c103110b8040000241c901050f903100f0101e11828111002013901518004d40e4000404440c0035200507188843c90300302c61304400148506288400602c0c0402c1107108a50010b0319018585504d9441c1107001e0450880d030042509020041c1000062082205000c485c151400c0d45000c03e0a01040a040d1a5188101030402005009010106004100905003181e006070b001581401d0940401d0410109601148141c0c281c074040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895242634 1250 895241384 895241387
    0x90d080307030c1803120c0507030c0918020108011a07021309020f0102031318060b0307021b0a030309090e070312050d140106230c0111042c0f0a0b0d03 67
    0x140d405416180c8043c41491007090040f40d01201030010011141001c0340200045a494140d580c04c5070b036146040c09803288a5140c4500e0b001c420351089400640d162400c0180d4a00341c401c03030312052607400303d4910000749c58000034500c1c041801509440400700e0309150802156501301e44211b9400780141380d4442944005400500d00400c059000b60640000c140f655840801156081925840c19400175400c20b6003a1442e504070740340040c0407a58921010400b0850380b0065842800d050740100f00c40c1d034080318142c50b102c100208942c0a039101c0c440a10000b6000602001900e0310381500184145966a1241c82d00308694005022640e01c0b84407035031910f41c010000c042d806002101404180d480d813071001d001007400d10a900000b012103600c1e1030b0b1070190341420060305c5408a0b000381410b030640c02036070031184241c0c0e691140d0762000504101c000600920480000c5502c500b208100d002c0b0380c0c0768004190020800580546070400190380d030399140d0f0007589000f601911030496911940340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895243884 1250 895242634 895242637
    0xd1704032d020f060c031306050a1d2b1b08040308040305060f0f0610110a060606051e0301210503040e040609051b0f0d020f03060f3102090c090d08 65
    0x1c05025400340704c1c001028420b0110440380558000c418150706420035460791701c0208009081082c419442e09032855550031020081440c42d44d010001e000d81c00a20400150120030030641405860000070500042540020241103c40b65084101c1034081e020b1401d070100d48283c0e00020403000d8080703008010300200040480c4074070701c0b403c0c00301c1454503820940c0c0380b40d020840d95290b014a071110901d00661040f000807203144030304021a0401a0300c0c0c1d6500d410340d0200d030004400034901280342034400b1102d50010302110041c004642c9954100303103080702c0c8445045e0084a1b104113840050040080c2042242c0090210402d685114142441d180c000b506140c407080c3e94500c201c0111411505008000c013500240003080c0b2102e4218034424095002c0c210841a40c0c4020518002440794405001c02485480c000d1049a02e51816113034141e0030364240011100da55101c600464201d0150f460286800c98040321400120740e51000541e51512842d1207a80e0403900510003a01003004420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895245134 1250 895243884 895243903
    0x10f050904060e10080f03070321060603050a0f0e0a020d0c0f0801051e070207060305090109020d050c0909070e070513090f090c1208030a0b0105040317030106020d1704032d02 77
    0x143c803410845e40d2201400d5032015a110181c035580c10400c034078000030b4000c004800d0b0b100c0c5c10200c3e040f813182c08001c468048600c0b540c0440c01198503003040054401d00c1c2e20607641208030444040081d48894100e880c0d44445c03211009014451022a44080c44815072049006181412451113943d854100d00340c00b91a040d44c0f00a24000106a0b01760130350b0031141d00b144242c0056000b031040c286440380c110040d00300905009003d55880007000e0160b1900c0c06c0807049035000f80c00070240b0200040a0207003111009010b00582d030000c3d40240301209040d400140c10082ca8909141c803811466510002100c49502180d81d45203001603c0142d60026008142e0440c0544140542d150b035075540304100d000e45030030041c1008020000610031b10640d900c0115903160601d001400c290b01c907951101c8481e510303111083d410f4030100040003a070b070341040410350548007450654080c4d080c140a91048540c044c1c0024140244c400900b03202680d2440140c04a240c0050701003150442d80c070740a5105e14014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895246384 1250 895245134 895245151
    0x9021e070c0321120c200303100b03240102030909071112040501022a09070504140f18060d08030703090b06030105060d02010f02011404141b0609010f050904060e 71
    0x44802a5008203610b070b101c65003c6a840b2858429840361000008202144854091003510598000304480c4a030048076908150700c0191303540c1c201103010000c03035140da5000c0c071100d8504001300710036204040340041c082e0607100264080d170080100140e045003d03010301d03140c01c800d0b002c0411103101d030f110780c006100031003000a44190454140c00c40c186842a4018140540d2113520180c888104034148130022900509070301c0c6964501c0700005900480c192101800144c01041c00e004a22201400e1002050211005881198140c020030664040c41c2d03040007140c60b410b00015119214600050400756100d55000d40d80e00d4014000f40080a41e503034140c40b904402c2c2d00181d01400c0501c5054042c15008002c11001c0701650b00454604206181072000c5540303841031001801d05420005000e144103411700f24100d09290185407610100307500300399040c19261213110940e12000f003181d051030701c2840c200107107007031000c020340341c500ca1055681d0b001407a160340044e43e010825611030103034103071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895247634 1250 895246384 895246403
    0x506130b07080603070513020f1306020f0a02220b030a03030c030c0206010f360902011b0308010b0f0408031309140c0f0310090e01050a0507050c0709021e070c03 71
    0x80c240c0c02c40307a000007181c0540e0194085032080c041c0e8504100040c1c81e08400d58805460032822045460050b00001c60420011340c13116010700030b80d601481145200b9800800a1084c010360350002482c09804480d008410380220610100c1901c00da04007400c640e90160403180c420b801d6203001001001000140300010303143c45440001c252020548904031038020441e000c456052400d62544001001072400c0c03141104a45801c42e112044985480c20100100000e184461400050100c4042e81003c0940c14001d512400020744c01440076410f469050038103680300c0d60302403c110f41034451383d040394840d0f100225116514904940703504003516100c072014050141244840c1e6600030b0207680d0703200034030014400104006102005903030301c1110540001c90f059521000030702140c034403d44e40c01150351070314100011060035000d0342e90800686d21381107207018215541640c8801d058094007540e039400040c24080b0410640e598512000b08107501903844c03400d442c00c4228001140300c03c13a0010130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895248884 1250 895247634 895247641
    0x303090b090a11120715030204030b0424110a1107080106091a0312121e071815020c010311040b12040501060501080c1206030a05161a09010c08070303090506130b 71
    0x104004142a42c12042c0014030410303080c00d12151b00c101e042c0c600d0034105a401e200000114048011080c0100d018801c00b440c14012001c41200e20384030b125228140d141400100d2000c3c0380304804455a0409a1070890f00140490755038030b003844031950040d4840e45c00c103100450702c0c00741a0300041c850481007101204070080340040c1a00c0386a03803080802c82c42c10034410040c0d0b070a00c5040c05070340109044502c0d41800c0a010000c64034480c02d03201100010f11440c040c261507502c0c040410b001c2c0c444140440081880d41000942e80d031102100d5074100364540705841ca80003441820344002c0c081c2c900703016440b000c000048288a0700d007140d066405e982044030002c1c0d1540601c00160041c01c0340359010b454849483e40b0400041800762070150140b15500301d86000c140305021801b40e9568903402c007890039180000000302c0c0740065400b843c0b000c1d010091150140c1c0c110b0079210105a224030300c01c1d00da00460400303800070213155a020300240145400c0211911020b00e0492502c1d11072004441d550703d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895250134 1250 895248884 895248889
    0x80d0e011e080106050c120a0c1b050a05011d030a0303020a020706051201030f0f060e01060915080601030605091e030306210705010305060301091a070f23070303090b090a11 76
    0x105101107690104010000500032a4070a400421000006804840058414100401e034551040c500c282c000761820b80810100065190707030100320144400803023105401c3c50005040c10718103203d11340c18455500442807851030349064414401c0b5000b01a241043c0440c03c01801030350151407540b0060184013000710316240200e05a4100d8009548060701503821541c81c00c890f00d0074100309680c3c0b1564085102d0003d1303198041da9207519002c8001007411460041520107880d03542202402043c60080c080c050b5180024200781180d0f08134901103008d0702d825900b1420705101c800c0388401d018100103280341b4010000f004500031002901d28482d0000c00e10992640e10402d5800340c072158000c1c400c00c000541c0b1a412258001c0802000003441c00d480d030b502d81758140c3c0b4002010230034550440c2000fa0464014041080200e6181042c2c10b40380032108021000d250012410f56114902080020034140b0035841042c0c515030047d40c1c0346007410f0880089580e00b102450440d0604901e0006140c0350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895251384 1250 895250134 895250177
    0x15120709060c02060a0c02040f06091b0203180f1201061a16120210091505070f0504150c080c100e0d051804020c160305012f0310080d0e01 61
    0x32003480d602c608a0014030b40c00c11400341d2200c110002007110007290840543d64038801c00c41c100c0d01c1c9400004a0b140340c16a80c02c251185034551325041d40c403440a48100d00d801008a40790ba480e41034902c40500007800c009101030014918503030300031000c0c200594041d04150f01400a0702d01c292490450101c0c8120103544a1060044151030b039041c5048030070007d2404201c09100c550700740196100c0140d41520704c400c40c0c074000c1056a81440a030b088505400d0684909508481103240001c2d4141c405070340544903120b1481030458520300b240b40f8010003840740d00c0402c10035034403040b0503a03525200740c002503881e103400051103505403606581c0e9409072000141c10003010543d45815007010724644114041c0d50b041e090190304a6003c010b1200703022424820708130a414120307006400707a411414610f08642110100c08110000f54403a40d0071000020080c82340d25046450382c690340d03035a00528200680381c070340c0445030910030070400075420b13a0000160340c0d14000030fa1360f40d6134250003001aa1038a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895252634 1250 895251384 895251389
    0x4081506040b1f02100c03060e0c04050f0607030e0612011e050a060513050303040b0a120509031206010314041218150c0f210e04020a2a0215120709 65
    0x105803c4494181c640410004000000c00d941c0103a9440b20b00300d40340001a1030203481180002a540c1c001800390940c2500844d070002e00e43c0c0001402d0504107400b10360449402c040d414400d04c07010401c1c4c01050301c901c10500034190060034440e22842c11112465401c002030181348581040e440c06401150441110401121001880b205c0380a241c1041a5034a502a804065000c4020000030650b034504100070002040d190002c01e40e12510000d000340403040710a0b40c0b8200a0804081c403604510000584002941c15105030a1644a140058004000d001e101d440288610001c00c010700484050802c2c0349001c60716032805018003040d4803469003c0390b0080d40c110113007241c03019450038407c0020071140391150030240707a000380548910a50981e003000440c180032303041c05101101540490411020003040c0c500b9804e2480119000e407040c0d00006c032141c803c40000e006000542c00c42d640c070f0840b190300030b0705c180d0101c0388040701d88441d0307030003008a8158656000c011503045485400203404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895253884 1250 895252634 895252639
    0x1801090302120d2d060501050c0a031d19210c0905040c03150b030c0d080711211005060a05030a03050c070b0408010504020307050a0605250804081506040b 68
    0x989402c4400c00c034020307800440328009480c0d03079001d05540041036210140900c200d481890b2511040c000c84800544a9941149040060900034034141110024074440c80c140c0c50306103043c001708044591852030603c82202c41d402131000400e041c500701030400480035240250388040541540710482000c6800d2003800802500800c542002001281d80c04250403901c1a2180c0034502c0d80d030340f1102805000c04000701e5885a80782000842850100070603d1085010340f1030701c0034140d240c3c8034500740d4010780501420707810740c10009800c9a51a20f0510b01a03041c000108502d07424881d0010b541c4542d000d440e0303100380340707402c011500c20729148214408440f0024001e00c10348030140d0302203034075400c50a1460b21920a6082c081041d8a0440140c806050074500009040c80e01e8010546001481e510140c00f40c0a400c1080c0889940308003290014015401191001c0c80f40b25a021a01101018090040540400d011072084808216250f04007a2001402c42c00d48441c01080100e407040d501155 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895255134 1250 895253884 895253893
    0x90c140304261c0b0604050303030906010f0e0403090b09011206090e1207020a0510034512030c020a0203121b0304050a0e0406020c070602100c080c090120030708031801090302 77
    0x90701d1401e00e411000c2c6804c0c02500060806640d0000f02e49583c005998075015a0030280c010300100400800c0c1d0001400405140502c42c24a074402078100d04440c02911815100041c0ba200c55174010401e000e2591017801c5c007041110b40d110302e4080200790b11040cc1086002d10400905641600019150a5a0000c0030481e01c00d103881c5c100400300c1e940c41102014180c41c2c903c440c072004a603000021448a40c0754504d1100b403000c7d4625040550801074003070780100c400034120003040c0d04140484c640c4c402401d001800c0c400c1c01c1e03c12780c54003211150095051003901407002c000800c2c800074004d41c5094107010b00a01700e419414030b842e40990701401da0800c45070790701003041c035041c900c040350058002d90005141c0b496030034040b4280355103900860090780c4214401014040540305500d408c03409490007414600382030410f00440c0c86076001031410400c102e021003003800c1280ca80703c070042d9000d1045a590302c1c0a4074000090b90421122030110184506e051140003070123001e49160f041d4941c0c043c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895256384 1250 895255134 895255177
    0x20d0b190e0d081b030108010203150907090911070f0615060512310501050f1014061b1504030201060b030c03040f06060906080f01060f030b01090c14030426 69
    0x220f031007210040c22529846180c0a2481e440000003005601814401c1c0015990389004c0e4001000d00d1a10780b4124051102c1c48100b009a61303200040400349d40c680000459940301444000805000c2c1002c0a05a080322805500400489900a0704401c1c60507014103d096900d45003035071280038030b95600064103500000a11440b911190303140ca07031801440c81800d150241c580c0f43c40107000300c42c03088601d03030342d20020700a004400c600703820752109440480000207410b0000070403c004113584114064840892000c20103581d151400c031828003c07804588440b11800072040d03008105030303004d6000d54030303004001c1603400405085a100f2955215007600c0c54540f5591001e80c00143c202c142c40c4650343d8000030610b02041d02407c801001800e0082030303000780249016007142c89aa200301ca2060345050b042000403c280109811103004d6000010424146a419078010b58408420b81c3c8104001041008000300d242c00c03c00c2601c600541c2c505812078505154011b4801c0074401c9181c6039420a60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895257634 1250 895256384 895256387
    0x403030305070320031504020301050a0e15030316031710050909011e020d0e0a11090a02130303050703030e0f03040506091807030518070b0d18020d0b190e0d 69
    0x1a0b044800380c980055136a510990000345811101c14204814400000384009100000c80b040e800070412201103165515120004004010380d00c03a4803000013600002070840156410041006100502030742e50721700340701c0006c04030012051400c40c00320714400d800c0183c0c0741d41c3c207680e14480c8440301250524a4103007010020048001065070000c3e64885540000c0c0302100e000608092050a1003d81c41c0d0444007240010394000d00c000316900e5204014410114200b001c0500b041c1c10f007030307c090702180c54210409003c3d120350200070201c100300801c00000c040c4d108000388182c42c000c2e42c00b000795a01d01c40030203494091a00b40704040d907005110512041c03400c4401003540b600700070007602e00c403036030900041001e4a08562070740100782d0711800c00403003c800910087c0b0342c2024070083c02099007044241d04181c00b842040782085599250552110480d5551010307245800070040102c40388240351601c0380040c2202c00c12944461411103900031072107801341017254041c0303401a00d001d4085200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895258884 1250 895257634 895257641
    0x1303230309011b140a050606041805060a150803040b0301090c02030304050d0e28140136091404030e03011401030209150901060e0a0b030708040b091213150f0504030303 74
    0xa8444c0e0400240f40024060308002c1903c409204002070600c6242407000c110845c1e25101032140e405075104012000900c0103d0501d501000440000803104002c1c0c00c0c0548002d225080240705110020f0041160005100a14101c9004050078000111080383c12600c0c3c0c00160b030010000d81c08941007031403403801144041240300d4060200f01101202c03010714466001101d42c0e9070361100451006010350011160050407150003070070813080020078000403980e00c0c801801200c100da06003041813803103180340c1610320000385030064083c80640b200120b2801890700545040b004a05a410030f101c490906005541b110400c000b445640c0d40e181d030702841480c40c40200032001416000c4843c41d103903039900e50014060a4a991000b8020003020280562a01a42c120031483c3e40c09208200499502c069402c2c0d018bd4081e0400d6141d4070341c10107803840c1c2401c07070034055040c42002c24800b020294a00c3e90700210303100e8610300490b401c5494000c2e076000f10784860800000c0d204000c00d0020134080e41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895260134 1250 895258884 895258937
    0x27050a0b06060910031a030f03030a15030f0302033601081306060b041e0b0702040905010f1a19051005070309030b0f04030305060306071d06130323030901 68
    0x10b2005180100440c000350010150440c0c40003c26943c00034403417213000310702d02054507a100350000c00052903282c00f03260740d0740002804840040d0311001d200c0316050702c1041c080011548490051a0700829140194490b0070118028200d07120807401003142040031041c10144800c110f0014001548140c011100e40c1e00042c0144003a20a40c40c03504005891842401c0c01005405003851300d4030b080592804003c074089242c840842035448040c000307031000c4c038101c8259560442e00080d5214052509502402c241c40b0b802c0407040c030b01090403000004104000c0e461f40000c03520000103000c501100540445180209170f008a518008089840d021784020a0401c1c040d0820000c6540e4a6480300704001d0301f01c0d07180411564a41c144800c1640500500b41c201004401800e01880d124100410114014100200c0348294090303440c117588940e4121401c80070642d06a440840d103a09207200074880c80841d01e0040700382c0b4002ca0300704102c040705a40404005946008520081e214415072016200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895261384 1250 895260134 895260139
    0x905130c05040b07030e270121060c08010501020c030106030f02220203040f02104107050f0c06070c091a0d14060714040e0c0c1027050a0b06 62
    0xc000100f080c1c100d0902400d80e4901ca565401010444242804501140429192158103514520061803001c0c07008060644000303040300d54505408440c1c401c0c4544084001400b000d01c6d2141c0400b1072544079407c43e050b07400c00e808440205500c0030905080711100e01c0003902c9076000d0340741503005140504550080c0e1480881c6100d0350760080c0040d408a80c01554200c444c80450a0210114103040e8140e0309034040c242861035401e12500e42d003000d15004000700000c40359448200d1100803901d035002c4400d09281001040e2107010a00c2c2050790f80c0c143c500d2240d405d110321039401400e8640782c0308681c407003640204420041440c20b58540044c1845060782e00050340596201d00890b1a0721200e110710502401c425a510f4000f0304800c0e00380f04000e4a644100708030b98101c400066102000c9404550641d00035240941c0c44080301d22250040c080b1040712402035259410482da003640108120b4000b800402ca038210804890005898480d000208103807c03169189021640b2159070b00e0340107034007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895262634 1250 895261384 895261387
    0x708090d0c0506030c031b0c1f0f0e10060b0406050d0e010209130b0f040c05090f030a0516030b06030319032c010f05060f1804051c050a030c0905130c05 67
    0xb510000b50309900201c812840000c404000c202040c109450110101d8010a5406140118661120b525a06004504a5854a580c2180b0800340030350b880345001c3c0e0030040c01000400024800741d48c90b0b086142100c8074490600d000411542c110408480c1214415202c49107850004606032020b8811260401400c2d50f0070300ca4a402ca494442082c4500082c5190000b1a44103044c20454a40c0380c0181d100d0145243c03541c0300080300c2d007120458445440c11550700860300d01c81400030303240100d20070008086000305406918450003c14080e0141ca102d00583c40e1107645080a05030350340175001d040301546d505144034a00300c901985c0951802e00c401c0100e01c45506c0103442200c0300e0080c030500504140e42d02d01c801200708081d4450140c10010031501008060102c1e0006003000c101c480c003400c4101355500c0854104001048514810307243c2e1260b440e107800d0300d8400039105401110403240421305120700c0341090351240e8910010703100f0040c01e41b2441c0030344011100007412980c400350240300c070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895263884 1250 895262634 895262639
    0x30c060f02190309051b030a061803110c090610020102130308040828081b0109060209090c0c1c050913020307090e0405030702010f12090605090705060708090d0c 71
    0x1501401900d1400c8200240c0c1e10304a5400d140041003010061000f09490040b00030005203000c18071602c52140e21400000d0440101d00190401c0945600101214907000041182004403040001081d01a84840f05c40e440211000b545500503059aa5444000c0b14001901480c01181490f01c1c082d03203100046c02c3c01c618001c0486e1140712a00184c400b0740f404035041028a84c200110001e086080c00301002c100b0002c580f510340280d008100500110011076580681901c03011341b0300d2040880e40003405990041d0030320f80c009501a155007800b07524002d0010302100756940407a0b0840c8841c070020020704100000024607204191640010024104032000309941c82c1c0d04640d0040e80000c20040c1e490900c410701520f01da00c0d9600103a070a405280410010910200584e084580c080c00c6c40c2c10704a00c00441220b1605c1840070b03a80c100c9103080500c0301480002e500240c80381b04040112401e00d82c580302049428003521500600c014410402c851907420f0070700625881d184290f501915454 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895265134 1250 895263884 895263893
    0x12030504082526180102011e200c1902010207050a0e090601050910150512130501051f35030d051f0b0318070902180301060608040b04030c 61
    0x2440020020b412074014400d40e091200c0600038125036090b140c40300c03a62a00c44846600f807030048181d548210285120f20302441e034002c1d08900d50310a000303210000d101940e884010002e2000301c0d241618001100442d2a64004560448080c0340102c0700030020601c0c0c240303100403200300e8204124118026242d0004031600d45080f00400741681c0680ca4600e8070b0488603907031501c401644418425110750b4280310703d00f00d80c803801d01c0613103c260310602c0e180c4040000690302841554491521103401d101000a10201c1e040c2800501b0701ca04028041500c1f8100c0140640250746a4810303509008002002103c040000449a010410b80d9004012030401c0d0010070131540d841e5446096040000e142c01060400e21038194001d41c1020005e41ea82000681d09a81c15814082d007028580008041441c1d40f00526150b0768101451080707402054617052440065000106030221809000304440300b02d02d018052001035400b16a6a41c0e040d03036441e200e100f130312080600103600340400e0b880c6080208 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895266384 1250 895265134 895265167
    0x40b070c08010e100e010c0905060a1806030b03011a4b120601060804030806120f01020d0f09110f1503070206010e06040e0c0909070518040b060303071203050408 71
    0x30b545a0f8040e10f00c14180408a40c1900e0440d840724245034500b00c1d0b801b00c0142c01c07000d03040076034070b00780d0344552071b80b400b04015a04041840010f0240307070f10180c0001071856168114030551002a00203010401202c8070400d10340a050348078603449803042c1601c001301c180001c803201d404140414215010000300c0000c2d80c2d04120a101407180c15809000340344a410320800e41c00301c0760603c80c001c040562500e54020507007900900020f08000c468408290746a58068842c2c21451081c000e42e044c140b0704000580c001e40c4010941d03600b1605020032521541743e18410b2500068010791030210502c115000c1000026070640c078290b000f40703061505d40700c80f000c1202942c45405c45400801d44c550402e0114103112000030040c9104608089003800d00c000c001c120f101d00703960241c41c003410300d4403060852401c241d1150482900300c12000c110001d02c0f04100d8802c2d02960103031040389101e031038410505032a0700c2030b40b8001d031802e5080f140707511850b84030350f000c01d500c140290303d0b290900c0c42d01030456408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895267634 1250 895266384 895266401
    0xd0906060b0c071d1f051f031a0a03020402030912040909201011031905042c040f240218010305090c060f040b030702060a0c0309020105040b070c0801 66
    0x81d040104142c000d0380001c0110030043c1414041c210111aa40c500e24030400708020007190f04c4025240d213403500003049001101c00381c40d0040560004030b00c1042000f1101590010031070002e410207507800030702450b1001020300b210020300144101c07411070302403001070b62000c0d14071802449400e1041072894429405813010f4207420101140748105401c008882c5100c8800f0400510184241002259100d41480c0000000ca00305610b0242c00ca00030607003540074058814a580c108a42c0d40200140d220000740213840d0349000301c080c0c1148030107809180b45109082c03044c11951007c04140030880c00c0913183d1146210f0f0300c903004040e405016900004690000a007003140c5c010424401d20b8584035800383c003060302868104214500650040c0e614021440124002c220019085003c4100c500484018200484c03c81d41c2e0380c00c0c0030000035a1000100c4140000d00d2500d40c288032418803d00038445980d40503502d860610b418040541050b5014103c101c80a4030001c100240700d080a0188104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895268884 1250 895267634 895267649
    0x2150910020318070b03221103030c070801140705070b0a0e0d0f020105150306060103020a11012a020318120c04090305091905130203061809032812020d090606 70
    0x380c1445030741c00f091a04002c0d8004507001c860902c100948914101c01141c5440c8000001e888003c501e810007900303070b40d8407924568060000141c010142e440014002d003c440796000200100c5242c0d045410949005071030700d100145040080c0d401192102400503008807211100044240107622003a203840017000c03d40000c5007010321943e21241d028880c50f980004090b101080c20300b80e41001940b5080010445e5041c980d011408400e00340c459064545441c80c1107001304115040d21000114140504087c02207546200e00c2c0c1c5001240b01100740e561054000030020110f50b030b1402000444601c48405040034461240c40780701a5035180207003070fa1540642c80741070fa290f400c1c00038001440240e12800c4c0110740828001c010a8454518601c2942e4404c100140c40b82c4452001a0148120301c0303d40300682c040a0510400c02c0b40030008148802000c60641e00703004c004260141200d02c4854003102154800100f1001500d5640007440340d01d941240024400341c0c15039a05040b200c05801102c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895270134 1250 895268884 895268911
    0x3101208121e0403180608040f0209070201060e09010209030607050c060f04080721020f1b130209060f040510090302102304080c130203040f03141b030711040c021509100203 76
    0x80e9031103009a17030103001c0c280601d854450340c9060f40b610702c106180e03d075000380615100c2c5c00190000c1d200307501010251110885c0c10003e0300784003941d40d02030b41012038914464003e0b103000c5144c10380036800310364202c080700d4098807c81d5038107400d0070701381c3c08000c01c2a0352a0303e08022000000b00030203100c821010030a142070180e200342c00c90003450b00c3c000c00080540d991101c410b07440880010390f0312030549142200c400840007004103201307000c0e008100300f26420072008078203000034500300000f40090310310039034a095544400d1003003120a4070140c4030180d00204004c0100c86070030302c1070b50565440542110241d14551200ca40d2a04540c02a44040340030741106010100a18080c101195041c014510070360444c10541c44001d20040d2104004080c44106490060082920819248520351a03004503a108801628540d1030b41d10459082303400c059054884181032a0a1054410403c02c982c001c00c990942569040b00003031016100c03c03624820709414422204050004510807000b80300c850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895271384 1250 895270134 895270157
    0x20a080d0203240d08030613150315050c0d0218091303020f03071e05070f0909140109030f050d0e0607020312070f140708070f0803101208121e0403 65
    0x30640ca5000c03c3c030008030709201d014292040d0343c410039205402d54002c0042c9070f40b0785038000002e5990b11030400521441d801c00d14050140c0840d99810750071280107030781542c800842c9012240071a0350880700c1e004400300500c90f41c00001c44507406425815220240201d5821500f00041d050f110121148581c2d03251030b421442c2010390602491a444007800000c41c24030009584d101d09185201c1d03820304500303a4484421042c803c0c10032400009012512244074200e8880c00c03200050140860140d5010300040c0c4400d030051014407070420101d4055560368480210311070708a4050780180703a03c1003400e40b51203100521b04424000103002c0c08003500290340d20a000e01c103490803200c5c000c00e9603040c4406030510301e0210350800c4d01c0000f464003600c2d100760740b8007407454142124014410b000d8401c000e82d4600f24200034012004600441c04581d4140d030381992101291104032075110010320140d010f1041084110038100c2c8950000605c5020106101c00d05807801154801158203030001081280403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895272634 1250 895271384 895271401
    0x10507060e10180f03030c090320010e0105090907080c0702061605010e0d020a110a150207090617120d1103041104050a0b030c0904081306020a0614010f09020703020a080d0203 77
    0x69034007016103c103109500754100d850703400b01c2c1d814031200a41030588034886444018800c10402c0041c0d503000b241c5200c12121001100003c50410700c260b80418900d070281d1040350b0240c0d05482142c2c100401a04850761250011a0b0b1311901a21102586206002080050f030320340300074004404480355144401809801c0240c00e40d111205507a103260032122420000e01da001c03034807028164002100402494020002ca0381c02c5000d5400074040307000310490001c01950200d41c0004072610070303400348a025201c554407000d04d0f41843c8807400c6a485400182036100362840503104400c24510001021b0882c0840d9411340e80c01100d003104c50140940a010300c9151501c03602b40c00c5030840508005d89029080429925035510300c0251003107200b84001000c21804c2012500d0f103891504440b10400d40d508006940e1f10380b000c1c001c9600e00e0410004d079020404410701c1e64122903580003090186880d04590000940c400c00c2d0590442c00791803404804607008100404100c40745100050ba80c0c82c3c1a0403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895273884 1250 895272634 895272641
    0x150504061d060f03100e0a140d021501230310110307120209010806090a290120070b1806130e0a060e071b0f060501170105071b02010507060e10 63
    0x5141c41070490100700c0d40144c40c0054031034031003150b0240024107001e240040500d405910b480080c400b84640144485404010401c009200503e400b1100c0031414804050f402d1503090155045e410f41c40c20546048401c01c88192444c15000303416560002d0549003007205580310729a0000c040740700001448240b585c0915200e242c2c0c51407100c11420704d040140000c100c0c1c4070140c00d11303220b15500408600215070765070103000d010649200ca4422181e451030070040c0d4246c09100c0c140410007080c10041c060803c00c180e50300515421001c1c0c40d46a04190701000ca907009481c80f814092016201d039203864441c1070080c00e1000529003000c072018030300040c8a1008500400f040c0c10300b414120b04010b0a844800c0640d0004440d0404450341c2815000c55241c0e2210b0002c080c1c8500c0c000083d410038081d1903800300d41a0380050320710303007a1031442441c118240d07642a030706280002c488180c00c540b000301c04003581541c14030500d05507103060426190380c400d80e02088030130421504803c640c0c0c0b00ca07605511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895275134 1250 895273884 895273891
    0x6160614010605090102190311060a0606030b091512100c120b120d1409030106090203040210170a05041a10050f04060605090405061206090a12080103080d150504061d 73
    0x5080d0f031a000013040000d46440f58640c09144c002d4051000804150043c503081c11391009000c1143d0043c038142042401a003510301c10315011920340861b1800310304200d8802480707460100301406c12403600d94140f0050fa0000c0c840c020041c055041c50401c00320050107408040304540c3d6400f4140004001c0c0041221540d000c0c13148a81c900d104141c81e030341d0020894131400e401600f4001d48002d002000c503600c0382b0440454550552030303c180400d1042165018502850094031a03103a10701c0000c3c02038039940748404001ca4110028400a0040d60840c0c100e140e22070304c206549408004000b08080a012059420050004d108034040c0715a0800c0b1f40e4940c04070408440034031020b481d01c003014000f8420761404500403034440c40069500d480390303554070021607072002c2140c20629000c403600b6100c1c4445842180c250b6000038005d4802c5102e092100c2c180e90f0800d00003480d01e60780e003241c5001040da440000c002c04c43d40b940c0c0003403140d50ba40b140e44010801d04800300040c411624440042c100c004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895276384 1250 895275134 895275137
    0x918010e0f012601060b0408071715150d1a2a0403020f0f2809020405091807210b0901020f07140102090604140f032a061606140106 58
    0x64004000d5100c4480070f2641160b032104401d5002450120554050443c640000174040381c0000e00140c40c00e800076484045800103150480030010701040540c940c11041000348410001001050030418020030700c1c21009401414003c4017034042d0f03104480040c260002100a115140c1000500300f10000c000c880b00000410440c42c403000141948101d0055001c06405a040d2001381e60700e9840303601002c0305880d40240b0000a0b80f02e02160b081c8c2681400a07210b03100615000d001030350301e00c03900968040d900020200040c0c1c0e50b40b02d4460466065002c2151854403c00e18002406c5036190850300358102c40f000894020940c0c0e0400829004018000b0700d00760384100001c40e000c0c0300741c40580b00d000740d01a5900901e41403803c00c96001e402044000c0d5400400054009443d001d005114005400143c2d901503024080100701a241d0000c81012241d0b00001c100f80c2c130350444507804002032110b00421090901102c0000030000011030036003181c00c9642c034880701d8000950f1001490040589 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895277634 1250 895276384 895276411
    0x601020a030f111204081c03110d0504060207170d1406310615080a0b011d0a0b07050304050a050a030c0b0313020d03081501030e1c050918010e 63
    0x100d6400501039000804454200100c0102c1903d40503402d1160011800704a50350ba03440725120060345481d40c8491110101914807940045240c2d4040c0c09944160300b1030105086c240007865105034003038a40284103c40c2580d082141d0030006100b00703004488203000100080d204c020905450080768580c1d8490030b00c242624040000e030b5a01d11070070000e88412958649440c07111f0b000c40d0000701c202c410500860314200300010500340b1640c08560890069039881d6082922800060000c86400001880c001068504141904810400c4d0030640c400d018050002481d9500c02018294100c007208640c50703000020304000902d40f09184c000502421940b6100180ca10340d0f68418421461044286070140803000402241100044654403500580650000d40329840c00921714102111002000400881d5401c050b500c45d214880c03071100c06070b0040a12110b4151105400764004108500f00a004c020740142500e07004000864040e07140700c060303150b5040c1003005242010051000102c01c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895278884 1250 895277634 895277653
    0x20315010501030608161203030b0a06020c030618060402010c290a05010b040605030a09030903020a091401080718020322050a060b032404050c0a15140c03040e0a140c0c06060102 78
    0x500c6d180c4031080301c035000d105440d1660545405d4024000001e040da605c115100000105a50081003200a080c8114251035090748c581c40074054100000e07011890a50011000a0041d4010f400904629000b01c910464076005200c405201c903110009203d0303c0c1405c84140b00c07115013203000340340c05031054070780321030030075043c00c200034001d0100504494107140c40700040f005042c003d481800185401501e010040d6469500600203420440c4852240250020000a81c4200403403c0313002d90384911207108400d03c054000e403020750400303866400480d406c0020f942c070300f42d02c01002210442c41017001c0d00304c140c01818604100c03841008003074020703000810001c003d484080400b9034180c0005819051030380703640c10f2030b17032411a0560302c498020200306030110304d9021042244064507520b0390740070007426408001c0301860090726070080f03541c0d2060105200020341846488c0c0d0250800100098024422901011f00c48080d14502e00c100c400040013030540754144040b95003d002800184001c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895280134 1250 895278884 895278913
    0x140601050a140c0106030b07120501050102030409090510050709210206040e07020a060c09090b0303040803040e181b01030518060c0c03071b05030601050d0503121003020315010501030608 82
    0xc00c104036030081000d0160160b400716610020b6a00310007640008024072522490881c1c10400701381c4000e000b0401c04203035081c20603034074000c0c0e506a64043c0c0c0614181864805250040c6c90010021602801203501c815403444e81446001d104205980d038012901d40713040188071310341c454221a511034440d031034103540c00340c1c032410300319030448201582e401440d55848108a00708503610b0b43c0180b005040a00e8209100c0c1d00030b50702c10075104003901c204541118101003580d648254800d0031040d800500c82009840e116079049940038001003c1003001e5060014240d0611390038044000380c1c000005060949548d0500c1101c2d4406a0390025200a1200a16141e510f080060503990711200c00200070075154414000e641203664441c1c4400d211511120010903070200c5400740a00911419000150f00c3c944040070b089280d0b0400e000c1d510f0896040c10720010002d00502c140740741004020000010b840030014001500c50580c0c0311011035040c500014140d40c8150f20000041d40207015036080305 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 895281384 1250 895280134 895280137
    0x1b050304031808030a0c0b090118020904030e0a0b040905011406160c0b0f04052707180e07050904110a05091e040c1d031c0807110d050c0114060105 65
    0x16400d07080c500d01c0c0002820350750842c6010b54115118900000c500180c4594004050605851040301c0f0110260b540c05081802c0321030b196245507050541c4000280541004030403150020700034500140340c009410081003d51070280e020080382440082c08026064851140318050000d0344400700081030498001049400749241114801c3c9030035281c042000294041c8000600d11811501c1e117a080b404200e84154002d40f00e664020300555050850000c507810b0059905104500c2d5008181c403110700807160850420440802040762075004a100904090610720a403040d954550f0355954403420300050f5001040c50034a4140244148018139400c2803c0c0c4001081c10386200a2900207035100b4804141d01908043c0c00915220303407011265070100660030359019030700640b41c00c10020000e141e540d460b103000700d481300d00301204003001c0c041c0b09440700c035003049040c9080c2e000790818140031410110900340017800b2480001e555102c0c11400e0081ba441c3c03000310340c03083c0700e01e01c2c010b030010f00300c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 895282634 1250 895281384 895281391
    0x70c06020307170a02040e0f04081b070810020301092d0e100903020102091c021e040e0f0106051002060c040b0f0d09050c210a020112140f0106031b0503 67
    0x989401200041d0310780d108454000c00c92000883c0744010b42070590002d8004d40c064020815003544120000302001e140c910b20a0045500c50130340c61800480c104007405038042c1d21002030700390084e510002030180041190000e40c0d5172040c801070780c2e94034216030402202c80d107502c0000a07002d41b01030700b0540d0030b198200d41c140c0ca05014003c500390b040443d9a9040240c00007602062516100ca52070074581c0c154060201c4a02c2510100001c0900d00b41a609221072410001c0d8418060b0071006003990740e0450102d07403800c3c050008200040381c044142d08000d01c0307200e45040b5a6403003c04100c0c034504081c80000d80c069034005001c2500704601406000d10450040110241c070021b1140404692401240c0700b469400c0f50800140300c42e0702c2c1007511813030440e1242e4414540c080d201d61020610003080b03241c904040c0000e210054850380191007000c4407440b4103100c03941d25040c44081c0c0002c080110310914078401c00012035070501130301030304880721060030a040144500083c2d412a40000881e0f80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 895283884 1250 895282634 895282643
    0xe040b031f02030a090b0c0d14010b0f0d091406041709060304020d05030708041d060103060e06150903010f020c1e1902150a0203092812050118030c0c0509070c 70
    0x3541d95a600c1d80301e0107170402d19401000c2c3c040c0700041100746501c2c42d0141011111220050080080041c19003204003030a02030000141c81c03c03c074403031006802c04010300c0c080385813601c04a0b8141250711001c46c00440d00c48080d80070f03040f65003000108614100041504003044075464101100d07070380815440c0c00000d00080c040c0702c810010b803007444070410584400303d500c501e200d036445494030381c1182a040d01184100341c8004400c00f0900c80d42c002d000d10002e4544400d0700300306998a480400025180e4422207034042e6001b0031200602c3d8a0a0045440b00740c140d071030250355060002c4103249000c0b83d040c01d046503c1580900d0f2240d901020138000300424a28000c460055240d0000854454503018000c601000001e500d03000300f0f030080f0107424001d5040f1519100309406d2419001418004180940400b000383c40901a01c1d56018482c68000e016200000310710342049642e003248000d10100764007103010060400b007040f0392885c004014080580d1076800d42c0c203000d24003801550050030003c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 895285134 1250 895283884 895283887
    0x30f08011d0411041d0d020d0c0308061906050c0c0a080303010b0304060e070e1e160302180d03080f1f05060a020a0f0b09150603280b0103030e040b031f02 68
    0x40034418002c1d02102550300c0180104501c0c03564080321903000e800c3c5c03030800b00240100310022280f140040762280001340181c50345225600140d0f403c46801c00014143c550005640e5901c4c604a0051549003000d0000e0380c4071260741d0481058058542010307100f0742442401411020f01c00c0d51008802d1380d04486000f007403113407241c0301da01c0c00078082e03c441c46070251a881807500011344040040780c16402841100250350022031802e0f40007410040c12151002d0381680d4060014041d07119500a00c0801e2491030021b0030803104d580080c162006901c415000a2100b8007071040c0486a203011542000d40480030100441c0c402004940d40195031080520514010031908030f00d9000b03005002ca0349600c00e80700d40030384686103810081c4040582e0070400b1880788500c1032035031001c1c0d1a01c1074000c80c0020300800c440c0c2c03104130900b0580c0851606203428003e050300e640d0f00144668075141c0c0038620907250890b1580380c40d018070049031030312480244079501084d041112074000c0a648000c0c50307450340700507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 895286384 1250 895285134 895285141
    0x603110301081203091e060103030e0607020307060813020901090c020609070f0e04060e0f0d021903080408030915150118030f03110309060c0a0605010603060303051210120f030f08011d 81
    0x600b40611806c0e6075513000030510003a141200c0110308107050341c1c420740791144420100300503c9994080c01000941643c08035a09016040c010b0b84086d40c00000c00e1011a86030380107a0100390000313402c0e4042140b0a44440030700c01034940520010b9442480307407004100c024900801d54031a04414890b0740c25094890b008103041c032109811142c0f54450a20448142e164047c0344265508820180280107004511a1109041ca06840100d0741501a5217050244d1a2a2540074842c1e20162103400f0911403000e084140a04004006124034442d4181c003a40890050014040f20a4880c585042041503601400003a203050200c40c990740e0540340c0600b0464120007128a10711400c94082d900c0000410024000480010b50305091403258001380050390380c840055054407994040200441c20912285180b903440185840d48000e1310750041100c955240a114520b11f820031040d5104840c0306440c4d4145a040b6181c0d0340603032410301c2c0400030b0390300d00940b000014400d1120356000324400c1021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 895287634 1250 895286384 895286401
    0x1060509011e030f0e0f1b130f02162402070b0a0216021e0a0e0603072304061d09120d0b010e0301020307030510090b060732070603110301081203 64
    0x400c81321103000c0070030000e00d9401502160340380400c040809851084041040b82d00e0a00207080e906c010010309a800170994100e030790000b4188809489440741c0c0d090043c041e16004500f43c41002d10f000d8070114219240340c1000c0c221050035404e99124490040201c000080d40314000c0700d9210210103401a21138186007088003071083c0407a0f02940c09455152a20312104801c803541040080803124040d100340d40c0c2c01340380407864048800f56855001a10700700003008040a01903080003035039000880f07802c01080040c080320026080140c007030103030705151080142040021034010108100903c90864151202945442400c44800c402d5880d0242c46482c2e9004000c401140032000340250344914014100400801d001c40d00c01160245261000410401c07511a5088110029140610382001600c40150110030813505a00000b0b007542d201126000c1032250300d4944040f28041c140c5540b40c081d004082c3d030180c01061800d05001c00c01003040400010701e003001d451a00e60f07070303603180d40c2e84a20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 895288884 1250 895287634 895287641
    0x9150509100c020708010b0a030c03240e010203010e07051306050c0111030f09150c0901030908070b180105071812030203120c0a3b04110d1401060509011e03 69
    0x2030070401030782064007500742d56802003500301c00e46411070001c10040752814200186644240f1000e4000c1c0c480304070900100c1d40c81041e16400000408004454442901da03640c116190180701c04404e1b5404001400113450040c001074010304640b80039420164055039003203100e401c5100c2d500902c400014080788004081d0003c035484440f000032a43c80e4038000100c0c0c2c0005104543c80c040c0303801003d500140e80c01458140c1c41c01500e540904070305002404006400410f403030001038840402c2441000e0002e5840c40c0c0840c42100c002180107440c1142290742820b542d00500384009104501c084181e507800d40c2c2034040e013210848240322400c81e03601c1c01c051b8158030500700321030090400e01003040305e015404c00061007006240d503191640c5c1150860811204100c410040d03011803030f4400c00b14900c01c405071034840c0e0840010b20008600801010001b0b060f40400780780c004960f10f444c01c104006643d1012180181202c1c20114508007032400001d12440c8038104031030617420700c0500b084030350344680d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 895290134 1250 895288884 895288903
    0xc040e0319030e0709140c1e0c0312070c1a060303070219053303070c03031a03060712060e0f0c0d0b0901030b0108010f1e0e0309061303050f0109150509 67
    0x200340d1340241d413216204005841042c030b08001940000c1c0100b80e520134000d045403520304100f110a00d00303819102d230080a036880610760b00752a00c018050704c3c0c1c0805402e0b4105014a01540305c0102c070410521702442d01040100e03c00440b20201d40400180b9100803045036141c1c0d42c1110922209404420580f20f070314825008075401c40b49191407030b2491601c0e009a05c3300d911803608114281542c141101c00d0074482143e906000410320000f190009000750800f92108007c1e004460b00d0142480201e4a400d4040f502035000908140d03900301164100d208000240040c0740420b9500d24040b002003049403c0a04109a011400500a40c001c4516442500007900003000702c211035a44c0c0c144410140d8081c06440c1c119441d04545011a003181d00c00d036448c2407800d0903d420f180199084004c000c044001c0901c0032030000708410f08296417024010070f207256a81644050322030071800d2032440e00c1c42c0103078419281da14243d10031000c038141c440084295400500085401d60b40c030381c442030a00311143d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 895291384 1250 895290134 895290161
    0x10203030619030c0306050f090721031229011412040807050109080304110d03140a180b180303120103020402090a080d0809010c0e0a140a18020c0c040e031903 70
    0x13810f0100030010303c0d400940c0529244204440552116010103480d03c0007407003003a0354071050189040c01c0c8450340d28521b00d114040d08109110040115000c0180e55554000040c0c0c0c4006404c0012035147e941b1140c040c0d0039007071801c1c442c0361180f40560441441000c4012082641060011342000a18001c0380c0400758000000c2c00411401d1030451745942054600f10b41c20210900010700ca82000c1e0410780d1100d40603902c10030000164419151143d102d072400342c00300003080d800b000502c1461045d034001030200c819001d507603a0350a917009400a825280d5144250020009000980814103c250640ea011180181d5488015000400304856648680b040d40034440181400341c0c0c00410702c500c2a40c811000744416208014100d50440701001c1d00d541c0b2140400c4184014108940a954251009404081040d0300c8150640910080d181c5500506d40c001034000710341c4201748101c4685290030380b802e124002000c4010b580701d0080c00c01c402a001c00190089070707094825040a020075940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 895292634 1250 895291384 895291403
    0x4141506151c1401171b0f0d0308011701020301080303010b091c08031014010c0311010e060103051e0105060a050415030209100f1517041401150801050703060501020303061903 77
    0x29803420000e0540c802102500c10700f0035000040c240c401000244804170380d00041d024083e0751a1214001880502407603030005112281e0f88566103402082115290007a1542c108035072404409840c540d01443d03015080b40d00600c01000303000000016039041d1224400c2e115102c4010b0004250405140020b08a0442071081e07000d05100c0c450008500810b410301404c001151102c0e081c3c0d00c440746141405000404c2c3c0021100860701c02d00308402e00160324000410b454520f0048980751800a030025203c0b41c100001c0400d010194500d400c842d1551040240402e15010300002e00514291243c81c0c0600d844244007100300300c07000800c3d005158002c00e51591820710580c15030345000b10b0700420110395001c500201d00b848441c0c440640701410380d510500041c00d0023240e480c0004002e40111060342d06100502e09500080c001d100c04507400e84084030f402481c003143c060a45d43d000c1c04034000d1600d00b03007003440540d034080300700ca80c0000d0640c2e98115410844500090640c66980b001d401c1010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 895293884 1250 895292634 895292677
    0x3070b0a050414010902030303061509030109031e14030f040602132907020d0204180f0b042307090b0a09110909010f0e0a0903260414150615 62
    0x6550199008502800c1030b4400300d2a982807044c22a100c4800280d07040c1e00920000d00785141c15401c1c51920100c0031000303030411035500082030945d00403001c110045801c0c1c003074011400c0d04440352b131304044080d8542000e50800c0c00d964071100d403002a01d00a00c0c902d001c0c00050910110303030100d807940340320705040400d0a60756026100c1ea100b1105c51542c001113081c000d021a18440c2c03015500a1900200319101441c902e600300801465400440e088010b102c0c180900400c000c0d11920324207074000d1060a10724a054034009c16030000f544554151042d11980742c0300c5851000418400352007070200c0c0014030000120016501d0011940903260145c10300440400c0c00c900900602441c100039a01c45000303036251a0140c80b41742c280d0282488503030304d900001300c0b0441c4903003101d42640d000707080c50581c00b00000a0750b022410a0001c03c009910f07480207000800400b1100e444c124140c1c200034101e05000742c0d00f82880c0031000b42c1440d100b02d0000054550b020301070422206000c00518040c002d005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 895295134 1250 895293884 895293901
    0x1060f27060305090102040503070b131a09030601050d0816110a0611120a050a12020f21090c0607030c1104051f08010902060a0f030f05010801021206040c0c02100203070b 75
    0x5140c0907510000b810032000c260f140105000303540a03600f004001d068041e05203801d0043c941c00029204440710010000054841d1056030075061400300d491449590310050f1050510b0142c060344179502904c0d800c800b1703601045c0800240c402e0000158080708c8142498146800b1075180e020fa02c43d404000300310001107c1da04109080c1c0380000000c00e95044a94803200700d00b0074058000840b01061040140740340b504c0c4034400c0301d00000d5002c0401801d0022403030480c0b246810290804540c0d03080480843c0140740c59801490317100408000401012000b0004034170213005148000301405441800c5104201012182c040d040402038410444d902d400c3c8041404000c001e200051100c1030048080764500060040e00e0403160080c04c001e241002000c0100d400c2d03446c080310041015610200b1048031482809058002c01014001589a4421000407016580081e0080b4495480d26031090710b01500710072a10392061701198860000b104140e01170b800c40c454003030000d001040300403c014100303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 895296384 1250 895295134 895295207
    0x190204060210270b04170a0306031109040305090d08040914071706030d11010912020d120b09060108060d0b0f1510080c090114070b2d01060f 62
    0x1800c1030700140450142c03640b0041c00086003500b0801401d060304044000320b00c003000d2264125220f41c0c4981c1d41d6406c0c10780350101d283c003d0810200000d407546810802e010301c900d00b20400b160201c1d003c41c03290405503000347c02849928581030040c00310708492003e10001d2401e4400030305241e2014006d85c002c0c005030032891507085810302d002c640444107000b09400d000e040544550000b500500b60441003c0c8250345401e503015110300b441d0740754800c0200146c52a0300308090000103070002d1580341c0346103c2c041c001032603150f1407021007444c100010000c0c0d40d443d002d0740d801ca2802e0070102c40380d4071003402040012100040141407440d00c00c0c1804841551180301500c5002c456641500d40e00081c4200140c040005405000248402011881c070590b040b00400200350305043c01d601c41225602d008107540c11414042d04e15243c094100000072410845410802644060300802d00c1030324181e90603060030600409080281c02d0300f090a0150244542502107410303500410148500342c0c0411508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 895297634 1250 895296384 895296403
    0x510060306110301032d0213202a03040f081b120d081f18050106110a0809011718010c0201020307090605071a10080c06040614031902040602 62
    0x414a07000640082c15098026030741030741e500903610221251480f03400c2c00c1c40071190b81001c50b085c8410700200c006036181c0030024114800840c0c0450b1000d403044204841d000d20003d00d06241d1410408408040f81041415820204004c5040544100d85c4440762440c041c81d0404080241c04440100c0c084000155400c02d050b056080d0442465109080c4180c1c502c3c01d0f10109440c1c2d00ca00c11141c6454062804c1d00d81c01410301a8403c0b0045850042d40300b9030f4900e9110301c00c2e081502c11850118031940c02a123014202500300700100303602c20300d8141e079070742565079010349031207004120880c103a0b114490b40c002d43d08a06080750000c1c20440840d505800544026007d198600b00418003154010b0090344d00c15819a2509003102e8540380c810750f015400444200e903c1681051b1040c020380c03203000854050a032514101100c54200072060b4505042c1816003885080140401c00c00d55901020340b5450400d407400c210780f25100c59121091240180c03001031140341c0042404625039a000810110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 895298884 1250 895297634 895297643
    0x809120a111507020d020102012a0201180807030f03060807030602030a050708011a09120307060b2106270d050904060504090209070309052103070908010b0f190305100603 75
    0x403900c00070080240c550b40d0380d500c038810310b0020302c80c10b40546400c5001000c52801070002183c080c05110500014008660000c599000c00c551046d8900b5424492112038140002010881440c01e071940140c50180a1b030007410481e0051541081c9846604600b005088050884408a40ba441c0010181d0011a1256400c80c40c2400060388207119520b600c0c1252000761040400200c03541c1044481e601405150f40c00c400000045503440d542040201085070144c000011403086450401004206000d00303078202203000b00044406580210310137402c0007491683d041c0b030b01040c1094070100c00d08540c601c6072500078800d80300c0f41d12750820000d0000084c200c07001c00c0660b450f02c040000300c40c2c4a480c065004140040000d00580c080d50003440d081e4042e104944004100c0301040c1c030100510108403004500100621480c160080e92001c0a001d00f80c1c002d00c001000400490303251409280b8039441070820780d8a118901501110107400b0715005400e454243c0d9020001502820040c8021035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 895300134 1250 895298884 895298903
    0x3010e01170a030c06050c1204060203040c0b0a05271f0f0f080c032a0403051225020a09020a08100807030b0a230f1005150708070809120a 61
    0x600d5410040342020200794142c8031465001610b4485c0303401014014421804400c00700603260b02814080b64a5100b14450080561381e07107007602e0504071880c03c40e4007140021030140007000b8140c0c3c024080e500e000f2224600704904a1400d129415000810440c0360380083c01d00180c0c0b00101c0842c400d80010310507a82340d03e40300040c0a5800c4506100d0302e0700c1c56001070100804101d5032205007000f10340001000b0601c50402000c004200c1c03d08220420308008a035002400f001000014402d00300c6003081c0c030790018201403401c0c0000780f20303215011800e4885030369000848115990031440401416010030219207a050549001d072018209440041064010b81d000069031000002c42c001502e90054501c501e60f19030307225072800b8102116201d1a0006c135100e14145000401d8040ca20075070060310034182600f4448540d440012140e0030440c0108130002546290844943c200ea2440351b00126503680c52070f860500302c07964000c500b540d0307900c400c0d0b408650b41880400184072221038050703035110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 895301384 1250 895300134 895300169
    0x120a060506090702340f03050d08040c05010c02041b09031b03080901050d1b0903350a030207020d0c150813030e04150f090f0e10090c080303010e01 65
    0x71034024001c80c3c41000580c808102c440f00e01031a2400c05560070600340009100111800242d4845007040e000411001e0301c0c1501041400310801400d04101c0032800c0c40c00391400c054890140d051214010f0303505000e5100b24890842d102c982c4165448001440e45d000c103030041210052018242d4841600c001c101508207040501d68103010300101ca03801010b1a103081035220054650303401c0030041550140d0b442c4000900310300c0e07a0703025409140ca507030f9032011554114a007206101c4501000d0f8402905200d0304074000640f401035140001c201182d550781c8407500d10200b100039201d1400029009400403803030000300036200201c030040e40d1f01003001e84c0d88000610ba04554500d4205c410f4089109031404039004640030b001c96180e041c03070180c0089000440d04c41c07800400c1f80306a0082244101e80041040b00802c141304000c815003180c502801000455034019590703800101c00c01c041160341e85840401c029140340711500801406055035100e40e5a80c042852884091141c0c420021314107907007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 895302634 1250 895301384 895301389
    0x102150103110f1c02190b0c03120106052106120123130c0e07030f05090a03020d0e0901030809040605030601151d0306131707050a061b051207030b120a060506 70
    0x10907000313440c640340c441d46844550200101a901d0074880400e0b07030404480070842c007068a00424034180d68000466480384410780f0680300ca00140d2084040120500c181080c0540c00c15000350700034190402080291500c00010344007640351100d65006610b440c8034445a40031030013940050b180050030080c003a50b92000762110300e900b54500104000f1480ea0b0610131111090003083e0440010b00e000290b1100c00500f903030441f4000d440f80d24180e4041e076204000c0513410421440705e0103080c940f1051450014010400155045c04001c11441000c141c01820392aa40d2201004060042c2100c00c0707565213540f0203000101c1001c0c0d810001c2e005056036130070b18280c0720000500f06000380041ca1143d850b4070541050340e84030070048600b11410409083e41400d004050090a4000c101402203058203103014801c0f65007241000445156140c01400a150403000303032103004103000420500d590304d40c00110020140f106413180d0204c410301c0f6a001ca01d400244d4106d01e20701c15007040240e6281d1404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 895303884 1250 895302634 895302649
    0x30e0f010e0d0308091f0b0306010506041a0f0d0212150306010e040b1801060605120a06060c030c030504030203100902090604140705130e01030506040c1514090102150103110f 77
    0x30156048031540c0a520002840b50462170743c450400d400b9540144488950901d80500b07203164644a10380300c0d0098403940c502813000c60300408044a4440c9400d203019547c400000c0642c40e628405400401d00c3c0c040499078104950f050404103008540d50448010580080d01e000e51302d0405503814103106440d503042c0010840d0603115200041d1b0403650711640d441c00c08060041c81ca006200d203481c0c0b1503590780024010000904482d40781c05844425400e002e4940c258001c280480c0103040c10750800a09400010740b4890580500d0903511500d10380c2401c2d111442594002074051007450382d54054244581d1220035540d20880d04402c49032512010001a59000350302c080d40c1e800101c01041706075005400601e0b281503c210400403255a0300a20086800d00b60b00070f40312900084104000c0016910010f0b0203042c08461007030710026014002440c60810740250204920000340c3c0b202181c0c000c0140040440d10884030701c0081d81c4900e0310100d8200000e0718240507080724a0040540d140006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 895305134 1250 895303884 895303907
    0x91c02010e0c13140a1d01090b071407080408011a0d0302151302090906040c051f122903010e0d170402061c0606091409190b0d030e0f01 60
    0x2002c00407400000c0086101040050440311550345032414070304001c854001d8451085400300190179901c00304044590300c1a9201c4450f56450304400200142000120301c0e0454010f00d800c4548070401851420745106019000c0c00ba400c000c1000980752005410021400a041030504e0814002c1c04c10b000320f031002e188008000d81c1100f90888001020a03c009600c1032403884d41151618158020914910040c0c5001c041070700b20900b04414083c103494000c00403d070a507015229007a003001290701c03941c04030782c465003088503011245804840e40d8010002040fa0480d14150403040415400412820302420343d00079400c054068403455808038510240c840e141d1200f6428100c40049012144001003040f44d01950a010384809580036440c0081440103104000883c2401c114018051801c581e201814400c1c008000c079819032512003e46402c0b6080c08004450740240716403503409002c819070341c1500044c2440e00030007415070080200070104010754150b88504004c9004560345400348 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 895306384 1250 895305134 895305161
    0x80906040f0620101e14010314070f0b030a060e13020411040f0506070215040308031b180910181e11250606030803061f1e05070506091c0201 62
    0x2c02c041c1030791300484d0040070426030030302000564003c00804071421900012071000416407114014420045000780442c00d941c6104000d1040741d00d0540503220240740c6004003d41702e80c010011131000c51060300504003070030601d44c00031601c2c41e008030b541c02a103030750725070070303481641031513007407000508101d007110203840160f60418416411300c01813100583c04000120380181903a20706000448a103405072001e180300da00c1456584c1000c51141003107070549070002105000401050b0002280342590070341c05082511140c12076550301e49040d03481506640f048094501680d8441c040221a91081c0180c80840c180000d00101c105c0c0c0134012501242e1b40d19502107400c000c800b6a14150b10700c03000c0f41c8c4021040200280b000b03039039034400741c50140c3d00449510b0804410701c845032802d44802035004800034400030071241c00c0351004050030190386c556200350310b0303008107840800d105c1d0080b105040c0d0000200e400c40d003001d0549a907210001000084c1d2500b0040d44201d10620601070a80d0100c1c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 895307634 1250 895306384 895306393
    0x1505150607030210060f03050f061302040e0319030f0e241b0406050a080f04020901090b03030c1203040b0603060103031d060d090b0103110f03031204080906040f0620 73
    0x24140912039001d9103060707055100c0c0a2401020703d01a0040d0405401200c1c100d000e401d203140780c85450715403600c1040c007568011104000322060401c0b80000c4407a01141d000c10214402148036085100b681010b000b40407040445111050b0540c01a0280c204201010444861241d00094644000d031019000f80c0100009a00c0c04460011026400030803811501d50810380206105006070b0080c1c1c0311001194010070340888941d0440140e540c004a010b9480c2020f1500d03500191000b9014064425aa6580c451202c2a03450400a131000c03081c10408483c3c038030b008410310714050b81040320110b07414006000014400d050200703405040b81e41c16100d0f9140b00303140402018032151150089a0086424042640701e041031b40565086940109801e11055055040c60000381c8260180107000d094140d0800d02192000401c81d01900166141285503817140d1900c15141d00c00c000b03410341d000c4004500860b900719007001e00c004131121902d500b0704200d030309030001c2c000b05005140046660007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 895308884 1250 895307634 895307671
    0x40b01080a0e160f0503060109020a020604020d1b0e01150201020f07080a1e081609060e01030b030c04090b010e1509041b080619060914070c0f1e1505 66
    0x2040d04036216031111507007982c040d1001181d1245843d03074554444468200340d9401081030b401d00f80034143c05000700040c1589032400d40500070f940c550380980024003850080c02c44406010040c14940c0364088103034044002981c2c1c49685040c0304100303010b000b110441c00070b0b4502e0018014400c40380310080c801d42d040e00301001a1200e981035005a000201402103018141e80c0c004d0368003d45404000050710b0303c81c9281440c1030008c115039414680307041840078521003071104582003000c891600c50246800700b014007450000c21308111260001940143c20b00f21041c080240b4000b18505980340300c0702d0b5101340d47e100c0340520800c2480c0002540c000561801140104003a1015410556504a020b60070190350300c01d403500d800400c0710b2854001d038551490100c102c5d83c0d4014103005100c1c10304140711405480c4003900c419030001d82a10148422aa01481048201d0264445a5800051012450300040306010034900341480031502c04418940d180c02403c1c0c58891640200c42141c0c003401c0004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 895310134 1250 895308884 895308901
    0x120a0806130209150c1b060d111b0c0102061003170c01091202011b050f04260a060b0103052511120c0a02010237030c02060309010911040b0108 63
    0x62030700c680505940c00304a4080940c82d400c02c0601c028141c40c40345951644807211082c1084010000e116602807914140d440355551401500c04039141d05c100084e003e20000c070740015901c100490801c00208003240c541e007140e004102c1856500c1c01b0307000d654140c3d94454803440b0840980c0002080c016040800c020080c04074009030071881e40c407100014403d2420707180d040e0058140c18004005171345a404200741c038149a480a013942c0b180e424a81d0400868500040d403c2c0614016024542d505c4c00e01c5a001401503101204110110350503202c5c1d800c40c9040041c00b90400d124030380e003c05e0403c13012540d180484008030801c05940442c45441010303050003154088001c1074803208521401c10f41103180507001d0000e0051161150040c840c4a02910001e03003806002450100c01d0782401c04170705e042060490010325070940030345072111895080d141c01e86034188940d102030f4100b0f00200400c00009815031090460328094150740c0109003094042000365986440f61070300144500d0b0100d060301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 895311384 1250 895310134 895310149
    0x60203030c0a0c050307140706110a020913120c060501050f03190203030d0e070806090f0d1103130b0c0105060f060919090c052520011718120a0806 65
    0x202d82450038800301c0d07006403512403640c0c120060507901c400c01c84003411000784042100400400090412981030102d200903030341c90b010685c80185c040c0d03d0a800082c4100c180e0b14055061390761009030b102008070b101c2801801024919030482e031261415001040c0d0380392103c40340b048601c0040c018600703142c032618150a4a180c1c04401c076003511040c400e101c1c41c030f03240c3d0180c10000310b540d400511400c0d03d40007d0301c2c81c0100180441d9850340012689441c00c100c08503804c7c03000d44007403c01c480840342c1074000d98514800c065846100a001c11004a1840b640c000100044003030040203104640320035003080015154403541981c003820400c0411154100220248455203c203150913440341e0745e45190700192440000700f20005800081c0c00c40340c0c2c060101000061040b01034019030903240c00d5940d907040e107031a550308001d0141d060346510526072045001e40d1482c02e0301800350705c540c00e040b000b507030702c11104406e0480d860003450880c409160019082c2d91501080755210b5072203071a4074041c0041c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 895312634 1250 895311384 895311397
    0xe0c0f1b0303090f1005060a15023a1e030e010e011404030f08090304090b030c03010e1c05030903180a12120801050d0b040201031509050c0909090601060203030c 71
    0x10358284401064051060015500c142c0401014000110041902c14100101510f40c0042d043c0717003005100b06a181c0c0042101aa20390101c00fa82c1d400c08444168942004640c5a0201001188010500700c0410f204222002c40140d035001c2400604501a6401d60346242d00c1e001d01c85550f002c880c03006209811000d80c0381e2400d4000038182c041c20003a20b0039204c9840c0c2089041e10504240410158000b003c1e00c514a800e02d40300b5014145603070300d6501d0380708510402c4849a00c46400c0703540f0380e03014480300703c900500500800c448060003603040c0d1221020358505640e80b010101d410280350190040b05d2207201074201840c503200049144003201680004002d8104c00b500c031010803038285801d4100c1403203000d1088c00e1103c2007001c80c01041c400050300f00318050161074020800082c040004580c1003035090030f01044850504c0c4a0744e0b4400310f16031000c40c41900b844184005d000c801c00041c0a420b40540e490441740d51403100c01582c42e0801c3c400c26006a208000046104216802070400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 895313884 1250 895312634 895312657
    0x105040f061a03240702030a12050406020906031003051902030703060c11030a02011401060f020a02041a060a110c0a080a0f0201030f06060201020a030c030b03030a2a1b0e0c0f 77
    0xb0750710729040402d140054600364038600c0c0024aa101c0041491401d040303511203040e10043d8580042ca050080c45500070001c1048030b1500c0b51b011400300711040c4c055030342e1080d025215503121700c0c3c10225450b102c0350520080e100d900a000ca00c000494488101d0501c3d01e401030b00030300040c2e28544d100001441411100e10422074544103503d2240805c2c03008051382041c960022500c0300e07140714030406204060344810103001c4450800c400060700401d40003141030f0101d5000550701a180700c001c800f0614660520b50000b00021007201c0d01e508803403400b030041d480204039600401c2001c1800080d0f905405254060b500034480703240058826010003c0b0709d44180b4010445030888407070902954807541040c0090f075008078208000c203501d03100d030f03c084443d00c1c07600384070f0b0b0a10000441d40700d100c2e5101c0281001025180314004000b1010b818065002105248044c081281015a1088541040c00e01454400b5400288500340410818000e4440c0341d01c2c103203400300c0208480c01d5a4010110281d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 895315134 1250 895313884 895313921
    0xf030f06090f080a0206093c030d06081203101710020a0e01080a110d0f110a020105071404080718092001180f1a070f15060501020105040f06 62
    0x100000c0b180038074080d900307104110321a04c0310241c1d50003908015004020088a5010088141120000d41c180410038000c8140f5031800c1c4403200212a034090245900616510002800801c400c8681d0300c0f12080f109400241d80c45000305826030080380c481559104d10600600c0d40a11024004250001030400c2c0c250850325000d05411600d03007680c10403c891808115204001c05042d608107107015400b00074010208400c110501c06800385000340940b00c2e00d4075586500f1048007619030f42c440312800c4c5c000c041c01c1d80c68607507000d8001d0191000b15138640000c6e007012840306080008a040d00c00369000d450150100c43e0518542244024900d40448102c6d602c8801c41c07408600c848c0510013045072160065140501c1c2034001400100007103290203010144a2010041c0240850140040d07406100e030f4249080c8904015203c075024a071800b4103130080d080c01034404c21150071124100c0322070007901030011316900d00044e4221881110068201c082d0810340100188160f8081d2a15001120511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 895316384 1250 895315134 895315151
    0x11070f0b13060f0f140f0a150302040203040503180102031201060503070e12070311240304020d170306040606030b03030a140c030a0c0605010e25050f0c030909010f0f030f06 76
    0x30269118060f43d8100e0a03030312010f40d01602c589008410314900005950802d9003800101020102d00c000c000308051079403100c1d04a40c0e00c210300f049200458005101759141d0510741805500da900914246540c0c08801038281481d50002c815140100c0c00a2084ca032980c0c608441610f0961000f417890302045010300d002c858541e20603240000052182000300b5801d0300f0340c034001c130008580300c281c248921103003000d000d9034200644140608404110b100c9031251924408a400304500f440010014020960b0704451180200301652007070304100c8081c06101e550300415001c903001c20f03141a070140c004100e075004107406405e21000f2200340d01345803841c02d56220045801d54000c65420400280950803201c00c0c080240505400342180d05010318040c14402003850701d021013540146241d441c510301080d5283e028400b0385035040310f42c000e000e80e00e00e510018140c5036881a6001c3c0d21980d40c1c0000031681c1020514010306884500130042c0d001401c5440e4070089410f050760407102d041d2030b090709 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 895317634 1250 895316384 895316393
    0xd11060d0b1813031b020d1101090b2d070f2402040609050d0507150f27051507050d0c1b050907050702030102070c06090305070b0c060c03041b06050d11070f0b13 71
    0x6000307912300036116a14162001d20005101d100190300c0b80749909414002c0c80402000c0004846010010030725404e410811080343d080180910b00c005860542c42c22504400c1c414410705840213805001c07201b605254540c1125401c030300840c05400000f800e5090b06100302d0514011a101090185085030050399407a00070b0f104980f02d0301c4050300001c4210340c480f00c41139046038011f40da403143c1180700801441550350b6640c62005510a16110360132801070488041c01507001c50304c0c4a0341100c01da4603071050300e2202401d20020f80100304c84181284407101e1a0244204540c0c003030300c1c0003c2401c5216200c0030021103107a044488184da040d5400c211120010b002d8140d0340c0014041d40c0c07107a18003545941021810004107030700c800324440041119042480d004600c1c02e51003245600180e880351a18100b408000c0740e50f0540416040fa603000120303200f60008060418000758020500c10035501e00d01035401c6009004e4018480c055441d181d1000030750f00005d44d0303070041d1892280443d000060300d0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 895318884 1250 895317634 895317649
    0x6040c15111c030f021c0c09080714090901020c0a0b06040204081902100206130201030f0b181609051c240b0301050f0f060d11060d0b1813031b02 64
    0x2c50680403a10200c1040c2225050b000780f0b1303070400031600118100010400564400b401095510b11629070781c02d03040d90b00382c3c0a01e0b0741e48082e081c1d0000721400c642c2c5958088c0400301840c00d040344035041c1580000c0004130140200c440007041400a05030581a80d9600c880e1400094920742d44a0703020b05c0089403c0508100c5107070350b140d015842c200307029400c2c014403114814103c43d520847d00101c0c01c01c058907990075000000c6035820310b00000e0850301040301710003c02c0c84000407680306c1c4d114000e580c0180c1141c5a030314000c89039001c0102d00c00102082c261004002e87c403a407608901d04080e40813441e03101000801181d409000c80000c94640260b080038003409000c0d41c040b496a55140071101801e0034495a540301c4404030345510a400c00314400050f244004190612036021070000404120a40c24411016035002e484242c481c609440004040c10302d1810307a40c015642e082106c00d502c010403074142d00604982422098400043c2ca0444100c0700c0c209400c401180d55035914001070300d4000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895320134 1250 895318884 895318903
    0x30d02060f010605040b1b120a0210060e01060e270408030106020120041e0308030118110a1707020a02031609050718050105090103060504050c04080f06040c1511 71
    0x5010300003914003590000000c210680100c810441c041c8400c0c8103902a8000320380a0703881d00f8401130320115080f100d143c544258105185a98403003c84c8010003141c00048080144039404000c0c0066078995030500d00b00042442201d000810f0081802c025040401002185800ca40c01f01e440780180c0c050141550300d07040d10101d85a02001004002641e820300c40c4d06034003400e002c00d405880340d0680504283d4020307401910109070030903541c0450046541c41d240010365000000507125039480788102c00c01c1042a41d4039151605007640040c5070081c1c40202d0b10015101d41380e00da185062081c030300100d160014640c0c1c0540c8911000d400c0540d90801c01540c802010034500720100e0305249846003030b11005403400c800c3c005c5200582c80c241080310800c6080d03650070300e0601e0f110142500100c0240c01d1590080750001d160400380304008085000400560b60460304846403106c400d98104d03641c40046402800303a80044209202d1204414140007a901c0146001441c090008420030700f0840c00c403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 895321384 1250 895320134 895320137
    0x7020607080901021206010f032912062703040f090b0f040c080606031902070804060216060c120309060e010e1e0703081308030409290f010806010e030d 67
    0x80400034216800086607610071420341c025410000d0210b111000c2c04030140c8810b0604c500100e143c19001d00c241d0041c114244d1003000308103158551190101c040d1070f00c400325030064100c40d2421304081800118513015041003041c10560900812031028820507019144015020070000043d40d40701c0400c03010003400e01c1c2c034170029811048400300003070444001d180740c0c0201d007000d6040c40300a4120b010240c1c00403003912016601d81e00c1e2000402c640c2c2144c1201090f2901c0402c4020502010b1360103070041d40c050740c00312400004800800000f60003144120b00c0064661016040016020201c2ca14850000c2c10301080c1040f03652768000c02e0350994444810719a544020030b205100302001410414044038451034440f00780381c3c2c00340c0c2e1a115207000141404500042c0c0718141b0003004003000081001c081034035100e580302d08100c0081c0803000f171641c03400d0540c648015a5417400c41c075400c1d01c5600c020305241422092100640d803000d00202200d05001c41100314214507242440140c010540c075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 895322634 1250 895321384 895321393
    0xa09060e0d17150904060b27010f06030605030604150227130204060215040f0f03020a030207051e1c0204020d0207030206150a0302012102070c2c01180902090702 71
    0x74451600c000d040082000c404842c0c210300c0f88501d81c5803620380c0758009810902c081008413154010036904008a007402010808d5400030380c1203410a1560181a00d0b10034010701841d50b60350344120141c0d01d981c0035403039140e08941c01003000201340c1100da81e64032481c40d20260400e400b107580c0fa440c001c0d940074140711082c44c0c0c2d05401401e217403500c544802824030f140214102410440000e5440941c8074409104071000b80119003807111015400d0047c540c004140741d11403400c3d140003511000c003400100e02510510402280c80d240050045500021602c0810b100030160004c0004c0051148180e40f00384002c40902c80150321039000804086013aa40c01581e15421894001d00d0103000901d41c50240015885003503960340d03469001001c43c0d4091924500002d0618403100504504100c002041d910004030300b0b04101150106070300f00d891501c499444c4144150b0002c02c00305062800b01032041c50a0011311892074445244924548682000250100107a0108800381c1042e50920050b910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 895323741 1107 895322634 895322657
    0x1516050c07090507030e150c0a05030403031b0e28150521060f010e09190207080f1201050a12030c030509041506140708030a09060e0d 59
    0x40900e0082201d0f0402003400790003446c0c0804541500c4c01020a202c40c4104500310b5580304c1c80080070440c0c540340d0410401c0720b40d03074001007085081c156201213a40690034a143c1c2e181440c0e500b9154130f00d4882e415810000d4884610780120001c40c104500004090f11078000c0c501111042203803920590840300c0c00782c4a13070003414200c0b084035000801400255258075040c0303009580030b80750300c6a61604040115040408140715a4000c011080803c54050003420f81320000b514040005050032469501c1403400d0707200852460b0207200c04034110b034400d405081e545004103405c45c3d0980c4814034014803500414a02e40000d0144942e40103110103040c003490440b048100000c004000d02e4942108420340c46810340205400241c8400c034042040c8449003c48070500c1d044000c550a5035507911481000d032421300c000705c1d80c0540380d11440c2182c0c0d04c10401e80f50703907182c581c883c0741c60f102 = true := by decide +kernel

theorem cover : BRFrame.Cov 895143884 895323741 := by
  have h0 := BRFrame.cov_init 895143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 895143884 ≤ n) (h2 : n < 895323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
