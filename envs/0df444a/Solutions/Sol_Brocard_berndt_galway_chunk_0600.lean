-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0600
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:40:01.929521+00:00
-- url     : https://prove2.me/submissions/379c7bdc-2f35-4ae9-8d97-3ef90163f817

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107733812 ≤ n < 107913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107735062 1250 107733812 107733827
    0x12010e03030c030406050f060906041e0c03020403060c0305010506030f0a1803020f060702030c0d1b05070b130501080123030a0501020301060207030b0a0504030512040303060305010c053001050d1103070303 90
    0x38040d517010091a10340300169031402c041560a103a010913040c001c5030951609600c80750b5260503070101d000309007a4400703d5109448440d01082e0110b0341c0400c007002446080d018940030205203140800c407540c1000006952408040d0400400041040c0040c403981c086a100c20300352500c102107501d8001031460002d41e0b42c4000000b060b528010840410582400042a03488500c601006003000300500181100c401400100d51408c601074401c0b01008140c052003480090949d201d922950340c142e000343e961804e9003585c072a82c100070741500108061781c11420240c500150f0b04060b49504200300c40000d1600c050020081d00551001000060b8541c0016412084038130501d4040030343d0340c42500b1a01110411513018001c6142017103401c011000c0811465441440782c01c0c00039415880ea240d031421200e0b079205170400300303500081c1810302d60784110341c8030315019598103800800e010f126211a40a40c06208580c000d64600c41140c082080b40366810700f07094005400c450078a90380781002440c8a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107736312 1250 107735062 107735071
    0x712150b09030d0c110613050a0305031914090108150a09151208220e0403050306091501020a0206030a09050609071a03040f1104020d050a061a07020a030212010e03030c03 75
    0x2441442c0103101603600414040f800a81c00104001c900e500f240203010310307a440300701181b445242c1b1f448041103a541d5002090301860140d4001c6458002080382c0d8240500058036020500c20311030100140c00006074101c0d9101c080c00c0c80c040c0314035104d850f04060011640b150140d401045a0400300f0321060036484030340c030b0f2000100d40c0d00300c1a0762158900008281a0b101800c8100c0401c00c3d070301c05e500040703c8180025441d00c4c51801d1903540741c01c0411002002d4078100c0010300000f0034005245030115030141c114201050a00b941d0358602c001035a2444408030081c058180840000e18107450307640000300d55a0030100b62185440e10401040e00d4002c5400341d0079a0889100da4a84500c121605070791180780c0c004c14940700440c5581310b008846481e40c0741154410b401300650035071005c080c05410300540140401040e6a820710004481d1010202c208412468044c0401009650751140300411260140e40440c0c130800c0740441c6a026080c45081140c0e944400424090610120740046204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107737562 1250 107736312 107736319
    0x210109030f0f05090612070c0506100e06060906071101020f07060801081b0a09090f0c120c0801051006110f030301080a0606051f030b010216140103230712150b09 71
    0x80b140801c2501c081c000e07002560342020341442244600c1d00b0b070710708050b0061060301707203c04003e08556502e460864200c6028080000000c2308100401008060f2500810201c640c1c030309010300d060210b452030040e050301030302c0d069070500400c1a0b07074003e21000b903030240d851058442072a19140054480c000a1183c0512441201ca80500d880c0c408107600c200304400501800070b40e031400401c100500032000058502d4810410524005048151050000c001882e0304800c03c038001c0c1094850f01c01c055202000d140d05100c1005420801d441d100303001d403a00c40c00e001d030003240741d01c00062800941c1510103040344030010011513009000280e9509051044100b4048240c0715001d10490700707000c02d18030340400890912001c0305406a0400311420708180704075211021403601001c00b404a560180c1c0f5007041581000c05103590500600300040c0c011046445000035101e8071411a000043c201c0040006405110030358136183e0304460007099401c41c05480786070301e40a13010744a52092004510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107738812 1250 107737562 107737577
    0x60d0f12020d090806010b1914070b04050d14042d0e06150405030c040c05090a0311030c0607050a110102070e0108010501090c1e140904050f07030606020f0c210109030f 74
    0x704c0c4803001a0303490507948a91324103820980410503150018407040b40020030b005900b20981d64000d000c0c405040c1081c05000043c4060810341020b40c00c0005c00c07010f400c100243d85030700e008059041022201110b4075800307203003244550100000c0c000e1101da910203584500170403002584107599100a80a2401101d0104c80104c0720240042d161040b442601d4150700465008001460070754000e80c2802d00500700149808805c00018401d01c0780e50b041224020f44404003003000d42070403c018410341c141038600d689420595100c09a4601c0c1c100d2004000642d000e01041d040d900c00c3c00701500401c1500400c0d01c0320b5031200d0025000c0e060034014049041e28003000c00d0219803081100c030b1082e0820003410790001012036402c40f1411044844141c0c1d0714020480e20040b51503903c900c070b11440580f80c8510560400c010b00400740d64255215001315484400b4840c4009400b04850200b40400c41c2d40030131022000ca820300740403603540b0b04a00c0c90352800b259075060542015491404039400d903916034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107740062 1250 107738812 107738819
    0x3030603070b0406120506040b040e0d0306120807020906010e03060108010605030c09040818060906070c030605130206030106030c18030b060a08010e0304050d080906030408130504060b03060d0f12020d09 89
    0x345402548680760000e44030104c54003600c112944091f41114015101042282030ba10110301612069213040c1860740c0700c429052200d940c54820b90700602604072000740c0e0b2211585032004d541c016070b02c001e84160503400115406038020b1201d00007040c030103019600c040da03681050500170f0a071446064001e01554034116042d16101e01d0031440755500088042c1864440e0080c0c5841c15482c410341e0350800801c12550030a42d441c003020f020600d01c20b2081422990943c44d040b41560805007480c10003c80b00440c1000680d581030039030303054400c1480c0021704182154001c44001014041202c96488142004018465142e064522442050761100e084541e9540e0280c2203601d00c102d815120f410502040c0a14500a030080c140d00f07000d40030f401c1c02c1801450015066510980e0100c41045002445e0507c0f0100c2c0c0340c00c0c04c020501124100b225510304001040c0c43d1000812041c46660900c1c000410010003e20b044072068111460040844c2e10840c06952188800d42c0340001c50305054002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107741312 1250 107740062 107740079
    0x90604110102150a0509120f0a02010f0204080c091e010b0702010206060f0108010623040e07091e12060f0504060c0320040303050a09080604060f051303080402060c0f06090303060307 80
    0x410302e41c101c4401c00380c90750b11101303110024100030341805441e00480c40540c2d102001c040107818086166911a070381d40001003c040c0c00c458000c2c1d5074020749030060000b04440400800c043c1c038246429a44000d240d911482010099030910000e05104421400045103515101024028044c400e80860701a6151402001645601d080141c1d0010346008018000d051186540700c003081100c249440311038a000741d80c440d480c0c0060b00100405032451007089000340d4840c42d00c80040101248541502c2d0b645042c560340100907009000c041060103510700d040000e04d90001c46000316100c410001c2d401c05140903806030450702a802d0020b400c0030381544004101d20b900301030010488004a20703081c0b565505580b40d4201d10039001c10310500700030002e9030780003d2210394481c2c0d21548000458094411526044480140138210359a401001a200003500903085a030401e0701126900d0310ba80b42c158002c0d203088100c013080512030081c9400d12103101c07800070246001300400c0742030700c1c0e540d619640c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107742562 1250 107741312 107741323
    0x706050a0e0604080c0f0609010e1501230d0614040215131a0412050d1404080607180b0a08040c0b0a0203160204061d040b0106090501051c060e090604110102 69
    0x428500750000e201260010300749800428648506130152007000e641c01b0a070034101a011502c81c0d40d0340c0d449101e0b11814920600c0b480503000c200140380046541000f00c801018011201c502060403004640e03100a40c2e1038a201301103c5600c0601840024005a240003030740c94142c030208d004043c00060065007100c040c0c00c2e180844c4104d5081241c407480d00000038903e10407d01000014a020000072640c0c0d540c90f031072650410f002e000280000e0410f108010009451050702403031960060000f80b010120204501750003041900c0d00c8483c8515400014201c030b401548603e00d0002c0008020b0841e03600090303d940705600620070300304170f19661180954030b072140b80c02420041e0410061801c01e49107090583c1d20749400030b4000601d0640701c0d03044900426031040c00141b440380150400c020803030754800b81405070070145882c5041519080000c0c000d40030b000340c0311640042032100b095608920381c0c8114020582060a00040d00700005040d0307c8600a40d415a41c80e45034030200d20040d40002003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107743812 1250 107742562 107742581
    0x7030212150f04050c0705010c050c0c030601210c18090302010f0207030e0d0f0606090212070c0506061e091006180302060403141f0e0d0e060a05090a03080a050706050a 74
    0xa040d12600b8208010003088001c0001a0b984814025031020510920400d135083c2040d8079080da0318018012820b29202d40314408621130b50025005001d1007504a6240820203082c3e5400c845000551504940c03243c03080e00100300101d001904800785105d941c001050301402500204070941002c0c030900b09901c10910040c01181da00e13483c00310141840c084400e012801098240a540034950710301042d0307a070f560300c481580c540100750091010348211200b60001003070b0030541c0c1e4160f40ca580b03007034455500810082c07048581e0b0b6039041300e040310003c00880090b8021708030903041c50000d1351032103000024090800000c00010181c098100d032020354a043e65001031006003814a145c1c2c41d040c003512070702c1810314107010710440c0f84034440c10380790700a072080d01d2500c000c07503d641c021003d1441d04031400e40306d1301048060343c0104656100d0104540e0040ca82e0f04d041d5564422078004101080c0050780001c01100001558201455000000e41001845044140015203505032030340140c83c3c4046 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107745062 1250 107743812 107743819
    0x60e0c1302120112170406030c03060504020c0d0f09030f05030a030608030408100f020c060a0603060e010b0919140108060901050a27050106050604030c08010b010c0819050d050703021215 82
    0x50062000c103013040c0c45a94954410340c01341c800408550300158040c2c11075840440070945510102050316058024a030180105840446c10719013060301d136907074a1043e2a0100c05210541842640503485100040b011b9034014005143c084d10714948107a803030f40b02490944c0064580000401c1640c0c02001300c400316101a4000d00788000ca20428000030040080da501c0e255608111030747c0b00c4a002d100c0244200c82e400400214103241d81054000d45208d0031580039640d141c80085a11a0f485000f0701d03401540c80041c0c002500062108040245042c44244c0301c00c203c84000010502c00002c0c900c2d02c00c8a00c18020700c00d136103c1900300420350b5510920644110b6207054051400d4900b074506c1e000c528022400400c040c0e56401c08605254090f030815500ca400c007000911004d41c0900800c070000c41c007807030b00310354628254980c841d40f800b03070031220020940ca003182d5144840c8500c082c0e485500303041000b0001401d00d400050001d5004c0800e803400c440c011000aa070409090703080355280e03d03019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107746312 1250 107745062 107745097
    0x903060609091b03010615030b1008010513020c01020c0102040b0d1a060906030702010b040f020c070e0606091e06030f0604140103030807050a050708040303021609021e0304050307060e0c1302 84
    0x4109016494840d80d01d10b03404d90f68696000540007081204200c20701c06079100081c0ca03040b500c05114020304903503141002d0015a800420840d20369042001405100703000060701c41040320714883c06442445550f075560360000c10f004c03e10351041300003080300f00340b401402c0016084040c1c09400d245042134003182d0041e000d21858007541882030040d5801002440001b49100080001804171001c40e403005035980e50200e9400d501d030030100b11050180c07485c0d0700404606d1400700c0000303009110351030344140145840b007106501e8014a81c104904a00700500d00f0792a0303c1c00000440c55203d0440e046480b403810861042e07422081914a641a2074041e5035a60761035641443c1a0340300c0d485403502e44100881081781038040382c0c100c405880a548268040d1002001c0104e01c0ca0000740540c00203503a0a01c10131010104408a8548502415031450b0258881c0d80b0790500300e00f1401121070107408030782404243e00040c00e01143c081007040044032010000c410340600c2604a010703071039200702e610b60103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107747562 1250 107746312 107746333
    0x41d04080a0e040b1e01091d1302130609091a06010e0103020a090503070305150105060c030706090222061814040b1b0d0e010506011403040b07030608070605090306060909 75
    0x5074690819890b0301900c04200508008049480d10070740000e8401440f942002d03402d800d603409030703c01e0002c0003601000e481181100001124184016007501c0b10568980150001c54841040348000510000401c000003a5110302d200094110f100c030840d1981c0716917004c0c0b091160620001c9009900c181e40d003401100910006400940c046002c038400e002c1000b0001500d982d04020420155206034080d0900194401781d002c00c031441a00150b00c210420301880725802030001c143c0d451550040c1e0085036950190000c190000902c41d06840442c040c08a5613a0302c070313550303003107601220200340348248200e841664020481e220302c22010500b11441011402181c0c10256041d0403d11140090b0341300240846400c0d05a403128641115054444204482452081c481c09c1e0b4032840a00b025034aa40913070814018034880244014011491a00841d807164402da0002020740214000c445165454010280441c3c0121100030303c80c0c81610b000812030f050840d007071800b51700c03d0070040046595 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107748812 1250 107747562 107747567
    0x50706050c0d110f0a080d1b02030717040b040909050705031902090406020904050405160b0f030a0c0201060f08070e060f060a0f03090f120e030109030e0d02040b090408041d04080a 79
    0x3d080c0000505440361000c402c4410406020070004076101e440c000c4d50310706913404044142c1d419201d01c40c5941c0415085c20603410b0b004002c44852941c802d24050310703d04685045003240c0100d400403900080702040c007086416869003c8400c0d6402201150805940c8508140d40e840c00c26904100366810b0b03d4011006051041040d50010f100e21300140c1864036080100d4102c54045405845550110383c09901441500c0a414007034140c0c0e4003000d24120800498000b94400070b081c039158a60b4400101485030310170740c0300d10f024148400c4143d01c01582c8080d0659103002c0c9018500c41ea401c0302000c2011854014104608508041c0034a030518010f44004e440740d044a0311a88185174482e007605000a4070201090356851143c480c1c18502000c1190040031580d824603c9400381c0e1410000202003600701e6401900160121482007a4941b28400319000c0e28540000d2a04016101c00784030800c45810082c0c03090b5412002030482e07056041c0e81c4802c020300c05413409407040e4001c000c212905032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107750062 1250 107748812 107748827
    0x9071503110c0d0512090601030b0c03060117010305010f1406031203040512030c041805040201090e18070e0601110d08040f240506040e0a05120d06080316050706050c0d 74
    0x71180591030700700540ea074141810904040d40707a000150b00000c90340007004240300255041510780d0000e10596040d507072601240b2001500900500038040000741e02da07031250104500d580c20800c09600d017540e5170f1030510b001c0d081d00f8001681075030804c00807600710110400035600c80c69006006007103503082520004441d5002800584140c000da5841c0741030204030200460203010241360a60340d03946032401c000308602e000390718041c6190a08040c0809030303038400004002e854815007110351903102c22604c88081c100110a00e030380c1c4e000e500700c00201800c030310b00f0051103480281c0b6130400b1040b00c001c01644642023014004c021030b5451000c5008501e00c10f4116501620588a2525407002c030b048003e01ea200901ca4022469260020840107041501074450035010080040002d0000c5907100780c3c881c00c0580b010351705002d011410b04000f030b00c160000f40080803500c041c0c0c1d581b024458810004000c10a6081d6011300c6480070025035180f0441c02c031240c2d1070110010300f001022182c02180d000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107751312 1250 107750062 107750081
    0xe06030402130e2a0a180e01020405180a051302030706050d09060f0504020328031b0c0312020c060304110906030a12031d0a120503190504030c0b09071503 68
    0xa035641c88000e95002003c010541c0c44640c881d4249950302c2442070400302e0b0010380300703215000c0c101500d02001890b00502240005030368481011030307001d021401f418020702484d48056440400c0303003407115985549080250003a80d00d50000d01c525920007580c130840494a590082d01540035990810280341318802500c1d008144010100300c651003502d401082c0d030a00c0741d000c440c8079035490601045250420425240310554460320510201c0c80900d002d007184d01e65005820b206d2401c11514a07140110703240500142c1c480206111a030b100c0c24915041d010403011040036210345813400580707240000036240300e03ea00c00744075010a1503a005110140c080500160307010311400d600308002907420368400310481c0720b80ea40041c5025030003c01d40c20f0055000b50041c1d1a400444900000c00d0816512140c0040c01c0e00b403565407034a43c50202d0f10f4104c00b20510503a05440d10f03041c401055807006440170520301590074522562142d001c0d00b61500d403036201d602c450103030321142c42800b6800717030b0020104c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107752562 1250 107751312 107751349
    0x201050a050a0201113702031e0f03090313080f070333020a090603060e01121a070c11041b0806060403060f1d0607020a03080a0603200a05010e06030402 67
    0xc01d00300c801e025060b4000c0a514049054154140d404061821501c600c40042500300700000c1c0520441c00780d02ca00ca080d00b89d1500b5103030f1154014060005030202d5003600d100748561030307030313480e019072100d0301d0340c0100908910844036440c00244401c000602c801200b842000544080340c515510751510441032881e1003485032840d03403003a04d040b00180710182c052038240d101603550000c40030000c0014450750000c1c0c050602c0d1820034003031450a107a81c0c41c1900c0709920360000d070b0f960a00344555003c00603031900b04016104d100300008298072202000b4101c0c440d090038011032582c4410401a982040322400c1901c030050759130f9540314858040d554200b000600b040d45050740301d032210700a4032402440f4001245e11a6a01032039008403281000381d203c511000f40040e0305107543c00a440b034220f480040c00300008500420a400280e9104c00010f541c403a00000030a01079030070034000f1140300a85107201e006120400a06540118040c4184140c001c2c001d91840e641c641c2002618486020141817 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107753812 1250 107752562 107752571
    0x8180f04020304060c0e03030c031801110a0807020102060a09021003090201050d1410090908180301020d09051e070f050d0c0807121403160f02130f0e07050306040201050a050a0201 79
    0x221030315a880154000ca0090002003040d9103180009480d6151050700c050080e401001501c0d0b907890041706a44d10b07401c0001030405075400d004012140c22001340003d0500340075400d680810070089500419000d8801e809548281d43d80886160840d0200c031000707074105223416084c0a41034407075441828402d105041142c14194219100402c403000032080914841c103040511030030b182e00240890007032905010a2149001603a10700e4010301440710103a5140c0c034002d040964a41d801e406035203c40c0c49894040000b5040c030b0038800d5642085038562451480300c6032203114842004618001071300c80b8040402d0030740c0c0c90841400340c002983d002c140c0307009000d410b021540e80c0707042c49106e0047c4242c4525811201883c200454013010702d84404030280d108100b420501d81312403040038111354002031403140c02243c07030004c62600307243c104610383c1544c43c05022200c1640b0315400485c40c020104210f03403043e0349400a240e03503079200b074174040e021450500c820000d95200d80d000340600781d000c1c8000725 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107755062 1250 107753812 107753839
    0x30f0603080301090f050a11190905130204140409030518011403010602011b080403020616030e0607081b031b0c0f03070510050618010302060315030f0a030f09030818 73
    0x1507070741007a041241c180e81c617510300a8000095004913500150a582c003041950b1038403040d0b50035440703002880b4502145040440d4481c031701600c0841e000b40409003080c281000e43c510340070002c1d8098020301001003551000c00555080610170171040c2513140d11424a860f800e08100049415902d05150400c135034000082d8841540d100030f035000741159000490380f40e140308500e200c4241003900e07000c10422094108004207a0000d80e15401c0002c80418a041800ca0303803084028245292180889104400a200c2181d41c04480306100740030107800080e0700404010103030010711084d516a0781d036802d10800381c007848600382c0086c000c6010b00012035131000103483c90366007145c20142040e43c0e260401100303548442100d01a8070341c03200c0125015121201000400c003074251060101034040c0d0004400104a41746081c12504481001400c5604440d081a600384c0c1e01c0550820031400561201c00900710315001e54505001c3d20341c421000f03030405200200011261031110012540000b0000d8250b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107756312 1250 107755062 107755073
    0x30a0213030501020304032715050919030b0702030705061506120c0703031524050408011508100b010c060f0605130e07080606061b0a080c1b01090510030f0603 70
    0x100041d4416000540c0f00e24140c14090055503800ca01d4400000281541c000103400488101d02950700001301c00c000c0e003130582c20456480c01442c510035003084844280f90320b00100ba030103c03810ac81c0304d00359034403942d03803002001c07a00c0340201800280303558000e101080d40d154070001c0140503d40040c00b0b440c01c0c055078444950b180002510b2100741d041001400000f0f06901d4003501d0458481c0caa91a2003080c035000c0001c2040c6503088450042004100d04541007d104000311002843c0b02402880705031003210851401c5219403040040d00c0c8201c0c99075064040503402000d5800c00140c5904150039219210711001d0402003280040750f541d0f8442c0459250340c0d060701404070907440000081c003100340701422440c2c11216084032800364450420401690341d0701c0d0841d014001e00c0751281c45406440035503586450040c000047c09000b002c0b40ca82c0c100c1100140301d405114445101e0700c0d40c00025001501c25680c540251500700030902040c001072400383d003041404039030b6084d0024172180e598444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107757562 1250 107756312 107756347
    0x203010f0221180d09090b0d0b070e0d06110a1b0308040b0a06090c030e0d09030b0c0c0304030b0f0910090b070c03050c010501060909060b0301140d030207090c0816020a0302070b030a02 81
    0xc080032454480c011b000c0e1903020301c1841c0800b10b00ba29140c50a468a40720701c0800320005000342c041100500260485403505200c000001e5400301d014014807504e414003181c183c1040302a003001401d60507500ca06241d900001c1d0418130b030552100a92500c9686a03d07103100c0c0c00806000d861625407070009400c0320030b4899422009095a40003500c5038005802e1410b081003c02110100814442c042c00840e0f40724540c203030004081c0d05200c0d81c58404a40540c15401a58009400002e0220420082010000d04940710300b100100340c62040b00781300c091404642d00c050000d00301007151400290640d0240b40c50340344040c080e051a5081810007210603095072070076004000019000740c02000703a220ba6020302c6014085589045080d90306001c1008856100255482d1140d11050903c80604d4005e00945010704901c1d0018040c81d04130360009800500280c2c0e08410076400c840200c00040d00c00300301c401c07601d0390581c050b101051400c05000c000f0b0700060030500d24554200003000108051000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107758812 1250 107757562 107757583
    0xb0d140f0601080a0c081f0506272d0c03040201050c061e0106050a0e04020d0209060a230c0606040b04150905010905010806010b0a051c06030f0203010f022118 70
    0x70a1518190700e03140000156035408842d5a9100c0d98010100c8805007040b5401405001c01c0002e80b0354640d00000c504140141c04000d0345000e0b0510510b40c0c0c2b0140c0107040c4a00054041041d004100021540f480e0091003401c15083e1f40e080d02060030307005514002e5400c00d0051420604000c06d0b8000070b400c0c070500b1380350304424400301803800030014135a41c044d85c0105964103100b410400850340c040e1203400801c1195200f01e078001484008000c650341a64a4298054000f41e220300e0301c210003820401003002004d0103500600c121000300d101c8032007100c0301a101070010304556140e4000b4000036100d00c2501ca5403044c2c8588401c0c12903e10b11800b030009101941000c103140d454046200e0886030182c0181c42107400090040c001504c080d022945908150320b4580da8444450700020480c1e943d002d420020b0605169001041c85520b08001184a000b00c0003000407038003003d444001c030300c1076261001d030341040300315418a00300011820a90007a8018160301144c120f40e10960b051082250 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107760062 1250 107758812 107758829
    0xa05040f0c030f0209030c090a060f06020d0306090c0e0103180b070e1f1b080c03041203080a09021c020301020903030a030204030b0c0a090e220309050102100b0d140f0601 75
    0x74520404503605008049412154240c1145005254808661500e0f40e5040c40b03809486203001141c150b6985a10410040180929800100786c880100039141d0010b203014000281c1440d001064201881c400d1101014050b1a900050229040103401030800b5101d40c55030100c0a8030782401160481d41c0f090312501c6150f0b0341d0a0a5080c610402449603407056512403182c000e640500042500014031f001c80a00d0352040d400c0303000291400d00c8880c810800c40883c0c602001c0b60000d141c40a02c9405650680b003510744403116529024100100c900c0c00c0d00c081e60140c0c1c03090748290b004003031041d040030460025002515041ca0100400c1c55a4030200c100030004c0d60010303041090110035451190005030084a4615025000c800205002c801e801052244001680801c1c140c4040c4500030600560169454802d000e15041c060081c42c4644105405400744c0c800100c088002d900c501092404000c1403514002410388402c1403107428149605180d10641301e02d20b201940400c8102d00800061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107761312 1250 107760062 107760071
    0x2190203030612030f030103020904050a12020c18060f010e030c04020304080c0f0d05071b08060a0c09151b06110c030d0b06070305070b04030e0a03050609190308150a05040f 76
    0x1806204084801440c0700d541a0030178040c0d400028204805c581c1102d0b01129103400d02c0e100c0341412070030b01015820042280c038540d40100c1f0490b130045440340384401c0403070300c90b40300c1407144031000d150a0301190308035400303841c00345071079030940c00f92238844a07030f150280807a2020b0b0502d20214049074025103082d00c0c044004034400780024410400d181044480b200034200d17580c1900405030042c0914600107040c45140105106035840034002c8100030303c0b001c0c080f80c020b81407c0314000001c1c480000d1000c0042d01070100440da41c080302c4602c0e1017246c03555907402d0031030900343c001c1c5458049213601120400c1e180d001c1c0005000fa41300140403070440c020081e69a030074030010010100e420702043c046c080c0030103102d8000425006404c5d0391680340c01511500540d0794600c1d04a40d40c1d405240c45981c80811108003009020000440e5880b61400000311070742d02c40ca058a0400903982404003c2c0000d002e5000580310072804201002007003000707040507601d40d0b250800242621020801560380980e036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107762562 1250 107761312 107761321
    0xa0608060909280615080d05070503120c0702030106060315032a2309150d03120c0306060e03070b0703050c07090903050a030c1119030c1202010501030c0906180506040219020303 78
    0xc0d480380072008170121007540d4240d031911201907120400c0301c0400003400000300d148070921a081c01101d448040101710359135145000140048981c10074202030307000c0d629004000c91260b01030301c030711180c00700754003030315071149240d07507a4000e000c01c01c00024980c00c0302501d585445200d080b03c285014000003050340c8482010f0078491109034100702c00c118440c58082050040700d441c003513000c030080181038540030304035161818103a42c0c0e001038005060702c3c50b28191100b1902ca41c15400080fc2c1c610780e907101c407104110380040654680c070501a690b1084020040ca00c0000d0080004181e0807500d00140c4203004c0d03403907070260700b103c00c80003003503021410000385140c8640c0d0601c19024001c03aa828540203078405820340d00d581d80c0d81e0000d040300e1002800003900505005048038180070707604c03003800307044010039150090190800b032100b111100d030001004075a61a81c1d014460a540d050286002441c003620850800b80c44c0240032031707400aa0821001480c14020440c01d011014140c00031962800c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107763812 1250 107762562 107762573
    0x12120206090705010504150c0b04061a040207051002031305060a0606030605010507050705130b0406030c0e010812030601081314010b010f030917130e0f150a060806090928 75
    0xc02080100e032a00300300d1040c00702e0fa8002c42034400365104070745080d090f00e2140340b00362680503010a024000182000801023009190f41124204502c01604041329580d450b003880300303070300070170038018850341140c050b51081038010350217507600c4203403600e4452550078207844507030800030f054079180340e2030741c50300390a00403207402d409000c00070802860302500d071400e6500d801d5103c0c503482c0102031190449900c0d8480c1c04a541d088500c1c0303810018802c001c001d030b50346002a10490326201e011440d0178104000a9542c10100d580d882101050584500e5540d855004446055004080820110007401d41d10042652004581c0b000441c09000090b0006000d001404c2100145c09840030107050500007000144e003800f0441c15441c1c0342c04d1098583e8000c0103000450301464224024252a41d810003c000c1038100119003d20720040090303003984451018064400c1c0c89025080c04215280c000c00c8907401c20900659004020f003003541c0c06500407480f064001068400b240c5440706402e200d840500c032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107765062 1250 107763812 107763823
    0x804030614130f0204240603060f0f06050409020319141f0f0303050f0904020c030a030b040219080a0e071706091b0603090307020a0b03040b06220f06121202 69
    0x1c0000340042c0322110036654040b4840d1540c40001d00a9840d0600403600c4031454440000c0c1c40c581c0c40500c042aa2107010060041503284507110490780c50304000101800c010950300299125961407a1419042008210296001400700c070083c2c04000c210f203400c0812032084001c14001c0ca20100e8050600101d1494800103003080c1d881c000b003040e0001c0203034051100c02041240da150a0440d00d5030705000b40540c090064203096a0010300000b4001030710703c8040000d00d1854070a407000c01807400020140001c0b4024205038084142c0184100d144c824010481164000a0740d400450800c1011203101d0078604980e0004207648009608900e120038240500395110000c84001d00f102c04600c2c0c0c030803c00e400314006080c050074001010038980c807014030480300c0300b1707401400004c05150303070310842c0485078030407102550303400e00100206030946400034400240c9c540740c1d8000c140e0001c91400d0900200102821880c4056807a5000507001c0e032102d00b000b400500542000d8a000c5581e1000307030905 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107766312 1250 107765062 107765071
    0x503010311030615040e01060e0a05011502010b0d0f0813031b0602060c0301030b04020114030708010f1e0302040209010c051002031f030c060e0a17061b0c060c03040503070804030614 80
    0x1d4101c50200003144c6154509444100000c440c081a600c3e0300e580d01c5801006142c1140782400c0d00f170b8040003901440b5400240c102c802c01e0f5041e000850605004074220355049034a603a11040d84024840864000102024558001c0040c14645018011211050703000e560044482c4600000f080100316085000c1000501c042c0c00030301403c4c40d00340310601c000e1105000003407c45810602050540e4800c2e003d071400d000300e9018107030f66801c0102d80170b00410824412582040e40003580400c0d5400c0104103400c018030a01d549446050071a0300300006504500150f90411080c440132201088082201405816903440300594038103042d4900d10200c0680e005200819060080804c001040401507100721801850008684030304280015420b101c25031124084d032500c0401c0454a01010803c107016086031807211000d94041e0542000300d014407103890641e50005c200140d241d0a59000441d4403612a005072441e0110566800300103410680003500c100e0f07500e600181005282044c8250031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107767562 1250 107766312 107766319
    0x906010905090103140102090d032703020603042301020706051009050906010b250b090d110c13021b1f050f06010309030314092b02060403051b010204060503010311 72
    0x4a6040030701160000006100c01800099640c481020000c02907041d103044000042590a1007495410014890b8202d01d1140d01c03011440030410f808400c505d09e442084913400b800b02420755960341c561000441610302110301c060b9800d8a03a4480710340c284000c5c0f0b02144074a00c0051507050511030444201c11541004071014500001e000c1422000114541118408892160750f6200d94000d03281d10142044031148c00c480781c40c070080400c0b440b0021b0f01e1190040000f2241a8014a02d080340c0849130401250403d0f001000240c0603400d200d0110b00500c1d42c000805880c007629079002000c0e8a51220143c41241c21a0015040341160b0440c041c1c4900d601c004103000300c0c00e000681c0e401e91030300603080c1ea0505989610980030580260415a2011a04000505079140c11508a6101c0916186521150441c00004550882240c0124624051660040c016030399a56001e503440e9000c0c0c84409112b140908035030400070001d000400c0641026901e0346e460303501d1494082e40343e86030820003512 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107768812 1250 107767562 107767577
    0x3140103020d080c0a1505070305151c0201140c010e0f0a030f0503040f05060705040602101512080d021611030c030d030f0f050c0703020d09030f03080415051005090601 74
    0x540e030b492a1421a081c0c22401840e40da81a0740c003601d02c0c1010482004012010880140742c1e015503990009206082ca92401d016a50310280402c005000406500b64008038010034003d0041c524034464070713000c1c4103060400f8141040c44a0103043d42200051880f50f0791144611030401c80305020950300c0242c3e41d4000c101115940d0750141004586010003010020302000007028840001c4104000e15008410348200b8100308400410940c480e00400015220702c106a00d1703648040e22a44054010302504070442e6410101e00b4034903d241400140c521030414017140303804080b58401800d000c20100c00c0160081440e10f808a50919502c5070248607401103045202503071001325502c0d2030703003a092800107010194902e1080091007155455801d440c5401c0030800c0c0907806d04000c0002074025001c8441c0e295075920100c0d105011404000d1081408941d0800000d02030251035030458801d0b00c00b51300781d0300100407103400c032002101c040c150b0044034002044103042c22111030b904902d00303207852403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107770062 1250 107768812 107768819
    0xc020d0206070509040605040c0309050705150d0b0f090f06010e0108010e1302040e0d020a060b0603131103070e0906180606010507020d080403060c120609090218040c050a0b0a031401 80
    0xd4858100030701ca1003e02200180c20500e640c2c441d48150094074004104002d14002c201e0010000c150b050f034125824030501101040c185052021175078000c1548281920303046281c0021800307000b60861276504107100120380e05403540c0303210035188289d8806084070003510740b000c00101452042c4043e241880459401801014102040e0750342c460034140e564802c48803148080b80c01000714280c100e1482c001d0b47c02032080740343c3c041116295140034100900c04038103620304002d070a120603640a0000f01d250041500080e00400303a4000348000142900c0d140d680e40c0060001d40c1a080f1035540c0c1036000707041003001e50807160b100c6101c0001690001c01c49850310f8000605a4030030b268001c3e11450100a1540c01c0044140c1290061030388120180028000c40320054900a108800304030028140140480d8101081c40303100c00342c0e5002030003d0704000030040700800310000a072081c0c1d6208400f1402045c507486a581400080c01203100c1a070340c4a1011100030200d4520034107980d0480241401003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107771312 1250 107770062 107770067
    0x1b0f06060d0812041103161e0b0418140403080105030105091506011101091509020a0608070819020714030309010f06030b0c0318010905070302040b03030918070207030b0a09060c020d 80
    0x680704461003521001e81d81d1203504200d405c1d01a400c003020740c544103201108041408021a00c2c04603007a01c1001c941020420280351304610060041c1140204240420019410044007900c004121424000b50b030401c00085082e034a2000c80d0240e010900903401040141130034400ca640c171402e400c0103400b40712164403203443d110a028002138100012009100c0581c0740070745c8001c559980c04140c0300b07281070b5440140380152060400c01d900c641c0742c00d40300084044c020f03100548140e0310395482c56880e6a401890a20b00508840d00b0907c5503420300180000034400c40c800e40b60700c5800c8000310b449185c0014150f095500040520001c1c46c1041401c100007402c40481c56000000ba00c1d1050300c0e0783e80e03103100b6895003100494004d6190300f00900c003018084003040c1074094074000e4405000d507032140418540d69218403904540c201401402032005080c1307001000ba00941d252040d5181c00340e4035110043c0101c015540050040d0359030f0000003c1100a106445000100d4009030402c2901d0358400b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107772562 1250 107771312 107771317
    0x50106030c030b0a2f12100303090605071101030c030902090a0f0e031e0c0124050301110a2f100209130501050d08070c0e0405030a230403020609061b0f06060d08 71
    0x100d203170000042e02d582d0706001c8030380039114840c0d9000e00350303900c91800080400a6008030b00c011703008036076194004a0030394407a8048500ba01c2d0031503600d003000084200110000c044403500203041595500700c0030b00503500c3d83d1619008018440c8081030441145182000325104540400d586a2041110f488002e55054640000402c046005500d600510052031701506020629059081c00c040c100c460003000c10000d2401da520a8008000d0030348079150a016910808911001140d0301c07c0140c440c002000d400284010101e11200d0520316080300d09900d45004e048589101c030340c0100302e910150070310b80420707941804404002c0c80343c1d514020100e0380e00400d162000c2c218500018401050000d207509141c000d1880003661807040c54681042c0d51241c02c1113210310005000800c002c0c1b54a6401c05100f84c1d40030f241941503260038034580c01c00004d5400805815044441070080000400c0314038910800d144526015182000d40f0041c81400d100d4020070f90703480b0710200e5030840c0101e4104401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107773812 1250 107772562 107772611
    0x1b06060f181503030403150c0206010e011418070c0318050604031502040e0411010806010c0203060a0903090f060e03071d01030f060902221409060708070c050106030c030b0a 76
    0x28681c07440e494400c54002102c680000341500b40c800020000100401000400403c400341d600400200f92030303900480e140c0d08280700b0000070303403002c00041c0720030400004613404201c00204440e81c1d50350102c1c0c1d143e881040c1124840c0200f880e200c100c0c1c003890782180804103142c03d403290101501e42033200142c0c40d03001f64000640840b0004011008850b11a41103c01800031410f108840d460140390481c24506201300d0340e40000d2082e400704000f9405007154554490b07009010380312030754690b440700d03000301b01c061360a03410040d80c140d0005144c44081c0e0b040c4054999a510399001101940a15103003549950025413081c8513940d440108480440882d41501ea004c1006410200c031801c202018044090307003e588800314690b2030081c0c0480b581d40c10702ca4841008184204401143c1e4000400c1c011600302c5102e8202c0340001d01d449104491450303010041e41001481c0503c4d50700d4050071101c96400413101e10010140900138003915115143c3e004034030a50900510303a0408080b003402c0050381 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107775062 1250 107773812 107773849
    0x103021531052e05040810051504051509060402040504061701060f2102010c1a011806080309060901021507050c06060406080c04150b0c060618090d0c03020a081b06060f 74
    0x40094541c51013802142c00030801c5100b00c2d10041c18910700d000040900b540c0c040404d080c40304020800b0304060140c14402c2d00001442611000c10b8003c0c482c00c808000e005940c016420040441c25940380d102c0ca4000d00102d07108061600800e244141c2180e6083e003020201c0d041c001000c1140381030340d401e0384a0b00c140d40c83c90b01c140000144010f0b645c0d0510390100500100f01d11040700700019085031388074121a41703c54a24521006000a64101c61490041c0c02c21904200b00300045801c148000700314034001031040b101c0c0302112180840d500303681900e01000260001401c208054005c01041d50050421a4204445494000e0040e0345400c8880a14012070702d440380c0c52420405805040000c3c40320348851b80e5100103000c101a00c560045518a1040800a41c809101050307005d0040c49000500c006000600050405960041040004a045110ba50102c0b8001400100a030440349102e519a0042910500d5900d0a09500408041c02035841c00076658241ea03400c8051104411102c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107776312 1250 107775062 107775139
    0x170c0d05070f06060b03060a0e060105090103050c0d050405030d240e04060b030f1006120c1211060a0302091c0c0603241d0c03040803010302153105 65
    0x501d000004281e8000018143d949803000018003441094000c6200300d90454408128030b44400e240320781c00c50142e485074002807050040a545500035804a40c0080d400c1e0f0b4001c1c18020300001c2c10b801d54038111400c41e00c940001c038485100c2010380c00359000c0a940010324100641c8803880d0621302e03400501c03c0701d5001c0b12020105080c4420f92b40083c4680340007a0641e08002c100c4203c10b661004258004200c0b11b103048000143c2048000704901707156800031030b407041d0a181c5542e4017084803a011098802e00c400d41c02890040c0e4a600c0201000c004649001da01c4400f01800c0040e00e040d101882900c1c00620103800000851010300601511003500f00080d40d614140245034841c808541c20165018181c0c0b00410041e07410400340d9000d414140c01c002007559095030500850009440040402d8000c0c40140010300d4078581c00f90f03160000301051810845400078102900e445606403c82004400748400c401f103483c4245c89000d0501501e0f483d0f1000901c2e40c5440c0c4241c01399007101582c0740711 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107777562 1250 107776312 107776327
    0x117011404020315180717010e06061e070b01090b0609012c060c010e071e03060b0d0b040b01030c0b120103200901090c081b031501030b0303040303020703170c0d05 72
    0x120b40b0b08141104d005414210380e900001d001007804001940d000c0c0c041024a11115a00d506800145050303804a001182560700e640c821720405030408605070510680b0104c1120b1020000350252280e24020442c45006514285800b402c1f111003d15030303130007050b0400c0482c0c200d0741c0240f0824000004800c050807425602c0181c2c5c0b040b44056500c280e40400001402104200d054024003001003020054607451951900702c5100c800180004022840e01c591341000400c50540c0445604000904903220107180c136540c5c0032940e9012502221440c60440052060012003ca8000648158079074903190440400c07180021040500c402001a000924112001d60000c601c000c6072500c05002d005265840d140710030040c001144055001410010020710421b2042d217491511400c1211001d280d0f403079080c1110210601c440401d0305241c1c036040854401d8030b00b007000b84001c2d800f239406416500d04610300501d00c02031017000180342003018400d44030340d400d012540300700d8040c844c00d000756552a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107778812 1250 107777562 107777581
    0x503040b0711011d0309040501092c030d090302010c020705031b090901020f0f0304200607060c02071502010f050f0f0105010c03030e010203010303030c020d0215010b1303020a0807030201170114040203 88
    0x500c00241d10200510130048800d0034000015202e0400d04503001d0045a0b250f0400708111409540c1c2c0c980c0f0100d6203580c2215401d481044628103410030350a40c0d16103000500118196040b000703044005039500c81c0341d40c110980c11301140014141c102d010b1303d43c104a0483d544541c0c80ca00d040c59108401000100e44580025411501170089010b52107444040c0b02101c06000d41040758251142d402c0c80242c0c4241ca52004440700d82030200502c01c1f8203050054540100038009001d11600b98420001c0124001d0082c6034070603242026a40003040c651101400f01007070b03460240c052001c102d5800c06000114240c0c1c00f03403d055410a2903c1c452117051420704070040e120960800559501c00800070051580c03507082044005665002c0701c00e200c03540003003281c0d034000c200c1101c00904c1604d00144500c28001c00100350b905e0000001180d46a100d80000783e4901d543d03845060f00d40c0c00f50400f00b0455070085a084a02092840364110940c0343c1b400380c50410100d8120284036603800400580c42c0c15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107780062 1250 107778812 107778821
    0x70618030b01031103191205030604200d0b0f1c0309170a02101b030305091e0102040911070c05010e060d0e0703020f030102070f083103120503040b071101 68
    0x5401c61a034041c03550352420314020343c213201d40c80c1e9402070041040c046001900341042c0305006600c00003051301d10080b03030f030211880e820152036654415100e901d1003401408074241ea0b0003080c5100c05c07803552080741c1c1c1241c0301264034000e03a681c003400482c120383d40c007540c1d24400110300c000c104c101c2c42c446502c980b03000c0b200d01031590410200103140580b501001080040d06a01c080e10030340d070700b9009040920082d40d43d83c80229200404250206c1603500181c440c6d003085400070344034400c44003916107081e00c070480100c0c048403030300319a9804282001850301900500c4c0f0080c914200d031501c5c08000741c644c960f0f10703016401001d047c0b1068902c2c114040e1100d408841c01e1141c203403400c0190500b00030a1a07142c0702c03148800d9100d404820011100c6150610807140619400407041100e92015a64440c040c0c2100034444c501d100103c0058020031520101d03800780824a005040c201c508600c4c2c966825800c1c4540c6904016040c001c0000040c2469000c58025100d410302c0290002c100e041d440c00f61 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107781312 1250 107780062 107780069
    0xb0c0706060e10061205012702040b0a020c04050c0301051503100b04030602030f060103020c0a0f051005130c0905010312030b2d0906060f03061306080703080403050d0201060602070618 81
    0x5034840020070100d500305184070415038100c5e03034445a110941c0070184055034002c1c000e02021600c008a01e0001241c4924072424010104101500386613036241034048a40001e103070390000d0b800c0901104414a000d21802e07a03c0090341343d40c142554180408070307807440c0d02950074000c0c000000010031200e40c440c6007100d00610101c0c100a59468491511002a40069802191340c5800c100814982c1d0700034004c1e164442d40b10030003481e0400c001d88845410030784132441900c0c1d41c050202c40248010b91401482d201e003980062507044180f19180c030b085114060340c0207074291460403006100240f1507418022128019107004200e1200450015940b00c007507191800c00707004103485034040d00104946401d5500012111540190307034074006d0085030b00c00c2a9507250300b920f0030400a160741c80e00082c10140b81d40d05d5040064425151b002080c17132310ba141c1d001a01d0300b03c0041001c00400a0802090030483d101d0b00c001e0260ba481e0040180d80d580d65402964248500c05a41d0207104541011601c000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107782562 1250 107781312 107781329
    0x403020a0b011d09070303050a0c0c0f08151302010f141207030501051c02030d0f11070609090b1c03050306060f0f04052707051303020915040b0109030b0c070606 71
    0x45503910760f800380d2107502c000118103500303070040c0010b102d16001088200840350942c940c0c070328003d18018110b41c5001d800b0070407030b01809050400301d412207400c1e0542d40078100b600c0081c42c1b88000304400c5080c40200030040000980009140c000507680601c43d00340109075800c01c01c407074507070014410215000300c0104202d051410000c004119600d6005103040329020b03601d140100384d60034004007110701850700c00f0390954080603a00380d40512507100251b20b030660340b5051268003003051086040c06260b5100c4000240440810b09c01d0b1002c0348135044660078200d4220002c251136000314044c0303449407000070b800d101d0b010000030758030380b82c500445861072580701c040d5039501221300301078840c0c2e0001d008681c003031044400b185038400c943c00015000314011000100c12a59522811241a40729400c080c1c070382c502c035040010040c0c8038004003500401e1001c00d00e51010031180140000c80f0302c03c07500b9074100649000c040010601e421029a0000344080c440d6590f81014202000501121f078040300300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107783812 1250 107782562 107782583
    0x8120408091314091207080d060810090510141305030d020d090506060604060203121506030a02090906060415030f0b0910181a0d020a0503030d0207050708190b0403020a 74
    0x42d02c0000d0b0312100241419020418642c4c442c5403402d55039052081d608805010100489408200760002a2107500345841010441e41d44840b2500c0c140500000803882030f0b61074213603810030450280441da030124040d540802c0005402d40d211005003101130f000044c0c40104451940c217004061049481054200c0410340d550040326604400030300039584152218040d01d40891384074548102190704441599008608000e41102040d01c0880b02404856003644844200c0c2481d4403007201452055007407501c0107031140d85400c00e00c844060000c9c508bd11070343e01000240201e510f03070103440300581d000c0e14000540c5c2040d0060000100b807038445899002c0c2050341040071307501c10341c076410013a0b415600642c0080c201244201d81600c43c4031942d03003a42c0210089083c01800c3c00d094a56003580002c005001a550f60000700e42150f004003011810184c00113000c5052000c20480301c4001d14582004160504808040820306008440d0040000c0420400b040c01e03d40701308100054107400c00e07400b51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107785062 1250 107783812 107783839
    0x1502010f020c0c010801080c0f0910030b0103080901020d090b040902250804031502160312021b010605040b0312030714071502030a05070c030e010f0908030f0c070f030812040809 78
    0x29034406403c1c43c407034006010440003003817844000c40e0307115554402909036448100f05004100c0c64840040141510184610380040442c28078005280298001d140321039031909910300080c20701c8082400d030f60070301009140401950b05d041c8211401c4680030381c80145c98031444206400c01000c0c41515200c0075141003071030401d10442000600c1164490303607055603000c8045419200b0781c02034800c4000c9040310381d103c03000424061141c007210902028001860000c3d1078501c0014000250704e031000d540c0d580c403070500041c01c29118042c3c0c440001c600425981041d10b1440d06507210090108007000b1761200c0e000361201d044000e94200961001c4004428440e0130039900094104550f545065420a401705a10a0180321109402ca80660342c0e075605040300301c0103440c501c0a4001007010000e449000268120041c4003414890a8401560f41e58842c1c400140c1d1400540d90070988440241035001c0000540c3c40301225120a00240e4000d0349a56608280703810340151051640c20540501d00403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107786312 1250 107785062 107785087
    0xb0f06060d060815061203040308031509040311060603011a040207020d0c08060a150501021b030f0a080712020f250509040b09100b1c021507080307020708030906041502010f02 77
    0x100c1484c1500746581d1080c4c0e140010400d041841c002c4600454000300020300214040800542d0301183c102c0344e10ba0391481c0e400124401d42001c480540001380c2150440462840610050f5000f290480080c0030046030040c000d011200500d55540c455035001480408644078164410005900320f04030501031a81d550819807503080131500741d404540303000260001700c0040216501070b1101a4000d024036032411100580c103a1a00c28003551511030190084c180060030403010500c1c9200d2996282c41e03111525101c0240301070a00707a0420764012a842004415000680300d100c81c0288a2a100100300307007070b400344001070980120380c2090308501040140045040301500640da8001203d108940400010381202d00d140d40180e4840c503201300795140541c11503a08070440740001c10b0410724880d64030f1200b201343d010315001c0720304200100c10095000e406108500c02040d044000d10b00e08036800d4009a0b0500c0b60b07000750504141c240d1803150005200b540040301341503200c0001c554610519016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107787562 1250 107786312 107786323
    0x7020607090506040e01290309010605190e04030c170a030b0f0312091306051818010603080a0305040302011407050c2e0504150c0f03180b0f06060d0608 67
    0x80c10100c1c0a100d000951410040308440458200340303c00d1046908100d0302c4040082c0b070301801d80780201800d0908480d290005c3c025406040007c00006940385000c05000f40d2030f0b0703084640d00d15014118801c200c1079850645440e40a9490714100f0035071032040ca4800c54000c1007544101c82410042552001c1e00e406034881c18071501c4c01c803880b80b04400b4401c1018ad94100001000e801e014081c4200c00440c1440c0004100000706810007054442d05d8030701289188040000409003605610306001400e5154852448903009600080c044d81e07045407180c4915219600d028000c26a03201c00150a00d8400c0d030002c10001050603021a05041840000309681c00030000503c0d14051060412a0301c02a00c0c500240c0c031a100b20030b03000e94060b0803510001081c1c0240103403420750b203642e552401140c091040134181d400549981005000b03104009040710302c402c03e0309020f000c0c48038140d404203048030720703055028646c10003c0030542c4d41c0c00003040c1240a607041d0345881c1c5050a90201c1c00c66004140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107788812 1250 107787562 107787571
    0x8070606090c090e1e15030303090d200712020f090403080106030f020a08010510140a080f1302060d0e12070818030307030f0e010302041a07050d0206160c0c050603070206 75
    0x40b80000300b07444100e20780c1c42800c261400142085c42d41e40c009810800c0701c1c007041c0d00c1241c080003c0f1042c100700010900b16401140d60440a070491004c400703002b81c00c201307141c00e20112500070034a41c6000080440d6a504140a540301080100004078119641e201d00c2940246010300281c009007001d20b8058581c490a01803107002c0380c105800c80381c5814052091307e00598441c0e6038141a40d00c1c0c03109000071240c0b661010010006000480a0f004001310010700440e070f02956441e9140c0f601c14100c105152014049070904100e10b42d06201580c0c9282c29518030402c2d4080c0003230003c2d620300040d85090b66501c161802d1601c0840d1140a0101a03c00703800c0c003100404031400842600c0c000c05840e44111400200480c0d5030090310f520183c0b00f4014800425010b050041c9482e4440825021903010b01460307002c010301c00110301d82000303400d000050601400c1e000034003485c103000070200d1119a48007141000c20200d48041000d0041e0a036400c001414058007080e580c0c10450350080d100c0c0801c85 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107790062 1250 107788812 107788817
    0x80409050906090303070c0b090703052d12181201050a2309030301060c170f04030302010f090209061c0f030f09080a0b0103080a120e0f01180506010902030408070606090c 75
    0x4001644201c0f01008032031041c109907440609112050740c80d820b0780d940282504249100d42c00340440056405c00021102100c151171614607c1100340355100c1503c091a803408458210a400c1a02c41c1e40c0e0801b6680c8148400341c1c1400c12101c5c07071001c81c4031940f0510303080f5020340c200401c2c04503201c0d00c2d90013a030f815030301035181b501194078541002001880a444828550b801003004101c01842100324100c5244103c1c800504101d003500c0380c25041c1c200004504144000040400c10550240f00740c503440703000a6014000c1004c20b800103a030070040201020701410518280c040d005c0d12052909d40b00e2948185a4a0290380700d06000b4400c0303200c0c034100c8c00840d010420100345081c0000b0300701d40066100b1f0b03421716a60f0841c0e5500321700303070000c5505405002c07029403841c1999805001d60b000f5a041813004003060701c5006c03219425101d00c0850816100c1d131500c1c000780441e0012410a0668800305000b41e9030f510f0b00e180110252041788006040640b134035401298403845a04501011995039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107791312 1250 107790062 107790073
    0x40209040b090106030204182703020f010c050a03061e061101060503031803010c0503091c0c021c060506010f020c0402090d0803182b110c03010e060105040c0509101202070804090509 80
    0x1023840030120348401c01d00004214200d2094065510785454044000d4131030300c165a1140e402c0b032680e03404d441c0c03100340c02c402241c0c0100d14103184580c1071040c1d100410380082c0803c0b9001080035a04031b1100c403409000100b10440c10132104a8109402c00001400c01078112a9107100e07483c2641d8880c00e002c408503100b03508004150b0409031058045d240242060000f41c10300081c22402465110420000c03040ad1065803508640035070744068070780c8030030f4250300c10296040c5200d18000040703600045c03089060103500e81409510b1540059018501ca0084d107005a48100d400001800003448490040c4441000820041c2e05044005510510004a811581c203c3c5010440c418007001c4000d070b102d1140910302c2600f810314440c00c602c8a4000100c1e05448400c240e20740880c2c00e40d5a00800c00c1704691003200100f1450601d442020450381e1349140090503d1407900010320032b08060754155082101c2d0045201540792254100c3d030126501042640c2e03180d41e203060200241400b150030b05950f000e01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107792562 1250 107791312 107791349
    0x16200f160906150801090f0f05040b0f01080607020703020105071703071106090d1d0a0302030115060207050d08040e090f07120b100b0d020f0c010f1508030a020705040209040b090106030204 83
    0x2607580618a4076072586403600a40c3c06c10042d00000d140300c0e5420715209495040361010380c0c19500c1a540581c0c00b5503606110781c80c0c218a19000210f045c1d00210b280c1c0c3c00b0380100b0400716408981c580075a9424039219503a0003080c00c040e11200910310101210820000601001a13000281174400c01800400e880242d50750301907070303030310703411000f0360540892030303001050a184020f5090f003118020000c100041b115180e801007400c641d0710b05141403450342da0080500c0000d030100410b80003007108a4040340c0414041d580c544007800703203101d0103030810a0300700841c1c50100306006003900e20148000f1259241e550f07000c03003502130007034802c140c0e00c2030f09000c04103c46071500880801500c459034411460101d04110300b8000354441903c0c0c5804603030510039040800c0d001c1c02454000d0040550204200c440486180107205a075805038009502c00c20205400035008038510040b614129001030305c0c1c100321404103025155a0900380c0d44201900e00210729280c15a0103081510b0304081700c6012002d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107793812 1250 107792562 107792579
    0x607020d02030405030c0f0415090f060801050606090f03070b0705060a050c180108070512010e01061713170403020d0b0f010f0305070513020c0604080a0816200f160906 74
    0x2035000c2c560b015085968000c0c087c1c1000c03d10354130078020103040060480c101904809140c0030641080101c1511074681110140d050700900d00900b520000070001401c02c14005415841900c01c21402961a100680c178980d400f41320000043c20701504456a0b580ba618020f51107507401c80b40c1113101ca1400011480c1041c42000390380070044401c0c16000e442e03010900660752901e0040c020307410043c08200c181d04910307014410300c1c024032034000c8444136941040f03030140c07109080020120044040350100002c4800320324070b590300203800151b10740155024281044542c0304941001c0d420245800c0f140c000c0040c071441680c441c8800808183e503a0740c0b580b540361b410112034072001e0521390000409100310b2410181d5000200c0b00720900501d08460301c2d1240782014011982503441c1c400206aa09055800241c0d07164020190540703c032468081400240941821000480d00840c21400308410b1131010404941d07140880030072580e40d03c507410b8494005510740c0c016280481c0c04c0020003d0f9018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107795062 1250 107793812 107793817
    0x7082401030b1b0f0f071203020702131814030a081018051504090507080106050105030112080a0e12010b13020a0f05210109061403161203030f0c020607020d0203 71
    0x20b80c0181054503503210342e0301e9034000c0c0a12158001d9000703001c21510743d01c01c1e5064010420003940c2420b40d40c03945644d09080904168120071001810300402108005a072070301510041450000d40000305005040c21f6060203080340c003001403610101c01c00c2e41c070148000002402d210080399031100001e03600c4456208400e01548070300c10001c103010b07140c0e00100700031307400036580841102d4102c8040384991001030180c54481900f81c0d8a60807800c014043d400080c01010003400c030a0a1070fa213554500500c880008070070880c040c105031808202c0601c0644240703521107241d04028584640b030406000c02c18001c051402e05507100f460f51307108030110205a802a650300540d65240c50b01241c040c918240c0f40b0b640078031207082448200e003412400210034008014082d10134103a00143c01c6040c06092990041c0d1144214820351013003426050303040786c500600090714100800090350408601d002c0d405007100d41000e100c42070521080211440c5e000400743d1042c40c00d40d0132901c800220704001d0b6142e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107796312 1250 107795062 107795069
    0x30607020a021c020f1804050601061d0103020307030b0d050102030a0c0e030705010809100f020306090606161203060503010f020304110108010e0f04141b040e070608060906040e07082401 82
    0x444203030250414010800981d43d882c6001078404002c01c5d50305400103030851030a105d80b5001a202c00140401d02200b0003130b00f030244c00181002445401e05036500c44660341c01540c1c80d4101500000000c072500e109070070085034a500580100b11200b02840c20728003030342041b44c01120f03940c6401403441810b0710a401801c030710710028000d45002410b1000446445100922802444c89104e011132001d00c030903c107405c0700003d24039005859050030010059804e902802242c420a01803020b03d110803c00c80c1c2d01c050f126400128202ca4070b22198054002d01120f920080e410752030b010000003004500c0d0001d41c8100e11402580b050300c10403500541c0c20810a000f040301c8070b2900400903000e9044c5482071034025004580e029504140300822602e401c462004603e109458024801e841d82042d00900c80c4074007052015042540c201280144003010007800380e8407034410300b070100305551203507070140d001d5000c41c0c000c1d5400947c480b940c4540e982c10301c213640c8034150a1400b43d20740c9401000000da059 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107797562 1250 107796312 107796319
    0x1306151a13080d0206040c0608060918010f090f05010f150308030403020a061a030d030501140103051e0c040e0c09060304030521090c04060801021207051b010903050702030607020a02 80
    0x2464a41800c00399580c0050300d07290429540c611011030444000c002c00201042c01d40e0007405185000c0c030f49600300703403110b0380103c0902c0402d10030b1008a40c1c60380c1405038450001e40c1c911808110031003403039015240115001c25102e140c610030805200e01d038407019882d94011402842500042c225a10885804c40300144801151400c2480019580401150064042c0c4115290004280c4450088483ca840c864284403801b100c11440c48c00c0a20a03034007084ca1900701000a507242c40d8103c006010103c620604160b0b454002400381161160703140490084a42c820440e071400c0f06041071036501c18047c0c1514000340000041e00f000c0500c0840d031003284050041820f6441d687e41c103440c02e400004a5140280c000c16120000704c00b054511485050354000a001204804042c881160324903005501541d0041103010600310440501d03e4201000385080790b680c1d04400d10000e204a00d0086034102e82d400d045d001c109040d0310601503c0814004c50546210742c8400300c059031b8441d402c9000030340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107798812 1250 107797562 107797589
    0x2030d060807210c030b10030b06030606010e10140307020d1806091406090904050606040b06040f030206031f080c040b0405130320060405010c09060c0b010506030a02040509130615 79
    0x1200140700b0403268480313206000c1c2e960265203a50314500117070411100c40000200901042040c0541003c040360844000e8010344481d003000000200041e40a00c204c50080201e8100c441c2d0980c8200100301c020781c41140384a0704d90a2100000351105040159500003c104602030b02202c80c1000381035048500c00d0300c03a084450314042107120031610340d2444070741c0701c80705000c0c02400d81c448002040c441c03071081d00500f21504d4070b40c081104940700030240b180209800d0100344400c0b502d11712841c0c1a070b074044503002d4032030365180035411250601c80d00724010441c03009000182c0b048001140d801100e000c48003480508003c5d42400200c940480b0100b80400c0c1251490300840c0c082c1004042a031078030300541c1c40010107010120b00e4210f05072400c80d0269546e00c48401481d0b07108100304090504d03880d20307801028064452107005901805181d110713040001c007007551104140c0c110380091402801a0b10145403021a41e010319803030341e10076900c1608000101903811209200001500c0c2115414403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107800062 1250 107798812 107798849
    0x602060702120a0f1215030203070603060b09060309010e1504020307051e0111070b040f2c0c180907020d0f02010501080703200303041206060803070206030c070611040602030d060807 80
    0xa40c21210b80c28100f0a0011300c40d8030074100005030140f003621b528101c0d000c00000b0700e10300c1498949030447c0e00c80ca003050310701a0244240702072582140d040c444111130f0b40b5141d4844080f0507005090f1503083e0489031248200e4442484a042001c0340304034021030607115440d64400a1026103000d182ca079006101d484204104250302455408100c003600c074003100c41d100d0302c408442a10354400c0d003040d5601050643e01b0003217840c1d00c0d0004c80001c00d091540305491403040301150040d4001030070904000802040288e0445960103d420810380010070705042400c000c036000e50bd90a804002c00b0000f46880e00300144d041c014000d41c0d040f10007810007006020310715242c07800c03c0c1000403c00c004003002c0804034100c69400b0000f401c050103282c3c0c14485642c41900e00001241c4075035015000540092000c140581d075140166503014400d0603029554400a1820030001d040c0d103c43c5a42d400804200480c45507070000140809281180c01080300d143c83e011250b555181611981d040d900035046200f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107801312 1250 107800062 107800067
    0x1051e0409051002030c180406080307120e10080105100f0f0c14010501090c2a03050c0c1005091306083a020a020f0402091e0f040f02040602060702120a 67
    0x1a51010b0107241078030004054110140182d0380165452103882c50301041104080300007021010311900101c0e010050240340c1a039054070785c0268440585540c1600000c2056503008041c4108464401070205040c1090f040014014010a002e5140280c80300000c20b040c207805100c2c103030070300201c030f4403480307090414401c007183d41482000d011180c1c841c3c04040300351218024054140070304082140402e030320120580c000c02500451440c0c401c54102103000c2400481002c42556030540c0610784141c5c5d40b403142540f5494808891145030300000000d1070b2141080c4d0060181500348003c82d0505955420100024251402070150309081c0d0012030fa40003680300a102c0300300c60031404d442840264410009030690080050f0183c501580110241c4001c40c03404600700350008904550442c2000201c0300400d0004111414422114510040990b41c40c0c2e280c17400ea4007030910007041406410500c0b04140065002442b80c04058450a0042031784140040307000ba107000e40818034181010b0b4006400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107802562 1250 107801312 107801321
    0x60411011706060f0906030412140304120818030706060512030403031d0301140f011d070f0e04020d230105060705030304030c0c051201020711090c0d0213120c080601051e04 76
    0x40e80540010445ca003055181c900255119501910300c800c007c000c01d860252100100181c84c3c41000d40800c01c00000500b42500701200156510b40402141d84075001190111140c50004880b07200202e4020100302140d00b00c4025100292801104591410220307507807801036010080106a400c6c81008442c119503440c2104400b004002213006000c1a1020030341640075688000b0000010006018038600e28120300018189130300450001d01c1e01000c01800c3c1c0d0504c4483c20b0401030b507103003403816654990301903c55006641c42c04021800300304003400b50300d400904007141d004c034003680000fa07685004003e586032540c1000141d4915503039a50b084a0b100340e1160100c98440700b000c400b2805407503c107107078001c5040600005030703114042e042200002d8032500c1903a208507001020442844607c4007076030307101100044090b071198615442d50030000c4098000c012841000f0315500140b1028801c1c403411500390350140c80303e69883c1c0051007803885981d4400b8401032030804c030401042c10507500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107803812 1250 107802562 107802577
    0xc030c020d0e0f0a080a03020607020c01080c03060a08030406020f07150207030201050f040315020c100c09090c050c0d0207050a0e011a0304140a031206050a0e040b0601050c01020a0206041101170606 87
    0x2000c180d003c21100007440355443d40c11070030b0150b001401202c101a01000201c0e08070341d650004140d003a203070500080075944014007070038250300003101090f05921400341000250003c0810760351030700d480740350095466014125848091090007000103594800d25904a14104c003070f4040d180c52802c6400560b2241c0c411030b00074038100801c12001010030100e520030040e07448040009030340c0d000c0c80c4040c54500302c00c030300c180e41d18146001d441c44405038000844100f02c4081000203c0c81c119054815101402a400000c40743d01400350b11014559011441805442e0100c0c0c10742442501e980e0340740c60b80d0409005802c4c0340c500c80345019014500c00c0c005180d1103440b84221484000d20b141486051120181b801c40c04a6440b900600d9000070900415010742010b690601100303141822040800710003074809808004040b002c204240d108074212601e120b03514009556420000342c0007503071120100c40a84d4200b5480c000300030998030958a40200c02d01e15581da481c030351281d00402405501481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107805062 1250 107803812 107803819
    0x21c1e2c06130303080f0105041404030305060a09091407170a0807021c0606080633040b031203040312090201051206010509040908120f040507031712040b0601030c030c020d0e 77
    0x440c0071050000040e000340a9407199517031004905010b60078008041068008620441c20240d4141c148401d50121700e40c06a05458045000d446010101e060744449400540d009410641081c0900c00141c0314461810881001c4540c2c159031420004041103003400bc40d0081c1d0001c03401d03140442e680b00b000d8200e440c002009251880700041d00d1488400b9204000c49500c0e450758020445550280403456026072000043e00141440c18085038400000c248000f03200e54102003040350549903036219020b041406000c96461500860361061245c20880d4110f00080c0710a4420811090034012050300d1541070310b4550800c94201030f202c1d00c00000914040c10000d040c4200d80030380c0d0360740c0a1103150078003c88611b0b55a0349103180d10384400200410b020b91809013142440005140000c5031400c40744c0042c40c02013101802036414240384030705c0d001d589201890005000a0006030f101e120f00070882602c0401a01440e12815420389800c60601c0c0d000d80c00c1504121003007801400b03400350340d19008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107806312 1250 107805062 107805067
    0x30803061305090c03010c020303010b040b0d0b0d0506091006030210050d14130c0e010b041206110d0219110304090c020a060f0203060123070f03021c1e2c06 69
    0x1004030b8508441c1800315521800b0740a5141c2401c2c40b0340c0c0d01414951014514660400300e0540c2c641c416845804c00030200003601300218034055000013026040103013030141c13849660400c0341e41c98901390b803c1340c0740d400b40e150f840c074035000c181c8203a03401c40e40c0c05400310046140c0c124065506402040309041015122106001070200c0c2008030780c492021501495500d5069040034282e00341300d0340040d075460882900510403400d8040540c2c088810007107845402c100030340b80c000058010290800d42050b00442c00e061004107580240c035104400039801402c0e44a001d00c100c50050780702444821076081080203018100598001c4904084d8600455026030740c00e40d030f800202e4100102109500c0e502100340100c0d03690001c6d4003000d114541044079152400c03034802c0400c52046d08402403448820741c0c0d00c3e1040600a105008603c4440d901401c0d07020006c03540a006000039116a680340c0c0b0710f0002c0f4040c81e6001d0544821380c0860306030100c0101da460101d07003100e0040d910070f00390b20070400d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107807562 1250 107806312 107806339
    0x60e01020f060c1902060c0702040b0303070f08070b07021b010e01020109080409021b0d090902070303090f0c080d03020c07121109070302090102100e060403182114010903080103080306 81
    0x4000c1c0781d003d0320768000e0055883e1904070500c010482003e154404540101041c00303e00d13200f0390300383c40c0e0301901160700103480c610400000c0d1841c03080c140000c10040d500b02010050001100140682c540070b4038080c00e5035030720040200d0310303400409000c00307054444da0507800423544100190058000107000004010341c890b12400030580082d40a00f100c40e400040349016a0700500000e81c1d410500300c018019480c034001c1c00341c414009409681412035010555000341446a004041301c10b401c01c0000804000c2401e110744004c0c0f580c060480301d0302c108002190510300c20300c200c0b900398032a0800b406000b424100002d6845400441c1503500740d01d03400d800d070000c1c1c0d609000035005d03000c16140182da035034102001a091601c051440070007a4030b05851a0a1841c001c00c0c269806903041ca032000882c20710368820908100c0da1f4018142c01c051454543c806004c0344020565410700403401a80b107405501149401d0b99407e4038020002858803004100003100b40001d160081030050582c1c000b81d91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107808812 1250 107807562 107807593
    0x9060a0b030f25060e0d0f050712061406030c010c020d052103070801050306070c0303020a090801021801021203091905011103100e09070b031303020a020a030f0201120c09060e0102 79
    0x54103100788000c4146403c1c1c141e4204925402c3c100521103402e119116160010024030a580c180748003811040b05420604100303c07080c00104003910450000b003054120908044000340f0381d071030400040da41c401c0e002c50582d00c0c0002d007490103480141c0d590344090503603a003400904105100d00b15001e1040007902c500f40341d03140040440042500100984a2070301c07440042c138010060b0700c20750094000701d041c030102542c817403070705801c5c07617014100540d683c5d40c9500d00b140d81c01c5079544029140c4d480030a05840d80e4241c8101550008026400c03101222200b07d903803142e40c070040c1c40c119a141e101e0003001440b2030181840e000781070f02a50000885d01d000a0031244150f1084172013240c16114003070180001403d05071101d1300189203900601c985410622010050311010b80403018810669200c0310805100704030004010703601820b041441640c81c905955110b42c0b5500880c04075416461000e4031440c1882103001034815540c0783c1812524080007039803110401e1412504500526818002514 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107810062 1250 107808812 107808823
    0x207030b0114090a0603020d06021b0604080c01151503050405030708040b041505090306040303150911040e0606160611070503131802040e0f0601020a050f06070f0809060a0b030f 78
    0x4481103100e454882c2200801c4004080103160302411442d010b018009078072102d6001200c1680028016540d89401000f60081c3d07203034082c005003e01c1490204802c0140c1680589802280740d0300030701903a41d212460511310b9105000b10b55510b803c9050542031548241c002d50341003030168054a1418507203880c5c0ea8469405900144505800081c0420040c045486003c80c410088c0c42c00604141000000035250100500040c0c10152600c9005200b09112b8007440001d201524040258024069a0000540142c40342840140c03200c00058124100481295049100751942280300c1c011603442400400480c0203a0716140310900c180d100080041006020400c2401d40410a140c42c040b0301501d0b60707200041060b0401d00500c000c001c2030116200281e08134000c0c451720b074110740c2e0301c000403072808000c07600c0a0300038428400344041d403401c04280f19000e06501e503913446100c40403c00030f8034544025140018030368400c030002005144c10f070b48200c80b0404003c084d2621601d81c00c09007407901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107811312 1250 107810062 107810069
    0x1806090c0c0a03020a020306010906123e040b03030309060406020f13090f1104080c120a050d09060e030d0503060105070c0b030709090f0603080f07050f150a0510150f0207030b01 78
    0x6921001d41d50b000c0d1f18040100318010207124600307108003800c003045043d00824000c00280310302c2c40e0700c000250710350724051401001d40100d14107101035680900e6402036081410701d2140190b19010701e0700230604011003240d10a4107071000400403510399558201c000c0d404100d503001c88a03c240510010764409904010051641030404030f25011782210b1041107516042d11100351203010801000310744c0c00492803c2c2a840c0884030310101ca844082c0c90340c20302c48001e800400a0198490442d80c240d003001140382990000e55407100c0485400040c0741c1e070340040102c0a00840c4050002507080e611030002441034a204100100d20140d480280a48a40054940c100807564210342406202c1452041c05040490901d003402b4107440e42d1a5410944644080010802c100080080500c0320410402c002d000002e4102e43884042502060b03141030b002625100c001c5424040400c080381a021100c0007680c0c2c5080441c0c00000c9005000d942d8500c1500c00c1c4025801070102c000040380cac582402c24000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107812562 1250 107811312 107811317
    0x60304060e0606041b12020405040516080901020c0303041205160c06030c032f0705030d05010e060105071703190509010209040b010c12080c07050a0f020f1806090c0c0a03 75
    0x115401c0891803401d0074001808203000d80c2c034144014540301100e50900815010600307041d5442c3c0c0c0700ca82c000000e40328039001543c00034200000e1007042c581101460003044840c2d61a003036141c5940c1e202600341d00ca400c58900e540d80c82840400c010540d041d00e0006240c000d400c24524101d941030003d0014604010160b420aa80d02e038100b1110b500f5000ba06103121142c6420070141940380c1c1d420300403030a1003292040e80d0000700780c150802d20030803003102c0c0301e5504003044130f0b15126007101c404003509090103403110740741c44100441e10b41d5001700142e461159010007500440d41c900701c0b905030311340c0004100c0d507044160103400c451000c0c003600c030f502e0090201000240e1349051200610094a01c000340050400c040c40340c11364049250299114800c0c605440c148100d0f460b243c1e2550050700440030054014010490400108007000e042c9003c028403d4487c1100b1500d6603081103210803001e8101d079660408000000d84600d0407010480e400001d1070030f054102000d02c000d891034080000012400f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107813812 1250 107812562 107812571
    0x302040e0d0305070f02030f0306040b37081b042301051c031704030c0c0602060609090304080316050a1b0e010e010f090c0207051504030b0a02161b030206030406 71
    0x14610307418020540d2144031420301001d1030409a000a550f03108810f23848007290000300101e17401e41e449410001e80701200034155500c1c5402c011241780140e1010980c0707400440d119407844018084c848244e401c882a0313401510007041818200e0914040d182012a801681ca100340c0700d4031529020b0309104103061400e4501d440d8142414441c59804612002050640c00c02c04400000c1d40082400c460342c140ca034440c0c0c60b80e00c861600751400c100d468401070141302400c0001c1380c0141e00007029489004203c41d04e58454a40075030294681c8100d029200c0319400030010744030410081200f0590243c4560111043c404580c0c0707035005445c00e080075901c50303121821020080d05030745130142805099020740c100202e500d404454044d201d10752160f40724090f11405503900c000d009004002c02807101a1100400c5c6240781d110001a61140c00115000920603001c1045140c4c0c501c00e4a00406904200d001c0301c900d03c0d01c400d2441807041400900d05104803002000503110384029602446c401d900c00704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107815062 1250 107813812 107813833
    0x90106120b1828050c09120309030a120e0a0b18010504030218010612050105010c300f1101021303170705070806061c020a030b07050405041a030c011407110103060302040e 75
    0x503844010031a00700711281484103200e4003542c5c01e41140d0708030000f2102a40d00d07429150b4100d066000b40011190b05005508000080c00610808142d8248569584640505c51101044100c01a81c068149a02400d10595926480301e180c1012504014103041d4101640d0740c0c00100150f03011810080a0f1508000401110b900110000300c04110040280419810040020000404110080c094049148040300c1c038112074514421206490031056903601c2c0d00c00406002017131500903140001d0b0700c13030381c0008c50440184269100d50500c624100340261031500d80303a9070003450518040c04600e04200d01800100100500b000810300c0b40d020300701c0343c23900000f0004007002d6803c0950204110400d04001070f510b042105040d294851f0810010fa00c81020440341c034041d941041c0c0e0064034143c110300c001d2030f91a5205840860032422901440b03031100044070011000030340400300350028004407001030f216090840c0c143e9010302d00000c202d40e0301d40004045d150803c4c40f504894125102c2d20 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107816312 1250 107815062 107815111
    0xc0a091502070915090621150e0a0b0106090b071104020702030c0a0f050103060b0a05030a050c09030a0b040b010b090a090e030904050711060703061a09120a081305090106120b18 78
    0x98010404506100034446403d200d030302074135800100c001e09403031238041441c5907440c85a00490030321441904447c0320301c5041c9407040c4210000e008960100e01310940c0091220007100c100da450a501150301b020f00180001403002940090710101c0e0b16000e01003007803d26450b87c15034100182180ca00341800d40f40340c035001404513041608100a94081080580c40302c80d000707011a5008042c0980000f910380e10990514010b0003032101143d8940580e00824043c0960b0035a0240603d000f503074071508590740c85d1134444144c8103e107069500802445007c22036811198800001c02007a01d040c0d03450400b0381000034081b1101281e50750007068200850b01101c3c20b04000c5e481d40201d050604100c49404d0100944d50502c10900305102aa0006001c2c081c0b915501104505480c3c894100e80c000c4149207440302150308110046130401c104404002450b2a207810994121041d544420108055601242c40648000c1c030049400408204100c0c2018540d0b02c85035118001ca60055822003a0b066100b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107817562 1250 107816312 107816321
    0xc0e030619180827010f051c06090c0509090c090f1012060b071103070506030a0917070b3705040501022208010b030105010b0d0903020a0b09060604050c0a09150207091509 75
    0x245d0401900c0b80c0d81c00d0103550050111b0b01c9a069100b1030076240070100130060080d003581e40040d503e0509004000d0b1400390800041d0180c242e084a4080003070743e4003582c41031107008801c0b0300c0341e04c00c0b40c2d07404818040c00d1a4045030369214007031800250440c00c0c0004401a03803d9a0321008202c4030000c0d5840c181310b41c6040911480074114041d28146140c03c0020300c0d54040948032010080d51840440c081010520001703041c1c00d00c1303250f0345440c6c8002c2c1c140a1041c00d41101d40b96410f1140010070302c400c0e844800720a0300300004c03a415214031a000d0040c10002c02c03005208450966081004100c06075084c02c050100c80758581228401c81d060140440c02d4583c50360700280240c0c100742c01480400b512405035260b61000600001380c180ea80d05040f842d0201040014084e08414010b2111820700401c01521034001910207009940b2110125102c502c1000c600b60002680301c0f2060004800304a0500c0d82c217582c6104880b01c1c20703100c0ea000c0080703071072020404071b240c08008000c110968041c0207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107818812 1250 107817562 107817637
    0x2092508060108131203020901030e0f010c030b0d08181c230d02070b09010207030f0308040611040b0901121d0a050c0103020c03040608070507060504060c0e0306191808 74
    0x11070f01c20300c29190740e030180f540307060b0305001046c587c01044e050340d940d11942c05480d600c44101d0440c0c15004159282500808140980100090071710310410454141041c1e42809039a0004d00140707400d020446090008a1140e85154000d8000b06040340c01c51311303816110480342c003c9544410191001e13040e0341446480c020404010780108002a560b56000308020044400000220740d485c001e2400403800c02030280c0008203080c0750310486105240e4000803152040784503c0c000c01140035503850700f141602491007085004102004810002cad403207010f011088414142c030100d410010302400701148240240c40070480e230f00c080380c01c90030303c0000c02a80305191001c0c07c04501d08404481c645890b8031030b600802091101c4c0708085902503100d00101c0b41080c0d0020310400650500d4503140000c2c00152407080c0c00034069052115031468040740e61405604441c2c03e94040d0785184da00da10161510313440b194100c95183d2505d0340030030411802816031840300c010703800781c10b240091030004086442c00e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107820062 1250 107818812 107818831
    0x3080307031b0c02060708040b04080307030f0207030b07120b0913031d0603041412030705040e0609071d040b030d030e0706020307120305060d05010c0509130905070302092508060108 80
    0x80c5080501d8101c01c41c02e04040c4c0540b011030b5114a2410008801c0c03055a1100d40340b01c10010f400290241c000c406805c901d8429507030030304001d010003401c07170703980240f400060541c0c0e90074008103b92078040c0706440c1e9080202c0f02e0218850b00e4071000507800c094222001c000c1c0c00c2c0781386842c074101075100d98400d9a441c58035010032071407016080452494003005100904003020700d5a102800b80c3e0811072149403440c00808583d903407810000040050700305101e10602c810b60f40c004582d19161030300c7d046104400907030310075032045103101380a03201240d11200d003604076030350703c1000e2100c4d10144403843d0041115100402d60314070f140d80d50b529180007641318008640061201c400021400070f40c4070070800f424507003c178480d10391200041e03145a400200078055860152294011904600903151b5480e0031626170416030040c440c40c00c25145954001080c07600301c803c2c01c0c401458110f00b15a000380d95076640c1d003003803059005021040003c3d010100f011800c00410050f40d5a400301c1c58aa2064182c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 107821312 1250 107820062 107820101
    0xc020c19080703020103150806010b0d0c081b0a030905160e07020d140a0905030d180807030305070f0f0b0c040807120b0601030915231b031317040308030703 69
    0x1e00c0180e00d415150100904040d219179240d0b520368070032014100a0302084080e60a60350751180d41c920701ea480101f5110b410350030070a101d95810b0080501c144245d041c1034200060805410010000d070744601a88000e25a6621070440840d408102212100041031102400741c0e00741208900c002c4402410681198080396084420f15445514200180070b03d42c9011340f9061100e6054800c44410b410070741e0548905150b03050742c140d01440d0960005c00404000d42e02a03242c1e604a80c07074120f2404046e020034000c025107000907603038034030320030315140290340100a00340c42e0354640c3c0410f007054846074091440132405016030501440800000c000400202804400d944c2e90390700078141c000d11060504d643e54400d00103101c0c07403201c09049440c40d18010401d945c005144450080040304c0074a0f0306286d80030001e034003107a807600d01e009002e0724070406034119500c44001075412460844202e030001146012036402400860151014501c100425a180c0c03401070002400c0b00c0d81c2d9141c10040c400c01c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 107822562 1250 107821312 107821319
    0xe0405100902010f0315050907050307090f0807060809010e1f050105030109020a051917010c020f060405070e10050a0303090821030a0b04140411011214010501030b010c060c020c19 79
    0x41a001303446000fa0402140001c00c48040c3d90710b540c0603034041d80d00902480c0070003124030346c4100154030905d9035896810000c0c0d00e07480950744d400040d00a01c50b00b90b11051042c0302840c000c1c035000d03074400d86403800401e44050000c0c200d0704000210140b03c00c0c1100760b6a80003100f001034050303e40505002d50081100516540000360719104d13a104950082d86c01e02e40501e15203000e0031071200604003a038824590158241d41c00c0c0c0c000e00c0c0d5121180d0042c0903165550312200d0340441c081c1c0c0038a070010000c0c6440e0741070900144141c1c01c090042c0b940c0300640ba4001030551a80480c10700114003a84401030158584460141800b9800900780e0b10b07006488000510703d0700000c00d07030703800c41c0308140c000900f40c10545c042801044442580d030300f44041c9900300810081403101c200300c3c29400b81d0741d078018040346412010a44440001142c101c400010040c0000e520070391008981420500d001c900c4105c458075910102e4500c82c940c02e0040e0402e003140c038100c0c10040e03e110508a407282d603d003406c131329 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 107823812 1250 107822562 107822567
    0x1209010e0618010e0105011404060501080103170c0a0c0909030f050a0f030e030f0d020421051b0d060504031d060a02100504030c0b09060103030815091512070e040510090201 76
    0x4014510344010802d0b1900c0b50711864250310032400c1c80d41660080042e0b50b150140328000c0c51820150f07a2189041030380101d22548503000309412a94802004044616103040031082900881040d12141c07080c021101e02103000900e04a00a2410000020301b510250034014406d008a1400a0902104112a80c03410380e12010703c0f0049050307840c0c0080c541403ea66001e086201e41100e8035907114000c1004070400980303134001c1c01221807c98107000d0448502202c81c80740303610f01401a090360000d03240407206440352182811b00200003029105001b2003561054101ca100b82c038140c2c005641c00360240c07c0c1c1c490802e0100b103810812600340d410141d010000030344d0340901d14048241c60f07840300c021900300342c042c0f0702889050384d00c5103a41503e8035000c1d1465613034810900c015000511014082010080d001e642201800f4001c0e005081540e500301030b026003905da450b4403035007140c10b2481000c40d04105200d804050000124201e01c4e50805044c224580310560900460081c68540701c0e00c0103030b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 107825062 1250 107823812 107823823
    0x90506040213020d0905010e0d0306060c080706020d090605060f0604050d110d060608060703051302090402010c02150c0c010915210906020307030506011803020102120f040302040603081209010e 85
    0x35411289038041d440e038031045001030b0013120294143c0604009180e020400190840344055424000321803802d45a030800302d05840b21031290a0200b1442001c11010841d1700d00100000c60058002618003071000e0030071403c48500c00000c1c0c5030a44d50f0010700c03280703141c10a40c000d50b010040b1030050406040c03400048081e51161002081d02c2c50040c1030008503210707034402510060b000102002000d0b070314801c06d920f4580c1119002c000925140c00240e5181002070074003189030b006025140556940e0340155071012000ca030a036408284450451101c80030100100f60568034000504900b11018001504040040e0050306d940001024040c500950244200c80e4282c814005844902e110525000082c111000080c01807800041040b403100d8050308010301a80d000c1c5d803100641c2601c5403400100c052079010007170058109031511001680c58070702070a000d60000c00c000b0710b00741c0c4d254001011100280d00403644900003040e03403400750074003420f2a80d1082d9107000038000c0f41c10b010b0700280c07240c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 107826312 1250 107825062 107825071
    0xd0309030f0509031c0c0b070302030403050a0e010324050f012c01110102030a060e220201080a020c0109060515090702280b0f0610050403020303030609060301092102060604090506 79
    0x20201080e0020b00fa84d0420161240c3c080b0040c500c162041c0c2040e005111003211001910700310203031030200d05998072a10850b0311541c3c0540e00c141c181034841500b2280c0c112882d0040d810951240714007424042d61050341ca004982225480e41d515290030144400c0c41821041c8605000654500c0520403240b0440e44e41648520440540036101c440c0041e181001c825481400c0c56101104001c0440da599000105442081c641c41c40607541303420030b24081805128800a000e007041e84920019402580c410790041080ea10160901001910181c02c40f09032100c01c0d501e090b229001d2003851031603000c0f5903007840001d5500d021030b40342c010320281d6035132090040804400c11603040505292041d0240345800e581c0308541c0880c90a000d41c0c214107046090303401c1742c4500304504e120000c00d40101d048078100c0b94090059400d46d51428108550342e00000c2089070555240d103200c100040c14412541041207003071640040c07003001558000c2c03404000401003809185410060000b140c0c2c0050440c1d4007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 107827562 1250 107826312 107826317
    0x30614090a0c021e030301050102150112030e0307050d1506050d0f1403072f060421060204170607080a020301120b040201020f060709081605100f03060b0301030606080d0309030f 78
    0x502c030b514104070318100260b0030b14505992041d03e802d14544003c402076048600076801c440315003c40c50300d56a1495002c0c0b068191501e07129900500190282c954050a0b034001030940d07444540d0394012811017251846c2c111448005481c404442200d131348500405090b041d24040c9912060b9580d100100000d60005007205078401c0700c40d0844002002201c0102c0c1c0c0c805840e400310454404c48082c0c0032440c468403501c1c80e0003142d032001e46003001001c1d182200e00000b070500d10180e402c802e41c1c6400b605024259a015004c00c00462001c808890403180c45d0444402000c40e03142621005064070400751040b110580108010010300c0142000c10400c19001155030100351a11701c0141e207045100c2c0b84040a03401480d080105140d0810309030070403240300340b00b0f6402c0b101741006580d42c2c585949c06403070381c42000580800804d5100f6502c11415100d54100007424540b108038101031178109030300444210f61a248244a0f20005100d42c8407070000038102804415a2035402030301c8203101c001d17048c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 107828812 1250 107827562 107827571
    0x150f020412060b0a17030c120a090501050f090d08070b07030c0914130203011508090c09010605091210050105041107020d0b04081c02040f0905040c0608100e0a02030a0c0f050d020f2701030614090a 86
    0x3517403408ec000311601250024202c20041d40c8134074000116800c00c3c10260348540901c0e000400c0759010340107a210320350031941c1743c01c00d03513042660403884a200c1c6665190044072501e0340040c40318407840113501802107503c038810000c0440704000c014140040548603640c221415041441d21400000e43c15103446e400c2c02d07919075907a10301203100e5845803100503e05206035040c00300e80c005650720460589405031000d00480f0510300c44041184214003009410448501d44a404a46046055074000d440781c1c031407518003c88000295410f413401110000b01c1c56000508118210410b80c50100407d41d0f0807040c070003850030303840d004414510352242e0703c1442401000600c0e01c44030118000c3c040c019046020005092a0b04402d009400848040740c10528000d02c9218642c010351481d815403032035664486c035242c040f4101d8000782d04554544c00400509100c180d07510f80c0f081000300c03940d040d802712810030190400c000600391001a40040042100404200041c0c6c98070240d0643c880102c02e000325 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 107830062 1250 107828812 107828827
    0x5090105191503180309060206070e0d0204091106041d06220b0a090c02030d23010306090f140d1404050109030201050f16150f020412060b0a17030c120a09050105 71
    0x4001c0c01c4d80818464012440a00142c1010b03001b402c0e580659030307903078200c030600e03075400c80300b503c1941c84402501d5201e082042c10800504c1d064101269072407040035a010584907507004100280c0150300050102014541640c0700e18400d60100ca6220710f040b00d140885041292111604001d10a105c40c02c45071164058038040d1951a142e6000b4000f08804100340342c00075800175160b800400020329242c0c1807014211601e05100d095040c0002000940f1175186d00c3e5544440007888079410440d9841440c000100118140005203a64a42000050004404a07030703002045908150184602280c003800103020070390717014652500744d035420708119541d00001356148001e805001489035040c1e0715007490307108001103007081d0041800031000034820030b10b903460035030300f40d01517030094a00070320301070f03260f4008680c06401039800e0000190807981b46030780b50480051494643c2d000243ea65100241c80380917a0f40400039500e841043c1da04030f40c00c0c80b501c40c8005048090074403c1904208011801d034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 107831312 1250 107830062 107830067
    0x90105040306091a010b040807091a0d1103011107060506030d270b0c010903120203040213020702190602010c020c0307030f0210051c1506050717030702070b0d06050901051915 77
    0x9a144101a11504d1465a591070070603c42d58858003507140b19004240d000507024405d402600c3c3c10a0000844000c60b510041c10312076425000715064508a80580b4800200d4400b881503c0d41916040004c0f585c5420701d040c85000d075000a84990700a5000700c2201691950041c02c405000740c551100a0040010409802172412150849541003a00148058040d081507006074030f1180729454440014886400410490100f20b070043d4100d901c0e4107079015040c00650040400e188004c1038134a00c1d04050881e01c400003455003151025039980c0140b140f09540401c410070b10a28201d0007810303140d040d43d80300501c0840d800b6009000741e0800060001080c0110103403041904000c1a000c0c1407007044003c0005003440801d84c0c0e001c15a000c1021400380d1150302200c41071500030081e40441680f01041e1101a1b1000b840c181c110700a17004082031320714005000b40b2000480038008101d180c20001003040c1c04e00c040c4e000030b01c64074040003200404011703a1001011a0600e1103564030f60b000101e0107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 107832562 1250 107831312 107831333
    0x16170115050918091603030509010c0c09050907061101020703020703060510030f03020a0c06030614010c06180c08010c050a141612021005010905071b06060314060403020f0309010504030609 83
    0x8290f44286810003128041d044090003903c14604a01111200c202d0165050850b0f01640009800100f08000c10072681d4064401120198400c0c1c145003c016500d1000e8003c44206030354840031600500410001c035603001803039800780440d5000071498107203182d4002e5a00c400c070b84001000661200c0001e00c0544442100c07200a58111501000e82c0c0860310740251a00d810714403c0760005840030000c503410b40301303100c1d00e03069815070f1101e045200030400c0150b4040d021040111036841d180c1a8440f44039441f20400402c10388242200640f036410215000d003560010f00f0050200034003072040c03030041a8480c28480c1c00b0540e501c9030665450114141110b83c038004000034140c0342402d03042c11103042d030000d5065a0540307059010071440e44c80380c01400540d502a184200041c0c00d21021096903480a80f15000c501c1c400c0e0701c00180280da80d60750816007614200f03a05415005201007000b810340501c9907008031007620014502d01b0480400290643c040c80c080600840d60b00d0300c145040000003402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 107833812 1250 107832562 107832577
    0x271e0605041505070e0a0303110109050715170610081b1b0d0e01020c0111070e011412060403080a0b010507021807020c0603010e07210609051617011505 67
    0x5010303915140c103022240450102085400900c1c1800080025205041e0340700c05c3c0000800c80342a60345151011107201c0317103081400c00503542e140841400100108280350051081c800381407040c07101102c0240c50101030003c4030607401980000c020190f0307540c0700da446103542503084c020519150070b4040b00c0c074280c0c0c000f0040c19250f40003a000d11000000c1e07952038170100441c4100d86140c03007054800c81b60140e800000d14050781c0100d00c102a11f40c000d44449003e109040c0842c0d2485548216406d00110280d0007094260310042c2c0c24661410422800c0e844001540000d00079410690303030081c1002c00c004c0c50006000d45c0d855540c7c016a1107074007218001c0303400501880e411000c032981407024590648805002d803084403070702c044505204040e83e0482e001d240c509082647c888109580b035400103c008807000c00c0740b50b403003c840c0e0710300d00c1464080d2a04402c005424681640d0100c140c040c003407851020300520ba411160611030442800341982e0b88889029041d080c00801607605010300d90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 107835062 1250 107833812 107833823
    0x51006060314011e18140f01090c02030c1011070210080609010603090312050402030a0206120a051003051e0102040f08030304110f060d1a060d0b04271e 67
    0xa800160840e4140c101e9070382c50681412910712640c0c0c44c08500e05080d22510b1a1484491550082201c1c2140f18001c0c010f4a00c041710110b0091104107100d6044001191140b5400800b42d0050095064902c240c0000f8072550001354030b8890603503141d03a41d0b41114010300620f01d03216000e08003140b25403c195546103902034070603d250440000c02405441c4101c2d0441d000d0b121000000814500c240a41000c2c0b0350551501030384124200500805080300801c10398161140d280c1c3c03140180c07242d40042ca650403521207851624104681d0301400c1c0c039005024600040004142480420b10200342c1004a5040e1091014050540201d1b980a40110342c02062032a00340e1800040c841000300c001c6108900c99010008030b25855410483c2c010f20b104415604a5401c0c06562890000d90b80f00606030001211803107160115103001500c140e0003801452031543c0c64166510301c50a1034041e00e28041304207070034215410740c06000c1e00002402c003d00942055820a52180c1445013440d03c0028a900314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 107836312 1250 107835062 107835071
    0x1060813020105190f11160308030421050a020609060c0d0e1509031309060f0e0a0e0a06020a0206090705010f03020f0c0304030303020408210417030c1e0d0203030915040510 76
    0x314014000408011605011601c11506e02e01141d03c00b0601800c03e6004441403440035003503445406682d04001d0040366070020200400004080c043c80905880d452540e0381175480706117101c020700b442c001501c0d0728180e5000c07100340b140030140081500d106007400b0100040010100c5189480e01400740340403040005c00740144242c2c03210110041800141120110044959609445048860911511401c2e241ca004d041c0308041210041c10303003000032088041030b201c1200d0000c6091001c141000c40e4882d500050700d210301078050140d0b540c85452440540015071502001a1604441c0084201050303400503e0404860700d0400b5a04985c080104884d1500e440307190203802984240940c0b4218452508100308048100c05101d06002c00c5840079802c0929040c1841454002460f80348150700051111000e0210200305142800404045036085103280760300b481c2c1080d003d422298115041001041504d00e4001000301d07004c1241c00140c655903480f400d180e8100406610208203440c1070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 107837562 1250 107836312 107836357
    0x219061b050d20040306090201110d0c021503070c060f15120c05030a050309040c09091a090919260307030b010905060909070e12010f1a03030301060813020105 70
    0x20090040040e41e04020040e012590b400d4200c0024110f407854681c5608000500000c0ca0381d4008039101c500c18146440004405d240342da0502c1ca500c1038000000e03100c0000c20096280013403011b06401181a0110300d18101010000d0503034141c03402c05032040341c58100b070071640c0e003842d0300130040314001c8a20400203070b440d4240494000086c90b0b081d0b51404800b00c008c81c1515011443c5040c1036031000c01540340c03e124000380006001d00b60508800d00c4441f0000041d1356039140540406002c0000c0030441850350301c010042440400751145000d5840207000d003a00803542c50000003441d82240d061030140302140f20078201c14100702d0f00d1055541010003800f00c0b00382c0503040a05101426250340700c0d8143c83e9400e01520780500550f103035010046801040c00f0074020300f4416050b04010309454608544034444600f510500301c0785410b02c0d560740e1544240c1690505a407009460103c0182d03103554501075001f001c00c5005005116107a1101400380b046a010b40e088580c030318070300c05503c0000101c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 107838812 1250 107837562 107837567
    0x1d03070b0c06010f0e190b040f0f052d0c0d180302070b1912090203010606180506030903070803280b0108060121020a0512010b03041b060219061b 64
    0x18205a0300d403440b0302c00c0042800d443c1c40324004141c2e5800710078045e20341e035091019012800040c0285000540c0c95601d822980c855000c1c0f0807a41489800115800300c0a405243c111000108040b0780d220204104030400c140492005a040410b1605003903982c850303840c0d1260314072078103054400083c41e03c20040040c010b807020704030009009409840c096075503010000c491744100c0c0c940f01c061101c40c0c05500d90807401240304800c10520f02d07200150540d03095000c41d0071034100e60405000300340d8142d61000d07548961a00c00c4040c2c0b4041d00e00f00d00b5400c15008081e03590085038801016180044002049681c140360304488511185001da440c20300040e078442c00030a290145d080c0000c030000b00085d86540540c1e08100c4164104400c1c420f0323452403d56807802900980c05c03000030000c1c10441d1040001e102e041e013601a0003c1a02c1e04da0324109031500f40180c0c2554114030340080c20540e400c1014580111703041d90310801c654440c02c0c00c2e1016190030001000c529019615189454403803151459 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 107840062 1250 107838812 107838817
    0x1110a0b0415020f090d1415011701021305010804020d06051e0a0203151e0d0501020406080907080604030e0d06020309070302030c03010612140109050303190c0504050f011d03070b 79
    0xd00608a03100107101951100043c1e02c140c0191840010b810090740c0c80506020303020390059400f42100884100020b2100d9040031020064000d00403244001171241c03094044d26800c43c1003c41d8021450f00b0000082c42c814650f0911079503062121090016055494103107402e0044c55100c0000c11552410b1344044842d181030300c1962001d010356000241e101e0819100b100e010301654410180e00450b008208004407201100304082c9070025000c0354002c0d04d482c000014028880c0c1d0000d615a03040180c01004100001c00c05075030303644031070820404618045640c0790819054034200b41c41d00050001700b451007001e6640108190310010030000050804a10401aa48200c003a0f07400c881620040509030b940740d0155400e11400391104000048000c81007240503500c0d14000310341c9035021f03228903083d030700200c8801100115a000501d4041441e201b0a80c55541c00c0c20018109401d10000c9581540d03940089410b210a802e400c0ba88030301c424208050000b4000c04603806251180d8a0700003d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107841312 1250 107840062 107840071
    0x8010624270911030c071704080a03020a0209060307052d0d08090301050705030615090d12180501140a081510030902010e0303250c050a060c0b09060f060103090201110a0b 75
    0x1515050346029030903003103002c403170051040003440741c10002181c031456000d0783e000c506c1d10b403115001c0200042c11802404000b40680c080e40241180000d58010702030701e41c90061400c0d200e500540b42c18060350f43c8040c1c80301c0202441c8120351030107500d03050354410340500403020107601c01200702c0000e04000145000b848580020b1b13000340310644805c903041c4c1c2c1c103002c00d6a205502136295501c40c5580104140a00000d1000400b6110110707600e80700c3e10b140920b100c403140300040061300b421043c4182a141c01005010a10700414498405854080140580d481210820980801086100f8802c00c0c3c00e4090b40c0004200a6403100359640142c000c3c111784600300c3c08107d907000480018580030041d5a22080144034449410700c00d10299058104501d5003120352a0800402050307a031100800480941030a8440c00e07544c28590800030b803040e030010294905603204e0001c01100d25051160150004ca086c2000328103048a4401600e0b9010081c1c000601e500c6013072030010a00c545155018000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 107842562 1250 107841312 107841329
    0x8030a06140f030c130b13050106080106080403090e060d020a080105150d020d0206030c040b031501111606260c03040c050d03171503030c060403090801062427 70
    0x10340300d0034070601082d4024075a00e158181c0149406403145d04140500b040a260340103000143d2112920015401f10fa02c603e0558000341c3d1100180081e0f9000918680501124103100d00c0c5442c0039a00103008010702c0c010f0744020034084001c15841d4440c52540161603500402013400c85844414a50080c4400c803404400079200ca01c80000d241000900b03100c81c540c0280000240505603000d1015076800540000262a810000041c1d032450100c0610701a154002c17405410380700c4040010800c9055001c00c4010b070f005508010054007207004100211401800c0c0400466081d105403d40404091882900f1424185c2005000303907245000b0b52046108401d21a0040d807a181400112408c0003030080c0800c10900ca9100c2c1140d0303051302c00c3e83c051030b11890311140030550401b213420b58104442540709a40060b00b48000c244d040040300015020b02402080681d00c0c050102c02081c180d00024154040c0415003444030071b11480e810300b00f100480708402c01858030031040c860510403e2203203252 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 107843812 1250 107842562 107842589
    0x15090b06030715020714030a02031207020109050402120403030c02010b06131a070b151f02030d0509010209010906080a02070c120b09120714010e0d0e0306100503030f0d0908030a06 79
    0x1000c40c0c030740c0402c8900c02000c2c0c0c02003150a050980b06c140100d800505158584a1004140010b80d0301300040351191000c0c03050207455080c98070003d48210101e41007140f08600600c64050740c6658081903d510941514002c10042c03e8003005030b004182040030140c21800000700034602c080340103e105d013200c40b44a045aa03243c4007030a100130600501500400000000b408a0881d52005049901c4217400406035041d00b4135800340c58501607400c410390005604042040d28003c2c1d0588941c59111b010f52009510b0150140300080401c03015005030f0381407141010100b56000c085606617040c1c10b61002054210a4070f440e4403003000b8107d00f50884507407400310001105400c0100b1704545084010b2306450074400359a44140201a400402821075941c50706000550001000010b03400b440c00d44400412051410505040510007810300c51102400a41000f03a61000000c95001d6030340c1090054030f4410100200300a06005940a000380030301006001c011074040c1c0c040c80440c4d690161008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 107845062 1250 107843812 107843819
    0x1080a0209060d0201090312090b0a0f110115060c11060d0e06070216060f020312010609050a09020c0307030e030f07091a09040b0f070306050a120b130c090915090b060307 75
    0x11040c407007900900007030480380b01f000041c400190289180e4401c1c1040298981c43d07840d00d1401d608001d05104c000f854049a12601c103030094900c084079034140e402480700c4112601c400950381d1941c4600e0040160004c544001c0c0491000b0503420408000c0109a4030320300402010054505c040c5911514043d00000c50313081030000507141001481018a0840140717068403d40d48080c030001f10740e0550004002d40f915070302c10029907030701900c0591203d1f1000350611050007911001600844449841000b50320711203003002040d02c07215903141c50315004400061001c03c0c10140c211660400f01c0c41003400c00302e40408540c005c0400400644400c6055072205030400c101140305035805050104101c0c00710704610440e0f00041d50002c002d081c04a04166142c001c0b54040f030b85a0320a61400030102507050070410320307c11041c0c10101d200307401221000c1c907440300b000451540c402c0c1d0110664414840d802c1001c15440a00607204414040090341c00c682848612800c049540e24428040c030360020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 107846312 1250 107845062 107845069
    0x60f0708070c050a08060f0402010c0203010c0201050f13081b0a02132007120e040b0a0e0a0606180b07020f0907120c030509100f0b1504030b010e1b09040609020301080a020906 77
    0x138811145c90000078001611003441404058001400a0341081200742c0b407440036803024083c08141c048140d00000d01d41c030f004108008070040c05851040c000305882c0120021901c2503040e11012080c800720040c4131001c1c481403c0c901002200c00030b41140070884a62202c1410b41c1c0401c0010766445940034240c003071074404ad50309104404000f040101a01e5142181c68411003105200a80141c0001806000080040e0710700b084d0340d200c9001400d043d03080086110a6001c0c110007007103282031404174a01017040781d00c41a50b00d0700038201032402c003003483c0043d556814104c2009010260418030300741084c0b18010f00032900d0784020105681840c4c0c101c20030074880c0c4985031042c1c0d0000003030100e844443c0000760150a22030381e10500162a0082c0e00401e41d10102d4111075240004070790b9a54034a517160011022405901009950074070300200b0500031002485446007111220301c1c15561a10680081d00510319500401c60492021002180c800300015001c400140200c1d41c0038666030b00c01040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 107847562 1250 107846312 107846329
    0x20706030b0d08070c0f0b090f09070806090c0d02040605071103060c0d0e010e0d0201091b0605040521060106021f090807110a030b0c0301060915020615060f0708070c05 74
    0x3415000161039603424007299403c0040d02800d84075007601d441d850b41e50303a02041c44580e20b1300b0405501d0b1000500310312518085000b244810f805603030700350f034030714244801808010740148014018860f810001d40002d401d00d045581c5029901c900710344a40d1038460003466600140012124a044c010302107285190010396075209801c00301030589816040d0508070050300000410351420764032410318880e0190b09000800d070307a0406600015005003282041440a80e502d802d007400d12800202c1444030703603445400c46050791020355182c01021000c039200003c0c9800e0000480d0103000700000032440343d5000c28485040c0c0c5280a20f01c080e011003003051802c40d80010380003001d43c0b408100d40800103c450351948000c0c1c1c4c000f80000203e9589468540d2a64400c882e108000b800010050213019041a091006804401046004506460406582d0795405410641d00d280b0b80402035a880e0746601c1201c2d0003130b402d03a031180d45a03c1146416120b0b500b220000301c4403004034140100300c50525240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 107848812 1250 107847562 107847581
    0x180708070612091709010311030f0a0b0907020604080f041509030c0801020a05090f0102120d090b0a0516120e03040303020a0b0a020f0706050a0603020d0f110f010518030a0f1202070603 81
    0x49084c2d01510060740301e40315503c9215070b036040c1612603040b0506111040c024500c100010702d810122443c100602804480c281846148a04504800e02c04403c2e07000070308a074000e62040000d5656807000070005014003940e031114501c5041100c4828203584d01034081c0044a03c6001105001a2100c0320103080c2e016441015000403c14080946180b1340410312049444060040d121403529404003600c456025044500300c860312603402500f0030050000003644140508030403c0282022100c00d52000c0c11549240f041003460403000d054085948d00420300442584d0807250390382d5807454060344946c00c4841c295141030074500024000281d0740200d5800740400c0410900d880e07110340c1c2e07580092602038050b41210303995900100058464046c0010218042d0724801944030b040d2a017440310304004c039074003402140701d540d524180e42d030450140ca9402408042ca60301d8030b02d406002c6483c01c8446a009081c4d20040c0074000c080c09036100704412108842e03429201403945402054080d9182d494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 107850062 1250 107848812 107848823
    0x109020906011e05030a060e091e07030309030b0402040f053103020606060703031e0b0420090f01021903050c1c02070b0a03020c0703080d0f060b040b0318070807061209 74
    0x843d60364a680c0306400840d40030450381000506243c40da5400307a2401d104607410150769011411603a030009010700c2410700d081554000780481c83c15550002c0c8074903aa80300088c50100382d43e01190465807240c1000e10300d45ca80300700c2004149802281944101034440c99404e004803944040c400a082c0c11140d00c54441d0960010aa0b40e242d40c000d128041d40012801d804140d44c0342142d4004982044075040098603000000c1900304090040208454084040da0509804511966100704070314064960050003140d180040c0e0301440300603401c0802e00c404e00c034240035100001404054022014141c80c80c010302c02c4074a10705200304a60f00006200c040314015a111940411050390041c0040c01c484400d4070b8054103103202180007070715190031600f04035243d62300800d03041c3d0340c03a40e03920406101c80c103404801c4c0065454190107440502c00d03800703141c0c811440000029141000301c40f942a00180300c400f207818555668840d543c40700e01e81e00a00700004c68090030807122601e103000e00382006401c81e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 107851312 1250 107850062 107850107
    0xc030307020d140105040c030308070f020a060e011103041a010503031804021e070f1401020702060f0d0b120708010b09070509041a041409060703111c0b04020c010902090601 76
    0x503020402d055010050031115180041070145401d0f9080c06000d0045100c0c0700340c0c4a10a04601d40607015040c010088001c21020b030035040c050590008801d40c510f60850300004402c10030500b840d01400103201c00c1f1408001c00010720080001215008501040c0d043c1ca003811a41c0b160704044c2c50344036810300c1c01760805aa0306040e84502d0640d0051070f1010418510304036a01600e11f00e000290060350055512400c0200384c1400c1c041900080c0b03a180702d80c60004c503c0d020340303580012483d00071101508410f05010440b16104020b590180585140090a00851020361405541c2da00581c0c000c05806500f03125144516041c00003100f03021394140d0310303080d081841603400c0c040181031018484400504201c0380030803603104c038854000c0c00b4085502110180c075240c145240b500f84040c2079681014a01200030041b11502801d44051145008651403c005e4a801250140903d800d07650351041c40040c4000e00060158003200750f05100b0b0b40c2c80b003140c1d0382e2100156940503000c9140315a40310038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 107852562 1250 107851312 107851327
    0x5071110050417030d051f0e070210020d0e030301150306060c08040909030e040f09030207080a02090106080c1e0a08060d0b0601050c0a0c030303140c270f10020714030c0303 76
    0x3038400b00600507601d03c2c102c0e4240343e040d042c0300040e2201918400e0482c0d48003580000300264800c80c16024008500b07100000c2c1c14100030096560800d082c045c00d00c81d0b400305207045d011082c2d80102c00f0450500040344e0720ba58441d00500c28100c00d410880020034a0a600020041c1c050100d401e55039404c2842d0b642400d1405048101404182c4012410441c070040b800106075994856100c00280388140000c1d105098035020349440c0181c0c0160700c039070f8050049100141e5810402c10f040d29483d00d0286007540714081c0104050181d00e03100da600f85041c01c980c031818075909025100c0444540d4985800c4c3c0c80d40400d200801ca1070b80c401070b000070760356000100c1950140000300241c20f420001c5400640040d1903510035125a40c1048001a440c3c0d1410100c10300d080e0046a00306500c4c5601c940740070811100300e89114140003030103503c52900c04040760b0542d1603180b0308040340c90180401e42d680c804d10200039224101d500400c0321142640028410302d0600058801c0c8645005e001507140261 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 107853812 1250 107852562 107852579
    0x9050606091609060c081c05091605030a2306070503070e010318060209010207170601050f0915090402060c0f0705040f0603030e09150a031103100e06040209040311030a050711100504 80
    0x803d81e404c6d40d10b1101048140364207807452265207003500401b10005030354148818141c2c10f2168844070180c0840c400c0506010325540403400360302a80e440400315807a0755181013091154001c07215040541c0c0070310000c0258660300300c0015032103031201ea55580059405080150110f82c1c034014542c1c4c1054100b0092000a82c20764020481c800d414011610b40ea60f940d0403913111110036074802000c50b00500300410882c14604200098400e04650402141c500b011910402c101d800506900c03d1840ca000b02d4150b403a42c0048540b05600c0f002500d0342c0c1800341181999030722003881a02d00035850a1500d0010302580d01c120010f480c0c1c50742c0d595280e80300748130030030010440c00f40c00148513a030221100d05d40e95032503800e0000118032520710a00301690010406081035038141c1c041d94002c0c241510010140808130b0101da00950403203040d00e00b03803902e0808035000d0100110210041c480010341400c0c0503009005000b407984030704603002e00c2e445608184003034040b440c031002012031420302041c02002c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 107855062 1250 107853812 107853827
    0x61c0609030e030307151a010c0602030411060a03201c050603030c0d0c030201051e0f07020c04060f030203061e0105130b150405210322030203010905060609160906 72
    0x6010b0b1400400000140740000d00b10b510940b0104c400e018140f54010b00403185000b09040c1907180c2c000004018119030010b001506d100c40010030081c6d0000000c0c081007041040c1e800b02084c003901c9607072120706001c009401001580440e501120300340355841782e140d0344076040721440d0612100c00000341541c07003c06006000042e000c01e43c103001c24084000c42a20400c1040c10100607a500e03540c45203204d080c081d0842e507001e0201070301c141007000050b0036052603e0016030401084c5003426415501c9aa0881c1000001580c19522a041c0200000c3c0c080301e200307824085d40d00072020fa440d07940f0740350740c0d80603540003d248042d1186010300040101d850403420850403402e012001103420f0f0092400101544282901d416250f10041002d100ca41020322040034004650280300342404000805a80d80e4042c0300a4007541c03501640c83c00b604c015419450400456000d0001d100b00d00580c0b1b404c41d00d40c0c6003201e0380303402811100002040540c101e00c106002c64040e0f00e8080489007043c40c1140c0c5038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 107856312 1250 107855062 107855081
    0x30c0d030908030a02060115020a080a1d0a03050f0d02150a0b0d0c080114090a020f15070204050901020a02160f0501080a0e061f050a0509060609040b0303030109090605061c06 77
    0x101c0e0712030009040c42d00340300420b030103800b82d409014550305012007201c0069a26000d8402c41d4001020140003030900c60445840d0207140c18640c03411007640760a204100c10f0b40145a4106507040c10000c100300c0001108000e12201c003041e20403d241c2402c04076620010380807115100c2e101c080c04654440d082e0340c410710415001030203400c00c1d200a44c485080001996021032203076075540703400d0741082e0690840301d5000000c070000380100c1071f02e540008241c0c5600d04003041c8248000b04440c4114802c1d201140c005540c064024005482c0148101d03000390442100c01cad0160003600c010181e6240049049400d499507103406c0c511007800c1a004440c0342000900f00042c066540165003400b040801515229481c403070001d484046400300005403d0090754410345c0210b510880038409a80d41582090f40304405a6034030752140320100018000c0c243c681000c2c0c0c0c05000000010945070b42682003143c0c0180604011300c8291501c0d82842030f90005a5440300000184030560030004001e072b01f028104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 107857562 1250 107856312 107856317
    0x1c110a050d0305070210090e19061206060e010501030204181e0504050f070503120904090c0b1c140105010e0904060b03011a010809120f1303060c030509060f010302030c0d03 76
    0x81a2900d01051260364810019404584046100011890035008542c050902e6240c0480120314040340c0450ba00800b90500c3e40040324101494000242940200010048145040c6805e000781c02d02d480103103140e0040b5070a4031803007400440d1950080c002c580c2158a503015065002d421403a10f02d0041402c8914048c1c0c8108000c18803100f81440d000c1c8500a50040024100491a1400e0b03145480301c5540b216010746c0141c100c201039203032124252a11110180d501052803072543c50072741d8201301d850b00040340290b00810119198024007081070f518400701802003001c4401900b118100420921410380001c3c00d001103051507044c01071809401910918010a0b841500b0000900b910244601d5111540da088200001907901410441e000146000039040e642050b0403141c00d948515004e102ca0b21000050784035140b0a4187c800c0005c58115004004003840c101004010b084255030450711031041c0004105c07540e01c14400681241d9008005040c0641ea41050103070340b1038440c070b06405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 107858812 1250 107857562 107857579
    0xd0b071704081b060603060a0e070e091507020109240b0405040b07121a0118090e060103060605010e01020705010e060f03011203230706020706110d0e07051c11 70
    0x454400c10050040340315040b402c0e100d40701c2caa64115220030400c0c0800966111005000d8039441c0402c00d243c1028500d400440c180708203054030707450000c1c0c0e5880b201880203c50b003048001032006c00e0080c40c1c203a4005e245000c079119003004034240d852001024003c410030840618001c0700d04c0c1041a2421900718000c07a052003628009000c940782190b00781e44551400e0200703d4001c0d1300c01c103c481c00907008030007001694410254a0400c0a030414a541807040d448031808802129110200003030040c4501480042c0140090fa51940b1003031004644150509101244c50741c02400d0303560901c0c0042e40101856841c1100443c0c210000c00b0095400460401c10140c092440c0341c000c601074550284940b2421031140b400401100b102c00c1d4101000c8103174660502020180e200300e40415403c228050386506480c01d011000301002d280f00341c83c650b80010602d1001e000b9400c00d90743c0260781c0d8260391040303986405000c0303507151111f86550b052000441030000070b160508840600e1901420118 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 107860062 1250 107858812 107858837
    0x1507030e0f0c010201200304082101030c0303021c0210090c05041103040212060106081305030d14040309080105060609010315080102031314030403020d031b1b0f050a050d0b07 77
    0x1820040400ca2090154002c0707607032405256024010125080000a501106400d14075242002800040e000502500b1f0002e9058500b860003a015a01044403100450316540d50b07140502c2c42280c0c41c40110094040c8540c000141882da040510490005802a00e400b101d030310342d4100181180340040703880c00d0625a002c00c10b516688506040c80140c4840c0c0d5039030303080500401c54040c1420700c130303448198010001400703617561100c0a9a042280b94009800124007460500d0a60150b1031440c5410b602c0c00c070301034a881100c11075080c00f1714042d03210003400316105d0b82d20900362042186d445c0d8104d04200032030351441d4400d0784a80140d403105482d0800403600d42000b1400d91384141c404c20220000d0010180c184214445c4010980d8900001903180c24919804a01440c1d501c02000e0300b07100c0e42403a000c4540b030a0708001545554000d841c820f0940560008180d480c54074000c0d40901554480c01081500b0581ea03040181e0350001d000900100c00350303440b01070307110300246482c04014031035000340f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 107861312 1250 107860062 107860091
    0x3030818030c0c040510030c0608040807120906030e06010f1a040306020a0503010614090109030201030f0207050105070809070609030b0f100e09030711040902090103080d0b060d0b03150702150703 86
    0x41c038010b0403100280c154400d910007080240c51000e03251400d4204429010000180c1100e058422240141000c036101d64503818043c0041c0030720b24003c1e10381c050380c0c0044091154448038110a03100b0039241081a120b52101460341c0b40b2090144a038907288085e4244241490800d4a903040c0d5100350b240c40c605900d0b941c422042c0c1c0c010b401c113540841e0000c0014002141c2041ca0765016801c0812503a04102038031300020720a0880b4800a0706240c1d84603555840e840e90754040300d01141e04540240414101100c0080001d4000c44009007180281c510100c3d03007601c50210882200d4103d110301041d92142c4408980d000406001b80e001e84a0302c0300b0004010f080c01c034040f0310a42e440005941c4400940c100258021a4449528401e610b000340385801a070b01d0a51041c1980d412070806c580741c80310744885030b0040070621015039100d000821035450048240d04005c1c11114203500b9102401140401000c101105803001c1340960011202140041074442c4550303801040f45c9008242d82030b0204d6030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 107862562 1250 107861312 107861317
    0x6040b1302040f0614180c1c1503021906020604080306010507050d09260a060c0e060d0b04150305100504050c2d0102071d090c1c05011a0a0303081803 66
    0x3e2001d0540c035200108080079200a50260012003039686c0c4a10b801908008408030900a00030141c140c00424008108689a05506d40c1040000010000003040c0c0f41003141c04220b5200880c0b00f03640b00300c3d030a118a07006034160000c450480d0000c0005890f035036141c2003950401402d40d810418103004a50100d00e080010702d04d40c450340d48641039400e0602d4100d903124584c80854040401106029801224000642644940e00208001a0524050f204446003440b070090194002004541d04103078000c10b0703022420140c0125400c100c0811342d250000c0c11030681d4400a1712136045100110b800e821103030026a0321138491400d6030342c842500c0700003901d07003031147c80300540ca988003c804100030303e05551044240d81090004002d1142f4090081003000c0d40140c8202141d80e10401080656108100e02e50b40840c2c01000e514603900c1402e1044072600e8554016240f641c00c091014001114010b0001e0124074090a02c0c103041e030654a041d1080100508030241000c400c0140140440040c0003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 107863812 1250 107862562 107862581
    0x1c02040906020301240302070b06060310170d020c040c0e09100b181903020303090112020d020406020a0c0b0307080a1e050901020901030c08060306010312180605070605010e0906040b130204 83
    0x701c601176505103140001c0c0d1125080641c0041c1481001814082901d1151140d4060f004968a5990783c0d90f00c2c81c05d2003504a154010714414a03211101c2c11040b41c041888507420003507508445c0d040d800c0500f008240c1b450b07200d21034040340c0c1a0781020100d0605124066000f80ca0b0460f07100117566600000a05500c01d0707850090300304558040c0e8589103480544002101e62030782d10004031904540010f07807a489070303400d11818409164507881c44c1c04203503016180c14590b6000c0c01c40d102d5645090103034030344001d66000c85039130170b0f2140089440417640042c4c80c016001c075600c001d10b55807003c240100402d1200c0c001c950000c2c8a5042208521440c05041d1080701c055001585900307400002509480f1540c40b05400d01c554002080840d881c0020064110703038102010030304a40111740d050f510700c100c1c000f1914280306001d070701140040c3c0000c0242003081c40341d4030410031030b0b80c2c80400065881c8241c44002180e0083c03008100861010507490f5007048980781504109100340d40060100c03540d406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 107865062 1250 107863812 107863829
    0x4320312010302040614130c0207051f08010b0a0207050105070f020409060e1605090f150a06090e130f030f02070902040f050306010509061807090504020a0e0a141c02040906020301 79
    0xd0041c421401c050060600401c50a0314203000815003000203083c114010195a156682e9605c10300411032003044040014078003d80f50811965203042841d0400740103401480105000900018064a0940440c0c200500350b5015054103800c00004503807903440024191b0b01524218250009031b541e0b031082d14283c6101d10030020300d44044400050901b42c60000207002c03040f166108102685442c4500340d031000340c0e448501b840d903441030074044016142c54010703074101004190224405800401c0309050f0782c26500e00011565802039195441c1484410003480030702c21450440009000d08503a41c1e9210041c010b0754101074032004a02e0480c0c0066100f145d080f4a000401c001c107003803d0040502400d01500e8484052500501107540340702d0001340300b400180a000015502c0748194040d001401006005568405502400a00a05120080c50310a00c0c1070003002032030303441050111707003144d2300a45000210744803030441500c3c0c0c0907500c03002d81c0c20a445240840c00100d080c4019800b074055903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 107866312 1250 107865062 107865097
    0x2150c030f0d020c010b0306090a0b060604080307141006030f1b0e07030f0e03040b0301030b090a0f0303050109050f04050601090e0106030c0608013b040302011d011b0503043203 78
    0x10139801d4030740041105009800150500c040b074140400c01001298100c00655242e4841c00041200f5118552124141c1d001c007041800800040070b29515402580d04120360244182d035141104a515500c00145100302942c0b408000800b00c01c800281800704c401c8030103c480e035903c20782c40341c910100c900c900044c0d03842d003081e40e84140500c0794440c000d155034000c42c2441c0c1060307608865484180009003103140d00c0d100080a1031801c00c5414031156008282a03440e0002d07240c0600905400e000c1c803a2034500b407800140948000003461031149402000412140c0d180006800041c680c590b041d600c10754031031102101007540301003001d0017010309598100582d0f00d454078550003a6891905042c0305001c00d02c0d0042004082e040062150b00c03061034402d01c54817540f9090380146003084003045121207400311b151035000107503c500700d135104904600b110645001ca0840d003620003114010308903280a05103805140104410384201c941c1300c0440401c4091000b840f515603080f10000b201c1c1e5a051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 107867562 1250 107866312 107866327
    0x4090b041b0605090d02011803050102070b06090c1905030604060e27061e060105070609060b01030b010201020f12040309031406090714030d12020409020c0705180402150c030f0d02 79
    0x1c00000001800e651425504110024001648161040030068104014000f400c035070801500b4032a401107611000855941080d450074081e5603d00f10f81c02e46c030900b0341100089070345015804441101915210940103810200400d40307064002910345a0041da5400c03000ca940d03800d0810355070281402c0d09020010642c1000d0b0b01d040b6451005101d0410380000050210104941c00d811801603203441c0d110803a6960800125054000c15001405803030404d141d110a202c0282c0c0002e02d236000c2aa000d00c00e5442e030038010782c207030300c1000260b420050007000302208481414003015001842480c0210304d156980d220911a40d800d40710148454002c0030500800550801c0390100411119200c0d4042400d00c0b1b000030b80b80c03282400940140050743c40261240196541110040d05070110f00b191a2030315030b101c15568884c0f0b401002e002d01d2540d101034200c80320894000e40701702d074014184c400d036020800c4480c48641008104030020302c03080c00f42d21030402030310020340340000d1404801a2110360 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 107868812 1250 107867562 107867603
    0x70303030e0f0a0c0314010f0606030e01050622020c0f120a08060307030c06030209012109110402070507180221041e03050d020903030c07030501150f0509060103050604090b04 77
    0x703105400c581c40c1d40c410f003042d0001401c4400e1460440750458602c0b12a8005a00ba40d409840740d411800d590a240070408940b480c2c1581c8511145403d5000070072482c0e84031400e0020000c6051000395110380880a1020780070b615400512410300c005003612025140b052046151030b03000c14010001c2032002c924805c00300d41c80020940d00180460052520300c2c510313201c140f451800b074050941055000078064107980d02803000119165810040c80740c03680c0348a01d0326002002089400c40b4128680100400c0c02d141030b0094503811508200540182840c003c40c01f2030046114212080301a000d0144280414826a0707031540103104840386c00340c525140c80c20039684028200f841208449084500000c07943c00801d07031b40ca4034459100186c2d50303090f200c0041d01d1800350b40003c0300e503482822404400c01c241900030811100d00e004c80c1420460b1a4900301c034004200d40601c44c6c10510b0240000c50340e42c802e400440c1c00801c00b42002030f4502403500c5603400312504940944281565a10000703072521b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 107870062 1250 107868812 107868823
    0x105040e0c25150b03010b1914010e211015030c05010503090c01030c1202030a020903010606021515040b1e010e04200d110301180609111c0b03070303030e 68
    0x1001250b40112200c02c664440000b22000c82031005031a546200c1e8035405d031003d52101d46d802c10001c00c0c6070020038041d40311001003440340c018661041c48000ca0503e155000da840d03e90100e100400079000d5958024a903070b0b10102011010001d4444d480300405110600c1c4140e80080300c280f0301d210415825070810300c2020f50a5481a41000300c108104030701041c010900090240d82440c1c049846484908222210050001c10009281c8000180603c40c0d0b101e03070040030740441c107900911240f41d03201b600341e1325031599024258104014400041d8401200002d01200074001440014038a28680204030180c5008240c050f15180005280c2811342c4c0000300041c103d80102c40500004404803100c009240c42000301885410002c0340c00c0c8480035a41c3c200610041300090400d8407503075a00003138051480a04010b62000345404004103880642d0f00607011055100640b031458100b03c414078210b41803d150f0f2070623001c0d079164041c50150307609221460080d03010b541c011401001084070b4a0414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 107871312 1250 107870062 107870107
    0x16050109260921010e0a11010e01020303041203090f0303050f010e0c0a0c050a0b1303140708040e070908030f04060306080a0201080606070609060603212307020105040e0c 75
    0x192010354090780c503241000302e407211038042e80c000e84990032105440280b19102400b01c1559401d00304004107201c0005094075171700d0b00030400600303400d950034015a041c00c950025180140c00810020300490018100307203ca107015440c00080c9102c040c0c41e02ca0001840304000c90000c2e48070000d111031596800d11090141c540c203136009006050454940343d1a1094a11032010f1101c480a0340c0103000307040c00040122904034004c680c1c0c2d45000068801c060103001d1084020900c15210003c0f007010240643d003800f0791011314240390504161501d1a1000000d000c00200038242e000400c003060107001070305201409210f001c2d1143d06001025040c1c075902e40002c1c419910150700340000d46c4e03100025a820000130340e200e980d207415504150300581858400074000a050400010030400344e4030645c50301c1c0520f403c0c044442081c0b06001c079003c12031180502550448450004403074000400201241441410400d00d403e1b615030000700c2c201800c07914800c580c0c802045020005c3c1d803100c0fa01c0c199 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 107872562 1250 107871312 107871353
    0x3170703020a020c2e020709110c280201031109040e1006080114010302040902010903170918071d03070e0c07050f0708060c07080403060e0105160306060804080f16050109 75
    0x20043e00348481ca141c103560003014031740300050b03264803410f26000340220405410841024081104c402940b4602a802241c03801001d01c1560b0f49084c4110a00b85280304919801c2c00d04c41d000c414603001103029007002041018820303020071034000669158800e8030495507120001e011004040150035080b21416408110036034104610200001e01c804403660540f541120001211181400103c404200765000185466881d018407440b40d8940c130702400c1030b80802c0351105d84044014540c4841d4000a4034900045030901101664001041030040d0200c08050102c450103a13030f41c2c080b050003c0c02612809001030380091a0401d0200c00d0003400304400d0480000c180c43c27031030003607859038442c0000c081e0079113460041a2401000b00c810129401580c0201c8141321a2205c051460700030181911a03031000181c840402d40c425000c0c0c01003000304c544903210f4020f1a542c41d200d02616a00c00310340c00809544c10407421021080759441918014011000000d4201451034980007102c00c4c01d084800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 107873812 1250 107872562 107872579
    0x5010b0609010804080c0102090a030b100506040506030601032406030e12042301090905091b0a0f0603020702030f0115060f0201060b0313020d121106181903170703020a020c 76
    0x199801c90310f416006a4400030340c5958104001c0514028000d104003164480c100b00400414000e1804c0401d0182c00d058000d10044c1d0303528420007030144124400c07580c21110500000d15190300a5011800c3c09100900841c141980c0241c0f03040500e41c141c1069011a69138004400381c80c0042042007602e4610070389503403403e4200710342d05500c100307584004100e4005001d07648030f46074803c0c4514001003800d8030050100d8107000e0b254640301d4131601c1c082040081031400d501024074001c83e50000b2074000c0c0300b03404001d80c104107088029520851003030b60184104613170010358110901c10b00d105103011481200d000c0e8100b49004040f01c42443c0038404581c1000028880030703000c2c04c112074000d03410240c03000c814210f40c4046408007440140c060045444c0743c000c00001c81c0c103d80c0440a2109180942c0c81e13a5591102c1c40c409040140540d022640c007414181000c08459010380d80c40342d000781032032580d20042e0000103608035001c03201ca800080d00840c8500205804001c0703204803c204071076098 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 107875062 1250 107873812 107873827
    0x2040f1706010312050d09080421080405010c0318030c05130203040507050907020a050f010f0c020a121809050a09020405090604111012020f041707032114070c0305010b06 75
    0x956034907060001814550742c1662070b0007041e01031000c80e001000000400c0c0850b40703450030401c1242d0054410410866201c0c1000052030141c01c0110120660105d80603003410b0602c03004440e9600d841a0440601900341c5103080410808e2510200442c400c4c0c07405002a0304210074410b0b0b00300725440152030741e801030042c000003560108840c800d03a80d051394100019952813008901d40948514054018021400c05c0c5501901c1904039814940307001d08103000300e0590f5a0100c3e610400b00f45c01401929006000c2d0725110f00c2015814280454a4940d44000391500d10369004c44100b0780b41d44010a540d510440214180790140030303072004030380018050318a03154441e4080201c00c96802d920409001a08000c0c80d070090f01000d01c05048000119142c1100d0404240503074002d02074a40740001011407515400c0d00003c1c42d000f940d034410709401d0f035128602c00850a12410350030501c00e100c410401c2084c4d100b612006407852034028005040140d00c0d6040c02030071102e1002029000307000421010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 107876312 1250 107875062 107875109
    0x3061e06050f091c050616140a11030c0102031b0408060a0b1c0507090f0605060a05070204020d0903180803030c0909060f0a080618010501060c0201030506030c04020d02040f 76
    0x45084a0302420110781c1e030241071404101d54410904110703440000c0d10800380d0803000c0480440e10f0700b40b0801c200c518645400b103c01c10b003000d03800900320016000a101450a8840401910b0340c1006030034100b2401380708000c050308541003aa002101d980d800320030014403040321891410441c020401541c13400d4100b200d82a1280002086816028fc540032054403a0b00c9039910705450794041d4001c07003200e400900d4130a8503010140b280715141820581e01554000203481864211103009210074030b40011010141c5080e080301c0c6090344d21650a000c41200034ec114000d0781c00c203522998403000c07004040300c0070701401401500f02a40036401402040a002101d8040714045130003101d680b4007680d11800025040304d030903204035400002c0d40d1000144448001009402120719819240307015200400141c201c490034492440011003000701e02001d035000750300450b04580081c0035103032000000740100c1c05a03070003098200c0c5100c0c0d0000302041860780c4c1c0c8215074090404c030b0514440030011204107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 107877562 1250 107876312 107876369
    0x806010b190906050a0f090e1005030f0105070c03081009050c07060c170a0e0f0d08072703060509030d0c02030c07050109050a090b011106071205060303090a0915081009030306 77
    0x2000034481306d0340c5100511401450014028011178050b500c0341c1c501407001401805492003007a000380305009141c01840c006004007445540959903107191f0701955201260402c0b0040c01218550403018804140800035000c0c640c420640d1803589543c40b20603107040c80403a540746c9480c1d410428a1000c02400303000c11503150340c001041403000300d200303102400c541d801c0c1110085112900c0c840c0414104051380c1010006104001c030340c0782c1c04034401c03600164000201c40411490304d50201304106000140d995802503800c0032500302200d003041304c2081c0c980c1c1220715419242025a01c0440c035209081010480e21010384400c1c80c04100e0545020081070040c12540a2205101d48818480c071450b4483e403030602d116031505048231268101881c0150050020200d039101c0e0500703290018000741400004c44980078809480c1101062a01c85410000c2c4680702d40d03e074558551000c0040c440104010021000c4035080c0c0002e08100076150107021220f41782e0082580800c5a031b809503022014102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 107878812 1250 107877562 107877577
    0x7050111150103050105010501080903040b030103060f0f0c021501060f082a040e04020907050a0c02010c030201110d06090e06060307150210060306090302010f020f040515040806010b19090605 84
    0xa080c200c2540140189081100c52408410240e203290000400d2001c150046e9040384c0003a00e400c001900d6185c0115203078482d500400c6503000c3c0410040002030f1060348102100c0c41400700024850000c40d0303215003590b542040200061340207501601d1000d0b541003810b4010b0100f0b040038803080c482c5480240040000408100e20543d5066204500c100d000540317400c0d542441e2116a0340b203855241c2403c03146000e8070245c0c003900b026000103001c203019800722160750a594940003d03c11056004450201b600d003000c40c115501c2c2c994448540240c1c0e030107442400c3e26a40c000c11002d042c90b51150407901c03415004034040c0d00c0071060100988001c40c0160944080e01021009800e5202e4240c0c41c00e2400210110100d103809000014800a580200e02041c0f280c0d00034024041080c0800040e80030700d080b802d200c24001c00c810041480c0c06044e800c0f45403a17021916043c00d584140b1541010b07026823040909020000317250241002040c141000255141040181d4508006000b049809a00e8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 107880062 1250 107878812 107878817
    0x9091608060103021e210115020d02010213030f24020901030b0d12080709080703080c06060a030b0a021612020102040509160503010306110c1209040b0a1404051905010602010506010f03050702070501 87
    0x81d15030046c0312484291840074200c0f400000c0c00e940e44088070207002c40c100c40654018050750a001c030f9040d206008580f422540250351880060860b1520700980011003012a82e280422180241d18213028004468906100e4070045e181e059120001d016100c1d82c1508904c102c1c8005d03400c5000540402140200405619001a0b560f41c4c0b004140d400c0307080c0d41c100b07104521030f4440c00002c20100070020001c108001d0305891507500d4800c20312046072450b000c010301c1c40c65000d0000700307040d60fa64094008046900150100b007403168848030f00101038440c031a00181d40001d414499410090110f50300b050ba0084110801444103200900358041800300030003241d26800c00c07884410955042d140d80d440d41d04203490300003104244001982c3e0001d01e0b603074040ca04081414042c2d14200321402d085500c210175600d45400004100001420010300c84020b440c06956023800f03000781442550b0182c1302c1c0c1d800015841c10010000750200801c040000700701130400040040c440c0e808a01003044900a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 107881312 1250 107880062 107880067
    0x90b0604030b040c120f06060e07140d141005090c0a0c020402031008030d06060e0109050a090e01060b0f030f151807050f0703030212090a050d1409091608060103021e 73
    0x2031502004e07842c0254030003414021240703c0d2100b8000881d16580e51030340f00307103002c001c8582e07a42100c07000b1847c00c03079050010404140c0000c154050700d50042642e0004c07103000081000480724800b81205065400700303071030286a00c0600c91802c1074049241c00014281500d800d1000c02200141b6032514140000e00403030f000b0000c1080840701e4038015002c0c00300740c401d03a07444140c3c04068000401c1b142c400c180010f1300541171071070f895004400302c10586801412003030b101810500b40c03001400842e14040b0040d90b0b10903000640c1030112000e0710004840c2d00003070343c2d01c0c180b118800c2c01e940c1c0d000e003070400300300032400090104e9695450703040760500c0c6690820045694620068071140150205aa4000f000044010403d94554014858400ea4003a40801c50300e42e0282c3d1384c1e40d1300207000018046d51152141c190e040c2e000389604031503503520114051030b120284012801024003516801c401c038070000000071030a500008401c0d4010020301c0d003141402201a801c41e01e2415010324901c000400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 107882562 1250 107881312 107881321
    0x908030106031107230d0e13020f1207020318041103040209090a15091a01030218090708070608040203210f0a02030702030102070b0106020607050f0306210604110a090b0604030b 78
    0x10109903211250040c07140ca001d1041c1ca0b8803210300b00e034004030703050085c0210361025598a0046110301f10800014000c1c213800c20564007200002c1d8856603445e4503075141409011075540391140c02c2ca02c00c200c00c2c3d0255413982884d0340c070307610340941c501c00c86440340d424002c0d44400960107030181ca5006404031a48440c0d40c60792102503041c140c2c244005003500c40004204074003101c0c9500a481e000e80301c1c1d82c198124080340c0a8494483c00f003070100130740c0000c8044000c0458061007048640041e2000140d501860382ca02c80b142c0340140903031041c0c3c00305100c5003c00c819440c0500211708203024148103040c0b104000c640c1b2007168072948410540690002c0340104c401072003042a01c104035400b03002117646211074100038540781024442d0030014803614000a84903032086040d41c26009450303140341e00390307120042001340c030040460b80c240c0c1c1e04003681038603180301c84108030b01401980a41130030501503150700c2c107100e00c4003904d0300051849414840c10801a071600001c5808582d000281651191103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 107883812 1250 107882562 107882591
    0x612020f01051215150913090302150106030f0e010b0d020112090803010e040507060c12360609080a0b04110d020a08030301050414041a0702121308010b04090803010603 74
    0x40c3c0008105800d01c060401901d0066540f002c502c0e1501140c4001c8003a900007420b110350721400d280c1540001d04c0e4640d070260b00d0586e42201c013969220340150f50172810740c82921a60307018268052800070b030701e03010f40b203d100d0080d214861109071248000c1c858200e02002003140014010002410003260036007101300c80c0050303800380f00d1072a4801d040607942c0d6540c000100c0440001e8a080c0e8940c003402034001242401100b40c045101e0348108179050f1003d00d0303201a01d080c0b41e104409051104552a00030703c070344911041201d10313600b00d0803407032042d820204020900c0403960461a560b910814101021030007074800703160300030741c4083d011b20350007450008503075004484d10b0025008000400042360705040400514180d4a05650803c207104107c204285002000e8401529030020704084001d0800c041c0842c1e607101d103c90048603803c41b91100241401d81c08031900907041e559459043c4400d64080c0952907100384210384c1070084006030740b5800e10324803041c4124000d041d62101107911200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 107885062 1250 107883812 107883817
    0x3060e0c0712140c0f1203040308042607051c0206091e0f0a030f02060a0203190209031614010e100504050d060605040203010603020715050f15060405040c0c150612020f0105 76
    0x50f03801d98215140c035442050180d0f1204402e224031541e004000c11000f0340140c000a59114030f07010b55812060345c0300e588509803804c2402c0707285448283c04a603000b01790740382ca000400040344510b005180070652100d45070503d00d40700068404540000b8207000da007520014213a0b20200c030072036a0101810f440b18681d80340c40190791400b203a0380201d02e401c80c203151300803000105c00b03034181e025140b00360399443c042e1080388011a4002d00c554000400308500c200d055002c1c1c59107000180407074a040b42100b4210481020b0365000304020003424100300001c0d40e00000300f000307124007500d01d42c140c103003026005441d60041e0301546005822a040c44000c4c030039683c00c21001058084e00855884d6110303031004029502541d81a90300100d0140b040c800c0004038070545114105a43d00181d4030303164442c24400c4224801c0303030316074842800e210200b4560341e10b00c43c80120680e5529074030480c03012442c1a000c45d0340c2031034000c0c6142e0b02e001c0d420070600f40082c80e40141d0960494403565844419401070700c090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 107886312 1250 107885062 107885087
    0x10b041e0f151203091707030305070812250e061806071202100e1b091902040801020c161a09040204030b070806040605040b0303040302120a0b1603060e0c0712 70
    0x18141c198005036580c00c040f004030300c20b0b00945d54400582c2e11940c203c840440307448055185a40191b20410119110740050700764544225403540c83d0400b000003050b0b074000155021012100754003402042d11100507a10103c2d030849080c0704041c0000800041c40c180101c1c00c580804410100007040c607179031100304440540364400c20481c40c80091501c02551042515a081402c0745007410b210703148140002c03281c50f080b84202010014208060900c076840c00060a1718060350b4001008080001d0107002a00c00381401c980016140d128000d0070078a81401c0f007040400301c04410030203000c03491101d20a00c0c00000110056941c1d02e0180010600a2180d60300103440640c40000340454a50310442c0640209411a002c0c00b06948450800045808401c0c401c0d605900400c8200018244610b025406041541c2030700c503a21705a0312002400032007121000000301010100c2e0542c1074040c810000600345405408019103001c624802d058401c081014080c91100f8260b205010b03c1140031102c0c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 107887562 1250 107886312 107886341
    0x92003010914062a0a0e0a090e010b0307090203010503030a1d0a08010e0f030c030901080903070501020a05041d070f05030907080d0f08150a030f0503070506070c0203010b041e0f 78
    0x1030b0840c900d01640742c10b402da6849003010b24a003142600480309650070000c01010321038032854403c03410810354040885a8407507070400c2000c0740000c0c007183c044c07042014036503d02001041101c2a01c00305410b0240a800c14441d4500c1400103000540f03000003580c09811584c2016079140700c43c40c0d968480c84045483c00c03940207401d440003141c0c020040d045039090085610864203012003806486840703010702005648554002c0c003181c06158403890056400c0035200c0d0643e440c0c2b10483d00d580742a42d00c070042c0b0381e000c01e0000030300308280c11520701c203404e03100300c0c05075460128108400c001308405900c0400070304016011001c981544403d0017400c1c01413010702c040b214464002c2602030010003203c080d00c0d000c16580c0c130008850340d00c200d15001c90000010310302d2403a1815a505c2c95aa030030104000c1d07071507200c1800030300001601080440c0c0280308039100c89a840550388101400d440a04500e20b00070350130110b4000b4a0700c480364190281454840c0040754007000d5112000c001c0c808802680d40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 107888812 1250 107887562 107887583
    0x30411060d091b090c02010c0206161205010608060102060703200318070e07021203060901050607080f0c1b01030911041a040203040605071b030503192a02070501030920030109 77
    0x3d1148602c010102110300d004000d00075030840750000ea0880d14005074050250300328400081c1c6d428810000e03000758804a090070796040101c81d001c0d40894009801040c04118070341c007070000568040203480c0c0d000c22503160a101140f840101d42c0f6031504e1500180038590000300c08940c840d00c01036841c02240f9035039070031954010383e40c01403416441410f80e0323508054050a5040210081e40700b088903c035010140031460f00c1d901e800300344055940040803c2c4c0b0780391014400402a028414000c1510391800301c0146405500b5099000031241100c130a0340c1414601002c000000e0764203101c1011514085400180d80c080d034803079074100c003562108840d03072180c40001008200015503201c980030f90b1183c1d49041040d0703801a00102001031101380034010510500000d58849010000c03c01405442c0c1c1d408614060701450343c0d001c0c070794107450002198898256040060788c1c1006400000d000918040c84841806d40741c02101c0c88050350f801141c1c522140015040f52000d400181c1c202d0ba00c29035560 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 107890062 1250 107888812 107888843
    0x50f0a03090b01050a0f05310504050c061206091005100512100303020a110d170c0d090b0702120a0f0c031104060e19060e011d010b030411060d09 64
    0x10300800c0703030140c11a44146688004510b40c00d080710910142d402c8410100c0c40c450515080042c484501c0030012081d60300b80c8a100001b085810b8030017074030712101d03d000c5100d092502e006410290f0710b12117903014040c18400c0f240c0030220021010340200040e41d260002e51284480d985501820340c11035908061043d11882d0700d85e600030010b00b5a841741600d50307075803501c0d006155507150840d48400350059001210302008036981c0b200c83c43d0103540003000007584c403180d5942c040d92107991950005d40c000c00418a0101c40da070501c02100600f8892a000e40d21602b48080d56149010358107029000d170115190100442404100c1c5001c5940c2280e200d80842805161100d100581800200d603440031204201d806070030b140c01080166007545c0c0b03550780e140d55046402441c0c401107208042e5029121b801c009030400140f4101e5001c0e2192126411511011401a2900c4231041c0d01606100c0e004104000208100103c10200803c0440d910b550b075172140b400050282c001800043c1515080b10200c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 107891312 1250 107890062 107890067
    0x20d02040e030c240105221d060f04021c0206120907060f090b030a02031e07082a03061009080607051224060d060b1306030b091e0601050f0a 62
    0x104880c502c00012104c41c9019103491600009441c0c0b110b41030181031000502040ca0301c459200d004d00004d8645130404d10062150f0f000303842c4840f20540800150802e4490b403254103211440d803000520b640300d103141c14a94003051080c40080103458403884181030420840d5280c508940307409080303114041050400d9800e803a11241107110340004204c46900150360706010b24131a070126010610a81d0543c2d03201c561503c041e6100801001d4440c00107800c400c5000b454800603030090007240d4411009103055101c900880311184241c00e1200c1150040601c02034100c0100c95105005803184050010600c209549095103a0054041c0c0e0050008000d0788550103409031800b40801c1c7d0f140f03100d40c0c54414069040341071084c4100e00d80001c00c0d580340301c1e6050a00041a140c400070500141060355100200843d070403174202c1c01c0d140700411602b040341c44e03454082d05030400d41c100d07803800301d42c20204c84c00401c220707016580d0b0b08500035490024034940e00407025a2401c0d680010410f9442950b82c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 107892562 1250 107891312 107891317
    0x2040603060b03060f041709010c02131508070b18030f060403052106010c060c0908120702180106080f101215060902090105182403100b0f0313020d02040e03 69
    0x180644602070005c1c0d202040000e80390300903034001c00a40d558245d40ba00f1031950390f020481c640c1c14081f04410307130001a2102180307041e401c4400a000940403840001d0343c07202912a03844210079a20000f0b0030f00c0500105021a0491009151464420f440c050042070500764420722500c502c4c000e05040000b13260b0420001c090070040ba12080101c03a00440c028064131005803021400214000002000250701d9484645603082c2c50810b103003920b540e6555145806207086601404c1341c004942d803011801d01c00fa80b41c440c0329603109661030540c1003000c0100b000000401d200c45405001020620360280482090050300c1c039041c1c20786240903d814801803110030b40c64401c0002e8905200052825814400d9502402059580e5480c1c4111501d060b0707885020010038540c840450103100040e008041c81d81402c031242001307820b40700c0c90200c02c482284c41080d44158001c1c441080010400e400c443e0407294003220100c4041250030743c500102d00d02880d1810300941207031503c0180200d20400001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 107893812 1250 107892562 107892581
    0x120f0e0a030207060e0307031a09010e01060b0403140601050609060d09050102160201020d020706020d110f1905060f010303090e13061a120304080a24020d0c0807080609070509010302070204060306 86
    0x1035600e4105c0c40041810b41c0d134111880013070425810241190b02e03c00c101c000b050b812480c864008544084505c42007400c5030385070790001420300c3c0001410410007081c0c503d4807904c40c0114000d0002985443c01003080c0c2e00c260703401c50707200307000026407449250840d074000151690401c0c0215200c0000001c810840f502c2042d0982c054800c500d42524001e1000415106985060307000c1c1c44403014816080c0c1c0c8503001030100e0491406800b4a8159460041040010032a20405201c00c43c5281d401e04030304009000d02142d64440e503104c018070103c0c1c0c01180c9001210804401c00c4070f680c0c0c540c404610310b090301c00d10040c640c40c20013502d04842203006400c3c801903030040700e140c000c039031044c000d203a640c1c4500e104030160342d003001200b040420381e00302c00e02c5d442c80720f0300300c0100c4502e544002c0c140403a8424541c1031440e55464140500c411b07070007202654442443e042c01c1400d814101c8c0058081000200960b080200008950103540d101e5019190319a41c041c0c81880300a840c0c0c40c0c003c0280c80400c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 107895062 1250 107893812 107893817
    0x714012405060c1f020702150304060c020312061003060b0d0501050411070b0402130603050303010b180907021e03041e08010506030114040b0702150103030302030a0f020901120f0e0a03020706 84
    0x40010641d440c0007022962030080034002083c01000200b50122003042c1c03410100005582409100d0268a83c640440c4e90751a50005036a40da103013a103002400c07034030010b070b07044215442481004030200c8010306d4a504040100d540140694143c0800c030b000e880c098101c0004c460380411407002c1594541c00c0141607400445040c07016101c0c554110201e030042003030140c80c101a080c045400342c202281a002c0ba007001c1040070499585036150186180e04c02c1c1e20201d81071710001821900c00d8441915132040310000c8488000c0c904140100075602c075181e181203002038425050b0360300d071414104216401400700d082d00354202c80070110981b204080ca4803940a007542098009140d43c81d040c4102c0e000d020070042d11030b2264980351100d9841c40002400c090a611545030380f803907102514a4035078000c0d442580e0250f503d00e869400042682d00701c0e407250741d8240c01403006207016a04509a06c139400035610300011b40d280c2c040030700030243c4035511091256000390100103040c0740d80810200b054440c80d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 107896312 1250 107895062 107895131
    0x50636010504050f0607050403020103021806121e060f04051015051c020306060412060902040912020f070b0f0f0d0e06070906091d04030e0307150f03110d02071401 72
    0x82ca00c1605c410b0201e0b842000214200420f000640c026400390400400c2e04061103030901c1500301099440c0d10078000c0444050141c0f00700308110400d9000c500b252000d000300c54a01e030a00c040405c50300c10f544102e5511841e2200c0001e038840d01140814002046c10000000d04044218000f6003954007a50b03040c4051000d45008010200040c0200c0b03000d1000a0105031030079151024000e001540031508558003078692909101699407805803002c11030041000280150740050064684a66610203c0840d081008100040c4030610700780d810718411b46a02541d038801c07040c9520020b01c11002b088071403900d46100c407105a840090103902c10807040d110780c1069921048191030840d050700c1510804030b9518001e4602c020705126081e04207109003040058400c000b00081d080000582002184441c0300a41005899006c1701d021244440ca050070059140c01f0440e600380c80c072400c00701d072030b01319000554081044103121909000040980003003007101c01c1116000543c800e041590030025218 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 107897562 1250 107896312 107896333
    0x525050309070b0702060c030703090504060501020d0c14191a100f03020112181101030b061201050d0c0f03080406030507030c020604030305040c05040c031409010905063601050405 79
    0x65400c880c080d407405801030031000d28000f001601c540c4800c200b01c3e0040000c3c444c10a181c0d1081001c0c1080c0b92003a140c13007101900f040300b80011904d680e44610b04540c0030b4030a001c54103030030403100a41d00e5004004290301140c6c2501140c5002c420303100c103544014003001c1301d10520480c003241c101c1040c0b003051400041d803211140400e120150707004032903428804420400041d030090000c0741c200240050040380d0000f541480000b000b00c0080305842c1d140342100340c80415a89489a0309510341e04030740e540c7c14900746143c0403ca0038414000d45000b009103444200501000c110071318004c04004080640058882c5000c4903035401610503017000c17138201030100d007100d4024000c1481040d82503005101c66500c3c2e841c200d0280801a200ba0b640003d80100850962202e0240e0365603c802500c000c181555000145c02021100130072080f29031f4941020580003a0010681640000c005c0e01003441580c40090305420103441710f41da00c1d0030340c0c5030f214030250300038010340180c0e00c914000d20076120a10003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 107898812 1250 107897562 107897567
    0x100804051618180b07030509010b0a03060b150313080c010207050d0513080624010c02060d0204030308011d010522060320010306080d030c21050103170903031614010525 74
    0x200200604c0d00c030320741000400e000d00c01e51107503501a144d03500104002c1e003244082242d410b615001074404a44031100280281000c94854600c1d5000d4031700c0904e546440c0300c0f070b910b03200074030040142080400038102442c82c0094050394001d81e004010b48128209441c0068002c1d484184803000800300c27042c002800d1800420f42512031408016005214400c00202400e118403000c101418008644412405616032101400c001c085030140169034500307604026000503016071000d41c04005607441602184d00d00c002c4941110003e03100300d90490b245031490300a888840c22815078007450618000107111000300c01880e032030245590030840c60f040c42e00440684032180a4403115500201d40c1766903240c880ea02440c9212031900e00f00ca41000320104030040e1b111888002108145c8500040c41441442d5102c03902c80c25920322640c0c6064042c1d00469207074011000b0900d150003a8262602c1882044650120000c40e81c200030802c0e0303c0e000300407070141c4c60b115000c4409480d640744207103501030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107900062 1250 107898812 107898851
    0x70c05061305060a05060d1218080f0705010809071802090f1e1504030614061513030206030402011e0f0807020d02070b07060905030a2606100804051618 67
    0x82d08100544a5961028000400781001411035504244240340c0c00d0f000c20310722001e2507a102c209a84020014442c60600362211080760014410768100c1c4050303000c0e07004005000401c494007820019295604c01d042c050801c0d005500100c0716150141484000001d5a8028008102c0469244507070001e014288480b801341c002d5814034003032a5001002c0c6600d0075200303144949000141061600d038695030f0b8481910103000d1020406088003091049a1410504201d540718404501500307094604810102c00c1509200c0a40111000000726007035910a1003140a04031844030340c403103407071190700000303140c0040d03404100c1c000b9150902051413030744045401d564140d0141d0041550b03a027420f00c40c4030543d00c2210300322255036482003150002130040c006000000700342e854803a0500c0c0c022580c00c8a00e4502c01c4a0441394031484100040d59640e0401100c8040a62a08190325910383c42c1462401358140003c80301c1c0c28000000041075910035440384480d000d62403007804009020060400d0300c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107901312 1250 107900062 107900101
    0x302011b031103040b06040609090c090c0806101211160b011707050f0d020d1b0504020301030b0705090109050316030204061208071205090405040c06080f0903090105130e070c0506 79
    0xb0403c002250206503c40030307058022400820014096980e40e50541c00c443c19030000700c034810340b814001c00000515115200151046040c01d81007482d01600181d04e04054041707a0080c000f05072002d550104140d404066080c1c85204015520f00320743d014a0368024581400315400c0da03000b00041000e24402c0c10b01c241d072141c140028007240e07040004010b0072000306031405070801c000d010a140076a440c002c204000c0c50155107404000c5110f00d0411b0b16000b55a00064021801040108001042000300c0d9510120794607110303469540300401200c288002da8803065162040010a810b98103d520705041101c1c03003220204040366480c04508808440d041024090050070300c02c0c940450b2940341d240b9840091071410780d1400da2128009403c884d0300342e0781a102c040c42c0390018000940c00008043c1c00202c0d02003038900ea0300d04a0412a6a80700308030041341040341c0814018230400c406030352600a0b107118040802030345045c00004004c0200c1c55400c2d42c15101d0400868030340e0612555950302c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107902562 1250 107901312 107901341
    0x1203120e01090206091302070602130503060f060616020f0d120e010c050a1e06020409090b0f090703020f0103020409021611060f160c0504090317060f0319031107030302011b03 77
    0x1d05c0e220000b0856801d03000c0c1d01c50342074984c0030809030b00012014070040c81c5101c5032840410f840c505040506140070030040a10b808400c2a20500c0300554450302540c91000074003041c015499030610215851060542241f41c205004032094801c00c07045207006219054583d9070001d000706114011188501038000180a5800c0746443c5008075101c070515207041c4c250302e1685c4103c00e4941c2e80345c00485e0700030307840038000c15a00c104520800503c04140ca030418607129961641c3d0408603142c6480e0045440004c0c818040903241c6502a40250141e400802c00e007182152110800050318800e2172031213408540302020311301d914006149c0300d4151020b03640c00748030f0706051400117186405003080200d010f41d482210202e00003030503035845c0640302803e40f01b40d9808502070444d0000d1008102e0240496120700c5291800c3c0905490000b401c0070f03d072000b014417458400e151f0500b940c000c1c800d0b0801c00710030300421b030010060640540180c0e144c075006840e031102c0c0004030201103048403d0000f60000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107903812 1250 107902562 107902567
    0x11040605040b090409081306080105010e220f0e06090d0c080d05070207050a030f020906060a020a0b06040902090c21012103020127020901050303030408221203120e01090206 76
    0xc0700b05110040d101e040740140000030700c50600c0e04c807808250042c100e207510b080c00c800d0081c40603d43c4051031900405081c00c204d81c05411110005035802500703a1030b00e009003282e6410100d1124150003e07101521a50070801801c000050040c0d2108070469401c6075070b100d0880b06101e00c1e0300c03514002030107582140f003644c100080003e03244003a2001501d05011481201030210703560752444603c00042d40705600d0800200568030620841d410020903440c0726410501c150f030340460300414002500e81d84454501c0302c0c2d5031400000b030002c0005140c082d402c44403400801202d1444000101205080945040c43c04007110044514240c8240a411800300411038003800f84078500000140641c424000800c0c850540041402e41c40002241e0050348180091044107500f4103141c200e001d040150080c501d5031030280c541c1c900030b208082000303120b111107450410910780403101041c081c0c580344400385540019820021300880d00240e0081e0010328245c5c552440b07410500c10040b07002c0c0d01074201030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107905062 1250 107903812 107903819
    0x1d01021305090f160c0b190c180b070201030207051e060903070f0305030606271206091e0a0c0605070204050105180c0d021605070e01150503040204020a051903050106031104060504 79
    0x11008106601400900c6850002600081d06910140e486038441f00e400f0307140305a000c100001501c44000305074007400382c08080c2d00e81d40401015180196420760014595600740c03440124001e01c030360300c0023070854010151411700c2d6a5055003200f000002e0f10f000c591741c507200c442d912500c1c0c0c0f1400d540140814150780000000a014501a540c4408014140da08041604e8080403140384a5003104800340d8071511404031906c1c0c880c81d600201c5969800a080314078060724082c2d52200f0801160300025810a0004a03040e000c018155845601140031501103944010140c125001064224480e5040c50004103860905041690300c1c40d02084e010502c0c1c2e01c5000c03214107992300c608040d48441c0e4080004415000d042a80c1e40d86952098008102c2ca80c0b501c44061040201a000289140d00f002c60f003140d016440410b1301d4202c1d40441e00182e44100c00003090360940305040d1450904048d2008030010181c15038001e178100c03011a20305002c19100700349041c90310720450107001d020a10601060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107906312 1250 107905062 107905081
    0x1006120308010608010b0931090c06020318090901110a050d050c030c0a031e06080a02090f0c040303050a210906060b040501051b0c190f06180b0304061d01021305090f 73
    0x702343d00c1041c0103c201c0100041c1503100e10082480702c403480340c0b0b500c03400b00c90708100031201020024103083c0b010310304181155000f8159031003160f002610410b440008101c030032100390302000041c0340d00d056480c0d03101849000170b07140b60844505900c0c10340c5420000f4407220311000c200d80c41020001042450800481000d800428580f5080204821a00000c036110701c403e20600014010702001052480900d2040040c441c0005004652800c401010300c1040544074042d00d007901d9050401507168540d00804403400102e28004140401c0b00d0b0845d40d078022120341c000d03558140100002d000c140c2e03c902c260340301403080344a010b001607030400c140b884503402c0105038115480034400751043c1401e0f520000700c20f4101c02400c02c0c129584444100102180b0010a200030030450a00408030b20803010704201e050031034400c4d03080700300000001404010091b030041c176415403030905002801d00c0c803881450007500311030140c01281c4116100440c0914101d8096446400c42c410045116541c0051a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107907562 1250 107906312 107906329
    0x90504030c1707060f0b01080417070b07080711070e01091d01020403030e030609010b030a02120c0409050313060503060a150203040b030408031605070b0c0307021006120308010608010b09 82
    0x6404001c0245800000101038103151104212816445600d80401d41010b0b412112843e2041007407510f003407800e8015036005640c0c80e0740a5000604011182944482038001d8480c2010051090048208200645070405c00480c040c0080d5640c0064030309004908a6941031540144030274240c65200400028204d03410008a03510404105440ca6288200c941d0a84c1c00035017044012956044000130745041c00c101103944010150002e0000d480709502003074541007078000c068055a001c201c500e910540c1044101500c0700042c108010000946c20030340d450b500001074041610410312030000f5104d201c0c00a5a02980c0c0c02000c04c600e00c0d180c14034020000c00c44000010030340c0001c0c40b000881c0030440000d980f1590140741080da5924040c010031600c04031070000b4a003400824010840410341d86070580350b03c034085504c0181c1e01d4132110400c4e4504140312121602c0a030408101080c0e0418208042c0d1442e407003500d40340410790303c808007070b41c8242c003d008110900000f80407403012407421004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107908812 1250 107907562 107907571
    0x705012a080405070b030c09030f030901031b080c03100e0f0106110c0303030c070507030f1a06040207030c230a03031a060c0a03050702010309081204020108150d060e03040b0c060a0e160905 83
    0x5907c1e1402180401090800800c0034541070a5000415801e0141d40c00d4090032030841d0105402a601180a0002515141c00500300c808034180c040001f40014030642048006030400c0d0503c6840c628017850114080381d0300f40074001c0007407d40103000708030081c0050700c0c9a0076880240614103580e10140200d03201d410548050721244a40003000000c0741d03800076590707003560241450401100080001c4490544040c181c0e90040b44104200004254810510707000703c1c3d4000d1800d0307007094030a10751b4411502a01001c3c0c20178002c03a110310080540690000d0ba040c7c010310240901c1c00242410440b0303e0103554401c409607080222280c00182c030850090803010700c14100003c8504140d2214482d40d00700f04460506140504240404e541e08a203155500103c0030303810480c0401990049400c0803070b0300c2801425191a04101d8502d078009106540142900000171038489000e0114583d0780c8800b0b65464090f5031804601c20b80c1d2800100f0610300c41d484484146078844e01d0b10303a018009010080c0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107910062 1250 107908812 107908831
    0x306040f1b1b0c0803030a06080606060711040b10020c030f0d0915110102030c0711030604030e06090102070801050901050105101e0e0f1002060106090617010909080705012a080405070b03 82
    0x900300042c52000c041000713048400001c50302c91038400c1c240e030100c9140d40c0040c0110f40c031175020080156a02c0c0e04480c2500d03881300380002040b02150101e00034084800c4c0032640078408107810032207150700254050307000b00110b00f102c00544400c03181984039500e11040c0c1c0b00003007d1060500c0300c0010030f450843c10000303d240c0224249074003440c440c05c9820640b501841035400040c01c506110016521621b036207012000742c40142080d07034001e4580c035021301c11580186808180440c0603030003804030b88000c00180d002406a458442020360081000340138013071082c440c070a801072000d84103403540100403405120041303401030300c10026a1000d9070501c0d0700c1e41c090090110845280c071000e14080d0110b259400a00055060140180c0030902359000002080034001d04440307a80e0080180c641190b042150004014103c1d0411444510a580000c2d041d5030a100352041c2410b440c0e01ca040d0007810000c070b40c40002007101c038202d415503010b49000d0825400060240415810000250740020000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107911312 1250 107910062 107910107
    0x91303030c0216030507030201080a0c020c041503020d06091202060702150a1d100b060a090315020f0310030b01050409050c010f050d0c0e0907030c0c03030b060913020306040f1b 78
    0x30f03400583c21070f45420454803034102c00310130011035801801154000501000c00e01400004041c02952100c00703500e42880365449441140e22403982d004984040c6802501d01c1480c0e0482d41406005001c03182c40403240440d100b6a440d00302e44c03010484a01a1207190b020f0400c1d000886011000200040c1a00403856601c4204030303204030006e50000481128640a0040ca0340e59100000444520f9a0060300441e002c00c41c08000c9035020209030107890f802042e181c00c1105940b40b8600a001d244424109464000240002c001d92480e02d0790449100d03510b80c15240e0380b00d00c10b000565034200b800500507840f003c40b0ba80e00750300820210710481c0b4640b4bc020f0a100a07031b02d0320710a44e10511504400700d881000c4081c0503060054038164840000e00b01842080103805004100c4c902e404d1001d0704042c1e86820010060f9280303011100326540040c8074110b80c1d4a0820541c1c025401546c80c14825850210002d51004050190007044140c0c010140030030020234900751000300100380c1c001200c0869 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107912562 1250 107911312 107911333
    0xc03170405090406090506060a0503030a14090312070c050a06083d03030e030a0209071409030106031a0a05040206190e061801020d020708120a02190809010905091303030c02 76
    0xca124041c40f880c010040424005414103229080220181c511800703010795001c2406640c07000402c50f54540810f01d0092110300b51810713030046a0040333101071941030268501460450a1103030291008500a0105100d01950703802042602c46840c0301e558082100000014403045400c0200e42c1102402c1c4a00d001a060080906c401c00310090340320300c0d0140d0810024418164400040c0c61541d00c283c000703010000c0903800213034042d6801040300c41000001080343c281d1010550995500d200090000c0c0301140d26071130725001103880d03450746551194043c8005a0780300158051180540e40144c0310900e046c1921a030158101d00d2060784005001c500f011b00c0041352102d1000b8280d448030b5107030441030814448002400d124000352244115400030340240040d00011508100d4000340202183d542d02d00704a0683c10b08114044040808800200190602103500020a07880e0400da03507943c2220344a0701001080003042d00d181000407103841c48480080e019a000c076808103028011618650032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107913669 1107 107912562 107912569
    0xb04020d0218070314090a020d0b0618010b03070207080d0219150510060818120d060b04120605070c050c10030f06060503150d0c03170405 61
    0x88011000360865542d003000110a42100d5031401140c5041c1c10007a0060803404008400200c40b100025080c80000c1010a00641e0081490303600f60050745a11181c2c400c02441c5c550009050303103903001c0000311090350038000d10041040560b01c0c5020035000303041a2540d8000f001651040300d4400b0071a401043c201080c249448090040340c501d4280121203508001c0d0f04210545810f0502541d801c2d402c410100303a50960b01d0380f200c1a100c0c00d800103910181351500000355000302510500139411325000701044000300c8404600d1036203841590613294406d5108180808200d440d0400304107060041c10303446403107030514000550140d03c0741c0b9154603c28080b00e101e01c2c0015143e0a10030300a03403012000d51078810081020a4032890060035070ba00c16600c07030108008100c040085441c180e20315600743d42d4005040030f041c0c0c2c07a50b6205806541c600303e00800161050002051540303 = true := by decide +kernel

theorem cover : BRFrame.Cov 107733812 107913669 := by
  have h0 := BRFrame.cov_init 107733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107733812 ≤ n) (h2 : n < 107913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
