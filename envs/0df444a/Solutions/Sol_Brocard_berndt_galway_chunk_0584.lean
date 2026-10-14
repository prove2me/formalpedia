-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0584
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:35:08.828002+00:00
-- url     : https://prove2.me/submissions/578f9b3f-610e-4c13-b214-f61af0628b8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 104856115 ≤ n < 105035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 104857365 1250 104856115 104856121
    0x603060e0d080c0a090e1e010509040302030d0b0607050a0b150a1a0c1c020105070e010306230303250c05030a020307030618022808061003140307050607081905 70
    0x20b80200500d6004007000f20a984a003d00c42c41a0b546101642040c440c1c1000c0e4030801884c402c0c000c148005030407541d0326280f900d0f41d82e44240000d1010594000e4016002000000000d840c280c001089960010f000d80d4034214030f075101c0600303040f0344a41c2299010750b01c401f40607404d8210031914150010440d440c1314054a0130401c48406198141c00726540b6001203042c02203044144031001d0000c4041256103440805902c0080c000e010884003500403461990514186520034818030094a8081816212080c5500821002c03021070404a941c0342c48104040504901440529250643d21722124551a0000d1508903040100f540242d0301030380c440034601002d80c2e000100c0c24104c903005200043c910007030a50030742d4840d4022902135040f4400c41c00390010b0b1781d901c0d05454030381c94501c2160f501c0b01d901d840295442d5030066803800010180c101061002c12000c4001e801610410411280b03070440e81d6454904024013142c5a00c007058214040103981c10742c00e500d80c6000584202c04100c185 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 104858615 1250 104857365 104857367
    0x2030a0806030f0a031110020f0409061212080912220801140103080a03060506030f01080105061e0613031a01080f0307050703030c020d0b1512010603020607080f0f0c010603060e0d 79
    0x18034010240c200310f08a800c01403d011b090202d2034044020080555031900c0c244010351281c0e0040c86801e541e030b480c1c5070001603072508a00030343d0300c110361100340f566107803240403012281c0400180080860b4010002400d8230300c4002001410a03001e0044041d9002d200001d100f107801009901c10030159040c07600c5218038044221185040d01c0c2c0c0902002c0e00c03400045800c41c02007081e500603e8100303800205001035205ca29041e18103d03102c48009000c40d0b620031061140f0f0322900c803458650319410744034480592a01e20080c00e504200c401d50ba202c01a500d4840c5850090001d1641900000f02001840003040903c810081c0100c500c000b54500b00701955080d69415462001a04109078014100c3c115900c00c3d0180410b41d4100399000003c1c1020720207011100c86d2086014810807621455941c0348006000f40c0342102e40041c030320741c14521140c86806440e8095040100b55510801078410305003100c00c0507040054040d400000c42505601d01001107a000c4540ca110756406030403418209 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 104859865 1250 104858615 104858623
    0x607110f0f0a12051309270b07030507030b04050f06010206070503040c05040c121a0f0f01090b030c070203120309060a2a091802070b061c030c0507050901030302030a0806030f 77
    0x182d4080003c50002c070030650200ea060203600713a402c24600c1c25a000003216907680d001000d846140752000e8400310700c500f605281442d402030b0001d0800c0301920004458a000b03620195200d1014103010810402080000781212030444d4010062250602840b03000d507410000140d00c4066414441d10314103294554401d040403601c03906102d070351900750501489100d802462190800d5140c00d01100390200c0b80050390108400c42c10b07028850f8003184110070b14041900c02011003042c0c44d10440b407030400c000e821056000a1060a010a04120320401a1800c200210865002ca001a0b031139040554505080010140c100320b1b545003046488080008445c14544c006070816800c0700340245041020340d4070007140d511090f01140060505144404a90001c140382c0d4859040d40e1035969424080124044020041c3d05030003903042e419000290141c150400814020411610042c4d900c000040d00c48100341c10072070043c1c001090000d0f0140d000ba484030b8200c401200a0190700480c2d104081c0c0d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 104861115 1250 104859865 104859883
    0x1103030a02100c05120a02181009061803080c0703120804031b0c03051b010908030406082a0f0a08102d0503030f0a0f0201050c0301090b030c030607110f0f 68
    0x81c82c0d0f0303021100340060081c001c5030481e2002425107101c03443d0a00200b00250410f2410810711030b14450640440d1803c06080300d40c6081c00e031603002c109404c100d411201c46054813410040c24089003000700204000c10050b03c3c1c0003451800800c0040d003185880400c000c000401d05051040300c105100020760001d180c000324403640b2100d000b11030201c0c1881407410025a0020707185001d0120580c1610f00c0e00030854580300d100303032a01035000b42d640c02050f030b591145104000c006058440451028000c0b11070f890307a000c0d83e05a01040c0c4540403000c140741548016030b0030320134000014203000005d40240754164001c0c20151441c90031450107400c4c0130101602c1010506100b42c0d14088440711843e0394544000d0030020301160b071194240503180b42d2550084e080c0e0303400700e026008070b520741c1441402658401d5440300070aa003140d1030011894042d20501c1c01d8640d050040c0c80c40440d0719202080054401c44290381c4bc4001c02d2950310790107041040e8a1201000c540020310444010b600004800e42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 104862365 1250 104861115 104861143
    0x11300301030b0708040f0c0e09150903040902160c090203010302040f0c020d0e01020106030b13020315010807150302070204051014040b011403060f0a0806090118020d020f011214041103030a02 84
    0x4d61507030365240a59681d40780090042020602020115080410907a21752040b00f0340002c07580105c444d003080c40040d01d0211020700482d807081006002800c0d45070041c0900d444040f00c4840010f599030303200d4402d030a1341e401c004213403036000c001003007540307041d0081100741032281d0f000300070301810303407000a403900d81c441c1803a400d009902c40da5801c940d00c00d40c008001103800581b079000f5410329000c240e5503005020310aa00c2489100361014816494040d40c5049610700f4005281c12450600031401c004c1c4044240002c1c1503081c4210005600c40c0e00629100329001201c0d44001420110792896030003195144900a52a2030900d00707007a608201c040340100d05170100c41d030312030761040c6c0043c40300701c0700c0401e058011940450010b407607003002401d41e0261500000034008101100b149a00d50099840301960000310880f1003000350030180d019101104061400303602c01911141154180c0e8a10070702c07522001e0303000c000c1005028004460b01c13207030b2008070051444e14035044002990758080090307400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 104863615 1250 104862365 104862377
    0x61801030519020c07090c0509010f08060105130e0901110a02071202040603060915060603050c040302060d11030c041409040201090513180609061803050a0f11300301030b07 76
    0x2030003031049082c21081441801002e40d540c00700c428049449003114030401c9149818244102c00c064002c0b801c6d18480b5406945000e4000002002226120b03400b0709114144030042140e00d00607074503800c09d40081c0c0b0043c1001101030400801880c21035007030301d2002e1031a0005014892545034007003801c0d1b0403145414110b440003400341c00003a00410045e40010030340381c9090f03100c070304001705102d040c0b40c01d82031440204411b41d5928029425540111122224030108100c2400107251080181c41380211800d000104070b203500c2c00c00407281c0c0c001d541d00a44030201003020032041816980c04103203114240c0c1c203000342c0e04041e40081c10b0a840340c021303244252000710400c000008603a00c0b00c0c140c07c0280115081c1c0c07003a58103000d8010002d4000039a800e60410640d503413800c60341d120340d03040194190b480d2071074451030803c1103030300609140c2d8040c1000502c1910000141c420081e10322450195903414450030030600c80f054012556810116103036034103000400104014030402540000075003040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 104864865 1250 104863615 104863621
    0x10c0f120e0303090c09010905010e010905130b07050405150906040909080d14060f0603070c02010f09051f030b1207120c05060d05090f010e0a14030c0a03020105070e0618010305 78
    0x140281c03020308441000c900c00402009601c40c000034071003c90f103030b0581d0500e8843c2d890300180c0e8290b0343c0074000c815240069400411221004c0d600139640803036040320700c0d0f1612030300b41d80301d0026030800d45070040002c1e804142404145400720307040c0440d102509005180124542c081403940c000e9200e20050a0756541c140750a00c05e45008403a030240e2001010007810340301e541da10102ea00c068581c14002d2407030709806211804c2c21030440307002c0d0b82c850701e41080500c260f900460b0400440c03800d800402001900000b4113807070303405c0c02003125100c81c083c00b450400004002000c55000d161505d105244140d801040d518000c40c2c24801e0315516151792010005504210403800d410740e00c840d030008000100908004140c0c0c0c00700d4050885541503813062108002d034a400d0740c6044c00d00914070f42104d0000000036523602c04140c43c060b141e0065070300300440c0c0d107412400c20409074001d60161351504100401546e200d500e0102c5000100d480a0615045c001c0c40802c0c5038410340100d041c181e6031408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 104866115 1250 104864865 104864897
    0x2090402030f07090f0b0901030b150303040f09051501080403050403030809010209100c0203070602010605011d030109050105040c08060709300516030501151a1804090c0611010c0f 79
    0x405801042c0d800440354466500c100000050103240d69800000e45000b80440461a08080c9903040f6500400c08041580324031680f9181450912240d1b50306200400000921200c0003010074010030204600066600e040c007001d0448801c0d1104607030401607844104070002c1d410100741c80c19250949820200340c1e075640c83c002c1c028451044541d07030064108e09000899903100c035440140c40e02c294191a007103a07489005030700740d54a60090501080a070601111110700e0724190064a12000380041440d0341d0940b00e6a0841d441518140d500c41041072080c407150a040204c680c108549162480142d46440b00c11120710545502547d015074441c0041482c40402c000641d40843c1c0140540b2a0080c40303500031003021800d1703c0120350950a04801c41040d468400101c003c0340c001481040415820074081c61940c0e101c142c403007441000c01ca2450b845038860740705003950184541d1450400509100c0050582c0078507110711411a030500da07526103540c0e80101d601220030800e08140740c042c110265 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 104867365 1250 104866115 104866123
    0x32a06050c0703030c14031602071214070609060f0e0d02090106020d020c0402091305100b0301030f030809030a0e0121020705030d0501050d110d0321050604180c030209040203 77
    0x1001410090402040c0304580407041c00070103255110b600c0402443e0310085007510111aa401c1010302d40e0010b0000030b0000140445140c6100c003070f4815500e0040e1142d50750400260a10416104524042d5011649902c200324110107480b16040c04c0320f8280c43e00320020145030f401c0e6403074420000c0248031075906465015140b088140c1c0201a4000f40d81c480d5802540c401511160000503c209485580c0d50300709031013181d848000103842a8001000c1340b00d080050328002d0304101040e4400800081d0801c1080003071070185104465a12151145050081c0142d0000d0a608510b420030080c4c1e4032010381000da0720352018000c1c2006508842082d04901103050101410321401d400000c1d00d4007000000f1000b4684e000504034100b0069803182c0a02c0084450941e009041c14107880c480809490800d0080c4440740c0b082c0b0300850b52482480728a803080900500f54001c0584071000d100721440c041c00740300200f030b0310901044000361260f160161412103a05c000780c001d540b800041429500c083c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 104868615 1250 104867365 104867447
    0xb070f170a020c010306060f020303040206032203031401320103060b070f060c14040614131e09021e07050c030109201509040f0e01050c0409110703 65
    0x144680c1d150500c80001070b403240d5043c820340340001d01d0101c0100303040e0700801106212141c1a4011401c1da662070342403000642c00a0400203a0a4111024062940205494510080c800d5030041014442090480045241030b000403403222405007c51950f10382039440c1c1a4803100d522107030064407484200580041c8115002015950000101c1c2024022000740d40c000d11071207000d0800031269207460403101050400400c00c0508010002007055070b105040841d140c80c02800da8070b2414002442c0c090030a0995804410381a000c12050700c0007030208611300000307000c80c540641c501284c00089045511b41000310000c0c0400105010041c0801000b00300521100a0000c000c0443c039401c3c1041c05040203880c80c1c041300c10251440b042800c00c040d04010138500c540645040c02951030800003c2c14070480d0505085640b001142d02c50360007402010302400c2c03070b0408156100e0800c50454162080071040b00780201d0b04008600003c0e920480c004040c24015928a1070f005d0881003102c8205102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 104869865 1250 104868615 104868653
    0x14010507030e0a230301110f0a03110d14180705011110051302120d02031602130501031401060501140a05090a0308070b070e042d0603080313020f0a0b070f 68
    0x1071004030303562044501c00c801c00c00542c5106031307080c4d120308201800d960b1120355800c0304c0041841101c030001091070150010300740354180484c0702c1640c80c039a040700d80c00045a805c08280c84044440b080d40d410300c00303c0d400407000e4071841c29100010b0280b5590301d04078414203040049248107064010f40510807642c10005a18040c44142410300c7c5220442002031b2060b031007035100c001c001400d05c40000700030009603440d4000c0d5040032480d400161103440e07400f8007a031f000341540303c800581d01028400c55020b54410549080101155174015003141c0403500080c3c10b00c202c3c0e400441810090307100761468505540783c000e95582000000c114911081e03030000b050604003140500412120700d4680c0e2184040707a0340d002c3c079516071390708120641d440d007551070480310448680040155982c1042424007a80003401141d110350f83d94402130680d01c2100c007850001070560000b81180780181826440c8a0100c4084280900301120b0307508920071800f00801c15600c41d510701d4104400d00041c2100b003908 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 104871115 1250 104869865 104869879
    0xf061f0e0a020703090b16060c0306030206070b10080c03060f0a0b03030d060501020c0117070e0102010b12010603020f0d0506010e0912070f020103050c040b04030320120703030c0914010507030e 85
    0x101c90010103074001410440204401040115900115100352000f400103441c00a101403155210007000341007140312801059260740011016840d50002003090714070401040390b240c03170440602e0b0b140021300d03001054160450b04646a0540d000a02039400c07456580c490711080d11032204030302c02891090040c0d509800046031b00211340c545548614100c500a1b020b480c000314620340115500c905200100020304e18040110b4032a500c503183e03030819010107000025412401b038001806080c85500072251a039100c04042c400c504001c000c0810803c000e55103000c4400e06035440c282c40350030502032203030440d0f1880b0010b41015410403801d403c02c040840040e507118001d0900000081d0000c6060b03000ca410400030030600e040300300c2210100d8003401a55414541556821100041628070041501d0242002e40101940612030000110f0074202c0d800e540d00468038018081c5c0780c142902c8020b0012281c410081c0c5040b540503d4103030b0742d0134070b04913071759041c14a0241e41d00322600d6586904404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 104872365 1250 104871115 104871121
    0x50f042a05030a11070c03030c060b0604090b010207080c0307030f03090b030a020c160308091509030d030b01110606030726060c04051804051e0a0501090501021201080f061f0e 77
    0x60800700843c080c6808040c02e10600d41c0c1c0c58003042d802d1140d46401014100c8070f92041002c24802c000807105103124041c0030500e281d0358000101540c2041d0000d00042d503460615048640c3c040007803100405d920400341814402040010b51200d80c644030103080418109100000c05103d00c110002910900503140d840e4240040c0240083d008642c0301c01051181e60408000804894940c00469034045503d500c0d002d05c40007440f541407120742200045840c10300c41d01da445e543c01d03c05410310080715900020500302c100c0004000c1c0e0380801c01010250001000d01109403004101d04041e00e080e108085583c141503503100654160313011443e941ca004080902048034140c0c00100201d440031990b0030101c80d021a0001c912510940c0c1c024407550103d00c002207100c1071403414511080059042d07a9184210b600d419080d10b85014040f80c05950028400c0016010b5078011400b40504030010400b0404103400300340e0341c19014242e00760195444290300c48003002014124098a807114050074681 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 104873615 1250 104872365 104872367
    0x2903040506010e06010203031315110d0c080c0f070201050913020d0501030c080d02030301121b030501020301180b090604052a030610050c0601090b0301060f0b090307080601050f042a 80
    0xa18280150f10004415070007141440d84000162030080240041c20341484110b0f940e018840c803004c84102e01090b86441007442c40204e410098009000c0020011490281032080200301d42c60003001c8095140062190001d9540d02d41c0c1038072255030342170070040c0c1d56054690014450a0f45141003501d60340c0001030349400004030b900309904807889203d01400d042d45403c400c6495155030b0352080300581c410701c010810355403443c102c068003a00804401c0c440b10040d541001c6004c08603001560640c1d0004010440010304042840e584400c0c078004010004401c1c00181c85a640600072a103d00c2d1190089842c56070868031000034101000880703414641c20790321200709034004880803845501d00907a040c4080c0d00803c2118940b225075400f0300f98603800c128050000b03051280d0307040d4041d9620321002c0340c00c4941030200400b400c0d00081c01600c0320042020103107001c8180e04000c1c09a04058010031054aaa43c4007400c0d288d02140c001c100c403c81e24003202154041c448101804050800c0000d1400d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 104874865 1250 104873615 104873623
    0x504170c011101050c090d23031305010302090a050d11030d090905060303070506010605072d060b0103200702030c131d0d020c040c020c0a142829030405 67
    0x810002e0300e600c110001c08000c41800c0301c40032903d43e11425410030a158040c40c00141000c00d581c03041150002c111f8604c3c4549100140c14000030510f85c0c400100340201c2c22049103013600403c02440c003589030421550108840d00c59901c20b6074001c0300520f0b91380301003002074150041c1704000030382101c03642d0405080040207071240e40b240202d010b14142c00315420341804003c0f00d4a0342d8100c801814242d00e00300085800b90322080c0d040d240340039000e10540c0f1010140428940e1800e078180609071840c0542042800c42d035000405505162030b044d01c21403800c03c2c502650f50005060410f040d11039190780080390401381d9452810358000341c02c01c120142144140d01004036000812140c40b031400e1509082c03039641c441454444007590000c120a54245001d030800350460925205176042504188007240c08000700d60090034503d50400c0710301c0e896041000e240d01c0e280c204003003e4000e88203c020300d0521088213020700d11407000c0c002e4000b81020300025500400e00307003e070540c50b82c03443c25040084d15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 104876115 1250 104874865 104874883
    0xc0e0711010c210b090103030f0513120b010b071104020d06091112010b0a0915110d0c1403090d0f0206070c1806170319020c100804060506060721050417 67
    0x4034880c80403c0b4100d07451184140f8410100140003140903900350340b8240c07880c0c4a1410400200a4200b1452451040f5070a000f8002d140c020381c172a07155180c0c1d180441d150031058110080041c003d1200c513002c5284a0b00106c0e21410a80e001130b6581c0f40e14003004003070070407074004510141c203054140c440c1c80c81c914014850050701d01c2d001501d690701c80c2c160361170340c1c420740d004840020070001c024080c5104152803074203074242d2410081c94803410440101c0c100060740780c218000c200c250560f80f080c406142c5078076114440200207146080c008000145101032418406401054407155240440d2142001c030381d4119080000100003503620013080003002a1505003c00c80e5003800c60001785040480c42d40e16411011a002e18104003803501d230001040c1800c8641402c51044034044100c5899418619150707500c10f0ba03901202e8502400c240063351070241495000381c00030400780c008030300d808030401242040003802180307840c6016012a0705018070341011140d0410004980c40b2401d0002d041c0314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 104877365 1250 104876115 104876147
    0x110304050d0e19141201092f0901060c0b0906010602120906070b27120a030504020a051005070203010b090f06010c0c08060711010515010503010b07320601120c0e0711010c 75
    0x4201170321100410309030303800c0070b170000c02000e100c803282241c2c040e003810051420b4440503010301078402c03000000b403003070042030381301d6004603155558000134402c448140c01c0e404482e0314000c0c1001c0d403601e50002d40e654000d48041101c0140400e00f50040d90700e200441e01899006451409107040480c018040e00040700703860b85440034618000d44041001040709940e442240d070003142044841c1030194003824000748203c0e8403440b07a10001c0307803070340c0c0710341513803078407001591316540c45081c5481814210346082801d01d114441100800800c9600150340550002c400e180003100000c06140c0f03003159201b1f540000070580145807c01a47d10b500c04440c01c0707004600c100074002615103c460b1000701c0c4544907194001001000180003100500d03009100f030034410031589140e0b0000400c0d10707200c00b00909816091104101c000c4030541000c10159025211001081c444407280b540c1d807618409142c8181d101790704401001909850080c00c10301560070b0004000d1080c1d0580d01340003840148060a402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 104878615 1250 104877365 104877379
    0x80d020d0b03031831050402030309030a050303150406180c020a0c0b0307030c0e0d03180801050a0905010b01022e1b09090501060207060212031308040906030501110304050d0e1914 79
    0x1c400340c0d100011041c0106015142084800000c20300501601c40140140c9c0c252008011910301da8500f0003d41d41401d01a1000d107850742000100c0e2143e00d6001e290309072055007020018005081d038111044003030560040006090980340b0410381c1080f080740d0000e05005000d40b00002c659080200452003685250350030468140169010b480d030ba0452403260340c1140e00131603040300107409a502142e140380b0f1901f2852900d69a04419806d4031022100001c00700d44641c0d260003084003d0052412840003400540300035004c0240b040c00c8040400800411038464001e4484038a503990320032201c850004500200103550000060000a11446242c0410345042c000044c5a4800f041e4481500d5481d8054882503020540ca109903410240503c541caa40c0e01147d840058810b800400042140746008210716185003801c5085510003009910361349400c00400001900214080c0e2a0781402c1c02c18a40301c1d01642c0c0824414844a2485c01e51b050f0180b8010840d15500079214440c448112481 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 104879865 1250 104878615 104878639
    0xa051b120601021006270f0609060f050f01140d090218040c170c06070c05031f05010602030a05090907090302040f0b09010b070f081b0106090912030603080d020d0b030318 75
    0x513004c40d81c071841031010303d042580c071a200310698000c0450032045080c0d00461406070846401e821200148e10801e086999108200f0504815a00d60002800f04032078002840c3c1e8070070006031405401c501c074030b400404c000411003011200b070b5010048903078010f00041c0700d010105413421130591066070180e4584c482d00c040014a000f0030425421800d40c141d0140410701c842c0c81c02d0000c1c6400c90501200c1d0003000310701c086180d807000c004031040c0e80000d040340d400715000050039034115501a0050003c5410030440040038075001400c484840405441400340fa50711000b00b00c929400300d4100030340c040e06100c03003101403800e1508011000d00048810762a6641e0703d40820301203124021340144400040c0f00404007003a4414081c0c44c12117141c16203404560b54034082542110203a03009031b0070643c2d031181c841c82030180c551040d40e161805810100704e06415078071500c8031350160280746140f4540006d0118802d10503034100c0008200081c084948030290002c03101d600341c668004a50183d1084010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 104881115 1250 104879865 104879893
    0x6041a090c030c061305032b0807090302060c010e0d0504330e030a1b14040c09090218060c0f06130308130201090e070906031b080a051b12060102 64
    0x8011041d07600900038031100d60f2010501010345c1088000e68180d00104c0d0000a20752024070181d2038401101203203408202181c45840c03540c83d0020031400400c8414402c024090303400004100030f40c0e070110b4440b0b07207801e152044139001d042019969001da0080c0d140580c00ca54004020b001602c00030940e26029404127840603002c840c50482c0d1452142120b050f410f00b00c0c2c040e1012002d5901d015050300e0b840210f5480301100c3c000e0724003505030311030482c88007000811400b043c00c8803090b4045409100e03201a5900041940303001cad000381c1004030703400202e005800302c12401c0b150745040094800b640300d4070945044c90311032580078810041400303124006200721411035807001c0d65540c5a26005116101ca4514403000004010120706100840c080403500000811010340315170745a903210000c4a0a0000003070554842c2100440da1040b00501d103418030707410a9407907074480602c2a00050b10358400d00605010060005d40e030a1a2000040341c1807000e00700344d440740c4141030a8086913546401c03015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 104882365 1250 104881115 104881123
    0x70e13022206261b0403050303010305060a050109061d0c041a0d0b030a031b0201020a02090a09110a080a0b0c0918010806100f0302040b030109080d06061103040812030c040806041a09 80
    0xc3c291440e524070000a5400c21848094461400c101d00456003020b4403640c0340391940d0f00a0b04242c4544c2d100304100300401303002e40141800b41502040c240805490001d80307008100300311179034070341e98100d07030b0001074a8038075100035540204214000000e0389020450001c2c8654000108041003e09108100500b81800141d24420b20f50590750aa070059501c01c0503640c6034001c000407030460082c40002d0001d40da030f096403140660301c0036100003044201498000140c041c0c01c2c603000c2c0905400034080003840c002040e8004071641040070386071140c0c0e036000d20f20b22038451000029400520004010009900c20210f03038181c400880446032a510760340f4101120060700d114490040ca2510001c2c001401d0175003108070a9031001c1c002107035000155a800c00b5075009021203542c4030f6950300d820000a07600c01d40100011943d031028516044c1040800394541003000000350a01e90004007207030303510920900b01c0e40100b480c2c0090b6075140c101854079100300841403644404441d421b0020450b5090b01003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 104883615 1250 104882365 104882417
    0x30f0309060403030513090504080903100902280e04050106080708010905100207020609040908181c0f0206040b0304050115090b030c01080a0603050106030501140c03070e13022206 79
    0x92240b03003020b15581d01164958820100640100c0d009030700040c54107424001c41d070050388101e85442e154100c000915203040350304640e482e03142c1d08000c052400750701e59003404500c098240181c2c2c08120174500b04101c000c401c55102034040100e060800040c46010342c010400d4600b00c0003603c1255a5866881d0b00361001000040c00c0e540110450300884c40b603d44c024000341e48080c081e81c0c1041c00d440009002c0300d8204c8010f84412400094000341030050100180c642c601c2100c03000b6008103058411001118020002048000300c0303900d100541d50345105990040c480000b001d65a4078040c9001c0c0d0103403007068221125003d21200100d1251041e0048540d47d110140c02480c03039031408001161103010242c0588140b5a403040d002c0041542801140040c600a600115003001508040d1041c0c01c8005c1500803807490031700511000541c0100c0d0900b102d2000c07589641040000c408101c02403040c40b403008000e21204030003600c1c11602c03844110860707420741c0340c0408414036061154041442c10f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 104884865 1250 104883615 104883619
    0x31707080a090c05190302010207090c05070809010c0f200f011205060a0f060203040518060d0b0705130303180b0a2a060606021b1804020409050c040c090302030f0309 73
    0x1410004541e21196409280c0290082c9241218190765202141080f039011410031003c1141d494240f043d0750701004480000c050b0741004000700b211400000f001d6004d0083c005203038078400100c26110740c2c840c0d80c829400b10f40140b00c800c16500780c0d1401607800d1402a501c101c1d00d000480c3d8003141c601d410b02d006001684103071115078540d0108100c51000389001480142e0220980c003002c503920f10f05130b8026003d845c0e40d8000b190f44501b803030100113403c01c001d41011400000841004000c0d181e6107a011101c59128600703122540300d14074150342a000b00300a080c1c1c55998a8000006e041c0c2c40200c084c0c0c42080e00c40c4212906d03407141d005e01e409204620203035000c20040e1030101c002d135900140d6020111b10400c4180c40d41703803865845000350340711540240010b0703002d6a02c42002c41c101c02c023000700c0a50211405011500a07030a81c1d0651200200080c1c85130b9542c1c8051018020107000031204080d0040040104401d0500b0140102c0102c1c00f0682c020f01c41e4820060701d816000085030035803540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 104886115 1250 104884865 104884877
    0xa06120b06130908040b0c010612080909040804030f0c030303140c1b190501050f090d0c021513060305090d0201020310031101020f0102121e0f0103060e07051507031707 74
    0xd56018440c04050406001c801c4503940c81655020821100150001d020311031504c0c0e9903401d02500707423801e40d20b00f500b2288a129a408100000803401e40445060240c191010880380c0e4550800c605c4600442c2d0002c0e10300984010300703400300100500c0701d1059030700c240c80401401c0c1d811182c03a519070038200c03000c4c80181703001c2080840002203070300d81c40d41c42815601101d9120100d000c1c40203c030414074900308e480c5c2c1e44580911a20400da01c04942d842580003000340514401c0343c0000f0408060707032001034007925451440d0b2103447c22190442c4c2d452110401300c0c59040360388070700050003000d0407038106116001d442e12604c0c17600d1043c02124081e50610030003a04060460f10f07110021500010028190302c21400080003000342030005d420b50f41c00740290a10686801c09915a0300c40092400a00546000c0c0c10840804600505541543c2e00040000f4040e040071460628081d0300c0e4000315402280d0510340340540007031400410b0303100e00c01e58412000d5030491010941144090780e000f030220351 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 104887365 1250 104886115 104886121
    0xe010c090e0606040305160303030c021c140d0c080604150308030a05070c051605010f0309080a0806040e070b130b030906011502011409030306041a030d1107031a0a06120b 75
    0x50a0042d0002001080540703401d50760b0f0348a41c68442810442214500484010818190117124a1450712082c1c005404001440d000400d80c5111540b40d01c01030081c00a0481c01c08220300c07058a506050003001000030076400d1001030140003044a5461245003052081d0304c0d49544c94009500b101c0e0b01880b000c1c25511016600009010b00030304840c104240144074801150301000181140c0c82c0312001025594240000108080c2840c40c00c201814103007900000011005030483d0465101d51810682c0740c0c444030001350203080000e540c100d4a1051071030106072280c200001345010301c040100100380b50784c3c810b000e40150000b1106043c030394110700c0040040e140d040e0100c24803a5810302c0002860041c3c80e01c0c02100040a03142e00b86030758008800c000140c1040d1086000041c1d000d40786001615210b00003d80e031750403c45035441000b58201c0083c0483c0c8007003040380040c5510024800d040c50345000340c038101040445078004410300303101c2c002a01f01028005882440d07086003002100350703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 104888615 1250 104887365 104887379
    0xa09051b100c082802010b0102010213030f0302120406030c0806030c010f0f050c0a030503090609070302150913062c241903030e131e0c09090905100e010c09 69
    0x9405000743c42101c4104581a003410301c0516940382c901d05440d40d0741d000b00070036000034219000001150b056a00c1003110342c103140c8440c4900c000b2203900070350040d80c0b4003031890102d0800c03050742409040c803071000c40c011030440e406802403001c85020703a450800302c1d5500003c15a42c0c24250300103602061038001c8078050144100990052404241000780c81d12120b80c1c40b071443c1041d14041580010f8000c0103000340d0510900c08650001d5001004008140c150f4002403644d80e10382110840d4500300064549540d1a035415407801e4040c0c0241c1000100d40e80d020552030200c030300101c01c24052807502590720580b00700b6602801001030b0031817035206a4503201c5980101941c04e110741e9004014009070b00c1070141004040300991311994904022200c45070510000c2d882d40c01d103054203d070416040c00866490f5184240310044003440110384034421100c00c0c2d81d1900c458001002440c1400035600070701c42d00203100014a060020f08020034a01d01c00c3c42d42c200e40010a2510002d00e07805c0c403c0243d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 104889865 1250 104888615 104888627
    0x50f12010c020624100833040b091509130203100605190303020c060310080f0a02190e0f04020414010b0a170708040f03020c1c05070501050406120903090b030a09051b10 74
    0x1018070b41c640001f98903401c41002d03507504010b03080203212030090782040c41c0c907041030700071021b507410180c40e826a0780c00c202c009515820140b0440c3ca00440d0040c000606184154100d40c0616401400381c400c05400b4003440c2018103800d0103164001d100340d480c3c0704170451440e8400021070707405602034140d60014108101c4640e102400403440c4405400300805c10440a22156104044c0e0000901000509105203c4224030965100218440844081103040078110209030b0081c0d1420700d00c0a585e6070740c03000a00901001035441c0010040b0400410501c403004014030b61414140c6801303000241d42812410b50100440b080000a03a00001140010b6031103400c4013503951003401a513200c2c0e801c0c3d07004100a0013009411440764000c09444078103100045c0b0089018050030329120345032074141700001c3c0c80c12460382840001c0a0352404080e040c144188040c80140c5000504240c3d281010070050025116046040d01c4a008444041c0c580510b45210300c3c00c46040641071682d60700070b6039021344031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 104891115 1250 104889865 104889871
    0x2d1202010e1e03010f1a012115060e0a060903021306031202070f0506070b061309060c0c0308130b0106110c0303030405071503021201050f12010c0206241008 69
    0x10300016090714119980c4182d0690402c0d00381102100c04902940e00300360a458030074144075040e40c0741c80e00c19014a40005c8450300b6042007070a04120610790b445941c54200512984014181e181c2100010a40ca840504004841311555a020704a0002c07040101c989498803e090100c0c034641810401401c05109071005240a40b01c00602180d480c2c40e88804030a00450100068000c003205102211401110001411054425034200103181d0b2301c0300c0c002d003009404180f09034000c3e400360b04254941e8200540c416131004061048140ca8103018091142c89001140802c040c980041c000c00e0912140141e10380d0083c0f944e80030341c0d2034000c00780c4001c510803802c0411409481e030306c132159071030070401180120b01c01c01c000c04100e031901c8800c00382c8000d20640ca10030140100b003015060700c4400e40c0d003415508100c035840006400500044e000144d1844488125400d02001070521500860224441c5500b1442f0b10382c01c2c546040c40e50007051000d0003a50f409050407035804600c6210390b0b00c1c1c44e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 104892365 1250 104891115 104891117
    0x309031812010c030b030d08090706080606070c03080706050606091008060102070807081014070504090c030b04050f0105120f1005070905060c01050a1404030e0906010e0d0803012d120201 82
    0x81d4001d80c904403400e4544032034519003c02d403140d002e50102c0c02c0402c01040803072464a409007490400914442c2c0303880c2a0321854080107105004645643e5850040f69581540550f20240c3c0aa0340d00e403503400d980200e02d040d41d0507450580088c00d18284a01102d28100c4014860201c552141100365044200646100d0451281c0140070401b1001000240040c1001c44010000b0780300345a50355050350500007001e2055944402407101c065000030584098418004011440e1907224100310300030011011101e510505103410701100c02c2d2070200c0c00781079400581d4880c0b860b41e0884002561241800b80e1f135911548664007070242c023480c030b0b408250010010b00d0040b400a0355600024001e40086800c0d480a96461060200c0e10710188540703040500c02c0c500d10300c51803405440191150441c400058091032600c2c001a10703d030300c614900708020700c0045c001d001c1010740d4141103006030030034040c50034010020340c0c00d441c002c007c07042031f42550b0120024401001d420301c52204410159a02d04034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 104893615 1250 104892365 104892379
    0xb0a08060f1203070210110f060105040c030b151e03010905060f030f0703020d021206072c01080a050a150602070501030f06050d021e04020d020901080601090602070b1606060b04030506010b03090318 87
    0x8161009006082058548d03600078003e0b94100020001110144142d42c424145040481541a200c551402c004024402546900c03211341042901854105e0002259001400400455041e1056000c0c502440007520008440c0301d02e01309040d500d00ca40d109035042680440010001454030040024840e03102600910303400143c68882841c1000c01e03180f0a01140c1c9102244035044558450300120003640307910000c001c0c10b0200042c0042e1009000e407500181c036440001c100031416003004002c947c01079001c1407507964a0f4402500c1724500d008881c0044d051064103444c01d8040e000d03040664900606d280190021a802c000c41041c070300701c40040503034801c04001d41c41c1d83ea900c0a00480c0d0034544002d6501c0391544001480c3c580300500440c10b010700400240031840d80042c10b0000d44411840e110355880031a0091a03981691080c02408242000c5004c07499421003005401204c2c422001c940c040d90700d4a903012200e02007140d42c05119031080c04002e03425545000ba180390141c0240c000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 104894865 1250 104893615 104893637
    0x12a181a07120c0224040302090604090c0b042c0627010603050a0e0105070806061e0d090c06020a1101030b060d180203060603010e03031602070b0a08060f1203070210 73
    0xe015202d601150010404240884055040c52100d1648071202c0360b45100782002d042015603124001e03400080d0107009048001400c580b40c60340302c200005c5e040580301545664401d4503100c16445805031240404030f09048055403241100c145c404440c040c042c0322850b07616039090240c046200e046516803440d551190965911a40380141c0c0600110f075000300e840e260842d0038909403407807061003c16503071410042020342c90b40001e180d60000d000b100c0d001d560340384656008030000034420040b6801c03000095146003403038903548081001c603c1001d034011099580c1c3e509030303204c00c004040917203942c2c83c0b540200b42035807081c0e101038101080100060b04028220219804076158180c681040da41544d611100794a002c10640d94440001c6000b4840c0d120b0148044c0c2c0c480c08084d00c4000c24045c8100c01407100b500a0100c00701401d51001c0c2c00b40c88042c0400001d005010a5940b50701414191400700000e05080740308183c20030141006600e005d81c16400d015800c40854004004c1158072415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 104896115 1250 104894865 104894873
    0xc0302120a0803071e080402011b02120d02010b0a0f080303010324050103031214130b0a02190207030308010b130303050903070306020d0f0605190b0d0b03012a181a07 73
    0x514002c100590700c04040403c00e203908103c86170303181000c0003840a04d03010400140c0c0d101d000800c200141d945810031405241c03000c5510100c0ca01d100161501400f000003000e181e055109071139010003190b40100281e0303120b884400c0e941143c041c4032050b4108000500100351640364400ba21003c0d08642a801440c004000d01140c02c01e0b0422030004490031104c0380d1024541c0036540709400c000d41090564100700b0040c808441070300c81c1c01407032861050000350080d059079042d6001c600800c808075540000c0420000d480b449a40011008a004a00045900e00141c020b550100d402c4030320103000a425910240d0300c41d0000c2d280c4c1c85d07141c0f007090400300001d012400600302c0d400d02d9a030080782190b8810002c2040c5d070700b2500998002d00740d51a29404c4848207081a404480b146154a5075942c2d90b0183c20303006d4400b81034441d40660034005003c15411003200b414506016840440c91900d0081c1c008031041002c00d060040075406010060101030304403051340d503190700308941807407600045540e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 104897365 1250 104896115 104896117
    0x608010e0c2b1407082b03150504090809090103080c0f030a020c0108060f0a03120906030b0a0b03060d1b030606060c0528050a0b0907050312161514150d0c0302120a08 73
    0x10307a40303120000686e41482590041e00c0d01c5100010766042c180500301c1360072001c200c2c01c0c2681c407409203c1ca45901c0a4403d200c09042200d9032031001070614501582c590910300919800086040700911600f407450403124804800e4130320501c029800b91548645040044806c1100030b030085502a14201d03c054069884802c41b070300462003411859681d407072503880034000700031781d5100e4001d041c18000300035059a90700301104203541500342c42988035107448011480d03400740c0031801404101609055500e200c0852603610823030f071080340180a01a12000d0880305403c00000c02401540b1a214094a2060030800c400003003180318195a202039207a195a454600d81e02c1095811403840300a0055a29091107d0000fa00058004144900b500c00d80308945215040c2d803408038030302e03115480040020b034a411703006012641d04140200800c0300341c80a20044107071180548950032132000381c401c1c1400400e2655103500622107102c1e10381755030288600d03c4c404000302c6829002e074400620000300104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 104898615 1250 104897365 104897383
    0x602120405010c2d050d0e09180111030903090901120b0a0504030201110a08010305060c030c030103080309030409060602030a02010c030b0d17120403080709051509130608010e0c2b140708 82
    0x51544d9080b0f00e0740d4140241030900140492040014082003000300d44c55940c4140c0e00441d0031400740c1290f401d100701080c0140342c100201d0f222900000140010458008054148400201d0351400541d984040726801c69070004001000f02910304000343c10764406034040ba034404c0c000e00000c181c00f1044c42c00480254801c20591010460200052003441020230407154442c003038889851450400542d2030f1040c1c001440020100100080011147c010510554009200a074070500219494090103503c0f034016006540043d8640f1030740700c2c103182c800d02426422290142150001d50680c0d118060548050141c030f501c001010080c11130842214000303d481140240d641c1c8105003003001c0d0003000d42980783c1c07240740304000c50031041101d100140b00311031000104403400131044a500b041d950141c03266900010701546400307002100c20601103040c41039690f04031503600321403403040d4480c807050f01082041702182d908442008000303110648108001c0766031307400315030515130f4401c0307401d02e048001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104899865 1250 104898615 104898683
    0x70f020f0303010f140301020307021903030608120a030e0105060109090906021b1513080a110f01050c09040c090b0a0c0206070506070f0e06070209040b060d05070902040501090602120405010c 84
    0x1810100300f42c55440424070341740417046000b940703942400700d0000d50b140703190b000700c0c20b1410542c517980381003500a40c000002041142c05961030b10401652403001c0381c0141a090010a0a008400001140c10300c6000d104945c1610f54941c0d46090410460052030124400c1f201c4c07660801c5140c1c3d100900313512940c00c5042101c0181a2101e4620032100340c0031024102030301c2610303041541e0740024900e400b56004201e5030303d007400c0402071901d0b0350307443c185c11821451070710751130f040500c00403d141c600100003c505c01d980a00c1030707400c0d01104452840041c80380c0101031105101d03015106128000c1100520300052500b803c10005807070340c500b4290b0a445150102e2400941a040d064020145500b41c20702183d43c0ba0808003282c012130080c9200910040c4800d040c03000003403040d503079102c1c402c1c08260003404031030030340b511801e036040258058000c960100c0d42408000a0241c80000c0c22000b074040e0407200390515281100540310034481700e2044a181030314056203010038407080c0b1150022804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104901115 1250 104899865 104899889
    0x3020d090609050705010804031e050906070624050a03080307020c060a020303010608010b04030809090403020f030a020a020f1918020912060a0e01020c12030a0f050403050a0f080f070f020f030301 86
    0x31900c0c003c0d16000c110381c0b0072410f01948404010200b0780020050f16400c1415610201c2c020403042c04641c180b00702c000076544058007060107824400c3c5540301e80c008121000681801c1c50141e940318262010502ca00380e804164848d00344001032500300510307007102c01c40c012189908040d90000d4540d80042106c50010b910101c0100100b65101d0005401486c054441c0d900d024210b0301e40320002e101c0c0c015005e01804805001c28101803081140c0d80c8040c0085e01520744a5400b050025190300510341c060307200d840131069060580c680503140340c08018184d2002a0454903110910800c850040030b202c61640d8280440d01058850090b00f0201c084050302422240c0340c42c0c0700c8003044444081f0f003510180c0c4180001820702e80005007000c803024502080c5a16962295449005001e0f8000e603070104500300014041015041005412000466117038110303076a4092404540100c02241d42d5100841300501050740c95010b00b034a024400003520582d404660303c00d1850780b4503402a0301100010b14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104902365 1250 104901115 104901131
    0x30106120605040614010f0215190b0603090715050702060d0c020f07050105030a022203031709010507020c0907050c010501230d05210706061508060415090c03020d0906 74
    0x1a845001e000c0d000c129010856141030410002014070b03070800c19070600064540d0505040e0080020308406c12041c00110107514004a03103200c0003141d21003100b00f060910703840c1240d503c0d0003c1503030300c580d14000007424601c6c80c0c085920b45025841a104003885400c120b07420141e02c82c1d10046c1941c14842c4000300305d110490000070719244900001e400113801c0442c05001c00da91200840ba00007440500161b02c07015a11109640c18841c200000e0902900c0c8000204042c0c0005003050720380b14002c080d25541d51048592400d87c3c9048651100503048840400e10a00d004a43d194000620707103019410320124800c2c8508681081c1c01034401d5000044007941c98040c8050150340e400815288803c400d0303007540c0c3d00fa6450031603084000c0703401c900c0010120710b410410240c402e4903802c24018800e440ea00c064a8046154012601001504100005065052074001d41d6601c1c100340307054105541ca0003941000810b03150b0501d20405400300b01c11684c051050103009105409190005240300b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104903615 1250 104902365 104902397
    0xc08011406011704050d0e01050d060806060108070801030b010324180c1a0d0903050c06040b1905010e06040b01020c0409051f0c081302031204030303091709060a0c0203010908030106 80
    0xd0f030611080807103800744410040000c101141705c0704500c0550612002d214a0000142c0759030040c00100c0f002c8924008000510100020b101406008281c83c0c150043e200e080301120030344800d0001820029100004000084000c20303051141d55220110000001030a0004000e450b003030013603524058024031418042c031000c0304006000744848468810700304c141c0320072000f40b4040d81c0d6031140c11035651100d04040c14010012510840559800d456052510f0302d024400030030192403445000c485070710f0380d105d9001c0710302c01c05040c1c1d03509000d46d0070a80e4941e030410000d000120340041c114002c840e041426034560740140d05583c1c0c861000350600c0f070782000c098050b40c030a4441c5060120b08103132429401d540c1207020b80381c01c0008560030b0186800a400800d1400c2c0483d8403258141d10002000814598983c5c0724460300c520035034140d6204001e13580315984134000d60814552104003001004030703384c0200d00030058107102500204a221342500c0301c080e81e4000740d114501142c3e00c1d000402d158 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104904865 1250 104903615 104903627
    0x6091d010e01020a200a050d020d0813030503040618170702030105060639031315030e06060607060908030c0304050d0f0c20040504060f060509060603130c0801140601 73
    0x901001c00007181070060141c0c00070540c0c0c0c0030f40c0007101d40300d0b02d03e095003244220a11003d00070b1508401140d09079484040021b40e11201406510001401035001c1004481c0c00c0d40c03a41c0c1e8440d0956122400c1da115030f00c8540040c0600702000c101703140d407070701c1300000a80107200030074100c06003185d03aa0301c640070741c0141400e480b00180010310030f0360300b00201c1402e590505070000f40c40c0e81040c2901c0080b98542d10743d5001d441d04040505103840081752160f4211003c403498420342d0f1450309a00c0c140660f03c00141c09480c2c40205188841e08113000140302424080050700d0b0082c080c010220340c1c03d00702c1d16081d849600c140d58040724004004100418088100402820f0307500340d01d825a00c0e1080c1941c002c103500200d40c0020039803c80d03500d078400300301c000d1284141051001042041503003400d00e82040103024420030301031080c3c100880010700e4070f0054100707881458050000c5185030703202d03016001ea0014030002251904d04517107021420300000d00c00c0105d0b43d40812030180d51807c0c004009000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104906115 1250 104904865 104904881
    0xc03091505010801320408121f06032d0204090e01020703180f05060a0e04140414070506040311151201051903080901030b0111100204170a03021e0106091d01 69
    0x40119a0342c0510b12286a000081541060b50711003117030740712071810140c0c922407440e024440c02d9844c4c0c140014151405c1110314090042407451948941c0c4200580590306110b80800c13010310340704d1014107944210345440340da082026900526254461108030100c46119034201c495070b5000c6019010540c109440084842c1c10440b06451545400c4500100909130302410b0f019210200e00110f55602600c100141081d00900600c112010300c1246603801c8011282a6181d4000b01c541c401c2528011400d441500c41c09401c0354030b01415500c42c43c001003201c0ca49650400e4035000742c54113068580c0d001d8000c64900c031030b5104e02d40d45040d003041502d05803a2407500302c44c180d184007000004c500f4822182c420002f801c0101d910f00d0200016a4020041ca4400519000b001040c0030820a541c5c0144207880c910464110004092240ea59580480d16001005680b1550703040c280072141316003900215070076030000b05e034254403880e05800391290400d600c0110010220b800e115007201b8050303200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104907365 1250 104906115 104906141
    0x30b06030709060524070212030901030c030b010e010507051e16050604060503010314070f09091a1e09071206020c060702010b1309030201020d0504120908030901120c03091505010801 80
    0x1055908104c0065142d82481c1d40f42403102c204011166a64520401078801c0c41c1d4004008503d17007400824182c2d01d940c040c4881038002850580b440c01c11038024450b03000c5e811410394500c0e000030f10010054406910201c404d407601c0c0716001290200030020180c0d40d81007000c5001505001314891180001c0e2403036078225900c5440140020702011f503004050342c0c1101d400c01c500804420440d0601c3e03007080c58a410000f8001e80440b40800c03ea80d464011103a500c5c4118603a4156000074440c01140d20001c1d101d40c7c6002c2d10780415494040c0c1c0100c03039617030050304503000e076448155185480c2031540100306040750416008282002d01c01c40138801158003080900081c021000c0c2c2c480001e0319031043c1c0000000899940e55084141403007507040e9240420024010491802c090a1444d0386c00c00c81c609500000305203130804980070303401000b52030800300103031510a9482e620450034000b60207803001c00d00415603a60414004100301c400005080d4071550710002c2c1550403c5404c5082d00c0c40703003003220303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104908615 1250 104907365 104907371
    0x41406070c0b07080c0d0504110f04090c05040506060408070834180905160806060a06021506120d030f0e030405061917040602030a060905090307060b19030b06030709 73
    0x107000c01c071085805540882d96141a44680c1d4803101d0030101401801c8014202d1454a006c0104214403411104a40340c400c55815006d007001e002044103403081408000c0040410b984c0412441c00c1c03c0d000241c000000500306c90410fa2900601c034a4a64198480401c40e031000300c00811aa00340c4034a207800e020104c000304002000d400c07207001c420716140f103280c2c1c185040c0380c110151081c040d4040b0240950001c1900c1c0c80c0c40c441c0b2a10b080c8465603000320310040c0290404540c076440c15400c00c07411502c1c0e41c0c014207050340400aa000b040600240b459400c119540c06103e80410184103101c000036a5131000600681407560780b0007201e00c4020a400341f41e01c1000140401ea031014140c5401c00d88c504000c2e108c2c40115002100c071040d45805c0f10814415801c10f020801003680c018520031001150108205640e8841420950708165410740e10340d001000808081155034006001080c401f4085030100300000c80d90341d40041b05a0f005945101d40b010a10686240621030390b401860603001c24 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104909865 1250 104908615 104908637
    0x7110a0503061602011e0f06080a030c0f02131409070812220504020304050d08090a030806060c15071710030309150e0607030302070201030b0108010b0a030e0c030604140607 76
    0xc00e0390342d00d0181003020000d02c000d0441500d030b4402d40195403c072804801000c07038420014490000344c80d004a440b000c550900d5408502e1440008078041416095a18801001044d80310034402010800c802d0360000381820a580072303210b59005800114a00500c558510301e01601d5050810b0b070703150009400303038010105200000d46100f040d28881080c1404640e41001c0907804864024032983c0002d030818004020081881408200031030442660b807209422503469600454482a8092000b404141403c1c085222810104050306144d45c6d5a01240c3c010760f4607403980c144c0074008465440004010080101c6c02a892040103034001c850b0740c504580d11800c50382d02810b00c8206004540a0a90781141200424400c880b0028980009442c1654402c8030342401406540060780c1a80072a0400138081d070254404c44c880c41c101c580181c6094240003100c4811400350071610881e104501c100404070100781c0d02804214000e80c0305140c00e4450990b040d1510b82060350040100e001d1190712518 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104911115 1250 104909865 104909869
    0x507050a1503050a060e1b07061103040212030307050a0507050c0a140a0603090f020d020d08030103060c03060608090d03231e0c0a05250506040b0708060a080a020603060103060509070507110a05 85
    0x2150840303d61403074a11947e086801a80f0140a400b0019095034107040c46c5c886080d120344c0c0254020742c000d0b98141aa0106c04140a41d02d100135200c00000400401140014520800280890621034400d0f02e00d158601d6000800070308440d0408841003d502040380c580d80f8100310014024403041c10240405040703900d034078184005045000c2d0241a030b04810404641d50041c3e5111880ea002091544950312410301000420902d050400400d107405004500f480c040e2003e030780301c0d840b82c0c801000b0498151b00110058031894a400c0da11041c00c1601031111703d24490018815000c07400003502158050b14809054040030b0b0000c0d0719540c04202ea20420f55008003241c081d000f00165244e03042000417500c1210b1440a0000782846c0134030410b010400c681c2c4450340303000c0c074515512110503840e25801c21803442c030107200e14412540006d24210040c01d110000d150320401c1410001045582d03003000c15040141201c1003000943c0005203d000c000020040500a89003a1403030b440303007414900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104912365 1250 104911115 104911139
    0xc11030306040203060a080f0102180a030b06011103040902070602120c04050a0b0c070b03070c0201020c100c03110f0706080108060f04020d06090f05010e010e1504030806010503040507050a1503050a06 88
    0x41102d0103030f5000400904d42e0b4aa43c00c82a004060540896070500d4250000304e000350010054036000f000b17000c105141c1d52405080c0502038035000781c1d81440c90b480700001907404000d5000c00161071b000600000030f20060f9803028103810f0b8010030015030303034034904d40c0d00b000c0a4800610107000118107101c180700540782c1e05181820f0300c3d421600c050740d13000c0781c0c0c01803460001c1c0d43d4041d11110000208012010360312208280b2854402c0c4c00300c4110001d8542004841c80501e022030b00000d821502c08030102e48603810340c0700101201800e80e500c0c40c0e0b140000905002c01a0010004036802900409c2610810401c04d0703409034500c1c120034554200360f40020821440004050039144e11001140140310b07251321440c0105030301c04002c000020382b510400d0f010304210903c1d00528041c0200c41c10450030030b000400d1240d54180c0e1a81455a20140107485c0c03038101030b006030303068882d0300b0002c106a103500070800c01034000308007205500d00450200401381e070303001001000501d081c00010004800d080ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104913615 1250 104912365 104912371
    0x3030f0203161803020a03240c050a0e2e02100c0507080319050f1006050c030a08040302100908030a0e1c08180303040c03030e090403090501080406021b0c040c110303 73
    0xf14103407a10b81100c003510400061640c0000c1e52000207000b0000c100000300a00c514146065214a120a16802c68803001c079a40c040f00c4c0c00114608020340780c9054466021030f21500b80c0203101d892211484116815000f0030b443c40b41c1d00c00c1d4080107480e14900e404000f4980705e405002000d02411104c0c0c20000c1250081502c010100d50011003ca40c01e021010707030761700708110316145c104940d10b804610710004410607180358040c40740b0442d010a08500c600c0854800c0c0710310074000c51502c80007441c01c4408850040c020740c01c5001d62030110309240729502a40a684e80541101500da0800a20714011221064a40220303603110000241130501c410601360341e000428280041607a0f01e01588844245070341d85000c405000010410042003041b144010549000765140c524003440341c028040a80c00035507002c4c0c04501d00100070001903220302d109640c82440381c2c10140c14420040350344220b101000c0a0b4280f80d801c0210ba495803070509200b82a002c202c103140c249594480c5015180d01e903c006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104914865 1250 104913615 104913617
    0x30e070f0501201014060a03020a031506210203071706160302091903110409080f07080f03011d0906010b0a0e0604170709060812180a0e07090303030f020316 69
    0x4441e03400c000210f000315080d02c0380c040d500b41c0f60050100f5450740d0081202120740c031201c003c404080f03241824400160001d495015159100b0113040d80c0b12a040c040941c5030a54000d0380f681c0c408100c01d42c2c8105205465a40d090715803402c59810310416042444a8201501070750030301190211344040060800d400074401d5094a8034050103010840c0a8031032140c007290403214148008150441c100c1100046902441c1c15070b0703456281c041000142d0710400005000040240100a6201c901c100101055441a44618a021000c0c45c1c6a040c980099218040c03d14a202d00c28a0701c0301000c00703050b40200d0741805010550b05081040d0293300440d4200020000071890080d11616003004980c003810031070303036a00c0b246103012022543e650360a0251802035030a003400018410b0001858440204107903420b02d0500700304445c140940505900300b2a0700508005000035017080c020040b40c0215200e80e92844000e040d4280076064580001680403024030410400035103103401d259246c1d0300d880d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104916115 1250 104914865 104914877
    0x30105060d02040e1c1101140702030703080702030d110304020102010f1104091e060902030603100207030c02010f030f06240206060307050d0302031308010207021c0201140c01200307030e070f0501 86
    0x7508121490442c081451142c042200d48440ca8100c1d0022020f41d2070788400700c004d000c4404060580c010a201c161589c2c40075a00510215002a018500003580042203104503400e091860400340300760b810800395105c807548000144030555038203014800c021030f90034100340406031210065800a22492080040310f40e0354101c071308802402010118500901e1920a000c1141c942725904001d5105903520791103840b480701d04c9038160b11607001b91030f513440c2c140d1a110f040b01c440d81c005552858104144608065130f900b03403070980c0e40c1c851080307102801e90b0610000c10140654071041c602c0c030f2410b0b9140155400701c400c01845540014454042d11403d0b108a954020316240c2030b0b1443c080c0c3c1068821a041801c0d01040145055000e003c08500803210341e15808009080761503044110b42020b800100300440c800f580c040400010040740e20400000101c1c08034095440759031071480214444041000400c0c0461282e06004501440a1400280040500c1c02c02811400c1d4018443c05040c080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104917365 1250 104916115 104916131
    0x1d0108191b0803070507062006240301020a021b122a060304050f103b01020a050403150b0d0b0601180305060405060c09031906090813090506030105060d0204 69
    0x40ca00403160081c02d0305421030b0f0702d5061520f400c0d80c82d00c50f140a60300004554040c1036111094003410415482180030142010381c42e1322a42240014241c200800f03080c1464061040300d032000d01c000c000c040010750141540322400728660314101003102c2030a120b14a406044003608402088100004c01c40a00c012051840d072501c1000080080801d40d84c809004420041070010100d031108850f4114000e44400111125102e400c484503410b0412041d518a81088859400d64903003100c02e52001c5101500c495030110501d0036603010b0003070f0b03400254011a0801c1003151145001d90200000481882481844d5000c14100c00d20380e28050300190081c0080703203169006000500e00340301c16001900c1a0b0b40c0ba8140a50742d0801079404440520036280005c0d20044042d0030380d602c84900030041e01c0c081102c05140ca8011800002c19641e280d03503a19820000ba003244010302030340c011030700c0e070500c0189441840d100b110001016940a0b0f414030003081020368642950104180d4100c0300028101c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104918615 1250 104917365 104917403
    0x200901020c060705010b040e0d030e2404020d02040204090b04051b160c03021e01020c0a0f050607030212041e0e06010c031209021e13090c031205131d010819 69
    0x4810031b0002d03001490002001030180020a22200d114a04e40307081c00003900322441195a0082c042c04c84039050107441c0c03002a9130b6900564241c220380000c0031911032910540005080341c1c4292b00c5485207a5442004405606060103183d40c4516600100100348002c00462200c500c1071203080d41849010145440c100007800025801450b0081c02482c0f5220032070400e030560708500e0308140d003d881840c681100e1442c00c418400b041d540e00301c00b900d680901d0001485441d42007504110250b000b81d0700d07034150030503009024000070b2040c154610400c0404000c03040e8195801d800464807110404d0420506903040b82c0c42c6034113181d140c0f0309000c068240500c100000c142d9180c00941c040251034108400d503010514000340c1800484003640e00840034111f150844111050041c0030f86540c42080022130542001c80e0340c51a06410528505900c15007034241007002500900c050750880820f00c1d04c0c1c644c1884880e809410441c00600c0ca500003902e00603040a00480000c002602d061107038a281 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104919865 1250 104918615 104918621
    0xe07231302070506010e060f0d140111122a04061d030a060c14090108010306090602070b0115080a141b041505030f0a060b1b0703021201200901020c06070501 69
    0x300091411900d41d101450301a0721000c00303100d007a1a00900c00e002c10004d02d806840682d180354024410058000282d43d40800d15801c04075506655585201101c9a003000c10b00030100c1c1541701e2243c030b403c0d01e4480d110003601c1c910700c503401d0b181c0c03003403241e0329102042240225800e40780b0718245043d03840100348a41d41e046003400201601400303011801c804100c015082114514000e1f00c80700c0c0c09a440801c1601d446c010751080d0360015010701c0c01000855065400301001700e004203001b6103820000d48030341000d10030a0f8004a10010041048101c440d80066030340d800101003a0180f003e825000e501503080003000d0440a07900114214030420300c500002103e00622000010405000e088000030f1f1950704211101c03680303000510002514410588183d8068840f44040c0d5406d10107107134201c10a40328460007401c007500c1100790200140c0c0c1c50400d104600d24107071002151341034908020b0040c2d800000800c0c40610300c140302d60441c40c0c0c1c000c207502c160340e40d059030626107170161810702c2805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104921115 1250 104919865 104919889
    0x204181a030307060902190605030a0507050a05041e09050709090b06041401111f020c070504020a0c0308090106080303010e04140105060102120a0203160305120c0901090e04020103022701030e0723 86
    0x500107c900001070060300700703001d1841612400d0342000a5503c1c404191000e1254082c0c190006204000900503098a0342c0342c0801c2c1000c2e8984008031a44817503500044ad442940c400c0081000090b0070080309a580c0110059480d041d260389042c60714000410303a0060441d01c103213040c802c1c50015064040001c200c42d480388114028011140e0224004041c020b5208040403091401407010100e041d04141c0201c482d0340e1010f41d0750310004010f0f514201e4848a020f440c50b40e1554030352000141540c2e0800156000c0c14404264000c0c6027440d241c605422a9101c80401850341420b040010702da80100c0c03c0040032207241c0c1c0745503990f50114400ca04610a41c842030f44442d19a40340142850b500401406201d10b68180402c42900c0c0d281c5900034901074140c01e00e0010b1000c03041400b070005e203030072603580040c418180941404c5042800c0400d81401911206100d482070042940340c0da80750003940c0340340c00c40d08050008a0300b459000c481e00940008401c00100400808640d81d40f26540365802c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104922365 1250 104921115 104921149
    0x15030c17010603051006050304050c1516080904060e0f040809010c140a0b0106080c091c021e030d030c170907050918010507030606020a1b090204181a030307060902 72
    0x305503840d1180034000300010b9815a050100003640440c2960041084034020780c3c105004088a070000e208005101c0e1401041740e200d103c003808890b050a1030302400000c0c0d05d21030f10229449848150601c0201d40441c0e2028412899020621002c0100700a1240d00550000d07101030f0349030403480058a44c100380d03540051940520103407800782020701040801c0f8252282511a081d41d0361601c0407540c00300305407038003241d919040211448604d841009a907054007100c080e140d003828187c0028005032111400d1110f402c400340004484d038a01401918051081030408100f2510920801000c444054141030021034251020076841c0c2c00c1081014000c0c40001c00b1040700f8035203080b041c041e02e400304020645540c2070001080c05140a40151400e4a042d0380c014085100039894502603401c4c640350310f0000841c0b40c80c000c941c2a1140c00140040c0c1410301c00b107294841c80034002c0c01110281580d0080c241040d111a107820796010088075040743d003103040400c90000c035000090108040c860111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104923615 1250 104922365 104922407
    0x4090602040f061d0306160e01200c040608010203070e010c06060503030723010603030806102a0308090109030e0d1a040309030b090c130e030d0c020304080601060915030c 75
    0x1c0b60f66020030140c01c0e03052541044d0075010681c0c8141560380409403501d05c001c4950140d40030b46c1c0340c4101d040c0100d10605240590b40c828180d042c81c081340d03c82090b800f54941014043c030712079040c24003c180040003108000c44c514989000e0041a01c203135048941d040000c06030940d000c1c000c003a04640042c24000341075075560703000f51804500da682ca110342d08a8415541c0e1803c0041e880610600040b04c1e0161908030300741d6a50130810500c0140d416001c4188445403228402a008450035808061814400c500d0340800500300178048001c01031400324140e046c540802d001a50000b100502e501e01030302c082820100625004010600504e00f5001c00842c07982080203040d48942c40100b164002c2030740e480151074554000b0340701c200001c1c0b2a070b000400d8a00101711901d00b5405995082501000d50b8107007400701010905072003243c003045005900104e4140304401040c040e440c0140940d06080c072600c0d1a108503203001044040c508410703d070341d500e44030794a1809180842c0d1625032001d412 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104924865 1250 104923615 104923619
    0x10906060b03071d060910022103071202130303030c110303070806091302030c0f03070f0b040e010618031118190606050f03010e07090e0106090503101a04090602040f 73
    0x410720503002103400d000021802070304c0540c12042240440710240c800f414161074100082c00b44502082104c2c415021841034944103a040d0078a11407036109014404e030425a2424a100010403c8501c4c01810101c3d03441008202c103242259401801169414200484e0102e607540050381d240520b4100d015a074000041040401c940c4007041500c1110121000e004503250301d858513004070b41e51030009400d41d2103540d04002c1490840302204070014001d0840c6d504d65111000e03945401815408071600a401080c24043c1c004444040b40c050096031801c110b030000d40c40140102c2107103520001d41608038034400c807091500c80242c01c2c900c00401c0c1d401003c00d410001901c1107260f0b920340d4410300e01842c0513404194141308070121342203603d1802d10319066900300082c0c103d08000203861001448100d42000600090300660035000305050340f101400c1a15250505007031158400d9508401850614a00580c0d904880b00700030b40c80702900c0009601c1e400c3c1c0b070150001d100d250003c9244103401000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104926115 1250 104924865 104924879
    0xe1f0602010506010906171f1701230412140f03071214070c0206090d1208100506040605040e0601181203030f0204050a0e0c0d020307090821190201090606 68
    0x40035000c3c59003a82c42039031241d03461500319030344450600d804002c0c01695001c242c1c20a01d101e500035000d0101c40d42c990140e0799a102020250903409031803680b0307035102c6030305005000c050303a06642a800c0042c0c50343c405140c907644500e5111481c5402c0003c0c03104e10300c0c4d4280380a402400780e540e07100c808500d00c4c0d0307242403150024040c0c0920800b0400590b0070300c510003808540b1040d140e40a00000e4650740000c0c1a16400c108554100300041d0f41c0040510f8940c0021031480449403e0b03001482d02c81d081e05090503040c8581e2442d46130011401607170100400c000c00780e0700500712011a816061200480d071a0716004032405590b074161502d20781c200310008220040503440d8215464483d8800708440061141d000050b070107207100b1150300600e2684204503144540740c0103a071102c960700d907042c0340102e1100607400701d0300161803031030020b40d903018103229201040010b1b00c4103907408a40001d81e41080820001213100f01110341c1403146074107110b050100d000b50003c02801d548200d080c0701d100e0721490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104927365 1250 104926115 104926121
    0x903070605030420011407110612090d050408060705090409050703050f1b0a0909051009050a1e050604060b0a030c15180305060103021c1e0201030f060f0e1f060201 72
    0x1d42a0346202c01c407101c13503841d0f1940e4204098240c80c184c40710408240040e502c02a00e4100100541d0a00d888868801180d9180c0f0000c0041003024850541603003011158546040007098a031001d01c80104011301c041c0c200015040e0340015507190903680d64111902050240102c00e60051a038030032844040100000401c0c007503003500c00001143c49944e008801e08000080f03602c0d255402107003602040c030120405420106400f400b41e0100d81004031400c8058048918001096420750450303000b00b03080054070304000b03100c852100d45000c0020041e442e0261907100107003004000ea50340d03180f0b42d917440e10313507c100c80c00441c2c12420f40310040341d44225043d0303074550315121a00051650020088104454042c2409032b0340c01500921580c0c1c256400d010003003042003501c440100d00082c85400040014055028101400040780b003880078510026080d04c1301c40d034032079101504100c410b012141f0924441030844a0048000290392a0130403c2c40c03d100c61000010364031500c200c4007094039a0150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104928615 1250 104927365 104927371
    0x60d110d030c02010e0a031110021608031e0a0e041a04020a090f0501081608060303041a1206090c0d091406040317100e0109150803040807030309080a0c030201080c090307060503 78
    0x30b202e00110b000c00c40b0406c4071441d000e0100400b107281c0c00350b5009280c208031318201148601401258001c8290b04030303040f00407526a1250000ba84000b40c424002d600e501c2c000d0390303c0c01328804a9410120034032000b5090000c3c0c50500341c051680d481250007017540b0810b5210038001c01030700440d551012030300c00138102c1401d17002c1c603401c0c4102900002810b522a205092041070b140c51019002610298100c070403003405004981e1502c811700c80400d102e05d44c242184104004640220f60710142e0401c00b01070307603200500f19840740e2042010461440500c03022141d0020391107900103000c0f060b034075000415401c074402c412800d1241001300010190041103911014004400c050346590f90702c40f40380048001030141c3d01c02c1c0700100004002804164100c04080009441040c1200c0e03121420030b841c5402c581d020b16010b6100303000400c02c0c55044804a0042c02e200c4000d4041e80d02d09403200140b46c10355100c001d04102020001464540d454003d5421042005083e20b070402c4d995400180503400503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104929865 1250 104928615 104928617
    0x9130605060d061e0510110a0b0703020304050609211303150203010e0a0b03030406082203030c11030702030d0c02130c0201090605070809061609080708010603061112060d110d030c0201 81
    0x1303444003862131a00c0540d40300c201c0300000c014041c0c8005418040319440c04584e0034440314401d0030000380c0001d0f0300c250054400c0039580c0e401a01ca1625050443c41e1100c0070b8110003051b002070a0501383d007141f516090100c541800c01142d690401c0c46681c903403440c0c0030f07480900240d0706200c0541c90780901e03070004d5040b20151a03039051161145055042101d4031114210b074164030400003008900e02603100554001d820b170540ca400c4860715000c450349140703540011800030b940d03682400c04403038002080f403007084142d1005605000c016070110707960790900b00d02e100601513450388110842d52803c00022410b201040300b481040d580140181c0030306501c1c841110b00c5414103000800e031600c210320300c3e031062514600428464499214009440001c0c9900c0e00800070f4605020a102608104003401482c0c407000009072a4076600b0101c081344c043c0c2840c2014403004118612410100d201d00d246c01074011210b4a100001524180800e42e40d0001030581060503001e141c0300380354000b001c000d4000e0007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104931115 1250 104929865 104929889
    0x90509180f12030609070e03011d1c141b07090b1c050d0806040b030a03090806100b0d0509100908070303061502031b03040f030b01062309130605060d06 67
    0x8081e06640d1556502000c2021a18050000a0340d17441c0c0440c840c2c0c0c2100241c00e0450084000304042402d560251030b10319083c5016002d40c0301220003c12000030bd280748403000c2088015650741c028188010010318551440001c070b5182c2c0081c51789030407500d820390190110348903242e89a0102019005203203483d48144005140c5c0c00d0200d0102941001a643c40800703040c07090101302d026540b2000152002c1d070415602c0c00820300702e481c100300c4c203290a40281c543c0b088a41c80c00311458a815402000e0a0002d4401c0b0010400710003084251085410005400700302c40e59291855807030b0194003000300c2031040c1000701175414011580300a1012a0107540c050000d5071b00e034140ca0ba2502c0c0700804044c016481000b2440c0b404c01d04c510700d003401c9404035003504c0c40e203a5100055141c106154009803482e0345100010400305030014000703440341c1030f2441038002c80d449848180d80a409040e2107076004691010803406100115800500034041c010101901c94101082040c010441801599035031a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104932365 1250 104931115 104931133
    0xd02072a0305071203090b030403031d0c0418021f050702030709050f0604060308030106030c050d020d1e0c020714032401080d0201091106070c08061608160903030f09050918 76
    0x2555044d00100c1070709038480760050391030a07021100359480148250105559149444007002d000154030486c00011402020b055100c00104800c0f10784141259005860641101005840307000203030f90501110182d6034503880e0702c050300717580340d01c68910003c1d03150041c000c0110b90b8119551103d0f0080c590080c245085a68034810702c01140e00c90302018148001c01d00040254034402d411010460001d854400d003095008007209080e80c00c0044142c2050380ca8402c281045002c1c4046661003440204091014420006010703464500074001c541c0012050007580f009510f08100c3c01d04007684108280e80c1071501d060b501c03450b40e0003e004010150140e4090240e000317205009848102e904110762070505250351081294a52260314100d4803080f4603140050900700a20085100700803102924049407103801000f042581c0040c0072042c04a400c00c480c01403030303a100041800762540b40c2010700859088000a40c2e03280742ea54011940148083d04115110000003070b508100c0144400711171140d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104933615 1250 104932365 104932379
    0x102030d11120c0c070308090a1a03040605131a0703020714010b1c0803010b0304030212130905011a090d0507050a0b0405130e061f09021b0d05030603030d02072a030507 74
    0x200c140701c0401303080e0f8084003003400441c2448004001000c0020900141e9540d0751120700044520004c9170241c64002208110a104440c021903a109140d02d28001c00b020715680d66483c800e06000001c0312210000002842580c06903044501968000760446803508510410501034a8042c15550003491320104051540c0902c07002d03802d4081e440700c10075041d0b80c00d2111203604c507000180190114130070182d8a10458544800804150004c2c3c0c503210179490901c4040400c2d580181c0c0036690701002c0b40c421108000505083c0d0b6402d101c215001440d0070b550741480e03454403405402480c0d000034101c0c0b000443c800b002e0014000c550080c3c130120400b1449010780c0b81120600d407110b16141d0000310025080103400b0400c641c0340152010241801502d0340240002c03a04018001c07102041d0520740510800d00030071030f10f1000d108924016246240c031001003616030190745e025421468001c0f0b500410064084000d40c05a9040710000c40341e809070320039828100c28180301c16651806040c1e4041044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104934865 1250 104933615 104933617
    0x801020c010c08071704080909040c1a0f03010b0304020d06290901050d14010f020a03020301090b09011a0f0702090c071b030809010c111002010b010f03061202060304020102030d11120c 81
    0x43c078061715034002402d1029800c4180302c03001442155480c004102c421056600c0541407030095002e50b20054030241030404c20b00200207006070368500080103001c2c8600070031811040301d0640c1c000758085a12901c580c8042608042e02000040c83d00d820810301c240c2e100b030a03100f286114401d400c012103001100e00248564081c00307000722a0421040c00405000c035516540c9000000d258000002e2803a084d0f0322008100e1b00f1120b980741c0025000001080100e54034000e030500134804545c044140c0d4544256010002c40c050000031811074003280c0303c0d0580884500396074469401821009061030200d0040503968000d0f03a0449440b00c1107410001062815154182983d5000460f5881c103d54240192140c10401400304c1d0520038200c0c3e040c0d8261110703d048595280240c0020880d50113500014005021080c0c1382020507251860030005080e400c1e026807103103501964000e96079242c07400100d0943c0704012068282a00f07016180070354604101c000e2014480d002414441d51b10390080258603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104936115 1250 104934865 104934871
    0x219050d0909060f121505013c090e07030b0c090405010e0403020a020d020616050a06050c0c0303060609041401180f02040e06040f180f0501051302150c01090209010801020c010c08 79
    0x512002d41105010305c4020300004030f001c83c010b646002413002000c0c0040d05950b026003044ca541407501c00d00803034081a9a0340d210030180700010042c01141c0c7d800c41403821034130741d109000c03c1e107440742d00008400c4803d00284001e160004503c1089140c40202c0700340740d074807805009004a01c0c1800008580202c8450103020326495405460020724940802803403c003520000e0368020f2042108541e012041010000d2080c400c001034401501241010412130744c00a01030780300900c2c20401032282200c04422030340d01c948202e030126140e040030404200200108511020b030079404a00100c0d40000d000306040d0050340c401c1d402c3c0704c0340080768110010b90103184210390300b28646a011030010315142d00211300c40c03403000d80c00040100040d41d1400040a00100580da10042c1c858060f0030302000b8041e40342d1014241820000e00c0743e90b640401c40324000c228500711b04203000f0412058420083d08544101c5400620211803940c455500d14001c0d40030440224040d0b00e44007400440d18003500700688 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104937365 1250 104936115 104936129
    0x3030a0206160f0507030f170702010c030506061e0f0403080301060c2a050108091002031f1401170a060b0a110d03060303050d09050304030b0c030106090b030f15010219050d090906 79
    0x1c00d04400d50780c25943d8541084561048c0b11194100f61003004030501141c0c45202141d0000c99608070041c809012914003921150040070200908c540e0b070840c0c041083d425403041041c0c281d540d41c20701c0e550000c50240b50001008a5000400000c4190784451110340b05070188440401c045442803a0414414880325400ca104004220411032980501078180d4072414030015161100d0800071800106e80c0101e030340450a4510752011604454014551000380c40c60a0007868020b80d14000a0301c0d072682c1040942d440c15800e00000d00e40061a0005e000425014400301d13261521404060301121000b5940c000358400e208000f107120740f090280c00100ca8260303d50a00c1d0003480c03440c4001030090300100b5540c81c80200800000221403c1d006445000100c0840d0780b42d504100008210b05001c1d804585940418030600c11030b0300402003541d4001b284031009030b00b41400040142c0c240032003600340720700c2840030004901c280000480c03000b032145a10350780c0c0c00b819603c0c3c003240000c41e4164081e9407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104938615 1250 104937365 104937367
    0x70201050915040203030d0504060f0e070503060a090f0c031101031406100302130509010e0108010e06010b0a03020702012607110a030c060905010b090a06030203010b0d110108060f03030a0206160f05 87
    0x40a00800c0d02202c0d50081e00240907603191a00c9024580103a680075102240e183c0d81c0c070700c0741a0005149204000c3d000c40a4005003420030302d0940046c0e941d604c00f40080d0951a0b54140e800c0c05c010001c0382c00389005900c143c4503002c1d0382c1d036420402c0c0703007100480000c0d002c241407807a0369075010403c22440b442440000c2851264444038282103009401c45d03d07612944204a0a000c81d41b5604c64070320300d000b480e45805e4180c082d0304040e02c0f0b030f00391044101d0084840c2d0040005102c8074108605803110b0009610f00143c4880c06400103c41e040c2c84030345410020220300c01c0c01d4035000d1402c101d0910801382511182070a0321074046d03084e030724150810081e00142c003110000c1c0c00a00d030b41c2c012480490144c000810002c0c00c1d18000303500402d0644856820980e07800e020411801c003809540f01d520000c40794044036500e981c0754158605011000c05040080b07007000030b45155103a10598a50b0500a0102c07034540d4250700001e503880400382c072003985000701c0e2014010811320074885840382171015641c80b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104939865 1250 104938615 104938633
    0x6070c1a04050f01060801050402120d02121305040207060e070501020d2c031c1205010308070602090d06020309071412070b0a0909110d140420011103210702010509 72
    0xa440c00d0140a00304403082e028407400c0700b00340e6800b4002d81002c1c10b02e80d0000101030509204208240408510244442e0000205455820340215001800703d030030030742d00e5984200502500d40c145034950030143e4000e1001c1880c50601c050340d80101c1c001e40f10541112030700703a21a001a41e65040c41c1d40c0181c0011542c1d1070707028000e81900c40b0b0403000080b1102540d006c1c10340c2400a402c000c104041e88007540440d440c140c464691006207400e0700010110f08003c20750541d210182140300300000030701403a0300000e4003451621007060340101242c000e02c00b19100d0902019403a25031074a440740c00007205069541c0542498500c500c5483d40319040001d0290600d0040300320019005101140d0034804603a4000030001254058055074100300460295100034100d07412003124000288940303070b1031318001000002540241004031001480102400154003000100c1c3c0c0240c0f500681d4515010100c0c841c1152000b07600e200906401011281c440703a541e41000302c1c01c8440840e0351900030381c084480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104941115 1250 104939865 104939903
    0x21090a0b06100306030507030f21140703020a0c03080c011505030a1b031a01030c12020f040e030d0e0604020102210d0b010507051b0306010504060e0109050a1b09050306070c 76
    0xb403110380b49182c0c1030224a6940daa115a414200e0740d0f40247d60394a0303034020007020002841509052412104d9000ca441c0307844a20045c0380c1c000f0b00c80d000821a0300040c5205c241402081502d140a60024082c41025140c0c5030000d02a00068028186507080c0101d203495010715010040680348050300802c102070352512000e010111096008000b01040342d000700200e41c020b08420000d4104c05807000076545180750078441150345610814408503022403640059803410030464107800116004a0a0624220020705602c203500402031524030b0a46400b1400401244107440340c0c1c001d03001d032100c45080c8035900103d602030005010f14203504120356644007071035900c0056441c0c0185042d50a00300c0c1a038a01d891314403e12180c2c888401d03c0c103040c103030600e410401c0902400c0103403002e008041c5001d026003070f8803106004141e0301a48070000941c040c21164050380c580000320490000300c40da000c90280c50700c00c0c0703405550b019008500024040b0b07401051640049a80304403030a0070301e880b580c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104942365 1250 104941115 104941129
    0x4060504061d03070b1b19030e030a1d0f150309150f0603010c022109040209061201060905041a010804050c040f060503070509010311060a030b030321090a0b06 70
    0x8407262541d0320b0600301281c40d0548900c40245104000715950051410f00e058910310051032070384940455849603801c0480941550813a80c3c0d10080e407424821040380a4010745640081d400b41ca10020546034130340d95001c410399081640501600043d05503e0701440300c0c0c6c08040b4455a00580c10703400c1091114258070045611040d81003d880846817403400660413a0307010b54480000043d4107052240d240703000e114a601450b8035000400405481c00c4e0500c0c160900191900880507010031900d107261030700d03011140802001000180e0350780c0d00f01c8881d6003144c0203001d9a000604020004a0f813420688030705810a030074804403908030185403004450950008004451a005124010100303444902030140e03034209505001c143c43d8184014185041682c3d0b021034420080700b0010004221000065610300000307890749569451160800d40283c080203144a4241c440011400e00e07804903140004032100100c003604180ea2140c0075540d582e58181d4502802d141180004260a484c0c100c1e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104943615 1250 104942365 104942371
    0x10c05090a09020a0c030f1b1406070c02092202090a02030403090608010513020703030b041b0e010201090b060d05070e040302030d05010b19030203060103061a0306011103031522020a0c140102070803040605 90
    0x101d07142d658130300c803100c00745e0f204080500125108800704a506c0260740d0302b802001c2e030280c00d43c903103d5808a403c0e000140c0d91240980b001d0f5100d601c04200c500c0d440040980010200c0e00904510030a0419042d180000d510444090380000c14030030010445900c142c0c05141242d6000740710003008507028400000940c1b000c00102e080c9540c0f00b10803807d0323484901070252003440b48070903000347c6200507001500e280e84440003541103903d8100c01100107880003122507041f000070b03030b410308180310b15140ca245002059040403440e641c00710300300b2041550000041c4028400f001c0c081c80300341d0707844041003ca030180000003800355000f54070011b00c0500c13940c007455024a0514001c508217507616407040d00c61044074041a06507200104000e80c0e560030002c40220403154600840c5035190030708003a80c0030144124114890410702c1a248030b40e0b29200f4081c0104522014115640d0055000c040c140400d2820100c4140601d100d82da022a034061080e51501508413060354074660b510358603039000308401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104944865 1250 104943615 104943617
    0x60c020f06010e270a030201110405090c0c190615050d05060a0c180308090306070c021309020402070c090c080132030703050a030503070801090b150304050c03010c05090a09020a0c030f 81
    0x8000344041e030848613484600d030388802500c1c09691509000f409d54403450481d80754400300b00310806c03041d00d8019070203920800a440c45a01c1e4000000c03824108032a24131b610b8880f01102e040142445081d61050700201c03600304400c074003d90b956062001802d0380903405841604804002012490386070001d018121075031070300f1003850356065241c0c00540e20607002600e0b41d01001c50f0695040c18200300ca107400042d0740c10030440405540c1d00141c0c00c09080001500d116894110040171526650103031101e0750750040b580d1418944914001000b07003504803811700040c2481740009450082d1282c024804001c00d00d0587e4010030417240381d500b504040e12516050300ca09040000805d80c01c1c0100b06085220399250307036407030800b16001484a403040c1c000401c030300d00d444900f507611f995150b40b40d04088090620142c41e40e031f803803c0040c00c0c003291012a07034241d420101c0071450180c0c010020b10b05800e040751511055070b00e0f058201e0881c0510008880850189401d46c40460b000745190295103d03d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104946115 1250 104944865 104944891
    0x201060503060709080f01020403081b0307021503062707030c02120f090102060a1104030f0827040c0302160809030a0510050406110a020a021212030112060c020f06010e 74
    0x14500110340b500d141240c81c1c0300020001c0c28203002050041c0703e9403450600c080000d500341811919066a18401c1040e0740241e1010003e1071038855000780166607526400901c801240c02e45c5c2483e068855004035080f40c455500c150303420004401082c5800306000c0c0002c80c00308940e03034030f038001c1d40242034001c1da403010f42c421221100d200c400c0300b00042282503265407140791254420b0002910301440a0310800c2418100703500f0403d040102010345003140c1d00a5081c200f40e000e035081140d90b030310820068200751442240c40744894085480680041d04e0159010800340721418411401c900a03107100c030745a424031608800c041540700001e801040300003025560b044546a07a998074003120115841401ca882c1d204210607c035080c801c14641141c030540e45d51078080403001c025251111800000d00c50307050300203010b4500342c08107d190303c14102a86490b641e540c41781c0b2051040d41c3d000394215034076814aa601ca6000d0f01c0418005510001310b401014540d00703150000001030001040c035612501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104947365 1250 104946115 104946119
    0x9080d32030903040e0711060412111c02071d0115020c0d0f0c05060a120903031104061805060705070e0a090f08090907080106020a150e01050c1306020105070c12020106 74
    0x20010001d5008980050003560345925124942d103440300003c19110606c07808041d601c42103040032822070b500c240c2c040c241d10b40580081209440410b5103514070710141c8a1034042c440b00c48642511003981c0b8880344c0844600703076030328184c0e010902903d4242d0505c175410f10004100301d0003544555540c41c90540181c900c800b099901080c0c281ca8840320035944800e20345000d100b403090400d201c4000c3d10f020f07210103207131220884020741814800e840540d115a43c40700c42c6800d25100342d10094500071a60400340d44c0d40c0e65a0700046c0b240072081000904070030040c44c0000c181c5000b10488510b03d5109010744442c3d4034148020f032082c68000e08046100b034071004501c00192a081c4a00d00051040c80b4654031030360034a05004910000901501c10b101000005102880e0005210607503a0780c00f0701092034190802c5030120141c0000d1001c1243c560900041c018603442a002030b20a03a844a541c5014003030b6148422402d0310401d0301d5070300101d0641605000802d440708180441d0702e03101e00011445903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104948615 1250 104947365 104947457
    0x7050616020312030f10060503040b0f07110f0c01020708161e0317040e102405040915030524010902030606120103060b0f030c21070e010308070309080d 67
    0x144c021030324002c05d041a4002c10500700c20000070380340581040d290003030562509544030a1042c8004d00803e04c4114880c0005020502c501d0fa142c00c00c0341d00106540c0303181d4140303101a5459012081041c05401764240200d110040004c050544410048018042510b040702c1c0603080c41d100c91481c9070762000306d5400300110f031190340084420901d8203d029502e61034100561001c00014064035944011043c04000b518087c2d40300008030000780011f4911441840003d55503882558003180740b8030f0904001e15002c0345a10401c0c4112030180003903545400e200c0d04840201202540307440123900c004001849004a154042c1d5030010001c3c00c580d207040101d600045140f002640700301c0c0c060740c480a1001803410700c03481c40c1d800848150020140a15001c00050202c05a178918807150600d201d10305194540030400e52000340030301c24030050343e943c403801c01e0ba0706580806015804181c42410010b061803000843c910b0031b0103241d4421b40e8940c0c0c00c400306034204500f4004120354288110000043d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104949865 1250 104948615 104948617
    0x20a02030c0f0a1a06030604020114120108010504030e09010308160f0206120103060e070b070b07031b0c02041103010806040f06060b04231206070e04060b030a0e01060807050616020312 81
    0x1c20001001405000c00f6844c01010581486400e60040340e00c0d4000d01c0042d880010b64503410a0b0b09080101a2210702d5020188a01500d54000102072581d0b000058405065221074080d9000307035224201d036401072041c400307942c000380702c01070004408014007078403040e0600300c2100712840703001d6032040d0300c00d00d400180c1c9030380180c07644e0050102d070000108100651845102008950f03140640221440e000846038507001d45400507000d2011100000c0104d4441d900080c40000e5150030402d8144030540010700c03450409070101d0007a803178240b050300407144800c1940e040b2154100200f1465807a583e5610021641c007908179841d544411010031603903144005803014206820300b01c01840031115070040c0d202e40e5040818011100ca0008000082c070104000d40d20440c1c03403c01d9081c40303200401080060205520101d80000e01005000f41c41583e80c1151040d2003034880284078594031251516241c0b0018840c0ca0b83c0301e40100100c0d0b9030305440b900c0428846000400343d69071249031484400311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104951115 1250 104949865 104949883
    0xd0e031209150604060803040b0d02250b06060403020907050a030e011b0215040f020d05190602090102011a03060a0f020c01020310031b05060409020f19080603012d020a02030c 77
    0x4940c0007440c2c0e0001d03400d081461140e00c020103c1d01805024941754504d80c070b91003240100c50704a000004d0188980159404582001c004240b420b041c500c2c80c880c05c004682d851020455400c0346280128140e86401016030b02603e8000305050304540714a00c0680e0340f40d000749040004e06860784000040e01100380721320003140e900d0040349031200050101c02414121007644441901100805200200e10001103400290340d066500c50303400910340c20001e00c0e00301d000021075010300ba1401000304108141d0003610520501ba0024408801c06045000403251502010b030f0f010f40c01540081c60340440c81d0001d112485020310014903000c64248441d0aa0707008271411110180390603000c200304900400f07940c6070b08840d0b002028071942030900040c4507120718803c148549401044510001104034104c2d50340381019514100c010b20461009050b80710110780c0c0b140310354a49032240010100c01521501e482d00d41024480c061886140c84c6002500312111043c214841400312900c8600704006d8a81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104952365 1250 104951115 104951131
    0x60103180c061206080c21010c0306050f100807050d0e0105010f1a1204030c03050c0a0b0402121f0e1609020315010f0f1d0a030605011a070203030d0e0312 68
    0xe564205200038141d0b40041003e03400305840c1040800001034081184481d8078022107803041e0581d40344110701c004c0031f80c0a041403055441c044042410075010351200003100c02c00e480025441400d074040203050402055180c0204140c0000502c140344030305c3c001c01c00020003c000081034510b80b0440c50854009800540e48001003600c184002001418105100f01c0e024041c9440c0170200d0710003c130594800f4100405012507099443c003054061070543e120714042e0001c440c4a1081030420000c8207106850a0303004145000d6803001c03d0f0b501081c1c1c49203c02808501340b0351010400150350041a00c0e401d400701c61701403c1c0320003200300780041343c8600400450078090f8680c2070150b200032200c54504401ca06100c0521211301200d41c2003a0310303590045490510000f1030111058030b0703001242440420358001881d40011042005c01d03800181a0340d1201e4080303204c105213070740c0f62890b0b01c0303805070195143e4010300130940c18000c15007000c40e000245070207482c14480220070703032050480140e55030700c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104953615 1250 104952365 104952383
    0x150204030804030512030405150c040306051f08030a0203040b0f070804080f190f151b050c061f0e07030209060304030306060f0207050a090c0311070501060509010905090606010806010318 82
    0x1003400001c00c100c24004c0c10701d8180c14a5400c1c1032355215030300e01155074140141015400020301014005095900035074001e8400d0005140080c10300303013651034585502d9070115044001150011002058030910009a0015445c0500345842074280c0d80000640c100380940c10401d90000402881c040d100505900380101000111a100a4101b44014116a8901074030600d00008590744060006c2c40303681007035410707202c40d503c010000702500d101403408444603403502102940350342c4000100203584032901914a95190820350883d051101601e4440401503a6014440e200042c29034a130040900e040040c034050000e004181642c100b16026030200b07503118400c108681d00a420340d4803082d21403001d410400c0c1028009100d00c1424003500441c0d0382c0d148241d03503840e80650301c01d0f89081c6d51038000546440d400d01c5c105010303000d41e0007030b207001c5c4100400001d6030302ca09015050090b00041d01811440e9204d030011541d6060041030346040503221010285451300c0582d2070302c01c141c0a280a9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104954865 1250 104953615 104953619
    0x61009060509360709080a08030408030903070f0c05030d0e0d241e1a01080a0b010c02131d0a050d0c17070b0906060f1305041b0806060a05010c051504150204030804 72
    0x20f0300d0a02d0751b0b4040c0e500c1c1c1e040b40030700100091106003104d41c0315500c0141e25460f5203640140a15500034040020500b0709110b01d01c1081c4042c4012100880f80d048086401d012401da2003262800428403206801271401c4603000700141441540140007005202c441004002e20304001c0240c0d0640c0c642080511891010100340104034041e1546074121041032030b1012500c600000c0502e500103210210302595030400c002140e206403032005409400900005401880e80d1680780100a810468040784d081d05041910011010035003403201a00b007406000307045a0b5103006d42da68600340c2070480b1107020407558003e5203c0d041d0f000c0c00807540900440d0703040e841c01c0f401040c40d059001e404c0700e21811281c0b8040c0c40e90303910b1284962000004510100f51034031245054080c500f0411589600040b00c2107001c0741c004000102184030300001c40e6000c002583c5c590064604225516000d0100c1e001a0754440040da4024000b03500240701d0194102200789001c0074408a81184d007003128504400202 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104956115 1250 104954865 104954867
    0xc030a0306060f1b02040f022106040b040c0207030b041e060902010801290d11070305031506070210081005040609020706050c030907150203090310050610090605093607 74
    0x80c032000b0030300a0405400d002d241c07004c0610b0b44124070200a1046446020300d0304840380703a805a07003000030009021400c10426010b00744288908441c00c50089d860100358160a25007402004903076400741d0040c20a8034155281d40030034071070041c01514603407610606141c480c1c00011880c1805130142d01d0014601c04284001440242d060380a4031042018070480c451049240b0a240c3d158030307103404015034031048548001c014203155259510400b0021510005040d0004001c42c0301d0800d0b410a4220018207004120582c0125070001c0e4220400d40030100e141e0b801007240d1a00300900d103283c410a10f0b035590005050f034810750003005a01380c021440408109882c01a02d401c01c01e818079150031441c02c0c40d4003075500d020a12030301c400e030413450301c12080d603d0083c412500c890340c001d07007a10301000c04c03000c4583c0640000d8a0300c5029141e10b08030191102d00c210135203015120140c0d500740c5811010010084008902c8040c54030950100c0d246001d40c04000c0c0b008425030b0018031001109151080d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104957365 1250 104956115 104956127
    0x4021e0d0c05120f0d0513031a040506070201060602060708090a0209090d03060b1804020a0c1b0f0602030307200c030a050c0a1e030602031801021308100e1e030c030a030606 76
    0x84007032036401480101c00e511301c00f003400d000c1141d0b80d01e480c50320b682e0050421140f6510640c0041d24044008030f074510403021045d50140b055009900725090354851800880c00ca603050310038900140c114802040500c2c1c03190740529040100b6104491840640307070001842c541c001c2c1d4094801e580144541400560140a400000c04170704c5842d0703080c40b0308520b440000d2081c0000851090380c0c00101018614040c40118070130903005004080402641003060b0300307180a070301907101c444080d59400611540f00000b103a00c16202c80c1c1d141c4c149041c030712040c1c1548003a80300c40301c625130190003007042158408101c8040c0f441c0c00780c8020034102c00724001340410000c05400c0100181014402501821007915074002282c0d4051801a643da91b465424114680340c02209409540009a0290180c2c0c0c0811040141e54042d41650b605408603003654048444c2011007503031580240001c03000500320f03002c942c5108882d4400b1b6038a030411700c04100c3c1c21030303100301455000b00e55114000d12400303501817 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104958615 1250 104957365 104957389
    0x426012307090612050408041e0305071a07060f0e0a050705100206040c0b0a020a02060403050102070c060e0a05130b1002060711061506070201020c040e0d030b06040b0304021e0d0c05 80
    0x304124070190700f4000028080420204c240e0711050705d0790b000c2020081d0b0b0004550003040101c004101c0851100c2d05020382e10032034030040e0b41d1803181100224076400c182403a04d10440c0110503092600d03500da0b540401030418503412407030060750303180c00e681381e02000c0c003410303036010b102d40064440c46041c03c040102c0c0300b200282400c1158400010000051180c00908081da101d0f010410340791901d0040491900045da68000c1d0842404940001002015000f602c1998407178285444401c1c1c9031001103c004d4200301c00755602240b4108100b000d41050554004d006800b6800402d0124424001c03400d002d804100300310050340010100142c0c0c59000380c10101d152600d4010701080e0501ca44080c003c02c00000026200b40c00021341c410071a8001c003e03c06425901400900c0100e100b9403031580c94500d9041c02c500480d0030126030560f240740510454003034070b03094248a810341e29113400b800244400001d03000d44500c5190b241e800c1c0b942d20141c80c91400d0f0301c01d83c4005203550505080c044402402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104959865 1250 104958615 104958617
    0x170d110405010507080313020d03120b1e010f141306020d0e03210d0908030a0c02030909010b09011701080c011e080118020d0e01020304050d140426012307 68
    0x240001c1c4426039200301210001c0d60070401c074030780341d45440e0b003100343c0710707143c4078001b5481001003880404040c0c03c02d0700da100c0f41544007401c10001d0f1003181032103400c04201e00300d0b01c07510000e500040c120f50b0048501c04600c600341c0ca0080c1844444407250805903100e420400f030b803602801e178200301f515410000141714010320310340f00b1340320215007020035a502d40080c40384914070700c1c00840b900901c146c00240d40203490195400d02c201c0065080200300e40e80b058031448411400c00c803610805600000484401d070300042e0065030346a02e003100001441c0c00c100000d604006440d070341440600c0141c88414068250321010f0241a814000098030070402105c11080780840a01c00d214126009900c00b41104c10003100030038070060302c2c0d02e608000c3c03051000846c0014500101d441e05008154041c1d80700e42e22039012540c0c0b00141d800192510824031004402d0140e0400c010300ca580d006c0054840d130040d45410124890548140e0f26080d00e001030310040d00440422040205200d203008019041041c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104961115 1250 104959865 104959867
    0x51309050117011112041707020303030a0c020106050315010b0a020a0f12031406060304060c030e0a0b0402090c03190207030201090b07081f0f0519050d030906021b100c020a03170d11 80
    0x1045000085c5050001e00140c5405d03541601c240c01e91203480100e8180369801800d59640c1d10744491810018240f21902100540c0790600c04141828001940300c2c072913407094000d10a5030718000070134031a540020101e0f400c5010380c000c40e00c00500030461030f00a00748500c2a00450702000d413002012100740c580203400700001001840140d860346070407250000c0c0c21540100b1641490360003580030b02891f50928085100d0300c1d2074003050064903503c00d40a80e108031200711043e04c0d680c6032803941c0d01065071404840850030391113240d21761803580200341c860712034000401d0b51141c54440754850700307044840b140800c51250410200010301d15100c100006440c4102d1005828a5980704d080105401164003a05203c5840d0b200071080e1583d50004100060940c02468070b2858004c141d0203441c420100507228642c0c0401e8a401c4000d45130040c00030261161070b5130f0781c0c03011003201c421070700c0a070070390300240c84010120100c1c102400100d15035110600c0c8554130f1102c00b0910049a502003030b4040300c584 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104962365 1250 104961115 104961127
    0x6070c080a24150e070c0c08010b01080a0b01050a0809190303020414011107090c030e010f0e0610030308070509130e0c0a05180103020105130803031e07020610060513090501170111 79
    0xd0140e10f80080c1c603240300342c01c0c03495600c00c070341610ba40b50400000b50103505070980000300c204054220081d00802070781e070018681c443d07048900640304c0d11254540407510912000103502c0c490810186e0241449046036036000722010080d406644004054000940020341800302346041b071314510998000303282400c44a0382d15403015403501c1187c000c2040031f0b81c0b130b1816041c45a02c2504110003540684008000d1081d010000a00401c0d810310031040c58002c2100258040840004000440350036841d907802980d00daa0702221350b50b01c00001c85034420424100300b850300d0954441ea01c03020f090fa200400ca030190640410206c0e105a03400244200c1c0e1451044440a45170140e0b41d04503076082c20300c0ca8480d440c6241c40c400301f00a07038106e074140748004003c02c500c04c0e4018600b110b0f04008e1602c0e419088d1120b80c8100c2c0c0320203040707d8940c072000816400b000314034402e00043c01d0b16103490010b0f035060b5844014400541d0002e1f0302c00000c408001a511003810020300ca404446140c0c81c0142e8a005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104963615 1250 104962365 104962391
    0x306040507140f06041d1b040306090215030a05010806090a050709200d0609060f03020105160206090a0602100c08010f031106120a0213090501120206070c080a24 71
    0x10250740280c16103034224040c841c0640e25581c0f88440074800082901740c075152510790580c24902003010501e49100741d60042070307903100c04803034580d14420b103e004a840d10303056827900c1c2c004c4d0000440880e00440b10399800c000e0703880f5903005580100d0380070038080b802d0b5140150340c0b840d105014141c410260000c0300b51f8000554002101d1040322341812000c10460440390b04d203404c8401c030054083c0c1d02c01300010600a510a04c2e403012041d51108507040242c1070f02c40f64520966040341c00003e000c20030420407040524032000c517851607180300402c0c65181081850100d0403c4055501010241c0d01002502d9090400313030040c8501c010b560318003902103601d400c100342c0c042c6a42c0d00c03000d08078080c00d48000081d0713101c40c01207506100c201d0004400c641071001c4400c00035440204074000150001101146c2c0343e40c0c901500e4100d0b1a4607490b12003108058003001000d510043c001c80d0001e40b29000000c1c0000140100720701c2a02529040d00083c000e403000f8101c1c034090b01c862000480c0391000f0b0720b15071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104964865 1250 104963615 104963623
    0x80417010c08091509210c0708150a05060d02060f0a030b0409030e0d031205010f03020f0109060e130204030213051801090f03030903020f01060906080705011403010e07091205010501090b03060405 86
    0x131800388100325100d0f200c00c0001420950054020000c621145508111000000d80208145013505007111011590796100070f4a500e0814428900384141340c002c80e204c2402c90300141d8000c400104a0b142441c020742c00140b0b00c0d800020891840070011441050f5a03406118245140c40162814031080b100b07a54000c02506444030b1962140700c041e13030510b0034503120b22001aa000c80c7c50034100000d50315010186116480c03031004078443d04076183c00c0d04183d441984039000300c0300b0f152101d844c10360300f10b1308116800441018081e05e890f0300348000000b6079141c115190604d14001c00025039811301d440e05601601d103001d00301095a0400d00900c0001c0c0c2c00190807011260103140010f00e050070b81c03800b2428100040d002404540c2071180100b1820b800394007040c00c0f2014072080300c0302036a449005594400031f80c50400702e0300506000400261402d038001d5a0701000d10300c0c00408050b240d44d00031121f0070800d0750a442aa5468006000e014180d1007a00c0484c141100184410310b01903032140c4d51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104966115 1250 104964865 104964883
    0x201030203091f0506121b040b0d0204050c070201111f110405180f070f05191b0309330f020705030f061504020405031216080417010c0809 61
    0x101540040090400c0740e041c0815000d210400b6030001d841030702003035000e028000964405200361242c2e03a4451052a0006200403d90400501e000159203118100401889c14400a9070040084d2040d0001642c4510540e0b120320302e840102504d41c44503000050100060070980c1c0c04580c0700d10303132107409044048414480788080c00700115170f019101d881da00c0075014542c0310903044180a01c4110301420582071092103803400c0e210354103c0c0d90b170307940007180c40031300c00300004002c20010801d943c01d40c01d80091444035030410b81880b180d020080c054400341c900701208143d00003054100103001560103e910605007503100410120300041d0b0801c240c910000200c0050180150148040c0b0003038000e104c040d00030b000080a4403846149000c0160700c1b03104c00c07149201601038200052841d89000d01c00d41301901c4025000b8002e03c0b440036110746e0280c0c40160701800c60104a07071a840001c00c2c120045c0082d250403469010f42051130501d00e400c0d5000c0201716828420840304200c610f520004004074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104967365 1250 104966115 104966117
    0x118030f03030f0509030d05220f020301060b040b0408010c05090901090e150a0e010f0c0e06030a14040809090601030c1d0f06031003030f020d020706030c020c040e010c1d0d0201 78
    0xc4984090300c0c080d002418a40a0019041c0c10a4104001e0660102c0584030b4020b60030002d00040d0b880c143c824030200c400d038040511032124142030001052a5181010446201500005409071106940d0303240340c110707510900c0d02200018040c0841413081c018035242c0c0d2500c2c20712034105150f07a4002030071002c0c1401495251556088104290034081102400e0107450041e031806030700306025840007800c4040311600f642c0d800c140c2e145540007202e2082d40001c620660701c501079042d101c400c0008590018100d0280d00c1d0b01c0314000c1e040038000c454010300581c8141c3d03c107070b42c80f44642c06010341d5400c000c000c10706061401100400c81e030740004000342d00d50640001204582510b10001e440c042c3d00d0764100390400c1010003045111250300d5190429039019484100d5044c1d05448120781c3c415210b0440d80040e00706d07280070000345010750015402d095240c010399844004880c0400c088881d24241751300282e4440d888101600d4100c100074840d5401c46944c2c1000c0d103255000314030280006a4002c4c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104968615 1250 104967365 104967383
    0x30108030406030203190e07061407080412020111010c0f030c11060109020a030f020d0e01060f0317070303110a08010906060309030512131502031b070f02010c08041806080606011803 80
    0x1d4000342c0c501b1400c4280f070b00920402c011540903880800c0e90f481c864094900840c65244000001c6895075056910103030b03002030010310306810081d105120b02034052040303050044000b546c680031042030144104948056503200c0007600200383c01801e4075845e085803414080c0400541c0074281010500030f0554480e04c4001d0380d42d40b504103084006040306500401c4007440480c0245220006800c6900301c145884000c3c003e450720340f107039100c65140c1444011305003c8231030021244240000090810701c2c0c040d040020340003150250199482e48000c03440380001e00084018000d005242c4200c00203044189401c200c3c2424940c0e0152982c4186049840030001040002d0000652108200d95165106901d89503403652401640065002a103c000c0e0308041c0c000e1010040482200b03884000d5000b80513200c2c808020b400650368a590200d05440c0c0da0b104200c08250203201c200d81000390a89081c3c0003c41030300d0b0041040c242440a44518100102a403842c0001543c1140c0d2800352500b010840c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104969865 1250 104968615 104968621
    0xb0402010e01020f030d020702030f0105220606030c060c050708190201050c190317060d15050901060510020a1e080a080903220303020c0f24090904141002030108030406030203 77
    0x184c2c42c0c00d0f403062a040c403030301c00018000170b0410701ea0041c10141d440ad030211070090f441750043c2401d8800c101c0b801040e9050315410201542c541115103000039001d54400620152251200c0f880360015412020101303903040003903420840704120f2440100683d1000d02179a04110194180c1c00b0400d80c40a4104800880c805000030014018607107043c0003809503201070f80451901030b00e040407c2107130f600d08074407000c005007542c14200d2640ea0195803151a284280703044050701c2d401441d0147c0424980c0d0369800b40030400303845d001e07030b58031040d11580c001b0402d030300c0d0500c0c11084004507007092100082041081d000020000000d95140113036900b0201386650f0340c4c80c035140c0796004009140d598008000c0e1034082d0603800e9079511050728001d40c280c03080507813988103003c2c0b030b04484181a074020952030400d88050b4410010705040a0071848228606014200003846c1c80341c06a9040d561190300503003442141c4000c00508107440540346082d41150700d82000c0030349901440c466541815000800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104971115 1250 104969865 104969867
    0x5090f01060e0f28030b010b0405060910020109020907030b0a0501140a0c05190305041d0910050a0b0604140901060f0e09061201090b071803110607080f040306050402031204030b0402010e01 83
    0xd100540356041000100c90103600e4044050b100c4d0700e20068400d4000d5200110f03058445008403029124068020751034030842ca000d02401c0d4603c0c40320003045540c0c070109080142d5850700c025001c1e144a13500852002c900b80c08011132200b05a0140b410301010410701301c00c54694400f958400741c1181010801c600403810f240c2e00f4201032145a200c0b4851031040c0400701504507010f007060b60805004030811a0b52400034014030750060b1041c2d48694020805145010b4554100584c46040a04003150089a4101280954000382c001e02a0322440401091150901c09101070042090703282c00d1410021146000d04114441600c250041c2105800200079880307400340000ca80c00c2c075000800103010341d41003100c00d550040e158000054200d040b20201d1100245145040e203412107541d00b08a0750309410083c42c0e81c0060b004984400c0d00703002041c0c0782d84071600a080150300542d00410907180c02d1040504110a003d204404000c0a10060021610038200564015420700b0040703190301e84080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104972365 1250 104971115 104971129
    0x90504020a0f0806040b160203030402040e030903030a0207090c020127020a05180906070801061403060a0306020705060a060504110d23090c01140304030e15090303040f05090f01060e0f 81
    0x404004200030b080002509040080c0c080e20480c01514541410b880740107403010801d292244050060303006101203009407500f070f800780141c01c000f02c0843e45810103000209003036400070804000541c000882c1000044903078000c40d00724030080d200800010755802501c0c3d070166410503048960111860180c403c5491b0526418050280100000f01401000a50f0144444211480714250054101141100e80684102410788045843e03000e50b17040040304050344d68000174841584620341e0b020001c0410340b14802840d045008002034101841c002540005460241e8851401030b450a404c6540640c0c507c0141c81d000c070541400820120030b40c600b8040a01c09000c08003845408250504c20900310008541c1d0303080c50280c891100d200e0f80550000341c140011680507010410f4100c0403c9075180c00c0c44442440c00300e0f46c04d0281070021b50404030b461508a038021441e42000c12400740614540034101390f901201d1006446002d604015005206090004401d801109021842c000304d41c5e03541 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104973615 1250 104972365 104972369
    0x8061303141204060204050315010806060f03120f07170403020f040b04090c0f1d040f06110408010c2d0c0605061309050a030e01020f07050609041d070510030603020109090504020a 79
    0x150702d503050506080480c020740c028480c00f4842d200d1454001c07885103444003424100c40d0b002c0f0140c401e0307956076024000c91407804d03404507a150180c034144411000e0300602404e9411076076220243c480b0040c4c0f4086143c1c0c9140340c10f120a8410a21040005030b0361a90030f191980c10a07140883d010101c080420b000d060541401081e6400041c00818000007904404080340c1c5050380d501106c03904501d0554007407400342c81c043c2c0750a243c2c00150010600540013440030440b131100d030030b140a0340c40e0011400c40305480140c1d400034201280340d4030503214403800c5c0000c0c60340300d0149101155036010098401d0010040051203e5203400001e0b07000c1c1d888801d08403c410b9481020b01100303032a49000e03034599022613401c402060000d00b8074203040d4400035403d40c5592000000b05003140c1403004002e03140e00314011075a401600c850110128261000c4000c8649c00d108000303000150406e8208080038286021079010185405c00410150f0b074846004004c680c9002030020f0f481d01e950000c9920350100f9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104974865 1250 104973615 104973637
    0x60d0303060806160e0402070201080406110405090a15050a05060318120703030219051c1136060307052505070e0a050901020304080f030a091b050108010806130314 72
    0x81c004000c0c85a03000040c1c407124200175903c5070b4080d0b660008100481c01041e2029001903102d6000900080c00c60b4804800441d403508103508050f0707a0000200b44410444155040320340b140e110101e0309021800e45005040115003e00b0b08605000102d14240802041044030410240038a801e1001c20300031640c0c0d09105610b40c90b568844d03800c026000e58840c10345a2040c1c411481a08809445102135403060040c400101c00d00c120b1000b0194041c01c41300d090300d2280181008004462031000101c00c3d507121a854640030820002c1d10100a040c00c000c24081c0680c008204000000e80d00504450000700b400c10796105141c80340302480b20505201000030035500c60504003103002181c4094031845607880d81000e00c02c40d614400c0240c02c0c0d020030b0320000e10010301800102c0d15642c091001d1a8040385180c40040c0c1c11100d03403518014092545d902008042d80f40b2020b00095a01c68a054007500104000700744c5410040003070812032503004000b07020440e80e00d207031140701c614403011901880a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104976115 1250 104974865 104974873
    0x109081801091502010608061f0b07080f070c090f110417070801020d200403050d0c1a0106030e0c061303020616080307021f090302070504110d0501031202071d060d03030608 76
    0x49040d004c0d00802960180d205144030b40ca000a80070491442c14042c41e202c1c2c40f4242c09101d2401001c071303820380c125034130461381c25406004820b41c0000d0100a844181d010341c41c4603043d54509010381044a0441c150b403250141806c41d4401c0542c1c40c0d0007203608a1b81c0c1803070348400604821400030f003030031501d4024089a5000041c0e500c69020130790455060808200c0000319280c031503428030b503a20b115500c00204190000c0c10b000111a0041c1107a104041c0500b00180881300c0c1000e80c3d00114000342c0015010950742c03240c80d8103a100c00c1042104511047d01c1061408403203c074004403614152100903c01c82c4001080001c40807010499213003550f0001d131560b200d01384144040c0d100c0c0c01810311311161078216411210300c3d000e035004e00400d05400d034014041e80c90514040c04060311140b10706466140302004170b6504c81e41d20b031241030700a43c0201030b890039007881c0c1c800007420500c0a61008020b07084c42c2c480142d8500d0043c81c41500544115042d2090003090f150a8005e40f10941c000750450107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104977365 1250 104976115 104976149
    0x603070201021210091107030f0302030601050405040f09031b020306010504050603010e0d17160f030c020313031b15020d030e07030605070c02010206100f121505010b07050609010908180109 83
    0x4c0f4441d5120130f580740b1440500500314010030010301e0f07000d042d4000d0001840150304400c0300f0b009030300841d0816018544280740c039031143d01050942d040034080118681d039a48810043c10390010300d0007080d07103400b4040301885801e40c0000f1b95862042c0110b80c0700b030b540c803004a800343d5001d520650288071120b09541c042003503020f024001100240502c1d034458614800500014a1700c038100342040301c00c0e02c89241245418200b100241204114070081d440308214070005502c044040c0c1000350b2158034503c222101c0da10308030811001d40e500488004c120140c5c041820b070380100c1c80721b036600d80078540000c2103074041e0066441c080040d88007500d00d51606052124a0303034403041c1401902d0017a000c440194136200e040e1101e01d030b45c61082c0d01580d211804240f2101044a9a000049016074405205280610010001c07100c080e4040052203600150b130008200b01848405e51000301036000300307d4103401d5107131079005208841110780d003001038200c9104240c2c0a28400c0018102e03807a05200555 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104978615 1250 104977365 104977381
    0x30a15030b090c03030306010f0e130608030901030e0c092e090606030b01080906130c0305120c0d140a05091207060e0414060310020a020312130212160506030702010212 74
    0x101d0306a48180040c001c09841011904001003200d003d520181d545019582e045c0c80121262982401004e42c400318200c001c442c034424600035500a007914002035642e403a2214000b4048610a154014846d00210540040c90b5a40180e4a42c8a24102c204031162081d4004100703200c148011000142c00002c503020441c0411580410140c490310f80f0f040060b040c0d02c20040d209400200d500e1540d941c001e10004e001080c140a000140502c40d400b0f4590b81070700c950342e0500b41a04d121007610a03070404520440103903020040f180f4502414180380d00105072048400401e0b208500c8080144030740000c0440f6180c0320b0801e4071042d205010280d84681c2c1c0c9030030000b444941c400400b01e12032400c101491080c9110403002d18000c00008008081003604610a240650051a00e032825400b051000034840c00d440b40d81e5522031344406090000c4035410317104210242035072100c1c840b815030100440c1842c5940143e0001d0940380121003190702c9540d183c1c2c00301d02901c10502015007888490741400009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104979865 1250 104978615 104978633
    0x180a06090803060a0b0903070306020a0c0b01080c01021905030412110402030f040204050610170606090306010806010602010609020405060703200a110306011406030c030402010c0f0302060414010203100902030a1503 94
    0xd108101c0ba5190005c0d615035181e0749030300900780c0d132a62641040e0b004000060b6203500402c003800041c03d105000b501c0c00e071030740b94510a01768007000080d0081c501021940d0707411700c050403c581c01c03040c40080031811502c07400d64a000ea8001c4411000000c4203d03414040800c9040030310110052043d03699151603007696940303000945080340164181390108400346050410b0145070380340d90b6a015507a00d248c50029800c030780007418154100000b0801061203860071300c4954080e10043e0700610301540341038802400c480d85039000024003031040c001844a0b0782c43c5800c03112655018904201c55004500c40c40c41d209444003203400192085032400810001d174200340001c0d202040b030039a602d9a036241510b081211702c152046c1e41c44a4200b002178000c01c050710240d6081b600614124a44141036070359900e800140e484150b0161344001c007040100180900400b071003c903500004e505609001c21880c0c85401c081c05941000364010000030b040c1c0e040c80e0310030110901549a00c0350001d50301d007422949 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104981115 1250 104979865 104979871
    0x9240319033209090406020c070303050403050606090403090509280e071502070608040609020904032c0109050103090327030c0b160b0402030a021008060103140f180a06090803 77
    0x11480d001900c2ca00310030114500c620300510b40d040c0c500e25100440c010840d240000030000c49815600b80107074a01500c1c01c028a0014600c0b0f078603810381d00c43c21400e00138a4090000c206500c80e164400403c00002e9010442408491082c0c03100c0d4034a884001c0c0081d6141c1c103e502168032407590300c0710f2240115850b00b0194401c148031094400f500d13102d008020361030141c01e1204015a001100801810348108085a8014080c640c0021807a40b258005900350030151000d50002e0700906a402010100b002c80042c4c618480510003030300e0001c0070010340300f080b940c03051506260381d812151040c9070080f81e403800ea6515491400d64100d08600b80114101707036900041c0d1322580f0b94500070603010b941404036070340360145055880300301d9000e40c0c48000c0f241f0010f100320381500075001f2010041e1625903541010426036155000d8034608840018202e0304130b01400210303010b001d0305000f4414540340c009504503030703600c001c0c1e4810715455120700d00c0d02d01d80c000020000b0b4588001076042c40404406180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104982365 1250 104981115 104981147
    0x315090206090d060c11062715040c14030616110a02030708030316050c03090607030e040c08040501150b07060c0201110a1d010822020f0a080109020901050924031903 73
    0x21140d50b40f000903a513522030403144110960040d80800700c0404003231541c412070013004000c40d00410600d42c45550304500c107480894811030f4004c402d02215403480e00c0090402020390040a440ca000000182c40e841002c0b410018040381c85ca0011031aa0180510981079401500f06c80310380d0b5858032010355942c821220020224958280c0164552143c03048800d0840c200d0300030760900005e1002c001240c0d1001300c0403400d00c00c4600700810b43d91128002c08400e040551200b0f040da10701070601c1402d403880301c480100d40b18182c280510031401d070070b070598221942007a0001040400a18168010a1070355075030b130030604000c034214041980c440000c02405002d0300700807026815040056a070610700350f03200801801108182c01d500041907220551450006012100d1000a080419900201074016010503516001102c0039030030288142d41c01008280d484680c3c5103424141c030010610f40d402500c801012001300000555010031840e51481300c040d91507043c24100340381c043e0180baa43c2042e05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104983615 1250 104982365 104982377
    0x1090c080f060103020901030809131a0a0501050a020a06021b190302160e18010f02040b122a070c0504050703020a0219020a06200304030302060402090a060315090206090d060c 77
    0x141e48001ca015412aa40502480301c16425a80c5060481d04200c0d901c42c3c21a02c064030014040e40c01f8001e06009101c0c8541002002e00c0c414107018108540d60841c80c14000200f04000b52543e00280d50301e000e54000c000123031106840400c10a0b134000c50341d000c06543c4524800d504e914584da0f030340314025920a0b000c44100e1076000b018010a180144a6100e0b1b60240000007403010021510700d480d44441c00e0700014401400d10110412030304660041020f210010a0034000607082c41d00454002c4444070707004455500c01e0003070780303134889009001303040e54034003c070710201081511641103000c2c2c140184144804d01e02144001c009400201c1c1e44001485460406e54005070804a001203840d00600905002e600700700301601d2840c81030200707180002c1c0b0100340c012148070034406000658801d90280c074103400c25004000001e000030f004807182d14034100d4100001020a24181c0c24901c1100001c81c03070340c2c00e90001580e01e00030a5401904108011007090402040c1d41c0240340d841c0c001d480320 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104984865 1250 104983615 104983633
    0x150c110601050303040611010e150601020d02120d0e150c030f0708090a060b190f0608010501180306090609080c01050702070803070b011403030403080a0e0f010f02060a0c1101090c08 80
    0x4166506000c2c8034075070301500100b0040c40510702c105030401c2c800c40c00d00008640c40f201d48544620b000940d400070f40c4200c6007101401440c0d80d043c401040034011503c010400c000000000b840c80d48503181c0f05079111076881c14070300004203042c0081400c081124082146602d441560701000e07601c07c591190309040e80c1800211075500419081d03001d80d0144005004801e02130f03540310003d00b0300350700f066400760900d88628400c03580b0302c0d104005445c108540c1e800151915002814102042c3c00c040d0621600e10a0541200f10f010741c0038003125045503020501000b642085001401c20b401c0140070f4070000185116580703c15044207008884070b0b801c035843e83d555221015240e02503c1802010040d101004210081034448a0f0400103001000c0d00d1030705035039940b191601e62140c0e20020228050806c03003003452400345114040300100707003404512046041c1000b5122080213017800c000c181e6a44154048900c1103070a9455115030f840204a035a005007000c4040d6002803140c00440e01c038050712 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104986115 1250 104984865 104984897
    0x13506060f0d0302060402130209132708120a0b09010b210105010e190b070506160c030c121e03020403060501090605060a080c0d05130b0708040c050607020607150c 72
    0x40c2d800e49a01540030703002c40e890300d03030810440c4e00f40709034040700840c0c0a00203160f040d9101d44a110304400354660000d140d54000d0300701211301824403003000e4800d07003008198000c141000211001c07191102181d22403a91460f16600090105408541d001038642002241303102989008003440c40f02520002e00540780000200030f203400034003503603002900c1103400800ca824a00d8400f40207084003484180002c0c0c0f5040003c080340c100302d0096034668012000d12010062485a5140580e9246400c04662409460240032821600c000030250010303035030000c5000b0312414180c0c1400f2a152400c4010308017510009021b50814001615218902400015044194460032086400180c107090400c0a40c1070300341c0301100c005010712500c0b4010001007a09040c6441080d2090441020074414582942404218501c00500d0340062001b410f0902022032015100d12046440446001d1756034030851000c15803900030f01900400100c01c60f540d500c49600c0640141c0e1503600c0d9581c44071046035602c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104987365 1250 104986115 104986129
    0x10201050f100902074209020114090301090b0a0c020106050618090613060b0a09150c170c010e030315060a0e010804020a0305031c0e01090b013506060f 67
    0x15400710407440d1010304024105140d0083c000c558042c2c840c146c00740c00045c104006940e101c0341e00d240041c81100d643c2d03190040c0304a00c0240e43d0b11903907041240c840c0c240c1c0060642c080036441601c00900200352400d59070740c01d4000d9032405a1080180c2c21500301698410080c1404031040030240d42091004182401e00000b0b403400c1020b10119240e03448010418821110000b40801e50403070040880c0c0400c4c94030901803880108440e071300b019510080b8400040104170305030422006814484461018a5031080640c54400c8c7c00c407460b4a0880080d9410b070314503205261008070194240b0824219101e004005148034018100710b110014030200c041040d18841d5000d00d0000c00c902d803c1c01515544101c0360780760300601c05000c0c407100300d44130f444840c0783d138100354400521102912100d844c8200385000318012452400020700000c1e2681c1c1c0c5040c04501d050042e0544940d11072034008103034001140d601c190b0a40041d8901c01c01e50200c4103591100e0045424a010300c420608511460500744 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104988615 1250 104987365 104987371
    0x307060b01121e05101e0509010603020301060c0b06040615090807080f07031104020906270604140111100204030c0312020601060f1d030d0c29010510020304081b010201050f 76
    0x584042c40e01900e10203003c000701009068030150450701200403505501d06211200004d003140001c0d004580351a08000095005802900801d4018001000003c1d0410000ba070a1544400d402c451681c0d243c0c0410010400b5512980e04032000240380c1901d183c026840b40c00340c480c1c00068030341154072020099079507101c90441d041a0362201c14200007050042d4038062801c98000d00140c80c101c0113400150742508a01070310016400d220b1a032450040003c1e80820340784400ba07940c1800c241c5041d10103515102025151414081d58010300e000181090015404800b010841107480c0d507180d05181c54107407a00c5c00201d502400107907851980c1d13800024000d04079005951119030910180804444458280c8940c0452640b80f226040daaa0f5007408965801d207440d41c0d40782400085400d040b14000c80242d100140142420060041e170204441a85c0c1518000d41d00840c0c03101c400301c0103e20b9403081da40310300e1795402250b0629071209a03072038810405440c02d80c028403158807400d14041094a042d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104989865 1250 104988615 104988641
    0x2004090501140603041221050f06030a0201020c041104050d080901232709011701111e1b071d0a051302010f02030403080309010c031401030c060c11030307060b0112 72
    0x14070000300020361046c2c04440c0d000562a290101c0d004174680d9036140341d0181c1d0f503024000d0300c50003040442c480b098012588100d08400a10210b442900040d44518011003d00e00581c3c96811020200d006a001c8034000e1201420241c1c0c441b42604081819820101000d170000340b140182055542d0703054002c40d443c41040151525019090a40f50fa008150b8028807009260380c3c1d640010030b80e51070316098024144403080300c00a50914400b107007110448903005c2082001840a0203160000e0100304100e449140090303642c2d01221403d0494045030302c0c00d8010b80c0d02c1840302c0030984600300340200c1400b0b04a01c00000c0b0644a03e0031034001d0b0b51080740d200040c03da000c980b2001540c40b44500c541c0440c06401640c0c9403923241d03220180c055100701e031303800d5040c2e4441b80101c01c803640c540300e52003d030303c0400750016403035040d40c9c0c5264036100d00d84100303010448841108001d210303c0700781c201e0203045c0050490390303124036070702d04a0090f020b0081064007113203448140d007801d0f24490143c0b8490b6501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104991115 1250 104989865 104989867
    0x503060c0708162405010614040e0a1503050706020309010f0302210a1107030305180a030210020903070f081f0608030a14090d0c03060609021c0e0120040905011406 72
    0x800d050100000c414283c003560110360390080c00c00c80700200500f03002c081540c40e2002ca4a5810302e080648400141d81c811701c5109400c000c20030002415080a84d000740c103402c40810344900e0711078004501c40481d00301070074034019444005540764000008180e1a082a200d100702c0d0854000d06034100d00425180b0440015011101254600d250300081c5e440404a03c0c005204103c0351a00185030700014411000300717580718107010000f01d499402100191990000b4140c0c00303031a070340c000d490740304103800f68407c1500802c40c140c0e03c0c0da0520801000d01102406c2410350740e524044a940d40c9a46044203a412011210100c1c9076030150003140d007940e45400095140030039000c4221484400c048080004071401d0040c2c110705c0e03582e01074092600c1c0c001c500303411034641581407000854080307074070600da400d01c108889002c5100303c4941c904188a0040300141014030203040138054800c000403070315510031202e25044000142c10250058071080c0c00300300103ea8a414041d2400560b07000001c2e0301802c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104992365 1250 104991115 104991127
    0x120f0d030e12120a150b0406031e051501080108300d0903030219111f02040b03040b0403120902090f040302030705010507030507110a02060d0b060d0606021b0108040b040215090603010f0503060c0708 87
    0x27001e13400060312031412101071100c40c40d07000d4113801103620641e624030802d1201410300ba010b40c2c0c02007c02d0301400c1200c015080104514030b01d542170341000c503141240d0360018817a810700c401c0f40b0b5055407502c02c2c28100074000d60b50b69140003002584503040756840e03c00c5179050b4a00a034403a074003091494070001d00500e03c07142560b0742071242d4021603619030b160a40070400410820b94400166024510419504441d414a89000740200c0da900b420164198a0116800c001d66119841e640d0464285590f80416496908040781035109070301c0068010760801042c4000d03103603da8000c52003a4110b035240201940d00011003512a8180341c0041d610807000c1c0a2510920b51581c02401e00e0100100036a103000d51030201c2005441050b0300074030150b0003040241072100f0300f111241d0b11b501003d203000c40c464545030f55032520f12500604041d00038040b111100d43c1c0791426204031084004001c000c42c0d1250303528005100ca007000c45c09110f009014020200321242c020b842600c0c560381d07005103001c2c1030107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104993615 1250 104992365 104992367
    0x1150f0c0809040b060c0d020114040b06100c140f06090a080f030601030b090103030201060504140603060a090606090905070f081219030b0a14120f0d030e12120a150b0406 75
    0x2e00314019a5602030b40d078803200c1c0119503403100108041d200c0b010181030851322558019084401550384080c41d8006002003000040e00543c615600600444800c0c0d070f031a48901088960800780340000304640742c1483c094442000c0010780500c0c0244007421034200d070340e0b502c0d116600c803605d042c4000d0a006090010b54082c2c4101405540e10a60600d400582e00740071000250080d002a403007600503075903401090025040030b00405801030100c862030843c1e0b007092800300399201c2d80100340a00450740c1c2c10125040029a801080040038440130a00c444034050a040da10780f04244608014a03100000010701c907040032501c2490b0b140c01059040c2840c200349903a43c450140c00c100030080541e9411001722503503918840c01d004e4442e62201c0c0c1003900d04130b401e020001240c131040e03e03055880901000c0d039111000900c50502c008a16020900d035051000f01440c00d00801c00d007414030a03020610025a0300401000792060442800c10310850882c0e800b9050b01c0c50180c0520b45018000b040f080c8001c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104994865 1250 104993615 104993617
    0xc0a05012001050412020c040c0f0c03140d0b0102060f04030c290a0b0429010e030a0f03050306090721230103060606090608010e1506190801150f0c08 66
    0x80460558a201c03280c1c40301111070700f110300c00c0350100c6400b10b4892012401503130401c414002c0d02c0081d41c0402c6002c0d00107101030480703043c4418100811020104039000c0600c50308010712021120b29074603071151214244140070300031404d9224018460040000c41814200303038010300468064940c181c02450703903140c681ca401d016048202d030310710310024051569201500c82c6481280d02c0740002a0b500d9080341040250b452101d240b44140d648940d02c0407280002100c1844030078404d0800001440100010a0a04143d502c01800e600f42200040044c507410400442c450704003210800e2581e035540d101520740903403400e0803841c0040e81038410300c90512198096404c070718030001d0508081845101c0201c41c00d81c260021100c283d10b07803204000d4250425641d0300030b44224200346c00f0310360502d0308c16161440000e245d00b82c0c44c1062041d5101a4880200321110300403030307041c400415010160081c0c5001828810703003032168803080d11500078911401108890200d03640d107410709a440c54070366000d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104996115 1250 104994865 104994887
    0x27050601090f02071e03111c11011a010f02070302091e0112050604030311090d0c0504060918060b01110303040b01080d0c02030312072106150302090105070b040501060b0309010209040c020c0a0501 86
    0x80c05500c21f5103c15880c410068508034100d000c0c0c403200760800e031004c01800407a01d0030030000b07140e050000c01c44030340c01c40c1c61142e50358850a02c3c00d02c00100d4040d800724a0710384581d0001e500404d28006010403072a651600307444481c01c03000400b48590340e680c0300045c5d20300000d1024281e50080004100002e01c01d0308009840c01e000c0c0c0b074107403d00c1c002c5c81c00107541800d40c0c1001c8030400c85c0120700300024103060203000010050000100484d0078142c4901410030501600184801d075582c1040800f0b81c000d400304010743c1c101404a03a183c2c41c0c40e00d402c41e0f8000003070249205c0c17480744a216910385481443e80302c40265000d000b0314200070000c41064140e000c050712540070700c02481f80c03a0150090f40c014501803042c003001301042661828160032041100040d1010826004111480c420398000e0110750300136034880034680030703582c4034101140140340036000104e601c1c00c00020f0007801c541c150041d05442101311400c00801208110507079461003c03410084e0440ea0448080101e0742c0070b80382540e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104997365 1250 104996115 104996117
    0x10e0c07020603010603020306130204050307050906030f0f0d1d010c020d02040b03060a0c170105060909040809060703031a01080613180f030503040b0f040302030d27050601090f02071e03 82
    0x2040035001d60000b54990400d0704140e0009a010003041540c0ca46021150300b460111b91f0708510705400e08000c00c2c1c49095078002c01c1d00030811440030035070030f0302c00304805a403580c4003d05455410321403000032a03c07440100c0e00078001450484071040c1048c20712642e10002503050b116950b44445d036600b48940380300b2210080e6845030381c40a4900c090345051080310b208000041002031125010703a400343c903c0c00c00460b02d22003003104000500ca503440d49130840e100d500080300c1c01e01059955240411440c400d03041001e03007015001c0307101c00c205074060f081032101071300c1c4000d0803814541c441e00443e10150200d40c06540810f1041540e69a03c130241c1c001e010403070520900c0c0081c00c019845920b02082d580c0d40880002e0000002c00085c464181d1000b0381244000c8a42621424291002035482c09a0032011030155a2100000046892400490381502240c0140042c00d0745605090740c480e41b09105600440d810301040f20461856132003121751060744030395088140c000c90a1444004200303510110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104998615 1250 104997365 104997367
    0x509130b10050406091706011215061206060b12011a0f2205060c03030402010518030f06090c0103090f0f02030106170d020d0e010c021210091103060702070e010e0c 72
    0x4091500d550700000080070076525a640e030759140080c02064515650704c82c0103d1000c002044000aa0201d03505044584954160b0300008090500c0d1482c2c032411860100ba082c9059000161145541006050b00c2d004280402a0b50b07501e60510710329200e00104e03002d81c4146a0014403203c10003145006000384000502401d01411080c0340034280d020183d00862070001c01c5400b00c0d03400c548240c0c1c00140c007041e101305044c03658280c08550f03607001c0504000d05004011a4420854440c550f003010500402000ca6000d0703122608070680340c02059409021500403441c003841554064019003000d9540424170885900c0310707448c0c10302c0a11041078200d905540320600000c00e04009180400440145405098218820500a46020314120100c0140f14100c40880b004d40c3e0084060003540380c040d030303640d5142403080d0107a508002c40d080000c000240b40801080030f01014641140e03001c0010b070100d40060310795020903641d4403440c2c0301d10340e160200c83c0cac018043c40310881c001075003044840c0d01c0e20b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104999865 1250 104998615 104998631
    0xc090a02040929010c080703031a150a0e04060602100f2c0106060311030c03190e0a0308010812031b0c03160501051b0d020705030c0607180f06050913 66
    0x140c00d5440f07030080c0d5007009404104090308041d804020f0105800c0900703100740c0854680e9181001805070340d07006410b25544140501c60340c890020300950880d001400ca00d0342a14240003000250003180701c4000042400582c0103540c209481402d040d80c02d00c0e0014000e071401080008080e085038104603a245459041d0300c02d0247c1d040c100d003107080f0705946809101040c0b0020b80f03401c41d042c60703011008040c03c0000030040e803140c64040b680c20103c01080196a035075240300220600e020000e0340340c00300b46416141d040135240410700450705480790340c40000f1641d994008075680c03036000d41252040441000801c0352402c601c040445071520300507510b820401314080c1981540c103c04001070f100003100c110042045820b200d419440800c00301c2e0204074441c03005808a840c001c2608112040c1e0380011500184070b0100305031210540800c04451852811501c020440c130790000d0080060801c484010855082c3d1256090542c1c04c4c40ea80d2605184090b020040b5044444075115880c903a10144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105001115 1250 104999865 104999879
    0x203100f1b020a0b0703060605030604090f1208090706080f060607051207050102040f08010509120307021516030501061706040b120f0601150c0201021203071103040e06090c070201020c090a0204 85
    0xa08000744541c0c018001e181803a05001041d110b008188204041c40c24100f0b018841d00842030340d030881c1081c0d80010350540503140440ca4884281d6010340315518103082c810075698040700e118031400d039400648103083e6884009903000d21090301e0281c40300c00c2c07500004205051550140c508540500b0444002200c65100c0d00070781d0380b00c100c0958080c4d400203014041d0300401218200240a402c000300603514246089540700c4611000f8100300b140000003042c2503a20800125803410b4840b00100e4050810f60403030303480364414850410200e410280002034543c001c141004590400445208132035461304100300003405140011a070180e501c100c1c2c0740018004020310429481890020300965060130250030310002164000020450000c00360701c0142d9011480351440041d01c0035a45e04e9445845003901c901a031803d6960161001160000300303013021800c018024a819100c10f403294a4287d220a0b6030310030080082d016070f10050600e0307283c0c103201c4801d40c1c0c004080344005062a464500d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105002365 1250 105001115 105001151
    0x90a0308160804090212010e06130908090a060315150903291501020c0f10030b0409120507110406030b37060303080603030c070e0901021908010306180203100f 70
    0x10340310260b0208030155045c2142140c41e0141100303035015002807501c9c100080c04e0324031400a1100d442d4a400022041290403010784125400040c151000c4588501d0020000e005426070b54540c0f1204910008884110022001c3c00c0102c03652005051f40c155240c8c40c1503a41040150320310001c440982c0008504600111405450f15102c540c03100e10146c00021300d880381100d941c82c45880840703040c48440d600e00341e000b0102c8031542408250040c0e004001002004c66020252031182007200076040c180d0b00c400181442d0b44120301078685155681c0900040740e4032800024014076500010401715500710800b1288110081c14480907120411250f0050090301b0003044803445d212001030081540000100358003640a030015802d200b99000d0099403880e0f10700c5000ba20b01500000f01d802840300307404851130610758100d000001d210000000b001c2c070000340310640b211850030f0229000142c0185480d5030443d0000d00030400805d0701907030500103200071580300751030944d1010950030311b1074242 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105003615 1250 105002365 105002369
    0x311030708030a0b0f010206070e010905060706060e070c030212070219080102130e190c0c08070b0601030e0f07140109030203010603080d140714030a021209010510080102090a0308160804 82
    0x350310a41c0364145010f8030b0040c2c44501c1d00c454070464500116a4843e41e00042e000d6018030f40d4905861030884113801601c1e016503540140d50070640000718801030041030703000b4504032180004401140d6881030390498510300704010040041e0442c18940020341c1454001c1c1001c0740c0000c28030121550b900c0e000c607280001541c019403072650049820f0701c080b80c440d410b0f0b02c001d00041009041c6481d0804100350124440d007100112169204180c403c0c051050044101c007580c405151541c510050602d20600c90044980c50300103401c108254420880218880c0c4040000000514001d400d2085050b010308007001f9241c10442010b1000026039824000e8800660080700400d5961a040e925601a40c1a000700302070070030381c0102401051544088401301941d90715111907100c0c2c6450b0000d20181c403c40c8002c450841c032000500c10288010340c4954054802005000b1076240d5035001d2501741d014012225900c20524941000400d0800c001803e00d045e4220100301d1b007000740e56441f81250015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105004865 1250 105003615 105003623
    0x1e09010606030501060504030809060f04080a0605062106070e0319060f0c030902060a05090312120708010e091207061805030d05010e0f01050f010e0306130501060b042103110307 78
    0x3154100318090b010b00c82c003805800d6515090707140c5402c0d91078000a51185240b8940100320000e40c411044240600313583c00b812044040e500d00c00706c1414050080c000a07101c1c10710031001284400107820b0140454924000e181c000307049203a42e041020b4604001906190317406004103002c46e0344628005282c1004244121030008158681010701c108031115404030406140c5820a04005642c40000b130751042000c1c0d240c4281d031150401e0119040c5201c2080310107050901041c80344003205880f00407449010350ba690041d460b0780e2019848403400050352001c0e800d130030001c2d8001d5185100001445983e014100c040307104000095400c0f958600d0f0030098602d41c00125501e007000311540a020700414011008504500384142841c0080c0018481c5921806c001b0344d50543d0369005041230a000c16001b401d0300c031146808074180ca002d03100c1000443d2154038040002c1280004007095400b03903054101c8103d6042106d851448009440b048250188140c91074040c070b45200c20001481a1407103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105006115 1250 105004865 105004871
    0x1203030123190308030a060f090203011502390603091c020f06070c020d1401061403071202060c0a060e07090f0207030f051309060905071808060f1e0901 67
    0x41480c5030480e40303800e208910404208000740060890030322100305407500804480ea41ba100d881544004220720b030311040c0c1c54082c0440006c7c241c4c00702d50146040307940f59900040e4689400c40c0403601c1c1d5401c90420302401248076000c503042440c1e41256425079286c5124003110b01b007003d0024403a0b810450b900e82c9a0780c0b0002c8254a600c1901c0c902030b4004145000a1918401d42000e01d83c44000040ca02800c10100e400752100307659800085e8011240c005252001c40f070522005240131f000540110700c18130740c01c0c010a00e07140c200040c0a40c1255118400347c0140b6066030700300f082c9507100c004103448500c0b500304002c0c0400c1f09031003640b118101d600c00901000c2d180143d0b102c251088144c610508034818400320010941100c24511402ca85141865545081d604425a030b01542e8002c20314440ca414004101c8050316401940904103e0321240207000b03006d0f035000102c9490380250f0791240c1001001c80c04400c0045440da4100e12880171407401c16004c000502840e200850f441081da80d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105007365 1250 105006115 105006149
    0x109080415050712050d0603020d03020a020a0b122a0310030314121503100e0307200d11040605040e03070b0a330521120a0f0305040212030301 63
    0x51115503070440100c60382045070a03c0b4094507510407845031a0044000d0120000f00304113010187c1c2d10400255a008102c1c010124903403d0003951402d41030f034100d0103090f004e040401c1002036001a03510308800c2d091800d885a54031402e40c7d801c100011412a100c042c1404a01c200d1100f03c0003452160100406000d80e8900c2c600f4014204e0301c030001d810310b102c00b08002e05810f040248140943c44040f0070300d4401000508030100f03141c5149924002141858100d9117a074256000c0018500790b8024101d1400c0141500250540008000004c46e400a0411a03001c0000d414070219803a5140080c00018800d6881c0080f50680c0c40b200129540c40d0030010b4200f04104c0482d070416000503000d0020459421203503481c0b81001010802c881c1503038a0748021425070000300380f5031400b414014040ea9525007160140c859600c003107614440c03082c05001002c610a81c0b0b031500b541c0c0041a603030342c1c580811184241c207400a00019205a811031582140110840d03400c0000314000c0031107403080d14032a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105008615 1250 105007365 105007379
    0x5090c0d0b0103020901050306040504020d060507030f060f0602030a0f030e070e0412020604111210060605041d060a050108090102070605011e0911030115090906080a0b090a0c09020a1101090804 85
    0x21041c1801e40e052510520403802d141e64004240c0f40d0124040c3c60000d5942c5407400011504038810310700414903410181041990b5134182c201c130f45103441e401c80c103000c2c19894441c00e0101011074090803006074002d1140b030490340c1c070076100d0420455490800007400a007180405e0700700086500503e04411107002444100501003c0d900f800230018400f504150400303540b000c001c0000f0b06480b61003104441204003540c0010b101c60305c4c2004070301c0b00803c69903aa8400290443c3c00030b101c0e03100f007501c10480706d0400d0301d40f0245031803291400070310844180f400c000064541c443e018100320800d43d421304c14440020980d21a0078080d0440d0b00c16401c0302c01d201c0c440728101c040e19401991801d17003404007100031585450103813415207444900c9058a1a102d003011202000d660740450324103428001e0018a0441c00f21744046c110340120344800d800c2c0d0b00d001c1101e41e2484d0415008001c204107070700403c000512603001c0c005840140c98089000c90460440b9401d48080b80c500340c54030742000a00700440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105009865 1250 105008615 105008621
    0x130c120209150a0b09060f03010f060801050111121c02031e01171914070b0705010c0504050d02040e0c0a14040b0f0d03050a03110412050717071a0405090c0d 69
    0x50150700d240c1e90710072206400300ba020f420b10300c034a014841000c181e89503136544030b0742502d011001351001280c903982c0d12004450050018030a603400320700000004281948a01840c0c929802e070342c3c0007003031980c044c52890840c0e07900c0810f0400030b00c2980c20b80c0d4041c07005140020b5000720120056118984036201c4000703003d00040e03000240351201d5402200c0b50b9100410340c11403102d80140600c034a60391508007480100d90754030742e64106000d0036201280206400001d4507220b0301400080081503250748007034078184a2406015442080c800b40380e030040c501500640d603070b20183d0342664005991040810301000d40c035017185c80700780034075001a103250070140b2480c4049030341101c13001e020004c0e48001c140c1e40d01000038082d041141c0092046405400307a000400d41c0d1502c50701c5183e03903503510003501c00c140c82c200200b1959801043c000144c0e501d0f81141c0ea40e03050341500040c02c0c20f07901e41490042800030200110081400030b2000044a43d46d408809210300c014583c4030f55030306441d9280c2030031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105011115 1250 105009865 105009871
    0x1101030501090605130902060408070f0602100c0e060a020f06071115040b0f0408070c12020f01020c0603011806050909070806011d01030f050309040c1d060f0f03130c120209 76
    0x3001c3c1c0707404010030056075400d03001c1200c21540200010004420300110310b25105640100e20a03100380d0368001510440450313060101d440e250b0a551032451607180780005d0b41d8038101070100040c03107040100e01e14075020700205000f081500446100d1041d070669982000303821a11180803504200c01800641d4092100041d1074800c0040483d02e4681580c0307151030b843d80585458030324481140014208140f0303d0458242ca03403c00b0f400d6510f941d8036030010b610040c182000702c0c0a41c1d180c1c06c613907915500004815044c0d01c0000d10b103d00316803c081058184802e80b07148101c4058071101c0c00500d5445421084e4001d4007040040c0c141c190600485074074022040c0c0c800034081c03100601140300125444a10350550f03902c00c0742400f401007542045403450041a074061760261608002164580d04104241c2c044a41d45081242e428500b07020001140100e00d001c0f032140108006107a88808044000c1da88585011503401001200e6100d20303030340112070b40181c01c0c910070707802070070040d4038050300e0243d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105012365 1250 105011115 105011129
    0x1c05010c08090d0302070507060e2103040302010e0303090918101406030601082a01030f0c030510050102070b181807170c09010c0f15090501140a0b0105070f0309030f1101030501 78
    0x1b00d0b1280c29030b5802d694404070301c6001c0402001148181156540e007004040c1d50464250f4120b04401f401440c0b0f03240d600c41d10040b80803c0320012801e1503800c0c044161035891000810100880d5510100d01910052250304500ca900416100c02c43c040b10301d200d4000e140e100012994014980138081c140380800c103802c00030f66030303000c803201d0132295600c50340f22103100107181a6103581c1038100d80180c01919001e42944070f484d04040d0401354166040d0700c040e1045d14a207003012200c0d95a8001a40c44035498001c4c0c0040c050f04000c555a02261440f000c400d14801a2203244a00c40c4980c092107044800d0760510001500e00340644500300d0500002c68000500b500e0721403420620030000b8101c4c155082e00101000400d400035828065109811005a543c1346020310501e090703441c03d00c4c020500803201c01c5e0600035100214070304410070300c6403090803a01a1034043c40c0c0f25040d110f910070a0b00312101101041602707800807001603c6881c420034114441e40e5607a0b21003413200000340035554160006c2c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105013615 1250 105012365 105012367
    0x90c05061308161a0f0f0a0302090310020a0c17040503060403080406061e05010f09090614180c040302061e070602040303080718060e1c050303100902090f1c05010c08090d0302 77
    0x2004d80c000e0000707900f24041211145590311200c0362030440c5036024249007100b52150100d032003501b80e60190010990007500b10142c81c113035142d94140004074040c00c0344d94000035190149150004a0780350315600303418a02c0020900b45696034000030b24212040f01d04500040c900400e200400405000c6c0300c0103410f0004032010700010940142032074075518880d0a04005e442031f03244c05224001c00c80c090150144007024411181c44100d0180c220f1680e01145020b91800c408202d546900465454060809075171040d28143c81d41c0c0800000d9004010f240720182070740005106000751039030043c8091361103440056180c0c2c0c40c608001e40a4840141018103100303071105800d4207009001400c000b81d0b140340c1018100689020082000c08100300405091381c0c43e8204624240040000958890340100d1040e1000700d480e8601782099026503600c031038000d54116494181840e217003014040e040025026080c0c6210703603440301400d590300c03281e1810118110009000149400b48100c0b140342003141029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105014865 1250 105013615 105013619
    0xd0c090213090e030906071406010b09010906030623060409050a05011d190f180f05010b060c030a030f02070206030a0603021c05060105100207030206030c0a02061e0604090c0506130816 81
    0x1c4d224480d88400511900000800340704003d82d6a00350074a028407402182c0881da161a048070305a4001c0500601058a005000480b5442401800195140150003038802090701c1c5120740e5040d074995415602c100b0900c40800e00640303d100b104c0c0300c0e1074441c0c800b140b0b6504d0310303031840b101c80c1c4c551801c4511040403030100800e640795480c1c0300c604240b00700b400060b1000c1c0c0100d0b542c000d20348800c4203e100f065044a0400340320300305a030300412602031f00c0200400da100408100180c40b6242241609130824001c20003035074043c0c0c2c001c020a00020001610740030080e400520240e00444241c0b09041c0e40741d405009504025040c581c999100003c3c100c05c0c0e140c10780314156142814031400d0702c04d0480e1645500c010b8401d01ca490002c55010340086c1e00c0c1d082815070a402c41d084040040e0052154200040840d6401002000c07903003e03c6480017070649604080c4009400607070015180107024004c0040c2503100c030002400d100202d00e80500c080d034144003020b82415544821606692040da0302 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105016115 1250 105014865 105014891
    0x7021f06030f020f06041215050106020f15040302070f030602070302150c16020310110a02010b030c01091421030a12050c03010b16020301090303050f07080c0d09020d0c09021309 78
    0x220b5000c03243c04464000c040041c510001c0c12502c640d400640d998120762180104001e0345c0c0906d82034a100b4442c0a1156a0300c94900f20b96030420940c0c46d0b10f03581c1c01002c1110710804d03902c1c00c0c00e40050091042d160459200d0030142c0c04581e41d40d00c111000c0380d000400800b031607414416aa0500c05080ca181800e081882c1c80a01c580079032124601d0302d464071310340ca50441d90304009601003d4071600703051259144003005d550b49604800000d0000d942400100040d0786804503031004810360584410709a0707400c240307041d1402052400b00315040304807903a0100c0c00d640030300170a400d14004d5100440d642c030340c01c010081c042081d4403116501c01d414141400185268501924151103101140f00d4031960b00110015440082240c065015440c000001d401d02d541500100d1003400c0e4030003400c0c816214924110750380d0400f2100071032400c40910600d060a4010b800c035400c0280020100300f002555a11401c460124980c084260150300080407001c04400182c0113000f015255410084a400060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105017365 1250 105016115 105016133
    0x20415170d020303280903050c0f06060d1203090203070f1403030301081203040218130c0b0a0e011803080d0b03010605060a0c0803070306120c050f060403050c091b0307021f0603 78
    0x403045142178a40c0000300a0b50068a545441c00303440310009001d003011609010b042075001c4010352045006007854158031103030003ea59405164040c0a4403990000ca0303c944084103200728004080503107402000c405642c0c00c1266030080e101900308414060b01c0c0060014910f44c6000b0124002d82080c8010040c0460200b100d44030000004552641e075a6980b001a4010302e02400b400b548c10306d41400d01911880202e010300310300b8410146884150f03114801200709003d4850240001564211070b1003195109503540c4102e0f40101140a24054607581c480c00c064001004507200c1503070b101050301c854602400b6a10060000b65102481c1014031703d00103144440004000e09140400004034903000e10a6104000511449a40c03030798210300340c0340241d041c1441c0d01c1420304c02d4681e14124031003440c00804503800c80368040010400701d00c0c0d06c81400b482640c001d1442e07981000440b4140c05a109403c02140f08031882d40c00b61202807030940340098120640c460005076185484070500002d00141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105018615 1250 105017365 105017371
    0xb0109030308060d032c1921050c060c0307050c0a030201020601032607061e020f04051e0604060f0f030204030b060607140316110d0f08070302010603020415170d020303 74
    0x1398104051401504080e81d20500844c0713190b4407400b0f044e0140442c8501c0d101c403014070403812140b00301e00080d44281c001807140c140c041d400c0b91016520085006280c2850440f44051040040e2241d28030544000744d007541000e122020140c0001810030f08000707044c0901c1c04105030446450849ca425900000d50758181404010060a10400401c01c61258100c0503134001d000c010415581300340f0b41c90f0130000351050b20403100d5001034450301e8a4108119009076082000f860720715500741450102007003481d6904220805540021301c00001498560b01c00400240ca141d85510011074400c503402400145103100d07902c00c045c41408144002006094440d4002c0c1e4104e59042c2c030f40c0c007181048441440264031201a901c00040c0105800040c0140c4105590089800a0b2030700301e6541032280f8013040e620000c000c051004000310000390381d04058602107020707200001b00f1903102d5002c1001c031b44140342825908850b10004100c1d803200382d0080d000d070f07111200142036181100c0d00e019699001c06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105019865 1250 105018615 105018619
    0xe0601050714030403080a1704170a0509060409020301080601080a12031a030609100b0102010e07090519020a0c12030b01080721050a02030121110607020a1203080a0b010903030806 79
    0x1c9007001c0c800194000c0c00c1c0e04660300b0a6030794072640c0c4d01c5c11318070b954080301488021903000c5405a90740750a08108500c5590406108000303440000f495111950201e41d0b500288138041c0410940798a80384050406000c500c20016942e5051110741032400c04140d00c14580c1e03030302402c1d1f5000000c1d01098130f003003031240c035007004580c440a610b05580b484001c2d860035505407080004100c002807000541452303024408004102c0e0b82d030000012801c0c0c7d140c0110008241c0d02c01802002403090b035602003580a008051401c2c806494102144240d911a40c0881f00140a4810340800e00a42c8001000140e180d814100300203d011000030b881c0c600010000d8062080c401c0f0301c29032080b1164060f108660307032403c08100310318205c415100290420f000d00c3d80050807003501601c0a8807a4200300c615183c000204581104c46002004920703488000220b8208200c034100140c141d0340c201a0522462003038541500900d000300350102220030000c565410800c0400c4200042500043e01d40e0701b1900c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105021115 1250 105019865 105019867
    0x30c36060a0c02030105070206010e1b072d06020a08060a080a031119030c050705010908031c0b100f2c0f03010204030b04080304050f0606130f1506270e060105 70
    0x1948015039126602c610003a42550030801080306c0d150303000c1903c0e4140d603040c000c030380a540c8074a840d10500021500c00781c50045020082c010100e100b0b1082d038500030052080300320003821441c81c0c6a40d90a0354031001c41c1c0282c1c000c1030043c0d00c01e41044850782e00080607507440000ea403802a07a241e60303020340302000e001d2085044080000d100c0c00e010f2406104401c0c2c84045803003801d850020070764180c810041d0b4440c01040c501261a40c4111115800c46007054000c504000a0b03240440c0070460511516400b29030b2842181c8140c0c56055501d22407980c561121000a040c000000d0440921140154000300c0c0000040149900d049500301c0a01b4041c2c560031010b8600c080442d0082c41180c00291500026004000c1040203000c000c6105500c680150b9002e220303040b1086985150994103e5808180d2000c0702c40036500c264440042000000d1020600043c0081c4521080f4482d8001d0300008904040c040082484111800d0011403041d10b60320710303a49045e02000e24900050f010a0400034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105022365 1250 105021115 105021127
    0x50d080610050304150e07030506010b07030c0b070c02040603060b1e0a06050d1d01020a14210606130902030105011106010e1f09050f100602010e0d080705040b030c3606 74
    0x9046002484845c0800822600845c1038a10ba0b80e08218441100c65100700350012a01c0c0041c101610145c6601d0307151034419078083d545419500b0801890b0004205a02c0304040c05a079035401920000c5005502c001035007040881400003961030702c1c400580c6404c500e020096591948085601252a03500c0d0980d02c0b10700300c21451014140c0201c264840d070284070910074090b42c041d4020305040b445d03500c0749400250419640b80281c02101c541403090076140d00c41001c20302c080c0c82c0c002c1d40300500074101c0e0320b8032400e80103a00628060750000c60744594080014462960003045101c051203883c0c00500d500d41c07401000311250a0010410910040e080101c042c2c03038052400c0c90000b80205483c1800585461950f007000d2402c00c50f6840004042078800140c16401813151280a000e00320180c40c141d101100c040d100ca21001d0068030030820100800a1890201405035001d1104803d0190741e0302000240b483c05071440d071104001c071281c2030802e1012080b03031404444440a050ba41162508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105023615 1250 105022365 105022373
    0xa140124030213120501020c070e04050d030209060c150910140a0b040603021210110f1603111207060c02010b03100e010f050a241a0c0106030c060903050d080610050304 74
    0x100701a805400341e4030280200713030200501074016061222020b802c64507056500e40703401a46a206540117040b9400200344990864841d800900e80b26401614403480c1c50b0048004515101c0b103880503050042200080c0060f04a05000b4170b0705c03484103000c007413003030b07440c0ca2104103d40c89010344001817455440c3d4901c195910340d908030f4801103400130b1210701e260110446058459000001c024004ca00d401481d501c90343d4000c09482109070f0176807540d414a55002c0032500580360300301e815818040e0081189240c80780030056091340300245454103840c2e100d00d01c0c000055030180f150f12019a410300b03c0320b183c541c600040910130000346503400f18000103403000490040074071140d000e11490806040000c180e02c2604040400741e500f451b40c06a21b407800e000000040064000c00220403501c41c01c8034403c006040151965099400001501550740d0b650201a0005507000c00c3c0495841302080050000034030000340c030a0301500348821a8a01540050211425030100c10180107012022030240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105024865 1250 105023615 105023647
    0xd050405100203010b03151503010504021303051204091a030a2301050a020304112b0519050c030d090f1a0c16090b010c0b060405041a0a1401240302 65
    0x1000070090304540e6540c507000301c907886a00c00c803100c0d0040c148840355004141000d8000704420f1000c82041801d6900700820032020350b000c0c885000070070b04040300104c00308209000740d0700d07440c407054603495641c0d10348904002522000c00400c02c2c45c1c0301e40805004241c4010a9522140358000313003450f00c46011100401810b0001d4843c1d050710b6180c03004210340500f4690040d4016402246041c0c840e100c20b0f070401000500041240c94825464000c03042c845010680d5040d02d01e2181c5c042c0c40400844004050403954040e00c01d0ba0950b10841e464006810f060051158a03510752800490403414400c070200041c98610464480310500e840c2c60718a0000340c020390b80080f000005584000d039019030009586066801082121413500780008a00e60041c240382d0805540941100c042d550b5000c2004014000100181d03903100b41c561006c41c900304003d107007920840028400080071007071810f0354840b000058210711040b48404001214555200d0741482c0749040c83d10340544c0d07980c120008a048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105026115 1250 105024865 105024883
    0x20306010317070b090714040509070612060e0903040f29030601110d210b010804080a031b05030a0507050a05181c0f1209060504061103040b0c060f1501050d050405 72
    0x91040d941d800e1105d203600115064048442a014565407000040204001c83d0010f8441d05041e81c0000000c014590003540d200314101120310000420960b250005000b214007181d034203105400004090001780052a0203202a000300c030050420340c1c216950000003018010074444500801000007031031a031140c9581c0c103040c101441a5007038100d69034000361004001e400742c05641c50303081080c0004e00e5404d100348030424605030b41d00c0c101910340c0e88174204558001c1e1059004c05032511a0322840400c2d200101600701070541c0d40d2552454012480360881c3c0e0080c00500030084200700c43d0040c2503000040e40c10800315039449181007034500001915511f61a03400910051a52500000340701c0303444000c1803000c1c003884580703896541e010341c2220540801d02070040030800c248014001c940c491001a4501108481264034060b00c8176045d01c226000b003031480d4a10361200d01000300700d00c05001d000b81c1101e59624030300341c40030b4900c00113480740c05100010602241d0f2540020244007080001c41c0b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105027365 1250 105026115 105026123
    0x309060b06040603020a0e1207030209040c0b0a020706110c0a0e0a1d01020d050604090c0b070507051c030e0114030a1e09050105040203120703050315030115080d0212040302030601031707 82
    0xc0d80b01c0d503501c0050003a400c4901c0b1080429400a40000c650500e107480c11018000d20300545401c0b815503080219004010300252107805425102240c40300300d603c000d14040d038140d001000755900c1e0443c000c1c81e11001d11152817a80c1c000500076449901e40c40429001e8460f1035a0038000c65035940d03c108003c20341a080e007100b034040811003140c16401940103000041c40e000c1c051029585000501c001e81e588400010819401790718100800c0e241d28003d02440c0d44914256401140d6400c0011011030061802c01d0800e92094011400c0581185800c4009102802e00d925a402480c025440d1800000c0020030015200e050b410840d00c454000d041032001d105008100340e0200d82011402440205c9049004c1d214800b030032132000b5680810750b000d4940c14703964140f8680e030707220009100c1c3c44180d00780d42d003541d00c80c241032034512a5002c2d83c00203403030740000402c2c01c03200c007150017031030025800842c403070b62042000140050b0b103001ca03d02d810740fa0072009090009000007990083d5100e4082c01030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105028615 1250 105027365 105027367
    0x3090405040b060a0503010608031b0a05010509030d14100b130306060b180a030b13020111030d05090c041a041a15090f0411030a0507021c030b040f021303030309060b06 74
    0x1004220751207003243e006201c140d9140004580301c3c4149800c84140380130703886160f401400044281112050303001d00b02e140e000300340d8442c804255580d03802e640e400c0d106508690000306030305060550520480310318844450b0b10789003d0401f40954145416140035400c0f45044c001000b8180629140d03401e001141e12000c10442702d5511108840c154005002c404680712002c2c80108191070030480070720640342c004100521a860b0705160007050050003008078103010405858902c016028405040082554007003c42c007454407136002c40c2031203c1c104501e1300c51841c0c140b440c50b103604000921a036002007a100044d01d80580e01c0c0c05507000e42c0852407281c0c4580d03600e039100600b40305100580350380c0300107540d0f0740081040c2c48100010303200b2202841c0201c00c820310002d40d0742002504000e4201a09005584110030f45003d505008180360350000e010035142d100600346814148a1004400034a032011801d000d12884501c100300000e11000c3c0800d900c8050860a11000d40e00c515904c9000620075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105029865 1250 105028615 105028621
    0xf0a020a05010f02070c14180c030402010e1012020d020409020a05040321140306041d03040e010f0b07030807030605061b190203100903030b03060906040c080f0d050c03090405 77
    0xe69580305000115025402c080c12811052401d000b915070182c0c0c4285400942401d2062001d8212805101d142d1b110300c01c014041081710b200b244a6000d00030201c1100d9481c03400c1e000140060044103681d500884d5580c1e04814040e80c0921000a52140c02c40056a00d100600105010340666003140f240d2901c0054080402d41e080801041128490442c401c0c20070075100d04d240780d0494a55041c000318941614103640ca551000c006c41e48060001c0c000071700c4c21180c1f070fa071000c800420f0b820211035600c0060240700d41811421141d00400551001c906841e08201909081d800341000080034002620085070300b82e4041d0708058003410010308010b89561034910403861a4034190440852805001c0804100040300c07908410b40750740240041602180e8120404001d20344902e09070105a82c460405c560340d60140061070051000800800090815081a0700c0d500c1c0980e1080d003155210055502d10504041183d5204036242e05210361141000c418070781c11441034182080d4414540380c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105031115 1250 105029865 105029867
    0x1107061a090601232502010f031103010b090102150408040906050604050609060a091203020d030507050315220f020927060108130f0311060a0e0303040215071707020415030f0f080f0a 80
    0x1c0146c001d076110b80c40c00700000e05c180c080f944c040801e612021070801c0148081310f101c60042802a4040c8100c0d280b01c061030703a026404a80544003140c5044000904000c018071a01603280a00800c032440e0746018540b40000d24a4803c0860150180e003010500031034180c052000c11008000000d1100b07413041d035604c0c0081d101d01d08007100c0004a40350030b02040ba002e219105481c4101c03200c02c1ca15020a003050204181145000c0b00f004804441c07403143d0b0f0710059507000b01940032030781d03100141e183c03031044040004402030503421300c000300d90f0401d501c864060380c0c1aa140d0045820308041b081c90700c1d1035803c014040451a0058560300190342600b003010f070b0100441120103192020340d211f54480c1c1d02c030f003010345150000c5d401c0c65a005202080151500b11104081e600107140c6031440e210b45036482494142200c5010100c3e920082203e02c1076050501994400b5038480c107803450042c1c01e41e07891400c000c8018030060311401141001c03504204c9007508031080411002d890310344a44416130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105032365 1250 105031115 105031177
    0x60403020a0507090506010e0409080f0406020c0405010603020f03040602031911130501020c012f01110a03050c03060d060504030c0b0a0b030c031b0d0302011107061a09060123 77
    0x2001c5425100c0ea420006807403020b172080e40e004100503501c8907011030000041002400c5901820741c1c009404000d01040048042c0007840102146e4014101d4100c8030420041100e805130710000500d0700421803446291039034401c503548164031000050b00c980755121400f01c10b01b60031000491080c80e01107102d246240e0140a00182e039510200820300ca0340750300049848480d00060345005c80c68880e1740520301d401c804414544802c0040b03d448400d400540d000e429549101d8500c1081e8000260143d0410ba0500503254042c20b1181c6c02480d40c100070b0045003082600940180001d0f0342c50000c101014844c0c00c3c2d5804203500b1040d14002400c0508240009020410760706120380710b80701d180006070401041201201c1045520819105020703810300856003100d44048045550b00e00184003007038045d0b8003514486004000000c2d00f11403030f03c6203201591003c500705210320b56100400145030382c0a407640003224072580444241c1c0001010180340740c01341029a90000f00c44104030307038071541422 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105033615 1250 105032365 105032383
    0x17130e040b1605030c0702030a0c0b040816060905060c01140a02090a050108040f06200406091401031b030b0a0503060a0e060705040e060d0311010e0a12021501180e06040302 76
    0x10346250503281c80030100950b80c1603107600c801194007030002500340021500030b03003803060010f01610440d00007079440f400103801d140c224201910001c20107004485040001c0345c520295040030101040c00c012000d4120601ea2083d64808d100000f903003d154030082d04440d030064407110501d801ca003451900d0502070f40252408900070704400600203120342c80745076064099a080b1450002441c172070f441300005021030502c40c000501c105020b404210740080d0082c402043c250fa14044114140418111401001520360381054107081e440760118401d0302c070800e40703542d050600040ca84442c2d80482c1c91064136a100d16810b000c0d030020040090304075080142401651400c0da03650303030382d0810181c074240102e0113a47c49100100c00000c046007801c110740d00107a4000e04000045821401d152401c3d540e0f828560740003600400340240401905814248586c0e1450014043c510f40c0d0301946000480c051142071315420f00000710b152090a01d074000703100c0d0025030080c3c5055107407609004c2e599036480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105034865 1250 105033615 105033623
    0x60d0212090d030c050918040203010612030e010905011e031d010c051306080112060908090604030302010b011e020c09040206120c0a110312060108071107060c0b0901050f010317130e04 81
    0x452103c40905115000300c81c26030000508207c445031130381203414681c21004208a030199a41c00010410b020600b51341104a48203541e25501500c0e41c3c400105002e01c1a84042d0502400041070020703500400c480090400d007510b00011015405400c400c00d4100300030842080d5440d112004503080d5202c8010401c019085c0d50300020107954417001c555241f030911558080300800300103540002e01c030b500015490781c082d24685040c00e0101000803940d84c01503008802517075540c003201825580008a02d4850b075500c0c0304400d1100d000d41d901035103501076400101d00c02c02c6840d001030700f10740e0b425040d60301c00540c89401c0d158518001c00300d0701c080e51100d040070380800c40b82c42101160850010485000000913f113145041d114080150380d03140b40980804140404841d00040742901082500001d21203a501c03001c002d415030070401c45811000d48041c0a90341408108001c04602c4050b00e41103030b034003504003080440c00d103164010364005c1c5d030142d40c4910641d0a001640d070700e05000030380c012802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105035971 1106 105034865 105034871
    0x101109030309060a180f08150709060c0305040807062003070f0602071a04060c030b0909070317190206011d06030604030806130e0a141b060d0212090d03 67
    0x107150895107007441c3d5907504007e908010040c1c846c2203030340c40030400068200b203d00100159018040c10742801411084032041510030300c200e030001c084003400d80d4042030f02d5101c02080c1202c1003403080011301003804034061512006c001c4800c000c1d807120a80d1500705450740c60102030b4104403c01e030f6070090308205a031600f00d0421f01c5a407159100d14000107041400140141c11112110003090080f5409070030001e0507000011800192500a40f185e5940550030f6880701d21446070910f410030083c080000010f44540016056050b1012254080000c44104845107030540f0201e400e03039030660002d000700300401e0094145d140c1007480901600b004000b51526041a40c0d5449500212980302450741c0d024014100b60311940e00c2c103110054480d580303c80001c1c6501e01000d01b041c2c1c1c803840000950003c01165039044480d4000000080869858181c00c0b0780e8548401300f806d0400300341 = true := by decide +kernel

theorem cover : BRFrame.Cov 104856115 105035971 := by
  have h0 := BRFrame.cov_init 104856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 104856115 ≤ n) (h2 : n < 105035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
