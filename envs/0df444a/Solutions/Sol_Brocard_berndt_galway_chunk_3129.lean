-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:01.707045+00:00
-- url     : https://prove2.me/submissions/36887259-e7d8-4e5d-af2b-5253e87870bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562589928 ≤ n < 562769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562591178 1250 562589928 562589939
    0x2060a050d02120a0204090606080c030c0f041d04020a0e09060a15030215070b06060403050c09070e030604050105151e060306010c1a1b0307050d05070e1503010906080610 75
    0x20390000400781044660900c10f03c0c0d001d120b4002c01034400e11041000607a11410011058221651600400d04000704503013042070398501d080c122030f0880f540f00c00150300e4070031a900c0106c00d8425500f0060340c0d2124458882061101e20780d1103405103108845000a2940b0707085c0c2ea25200740d084802000315441140414107201081d440138040f0003049880103401a100e4000c601d815880d19001a81d01600142800602c801d00207074540100003110205d141034956118107540d030844c003510f280700d42c4107a40403405550080c02101d61148020f0243c407018502810082d00a00f01114050046210b0f000b24100a281140044070001070000381000f030241c3d0382e0705010f40754100602a41c107110110f88e075400490600c0103900b041c1e2101d100454464981400d81c154806040072150000d0304052040c0704109421405545009c400c000000880d950b0741c200450b150340c070410250380c000350a10300840c00f21703c4010045040e10080041845807598850000d55203000407182000810098901400b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562592428 1250 562591178 562591187
    0xd0c020325050307060818010605010c0b13061b02011a01020304211406090111071104020a170a09020f03030406020a08070804091503030201150803031b1903020703081302060a 77
    0x3503007040614003100154454000c80c0c640000d580201c0003250382541084101c0b00c02d490401d8002500200a01003030385444000f900d212000c9000501c0c80d0a2030740003a01055040103481070441d00b205043c0000855105403036040c40c004800d29005509124482d840c555821010485801069008518151509407420481804243c1180f501796001c0c0091001c911520501e130368114154000d040745081c51034159084036a004081c401e40002408500085400c2c0048441c0003030080d140541c1c0c2d461041c0302200c209005c44000100c440c00a02484180c00303c44d0311500034244240c5440b206905100b04040c1e4a01852040c240140d00c81c0340d51100155500018140c000d00c039003541e0742041d03100c20302c01c0d00340c40e8148002c6c0c0e00d1251140782081410f9090007140340a16031040350521840c01c0c0075100d500d070710000f04209420091145400304008600f4119550451240324480b012695580010041d500407034003038002466140118044ca40c2e10211a50241c0d8004e0140d4a85204060241d030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562593678 1250 562592428 562592473
    0xe1203060d170c0309090f070c110d0507030506090d03200903100903080f060415050405091609020318063c100f0f0614070501020405030307030905030d0c0203 70
    0x11402956142c2c103000c403108050107009442100c0f405541c44103851400d100c8200070040241500803840380c240a5171581001c484034002d90006580c1c00b103030200c140450301a180d001d1005006105034000082840000b040c00d50141603803405a960956800c68210700340c5401603100007410342044007120316005041e009144400015084c0d0320b044001c40e0183c811512640b00560100d16980c04008004135414181135210000300d03400c01c403000e0220505448400140a19802940d540e0085010650104459000c0030500580d0604c82502c480750603000c0c0d00150b4240b65041501b903940c0d90420004070751640300b0900d104500d178076442d01c2e58038042d804109130f80d02c54180000da1201030483d08062050785c032480c1d2005640018620b4264080f0300c42c40960300a03900d60007001801d000b500c1d40000e003c0e001c80d0718510380079283c5110342000fa009114603131003950b15202c0068136400305904000c0c100d04503201141a40c040300040e202c00d490f081c5032400c00a50641210640e4a6411582c00100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562594928 1250 562593678 562593683
    0x31d030913110d1a120c0d050322050901061103030403050f07020d03230339030118110a0f11100c0c061d07050d081603030603060e1203060d 62
    0x1181c400ca80c00b010802c140d000c2c03030301804074544506001c1c00103010b5100c202400001943d42001c8101c41e0f034490307911020405040c51145003144010401d0210400a80b0910380390101581280520320304219070b034400784c5c030442e4001c080f01c1d40005001801807419203550305a040c051481d650711035070201c520f40d0201001040303041c0184159009600c9240d600401c1d588240c40e44220302030303c81034607540e40325182609a5041c5040080181c001d540e0003241d8a803e50318010203041041503038104508542001300300203101008000021a4070301c488486100e60140d490402c01001030700e0600300700344601001c0b00041040e10380035040c601e21400c1c41718465503407002a19018416030340e024082c0da00702940000041c50100c071a805014462003038409402c52604100e40b8420f034140019220300c400e00c940d030700c41c1707210701821000e001603002200c088040d02c28040350042554074029000703040602060350281e1403c40064a0f0701400180f010740c00b107180c1e0b055800c1d907840d03100b000ba07a502440c208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562596178 1250 562594928 562594931
    0xe1c0c150e07090209130614010c030201090209071e0314010b07030e1201020310050a030c0905041e0c030c08030a021c23041502060c0307032c0706031d030913 70
    0x4525940014000b140241038551000341c0d407040030104002c068003601c3c880b080c404c0d00c3e00400f0800f003074000441d00d0300d145082c20072101c101c4003030406034010000d80b000a500802480100400d0720b60103980f0000344864031000c0043da07a18106e04400300e4903030582150300204054010700c42140900e01400c0d41d5882480c200201000e0030b4041800303202e1031100c118172070b0740110610540300c3c0d20412071005003c042d142004180c0c51a1100e041c0d00c0050b100b411902d640d5080850309010825906040e62900c0c00b1b11143c50b04260301d0880d120184074401603e1010200e500403c0f0300c0404400c443e03400030309074020301e03c141c8507104030300a0315405601c031000e2200c00248540c50b4042590412072a601d48541c050301c492031b1503c84041d4000180c114021504110f041105003040300040c0d81e0070001d607240000d4030300e0030498403040c0e000d86109078030a80d140701040d011900400003240819917066940610a03214098060320707582c6910005004240c000b030010b4009810142340c807460182040c1c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562597428 1250 562596178 562596191
    0x801170601030b0432190804120f02151207050403050a24060611010c020a020a1215020408030310080d020a060221100e0106170103080901090503010f0e1c0c15 70
    0x520505d9280c4c2c54214008000311801814078040b00f40913507030000c0205541402c80b02819512084940308902030154440b040b2100320b001d01003007118500c007903a0b02030303c540740c84081c141031121071ba040015405000c41440000819a038812406e890480b03038070100401e81c0c204240e5641c4210441e584580780e48440611720780d0401d00b41d0303005003401040742e0340390404400740c00012107007901c82140d10102503621160a0300c0c0142c544214100407124045e002c0301107010a440d00c0d8894a07c10400d00c1d10241c004180402c0100020004501902c8200c0c01011665524064640c0780d02890601402503000908a000030a40d540c006209621022062003807100000c89c86041c1013a090303a05005210322190180030310542c503528140500110b0401c10301000d400c00303c584502005000081a6510208090340e20f80d000b40100c00c081c28000b4001d00203002d4124240000303004071200b800f500c0c4551002d403910f228a00c3c1d000801042c60b40d56902a49109841d5402103007450013418045558580c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562598678 1250 562597428 562597463
    0x41d1b09040c0c060222050613061d060f270f060a051204030903031d0d1103030705060f1006050f0307030b030f0d0503010311010201052401091707060801170601030b04 74
    0xc004c060301d8052140c0074460100c0050b441581b00e0860b085140240d070708210105641e030800c44404111000c41c0341038204d060380404a059003e1450040d150000c0340400c0114005613400050014510700c00d07041c0080807000a64513003542c041c013140a410030148600195903052030001803881c0343c49410454940344020280c50500c49040790281c3c002003200609204041e440050f60710541040b00c4950800a072000020740b034005c0010000b800011295082d04940d00d007402130380c800540040c10703101b0b94a40140301070600c0c3e8044541e030f44907500201000c0f409074001c00c1560f44c80300412010381c2c115078407240c058004081c03c0c54103c0d4584620304144503415030800041d07159214a60360380b5125499864400614120b0211050559041c03d0400c83c1496903484074050b814a0440d240030319080b2500141c07214450b682140c0c15010800b0b6814240700000140301d8101c40140d43c070049260707616100c01d102d00511042208041d000f000042010424005501ea00280100c450901000028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562599928 1250 562598678 562598681
    0x70512043219082b050301030c120f0501051810020f03060f0409020901090e010c080402030a02150f0c0304031b050a230d051c020705150c070302030102041d1b09040c0c06 75
    0x10542132000780303021001e42d03035003000f04600f4124200300c600f000c1b401c55056030340d40c486441c1c9900440900043e00d0b43c950f000d0203486c41d43c6445584d001030080121341421003c0b640d518100a203000d031188140e02d22110542c2c082d01c01c81396003102150f0440d086403212000c1008902c140e00281758429101e815060150341c0d1070102c8d07070007080c05a5000401403a50340e845030940b540c0c0040ca0090200b41004c0101613100400c800442940c111030000307a50650b810300002d02d004010614040c800085442e0480c414000001e0061704d016195448284111800e403251842450107019003082d484d10302001a0395070f1088040c41d2020501d06000868060b40c0828807104400400b81c2e002d0348210030540002031000c0185004040610251040a06050110b480c5010406440b20424000241450040810b11840025640c000c00035035903650387c0d544018018021017126030961240d100803444041004010b5611885004055801c0004100412008100c0b0204401c2404101d05040c00003030180e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562601178 1250 562599928 562599943
    0x30606040b130618030c0311010c060c0e030f0105060109060f120f0603060b0d2a120c080d18090b04090b090f0d05070203070e06010507051204321908 66
    0xb2036400e07544081c03800c04020065041c840e6000304980c0c13800000d04c08140c00c03842040039260800c03400c0c01803040910049801d22101400a804149004012000140c0c42644405402400c84c216805031400710b0300c080c200c49090703401602090104004101e86801501c14001c898002c2c1000d6602c0e07065040401c0c192101d169125031081d503242d03028802c00925204074440101c00b41c400110701e999a03503903004103021101c10442983c0e011460b80201520141800c0003402c8580b50041a41d680c130300c1c00004040d00c9008407000c5d400303249141c2440512a8000e02251241070008024039450160f0700740041c600280c00c6500940c45021a10200e4990b03464079000752400001840d01d065074142182c10310301c5220358041088020014140541d0303000502c1c6003074819841c06070100347c58004c011b83d00d51082c0c5100030034070b0280780c07100003038902c4a03000f420807201250300d00c2c1d000000c2001c150b00015158481220340c1d042c426003c52050a2050010404010580311481c072103440303500700c9150094 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562602428 1250 562601178 562601197
    0x90b010521270115080f0a08090f04020c01050f060d0807022b05160b090603160201060509090c041127040b0d060902042403030e180f0601170c0906030606040b 70
    0x4481010441d2813a03e508040010511303100a8050620481d5006445001c4070001815013400840c1c843c10070358501018990740c000c010030466030740c510050f00a02800b001c03200d0000030580c650004d9418101341d80c94400455200071141e1820210f0341c204010a03d440c00050400940d00301003082d0000800e02003c011401403004254070700340d04109640201150b00071803090300045c000301c0c2c81c54407030038140da803c4481c00800c003541900f07000c1c1c120b0042441d03034030441c1c2c407055a0301400003c2d5030101da80604010140e6082c4194513850458078820702c035044a83c40e0301040344448210079010158815103411008001140700e51440001984483c8140000e0360000ea9039a43c14045203042d2061060402c408140ca00c920780355403d8a48601929200c05400d0044245d003002040d541c48582d0f01e00c80401c582084800c1c2014003546019140859a10f400b207000c803647c0868601615070780c0e070703c22032000d000c40d80b6020a00081c0041d0340c0014100380e400c020700f80004152408008090407542c00e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562603678 1250 562602428 562602431
    0xb160530040305090a170309040e010e03071a0a020306010503040201110109170a0813030507140114010b0a030f090b01260304060509031902010e06071a0f01090b0105212701 76
    0x2138802c8200f181035241588035031a0420032002941020401000b82d6400690454000030340b00d40d4840d499014011110500c800c41c0400103c400c10060280341006c0030481c007022540d280e946c0c60618504901c070598056010480500016005620501020020300142070000c240510b55039a001420a070b54903092005000120380f44944ea9400b054066000c810654406401c1b451924003400c2c0c1e01c921a80a00000c180350041c0f40000025080004480c030180500e980d250394a4040c3c40c480c3e040a040900040d040400c2004001602c0c081c0305411a0080e0070550182d2800386100b00801001c11403408607840000d20390800e1405101502c010720070f503180c044d03072a008082007505160200056101a54142c480100543d920068100c1841c10545501b6a52015130400300717441d40d04c000e800034101900c0810495018020040c0320b0403142000d00a0021410a000558050180000d008031401204c5200008241c54244c00c41d04140b4014a1002c4caa0703a403180d42160b40500000e494190703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562604928 1250 562603678 562603687
    0x4080c0106090b01030c02060412030207030908070803040302090903091f030b090903120112120f090506180a0b041d0c070f0b090d03020403051b0a210b160530040305 73
    0xd58050150301b000041a2001d80594503244d91088011800b102441d0f040650204a110815002e11208000b8242a6045420107a030340c0c0141c942d03030ba2050004074050244040403c1441d0b4001007541d1a5a10041c0483e40005a21011400c201c0b8002c4214003019142c046404a070b4031800600d9024040500c081e5584071898080e25003941010b91000c000c0b03502c00c60042011070b558608204601c00b0320301d09540c085542010440e240d003055004140c0c000c000090358a9249075800c3c1030098150305640c100c15281e60740c030382c81c40b045c0110b10404020b89400000c01d0005082044010340c446d00c009401420001c20380c6640a140010100880311402110107001820f4000c11103950500280d10703007980303801c2c11966425100c0800040440d01443d03d00b050070001d595004644018003e22012101c208100341032000b150304c2c081005440e90700e4000301040306040d088031800017002c80ca44489141540d0725064502e02c118031018010742418006004610b494400503441c01340340a03580300fa4aa = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562606178 1250 562604928 562604951
    0xc020c100e0f271003021804120207080304090b130e03130803390102032a07050304050d080f0403140105060103060e0c0a09031b0f060219020904080c010609 69
    0x1200d095000d5584290307442c1069094030f101070284501c600f081100341948507100c0c0c4810415034155500002d43c400c0e082047c208030b6501a0410754803442c010b5203c0301d4111031102003a61604e14901408025402c1048240400701603034102d4811aa00503006081c0307030903a010700d04100c03580d600f01003c9a41000984030300c0078007407400700390291051101942c541041c207100600e101101c5294000880c490350401e10454010b50841c84401110030700955892a25011100c403e0388000322003400c9210701285001c1d07210902041e28009544200114507060900c01045100f1107041c03002c55004008200c00d0804400724409000250f1066041e051100c80d034095803802d6400041100d41010300d40f4004210050b402c000ca1608008100105651400000d0781211110840d030405000700608a110040b0510110f03450011107050040041e24143c45030700480c0c4842c4c59601850307000e1040a800030161502c11019a0010f2240c035044d480c0030105200e00d804d40f4201d611003000966500c089010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562607428 1250 562606178 562606189
    0x40312020d050901171801050705130e0408070318030c0303080406050a021603360f080a0506160e09041b0807080a0f02040b090103081309020a0f030c020c100e 70
    0xd540c0c1d6142001820114182e000030700b401c1c5a5205002e1464469002c1080000034a01d849403104006000740020700d400007018080c1e0b481004038140848240c040011540c0041c0d000d14082c40c2e120810600d4404152401c031f580c04d44652560151002c4000000001900805030b103005621a440d041d54500d4141030030340445600411010926004005880d000d0072591180c1254a0b414106070fa11000e443c0307030b82d030b54544010f00050010082d00091a03c1d1084000c140021220542002c0d00102c0d100c010b095100c1d506040000e195621410100d2905072000403841711512961070f1021584a0710400034006001c26501524001c81c200850740c004101c030146c00014200c80c0340100080e80c030b807d040c190390380b45112028040840d030b00000c10442d600d68000c443c0fa070100600f0803070156120308009500d41d211440102d0306d0001d14030b0001e030a00c0a402030b00c0301c01b0207685401182d2070540a0541c064064990943c0450007211303291081d9170755242d00c441035a0655582c26043c40810000d009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562608678 1250 562607428 562607443
    0x10f0b090705090d05120d060302030c01051303030804021302180103050907050d1112031308190309120203011b031505030102030f2805040b060f090402010f0507150204031202 77
    0x24028680342080201050700503044a90794503007030380c00002070010b60030300c1410407000c3d03031903010f090000007450340b0301090303540200d81628000c5081d600e01c410b0030740c01518917100d007001d0903030fa0310140041040400c2c000c804107035105001030400d040d07a118010000049920985004950300d00080d0101d45c9540d05100c0c199010030080000c0200350705040000b44461a072600090903000e04184100c002d0f20703410703202c5405000c9041123a4031011a40014180c0000c0c1d030013202c2481c1718001c920401c484582000c400c1c11382c0c050711010001400c03d0104032468030072060a0784c0664842e425a40c0540d40141c009a0104e0503540c0000c01c2002d5010340d105040b0b00c1c1c0c0c88140300f60300600a000540c840d50011035040142d8a1300d5526041c500740e10109250201c402941a49180108000074000510415840385404442c07007460305448a0421031101003d03100680000c80d085000c030b032000e0055005000d554000c011080b101000c2c4010841a64000d4004070360700100021a4408190104a0703007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562609928 1250 562608678 562608701
    0xe070818070506030a0c0c0203010e070303230d09240618020f09040902030a0813090f18060b0103020904110a0f08090607120605031b0907030204081002090a0e0405010f 74
    0x6101840ca8200003d40e1404013410301c5458543e2400245000c60107000c11000066025009118842c03007201c0c1d0035156552440180c0205002080132038046a107000550603c42c00c2001190a02500c03c04020003810740c108125040c2c03055500c8101d46400c0003020002c25030b010140458045c0c24100b45154040359001c1e2400d803039005003d8100c01c000d81c0300a490401800391000901038a0fa8000245080c42c002c1020b4881800003440c21504529400f940098649803c410b20038241c494240c0e9080304d0f0030031040c030713041a0f1001603000003031500e8000300115041490701500700800e80c8006022507400140d440500d040c00140488265000140002100800d007003102052601800c46515014000d0858003048488240d203020010240e0008002d40710140843e1005580b00c0070a00000000d48070240c0b14412a000240ca070340e00c40d008403010f44040201800c00343c0390310b410000203900102d849a41c01050303618045100c0c4a6001020b11460191001040603800450030500315071005510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562611178 1250 562609928 562609933
    0x1009052701050a0b04090b0604052701050708010b0405090622020d02070b09011407140723120301080a0f020303070b0f10120c03080a02070503011806150509060907090e070818 77
    0x6e04000c1141c4101e2254004000d58000c6807980c0c802c1c1d50041c0301c6180301c46400b04121849400c407085801584120310801898540c3c2e01682d80703804180300746020350310134507a01c03e0403540041c60904000001080d070140c802c001c07076401d5101d40404c1c8140d80201c0e003a901100e60120301d040174840910070698011402000801130008010a03402d030350b1000900020034828060030080c0054203800c12282840e40000f814502c254448085400303000e540c10031110746d0301c2001411814845240210790480340c64600506186c405642c074009141240c031411b990500003400302c40085865140100e1040e0f40440c500408ad252640c2c03140300d080c40e141c10250140441420000c005021099108240ca0f0000611034542501807000c030300e44403c54000765010750806010b03004968110814401e1035120318000e00000850502d4003820705943c0c400c5e20f52110309140425460306080c0d080301d030010442d00e44200b01a07118514084140307002e4410400003a07288081108003082801c0d60040c1d105007001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562612428 1250 562611178 562611191
    0x60e0103060918120e1e0108070f0e01030c0203130f0302120304060203090904051e1c170403050c120301030c14040207121101091407090605091009052701050a0b04 72
    0x18003030120420008010440310b44100ca101c0300c9402505e4204a41c00010304841c2004110110300040042c070141d164041002c01010400b42400347c40c9003101000241ea801e0320008036900110050b0030300b106140c0640c00100030102018810010b608054928400c0300d408061440c410b2124480302c005502c1031581045c0300134131000303030f0200807106604403c5644201c00d44171801e080303042c2131242000c050042403040c2ca22239504c0011818540300c00d040f0205001c01c002403202621080c1d80f170310b42d20050311030400c00240020b004030081c05105000a003180d0034001d03071041d11f060650003030b002030b20103132004102000032201c1158680c1c0c20290549041d03083c0348c0e09695049105035075600090520038030507001e140010095012615042d00040b28010040308526519150310580c003580d0703c480c0c14607401040034105034820760f0007407641c0c15041d1403151500624134010300e00902206040c00c0c00700d138003825448941c00d002c240650007200001b0141015841c9c403085528000d29640500d003000c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562613678 1250 562612428 562612451
    0x2090405010e07080d120b01170702010c020c1806060c03040b0c030c1006050105120606310608040201020616030b09071d0406180504080702030d0801060311030f2806060e01030609 79
    0x40030b40240c040c1180010814039a01801030349c0c404140080c04070741071000c0d030400510315415085041944042e409980340d0300c1205061004402d0300400e0003407426031040109000b0306140009120308060390060700d0070180c41e50f04e2002c07554000c01a032030380c40c2d0003c156000c603140180b140e012050b81e010002c0207480c3c50240083d00718040d0680d42c821140840e00051080e84441c02140c4c01d0f0b40d14440302941c61100100b8002041c0800d0105081c40b170f0b030100d000714a203401346030098015038058008004990700c0ca80c03084215180c0502030310400d6180c210600748c41c1c8951000d81e009100d01d45600300804008251020780809800446104074181041002594415240004020910b4802240b90346e500d04140d00c543c0308030140203401d0f1180300548000306a102000754165101554180807a0728a54034006050106039083c640c80c5e03581c140804c42c101c200d8141c441ca0081e1032250f011b004140c3c405880c003107445036440707400428111240d418940da450f12460000c0c1c03c405408104080200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562614928 1250 562613678 562613687
    0xe0118061a0a1206060c032a081305090708010810060620014503020d03020c01090b07120f110a05160c3203060f1302090405010e07080d 60
    0x2a1890790340d0540c005a40200ba511403c0801a4207040300000d004040e035404000f80030800da40b0b81900080e0080d1418400c40d2060310b10005014012650fa800444c216140c200300c503032180708422042c840411000849860b0a401c04d0b205140d035840d8100c5941c07600e005641030801c000c0744200180d14144050107019007010240c03a001d5103006100c09070041810040d401007019050040000ba08101d0f0020341ca003030002c003903a00542c510b2aa00e00e4100c0c07010ba40561a024140050158103e55000307080c04d4031940c0074066241c020800450001c0035500da0320084071090380d0200016030003100c140e031b0b00d001501540224400302c2404000300c10300c060907014980180314100041040020300c048640b07040341086036009800c100c21150304c640e64008180380300d0162031a12134849151038094007541c82002c1c0d40895060290240c5000da890141980c1182d4005041501006106c048880540c4034101c686105078070640000441c202c1c1520100e1800c0420303881503605902c0581e110040300d520 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562616178 1250 562614928 562614959
    0x603070605030c040b030c0901020d02030418020723060f1302060d0c11071401020d0306060522090207110405090706020d032a08060a0b090d0b1f0e011806 68
    0x40e86455500d80d120809a01002c0c8120b5000e140607500202c203104080300c240c0000c0070100003d8003180c0d40e40301e0203141640c490140f4860040c0044064980084010040c1c0040c08514469000c550348220b22142140103940141c040b50404e9120008200b2000c01140f0200d80106503158562180745d0301ea03000480c1c510584890001d1a92556044c0c038260707019181510141018200b6200b03400c0c0c480c504405407040360440035005108403059605050300030710480d07050f1061039843c0c925051201ca910b42c0004245911490f80005010000500980d684080d0030050702c42c0c10351000c6042450200801da074400b41c030403009038010001c100025034001070060041c642a0501198038540d816032000c0303030000d04824003101c0c5560403101040c541d01891140c85608100e4040e051291603070f6020119010b100d044c10b40003035081c102c1101180078405400d0344140c0912601c00d440c070080c041007026840d65800b6a000a00c03000042c800140c095880e82141e20024404109007880d01c04000000400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562617428 1250 562616178 562616189
    0xc1006090b0f06160b0403050a120507080c16051002130803190f020115120302010515031b0a030c030503120a02070221030d05090319030b060a0807050705010c05040617060307 77
    0x80018102400013030700a100c21425070001c208242c5c2d4945414054465840800c2982c009039140e410782da00055284606401090f4950f603040d1550b465941b01012030317100d24a042c80407a40c0c00f001f03000040c1c08200703000b01c0102c07400c00541c031041081c041000054030368000e181103810a00400401c1048190b0002c8007681e103103042c159020013214182e0050004425801c401020180d011454050416642140c14840e500070841640d031004030880c86184032900720381c150001e14080045684209120103c00070051a0409003507407999400948140c56008031507a40000c2003010540d41c001800c1940004001d1003036150260550020300024040260074042c2903815010070b035080420401e58071121040f2800b0481c0d03041203400c1035565008010692400017041410300b001138402d02030f0701184030000d484c81d410074803980000c2d0769090008004d401000000d008840104d0fa00340035a6802902d161035a95a843c10450700800c1c007840030240304100e1159074140061a10f000a10000311031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562618678 1250 562617428 562617439
    0x18060d0209100308040602061503010c0816020309030f010f05060604120b130b071e02070513110c07030c06080708060f0108040809060a03061401090807290c1006090b0f 74
    0x42c1c403000c20008072000780e0009045070748003080200700c072500080c01c5030040402c80181d10340c552100b001c060030f1301d488000c294001480300001c206000d120000204400c071480c0107485c102549400032030f02d014103c1090880c1691a101c5203070302030542e03106844e0850402d0721028a031508100c0f465030004080003000f07010030346c400300113070611500527140301c3c08540c8000c00107001d00300b4180c000c0558100c2d08070b982d00103100441681c0664000280c0c003040f41c00c080c0c5019028201100c26000038009085803100c142400c02908020500c24040e110155108111907140d8509004000303002c4000103280c0801d1000307000c28448075658030f000d90941c484092074a50402d94841c500002c0c540141e502c6507801c21400f08000d094290160414000c0e550100c00c0700180480769401110041c60070312a4072040d421035070341841415800d0403600d5415240801c0c24066603283d0541e44c1c1964071042c2c80b1881a00720b50030b080d0006203203020f0000107100b0840140f02c0c000303a000c0015003007490807070300c1403191 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562619928 1250 562618678 562618681
    0x140313060f1b03030902090c03011d060406050303070c291605011d0a02031209010c0b1b0a0905100309050d1d060a02010507020d020601030c0b0703030e01060b0918060d0209 76
    0x24464249800d0300c1c1c040002002c150140382c500540504000c0004030f00c1500403a00068a12441c1c00c140c07030488416070090722030741c65032070420501c82502402054011340c03282004203160728200b004040135880707940189611454800f44800c1e900c1c2290440c6020613400040840d50034a120580d09411224921f0705500c066926100313004011b006191090982000400b030100000400c605440a0083c3c05035040782c06031101c084c080d44a200c1481d400b00d821540680c0115025085d110342c042c5d1500c1c1c200c0b180c041c0c51000380109410010304880043c01400060045003040d03409995004500c1c241440080241e40d5140d8446001043d03100810840c0003168400441080348515400030140145544042c5018002d010b410308541000152140e00c80002c0b04610000e4010704898101001d44030f05030400700d0b040419802410141c2c00c02d5228400c1c101211002e00c43c460042c0025424103950701c0d4840140100d04655545403c0e102012400304416130300c43e00301c0106503960486849005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562621178 1250 562619928 562619957
    0x105010e040c110a1209290a1407200937020409060306200a1d030115031202030c0c0402030705070807121407110d030e03160314031306 60
    0x90429540710415610884c00310000744100e00b521030404a40a030340f000d126540b039130761031020000b4440f131444840069101c4c583d000b01c4200b0291007054082c0c5446001550307040010039258000c40000e0350101180f0007843e45104094248582c82d02d8155142510b91a145280c0300c0d514030084428184611100c46184125045a1410201b40c248000441d165034499007014000c3c501c900040320364614200550307500395007112120084004075032040c1d2405404031300407607481c0b55903d4140f0044926030503404059400b03004c0e00c025806165202c4131070f41d20318180031100ca0800d0f2040f905541080140f020f840c03201107400320104ca801c0d2000b6a484e22038070f030121018480d040e000350070780401241040401c14240b441001010480e5111103800c41c3c104c3c001801032040a80040c20300c01050141045400d00302c11007202d580c080c0c10411140006030b400301e82000c150b40c00e00300d0102a280d009104100311005498800e03074080d07000f035091003aa41c02a40c201c0c1500d0190000b80100d0003071140c071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562622428 1250 562621178 562621187
    0x8010b0901030f2a09060807080a0210120f021206030c01051c050c0706090b2406040915090608030c10022a120d05090d0e1c020a150c0213050105010e040c 68
    0x44c0c015a800310703610320703a20701e030300300050005003c2c046045c09a07440000b501d8400041813004940c00a00c1c0b10a43c2c82e5080c016550440b031b00d1410b6007069141d500d034180c07000291003d403000c1512042c850100f4500002014100056030101c2814484d082c4201509411041b140e10310702680c990300080c0c0c5480d03003a031082441c011150000d150b14100b00c10a4108580700e40c0d8280140022002d000711340346c01c00340e411052200000d1150b0010f030180000c0002c0462a04204140346411200780c44240d1a0303a492005d42c3e025800100e606d81c800520421088002c0004514079140303a80114145184286a0703808190034850b5021b441680c0d0703c0a0170195402c0c0111400d03040d40780c0c102035640b03c035011200003401c070480c2c0740c5049009003904c04050314056403562048105c02010182025509661000c40198000342641c02c10140c10000c61b0880340c0381d90b01240d450584c4c4615108101c07510410410240554401d030b0f5460620004101c50390300506001200042100d000c1442d2528000848 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562623678 1250 562622428 562622483
    0x40c090b0303120a090b150d30030b150c1e0f160302090603060f070f05040e0112060e0f030403030c082104050d0207080a0f03140301030c08010b0901030f 68
    0x81c203d460440a00481c02c0d0746a00c400b25051040040380125501d4001c980755000d03008060035040005102c05100041c80303a003400466414903c514900041e4604c00c0d42a5082c0f1140600042036654400b01000d1030192401e403034140c1075100d1246099076642c03a82e41c1361041b820302071910481c4541000c5442c0414410422441d0144040714a103a026404411240086200c10390091035160046084da040100d03d092092030001c811034043c0c0c0380c0e12802c4030b80120310320044c820401300380004209001c065511a0003400b44100340e03001003030720341445400c5400e50301c20b5100560060b42003226000c0044191022240c1504103030340d4144c1d032070921a07903510038020280d0000d0402d5003c0320383d010a0071a11030141c1d0251040700c14030403980c00c0a030b0303603803001c1d001d904801c0d0302803c50640011620074891802e03a21a24021000d40680c18030b0b9040ca400a80003140c0d40d0b8290750062200030300900c5260905982200d0300712255155480c0c0040558a0f01c01c00b801490b003205070300c00441104804d04c3e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562624928 1250 562623678 562623697
    0x13b031b040c0311070602040905160804030f05040807080102030612010b01020703082101030f110418021c1a0714250620070209010f08030f03190908120708040c090b0303 75
    0x240e0317124100e244c0840298032600516034124a05004100001c40813002d01d1240120b0303450b2082640c5444d01c042d1519003942041408126040101007003000c01030100c20002c04c80714001580f24200031040050203400c6103136918040e031504440d642c40c1da0740000d100c0d04694010300419a034441c007810314100d42554515201105c540c2d2000081004080fa0030007a60364010343c82d619240714003004000503600d8801c194a50207981111040240c82c016500c0362862080c0d01919a9030388499035100300e411114020240d4801e660020488025000400e40031180c0451594925006034081644c1c951110422040148a02c6820301c404010f156032022003151006074004009214a00d59a880d951041100b03e0141041d540002054600120513409540301d40c07010b1410148000e01e5426160002850b20203481c16200f0f842030501c42c00d00c10001e0090040c03840e0f69447c02005504840d440010b0b200e001040030010400c0042080014000180c425454021802c1001400040c3c550702810210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562626178 1250 562624928 562624961
    0xa080d0e1c08100f2c041214270409020415051203040b0f03190c02060a0c0f08060630040210090803030411013b031b040c03 55
    0x2021a612100c0c0c0c80d080441d90580d11912595140c981ca046420410300c20a40380148051040c010743d101d18100c00000168015001046841140150175200040d03d003507403000428008071901b0360740b003000c0b503508030302402055181070301e0070307078008c0d005038440c40319107540500a14080540e0303a942d00f00100e072075002042408040c03124005081c11140c10301c54103104409110f0b480c3c550000c044240ea003180e038144c003010b0070120001c0000c08181c0c0024101c1d0085000e11075a007807141c01a10805210011039401056a486d0400d800c0c0200c8003200003003014414490f0b070603508c0d85d40c04800719603c8482a01d00c183c49485900d0790744c9902c0010052010100c009885543c10354201c4c4060702c2c4658001c46985103071b0081c1e42c1c02607500c034140340280d03040e076001000041c0c00700e000348520302514141031603c00810129000ca000d4840000403044150341c400d03040100c00e82090030340014807400214040c04801c02c040401c6240c0c40c4800d0441070045890b00342c0042c3d094041e500450075603030000718 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562627428 1250 562626178 562626193
    0x3030f07140f03101809030228140105041106030f16030608030d0902040c0e0303031f0306020307050c0d0813141513050607020307030c080702040f0c0302041a07050a080d0e 76
    0x2c45880442a40558117081000c0c1d85001c10703140361400740702e20154250700500400c001240d81110703031160140d0307154048521005140700041e0171070b6002c0e00205c0c0210000400d401d01e8036050100c405042c45246c4145800d10900c2003070000348024542080106264040012881005401500807540074003a41d000128030801c079070754641c002286a40c0700710340401543c1054402036030804d500040542d0103510500c0042c09001e031814241102401e25044a1119960782d5940816640304541c040d00250000c20740200c58501008190007840c190304001c50289000f02c400401041a804c010340030000b15030000c0c802420921064404c0f0003e10802d82081c03500c1c441001210f0310320002255503210303038400548071a2000c001e031180d65515542e00e22f100942c9483d854165080306006a034080c1e0f68001810500200b8031503841084031a840158440780352008090b45100020019965458100055000908049810040e11b90303c0120302e81c45401803c0104010b000e1029141e02d98400c942 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562628678 1250 562627428 562627441
    0xf010612020102150f16020708010501030309180c0e010e060903010c08060901080319050c010b130b1203040302280f030602130605070c0614091c03080903030f07140f03 74
    0x80c28200050003a000ca6045800f460004503018604488181c3c14500090216965160081100d120a01c840c4111150161198640c6086490a9000303c0109051180c10001e1441d076080c82000c5001c11070040103a030140e03000c080c01600200c0710050400100000032030880e6100004d4039500c21000d00200901c808007900a050800c0589001d4810504140001031200001044961014142e004451241d6200c001603900d901700c0b0101d0340155481c0d07002880c0588843c03002c5240483d4404012030440c9030352090000910030702103007609540080100b800582ca0b0702103240f070000043e54094000884902c00700303154031020342186840412041000003840000d40140c03690081061000e070b14295a440c05072036610404c00000c000088003041080f145009608801c120301c0140102417500c000c844c0044e040c0c14001c081780055a100d120b50600f4940d0251080d0380c08031a8000452560401a49448140750020b041e401007109400810103840d000300305455500901c210065242d04103417 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562629928 1250 562628678 562628699
    0x5100903080706020706110406020c010e120d030603061d0a08090d0203060405100f05010e0615043b0103030801090504050a02040c0206370209030703022205010504061a0a020f0106 79
    0x1011300786d404505011a001e00300700ca400440d001c80f90950000c0000039045801550402d00d5418415442140c0c248000d01012080c4820041040213640004285e401d40c41d020f012038101011400d028000d620701c4003450000003d070701d10550b401860f8241c403103030084009a0451098203009406004110a000c02c0100004100c0300721114181c0901c180074107a92500c045031000d100744800060040041490380c10304c40d1510488050240300540342c04d80f61140b050281d1a80708a4170011300c81c80c101f1808041d103905900100c2ca0301e62450307601e01c0d450340d01e00401144040c021080c2045d0f8600100d02000401c0284904482e800703001480a0741c81c2050181d11160100c03010b0748107201c0407040c0b04076490070540e030101071600f1a5001010704102180356000f9040300c03004c6030305481000d802201580c1c9418030380c0c4c14641030400d031600c2d90005d1101700c3c0c10742c2d2041c0d00250080d41080c9080c8172662440d8081030188629501c081d071500b8002070124501160b9a108040d40d510b840300c00310300d10100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562631178 1250 562629928 562629937
    0xc080a0609140601030504030207210b100b040510090503071205010c021f0902150c01060f1a04030b042a0518100e06010215070215060105130510090308070602 70
    0x150041000215540d150110a86072044a032040b520118030008034958000d500440c2c2241c0203104a5100c1607c2d100c6104e06d21502c42e14548507443c0010406040001c54504140d102d1541801c10a8461600300341ca03840780128040e041c420f0640680c01402180314848400081900404075250155038003000c036520100810156007950070501d1015030075000294030040306180883e544038110001c05401c00400d00444103d91000b0b000f2494100694040701800106900c1000050907900e0060104001c0c03155030320956511102c00602c01510300c3c48000c1e01d0841e9044540940306584901d80f401c8080307028191080800305a00940c074911843ca042003054400559413000c1d01802c0c8102144020301c1180e00791081450202c0900c07860500c031007080c0d0850418011206903413424001142030030000c450b10300c016403015000001030005015000d4204900b800c0080c81e18280d00017844003008140690341c09100103110358802c0354070500c0341d08000c54100291980b50380b000d02d0301e08044d501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562632428 1250 562631178 562631191
    0x30f0503190c06061415030c120a05060a08070305101505061605120922091401050a0507050702011707110d0c0c050f03031e1b0d020d0305070e0909010f0c08 69
    0x81c0c418003182c0170400480402c103c0318010140018001e0f620300036800ca500042050444e8601440214042200e480e1000d0061031b5910000c40c5901e0b002d8140500c5a605901000f0310b5440a4000c2000c00e20218884d20b07402e884d0b0b60040f40f0420300e0b00555454504540c803191300700c1c0c80050744014003941c404c80c84012910400954040d92107901525490740914030441da848803090098030241c007510a07210740100c08040c0049003c00940d1038082d59044000300450312039441c1c1c0300b000b481c1e4070640318407a80103181d82805410014075400003410085135442e2524040c0800000c9601c0030701404e059001c81d86180d04a400302c5c0c00401c0010000002007204407440860481e000c1510b00e040b4150340395020001d0000c5007401c6c00c0e00c41c0208000541003480082d500200460180807881302c4038034520341caa010080003401c0c0c06602c002c0c58252180b40b000704051500c0248240603510059540d200d920481c5c0c801d8080d258611094014490b01140168052400c211014035540100a082c414123 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562633678 1250 562632428 562632431
    0x6060103110c0309060706060b0a080406050a0c0f0309030915200604031b03030902130506090928020102070b0a0806190803040308031806070509040f0213030f0503190c06 75
    0x40285501c11990300550381e070002982c0042c80741e0851802c00001400986000b0310700400c1c101d54862120703102c0d81c42001c0b41c41c000341c0b0400030030040c01803030b0241c56041588920100301d81c83c0000e41c01024202d50020748020035813580720810915225580c10f6000e401c1c038110b03000c01d6400c1140d0140c0004520409103450391212302510ae40d804e00402c17550701c550342544845800816400300e0000c2003c034281c003102816640c801c10405070b1112041d905000c8a0b2000005d00d60510038100113480c02c00410408495000075529400700d1198052113460803521002807100c1c488920040c1e0410742550003a4080500209a110505921100d80c60140074151406000501001c0760780b1000078141c0a074280ca50300c00c00040000541c4280190761040d0b04a40620003d0941981a4180300081c0e43d420001500030503e0006840c0c50b119924101e0100321003140360000c11407400402d40c0b810320001d080c0c0500155440c003070101c00c1c802c1300c6200c00b02440316203c0801c20b40000c4d00111180100381c0703600707 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562634928 1250 562633678 562633691
    0x307050108090601060309080d060b1312020d080c0c06070804290708090d0501020a02010e0606040e21070b040f17071115040b040303030603170301060504090b0a0f0806060103 77
    0x550080c0040c0d8018012400608140e03801d100c0b081c2e020b84540081192403038010089e80e0b012036941d01c9510090098006060743d00c0c484041e1f00203c0488a0300403440a00c820745001c07006a9400b1020319130154016802510f482c0980fa4803070612910508103500142c00040385410407a10400400a9890f40d64048480801440c4004050000d09018180380c4804002041c04200c020000e006004002026502500041e959031802d9800c02e01800001d40e440c0d022614605a060049a501400541c1e0412160748458800c541c0c0e4110309903041903d81542890001c241c141404407000242c028201c1074050605107061460485140f8007610340740c1c1c80c0c10403c40c1d0b05207021b04440741c171604122500e8002c030310f010400801c3c60345050200070384001000005112108180a80300070350103a10700080d42c6195080c0486080e4085141c3c4104003010401130081d20b410405039000d89620020000c0c80f41c081c41e0108103801142c1c1c200100c1b01c001d0b441c1c00619030780000398084c45000700780e8050055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562636178 1250 562634928 562634939
    0x305030105150406080708040c1206020c1c120f02040e09030714011b081038041a2b06080f0705031e1c05190f02030702130e1b0307 58
    0x41d000314010715001580205c04540b09500c070746a1715070404c0c019034420004658a02484c190300b40002d02c00c440d500d4001c2200f030113480e0f0500120248620f260b0320025102d0000c2c84c024014003524013940340403a6901c07240c0c90b0325a4207a0596000d046000105622270902c05542c82d982c1d04403030340c100c0b003030f141c1e03482c02034102c1d01d060007a0342c610082e24560b20a40c3c2c0450b8400c0d50301c01c4000704411003a1000210014001a0402d00c4141070200c01e0140303050908041580c1941c001ca054052a071020204020000c00c1c8269401c1e0445071094581d85071070715012848900e411445080d1004920340340300301c01c1c4803080385601080403500d03250111603c0f8003040c100b8035141c50303883c45100e1b03141d04031040c0381040150709800d00c540e14501c0000d076009104580c5551010b0750683e41d0b41000280042a0000084680419558840c10a05129446248001c0029602c0c480e15030000d00442c454210313210720340441e40080c00f10551841c01c1d1080d242c502c0c0d06281c008051962000e100340718a1900040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562637428 1250 562636178 562636219
    0x2070b0310030c14060f0304021f0914010507050a0b070212070303022502100806010e04060311030c0604030b240d1b140f060702032401051525031206030305030105 72
    0x8544005003505e0f0404595400c44e481c6600000d201741c0c1c00c0340391034138024549032030080065460111074440c56981420418044141c0b100a131503141404810040e180104030000350200d50f141d0300c1a80d42401d640c0c0d1132401c078101a0408103043c20b612002c00c0f1f0f4410150960007900a03400e030070000801c15540607490a482c0302c0c40342002780d084980000c20090641c8035400b6030b54032620604000c24480145c90200b01110455801a25a01403d40719600180340500011804045c122401824170381103842e0000c002802815840e003002445648a0280074440e102c0c03049208018081c010000060900c111035103140d900b80480400c0044022070582c040111514000341d001d424146001000018040340c3c1c3e0124a0590b818458007600551407902c4030308040615040009404565142809001310281c9440750303040201024084805505d000340c07000400c06d054004120381c10b5803d03042c00da600c140041c1c10340340020300b45030020041c1900140151304a80c0280c42c01d942c0030744c0040d500407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562638678 1250 562637428 562637459
    0x80a020f06060f13111317120a2a0b0405100605100507030806040e0106080a210804030e1306150e0a0602060112050c03060f07031409070603090302070b0310030c 71
    0x91348070011301e512140000c0213501c1041c01400032041c66180c64001800455102880c0d801001e00411405100d01003800502000b1103503918454158104000e03204041d00280807014000d0802d1070218003440082030350b49604d0590754100300c1801403801e01d810025114180c400103c0f2103d400d106001038603040100c20502c01400981d201070810a0079a405c840207000030380310b01d50103034680d94100311501c020701c54100103042900c0204075030020b40ca04000b01b154584260000c180041012400c1c560f00710246980c410b91601e4404461085500000e0305044c1c00041c41e50701c3c0e4a40303240494508004803000c10306102a45030041956a08000c00442e51980d0180e58010381111004020070030a603c0c040010f40d03c60b8081d56081080000407078544501161079001d046a01c3c01404038190b018456400820f0043c031060140d0f01d44140f4142d82c480c090b203d00000c25684002a1003458428890340001c1c2000c481495902d007040c0c0c41244484081d40401d844100c3c00d00c10000700d2941c901c4080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562639928 1250 562638678 562638709
    0x6031407180b030a02040f090b0703090c06050f1902011a060c15190e0c13180b0711010905030306040c080907091505060a11060703020403050307120309080a020f0606 73
    0xc265240001c01d4000c0d0032003004041d01072055140300c07001660350303025a0039101e04921001a4040c21820071203408080541803405152800c3c8003500860a400d1400c02510142d080660b40d41c1c2c50042443c1d854810803110440302116100271000440d810342217020454039068515001007000740c100107881c8030b10000111568045040301d401c00c00c9142c0901e41c0102d1085510100030041e2000d44207903000c880403101190054229070b4050318281c0b181c6100a14004800c0058066464100d521000c2160000d0000c0004400241c41d0a00c07070040c08001500c1c1d840280b1030041c01d0300e0b09660303940007503580c10721403805c000078101c10074801c00580c0d200d0700380040181810392405807283c0c010803070013006240d000121000400c96032240c9000301202d8409590b40130b0007500b0302000320b0a082e8050075010805004000030000b00e20000191129a0f0304000c00d89041e02c040340094000b00442a401420b010020030a900d88940200c1d50b00d86004261083e201c8559541c010080240701c800c111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 562641178 1250 562639928 562639949
    0x27010b03030304110a0302060706020c0d090e150423040b0606070f080721080702070803090d14010b0a0b19020d08072102040f0f0e010b1b01060506070606031407 71
    0x20300807a004d4200b06600c0407011700b400c450140c60750041030b01644807600580b0300e2900000c01c8110700c2e6081101d90128402807500a241d54106481d0010400025014124108000c0070942e131b0703507441e9480340074644141d01740300c8200c0025490503803c02e03404031010b4961448080c001141c5041503011144601d0f404110001c0c0c0c1540760f920024150803410301a140d0725079a07400800c101510700c10f0310f1102030a41e120201d03c1c1c9019580246000c0c003075001041c00b50402e0041c003040d80c42e8040310070071503544100c484481c10300e907840950041101d0800303298886050780c0d00283ca151070500401c1011442418403407040d220728010790303440c1040418100003178000c40005252794810340320303400b44a071030700013a03800c001c0480d0018085ea00103030001400303100d070240304109100318400010300600001c1d10308540c641c9000400d04481c019030746400441800c4460300513541f0401c2d800500071b03241c02023111f52100e400741003400040c01daa0004990010b08070103441c0c02c03036800181980c2183c50f00c01d0b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 562642428 1250 562641178 562641181
    0x1a03120c030403020d170a030515041e0b0f030102030a090213060506040e190504030809011d031605030708040f0906051c0615030b0c21100509100e27010b030303 71
    0x340161a085908140ea03040d551b1003102101e144924020005000c2540c0c000c42d050510031004102502c01099240c41140341251810708031803011002c5e000c0801c6d6810000c0d40b10300e000e021850001c450701a15615504c000104800c020090303200140c201e00964560310024404c1e088103041b2421170154641c0484280310410004502c812040d0b408003254021043c83c0030010200301c142c5400b079034100d01142600c0c04004a02d00244141d0b0301100501a000b901c0d032003211012503d80c03013841c01041601c00d909030406d0038040308000f20f1f0143250780030040560382ca9070703080c3c65803800703026004020510342040c1000a8a140c000c56100015004140e103050110040c1c2d02c1d4001455514541454440004800004680f01b0980980300d00202d203000e0340c0d984289160700200140310080901c0e00140700003070060039008a00c03120300340d070350659000e41280c03151102d20641001980c04181403121520811503d04032101044016112111910b881c102401d0a0f040c261202c64a455425038010300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 562643678 1250 562642428 562642433
    0xa030c06020a0c0f060915150e04020a21110604030b060111120705010f0509070305100c051c0207030809070b0d150503120408070e0402010503071d041a03120c030403 73
    0x207000305042d030032504010ba002d080680e00d095050b40002000d44643d40c1e50560f05080c0100d8240c00704541e02c03200420051018450482c58810b015030207140c10b0000754000003402c40d181d10101002038a44c89816841c0454041c0441300c0c80c10ba01041210822030846004185082c068107840903207a00031071840389540c64100440368904000c42d9074030184078440810006408a40052000c2805100003017000070b5015480c1d02520009402c404055011410400104a02261a5031030002000004c541080180f0382141c0324040c581c000c1200041c02c00c41040000055070084c10840e00c00d03195600565546441a034444015210f0011013403000c0200d10160509940201d144481d0302c0c0f6010709958544011a15040c50814070802d00d0b9030008090004600411a070703001000100c400040305c1c03030b05900080c0b003404098008001e101d03040315442d0540c4400206d0703802080c0060400c020038981c030b4881a480c4544e0594490081c0140c0c0c40000e08025440c0444904801c0e58008500d4145941d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 562644928 1250 562643678 562643681
    0x17160311040509070e0a02220b030112030e190302040f0501050a120201051c050609090c010c1e050d210b031e100f020a03050606180f06090310020c07080a030c06 71
    0x3e00007a0303503008145011404824441342d003401020074160058507a29400520b400d0512120305d140102085020100540c44c2201c045a055401a000030189120799140942d10007940c4030303005178020010090150045030220040003160b00841e010720003040c03140708042c100c0308203000340e81e04404100030a10801e515010003e80d65841072510510784a4649540c207a1201c2c5142080c08540d182c009002062410096094000000341c2c05000850341d0b01c40040d200014444000f04005000244240c124200c520103c0d22190460291040c8505005006010b650320050344041480c06110030259040d861186c5008008d0180080410182d4259a6210510001c90b030500c5845030800c040d004ca1307071600400c10f880c4012000035848400c01c203400b0b0103481d00100749030b014001c00c0c00200104d4a00414000303003518241c65004501c1b4000007c01d44510480300015018869500190306010855004100b4518004240c0381c00c51340f240e08190b11a500788030f001c3d0000711003801c0d82c00806e607203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 562646178 1250 562644928 562644931
    0xa020a0e010f120501240f0503040f15142502060c07140703050703061a0105030a05042109050a0f0501050a030e10110304060b060324030a0804171603110405 69
    0x41d0900000488901d1a80020391358240c1000e04400001e0040c2e00c019100410511038210f00e5041c54a1000303421040140319010046c80604025a41c9145da810b001d9103400b603610a100880702400341c1d25103200200e214000c19140302108007a00550500305925421401010010a40c01f030300242e00d8141c01e07000e980c0c001100c20f0755904200c04d0060340b0403504118200040d07100e0030142c0340403495030504804039482c60f000340e0501e02c450550707000c0581c0d008044a0340109011000102525207040813103500400d4030b562841e9010340456424026002480c1404841c000c40b81c203820740361220080405010107110b4207012400500c041c00d039203402030300000540d110890440d4041080c0303800503c244c81e0459800409210f00000b80070912a0383d00031389480c80810b42359249141403841035031560010551746440381a0341c81d401200565000c0c004a421203070800c0c20389031116120b9000c00044124190009440d10581c3d49440003002d02d50301c01001c42c0d4005642034400c0d8130603070a010203003c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 562647428 1250 562646178 562646207
    0x108010515101b020427050601081902130f0c03021c06031208071106180d03060807090b040b0931050607111009080a0909110f0708071205120a020a0e01 67
    0x44614442020000d0300051b29030101c401000a6001945410406d09061040c0c21001280e00480079100c09903a0f100302c06115a5070545110642d41c010310300c45801401e0014011024a003800c6ca16078070340340d0503000b43c0940001000344800c0040903d03641c0701145d00030b200080c4401451901d40300594000c1001c10380c007002a05000b84c5002c00d0106c22818008220341c001d0314a561040e48104125040007200102c030070a040070020390b8184415641d44504610410b1544c6487d000d0103002602d480c0c11120307002c04003a0050145081c00030040143c2004228070100b000035600c0c0c00300c0f68001e245007080580d5080300240c5084d886618040313075054800d2904450b948100d56040c0d101054074404d207142c150290f8003841d08c03841e2074107000300b90400d41d0b400340d22400e08084500c40108603080484006011345040141e5501d0940b502b8911070040b04009449414651244551203170001d00a081d5000031083d80441c1341d56140c40311040b80552043c04000950040d0300c5050b95014a801c04010749 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 562648678 1250 562647428 562647431
    0x7050a170c06070c14010507080406200c070503010e1501050603100803070c090e030915090301111c06090e03031902090a09091a070f050702060904050108010515101b0204 75
    0x554100007901e004010348200b0300280c0300a10308014001c5070584d5481c1041424000d108905141c81d00a20b00d050291014018941d41c40c0300e1f02d0746120020503a01c6810f240c114564a4203401010705480d44e016205440c040c4d402e001c0c030302c0131014000c140d02441185102c14400c0030f0f400d0500b0301103180c100604098481c2c0302d841010443c0303803080016008481c491036203051031310b08000001041d162040c0c01040303581e009000c600c4680d6103c2403010300d021511030021307403510f1310400000d0145c140d0401d00b045c000c00c00205000f41072011040d40e650a090450240451541c40a03440d08603450080c01c11519003040c40403481e1503491448066503842c2403000903050801d0100003c10410741a441003110350794a080710340c20021034182011305c000911070100060f180151015010748804040e503000c201c0001104c40440d43c4800640e0a04540604104035035078442c00c200c0d00800c0706842880c8440c164010b24149442c11f07201d04d061500082d80c4200200304d071034030800e510b0078801c0001c03039200b07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 562649928 1250 562648678 562648687
    0x3060b06070b13050d091a07210f0f08062b02041d0c060304050604020d0f0c0b0d0b041104091806020705250e0c0702031006092007050a17 61
    0x48050414600a40014000d80140f0b0b03a9843c1907444c0c50140300042e418418088070803c0381b184034581201e8450390000c0400d45d80e507418a00007001510120490f0014200c035002c03c0100c0750f01552051441c40790780c4400228050810060f50a46400c41d18240d00c004001c0744000f804506800d94003500320305024640f039039042a0f0025040d20b1040e0350300c403144044031080203c9400704010704c0d5000c40c01521705518608103512903c0e11002d00900c060302070000c1341d08010400c180741303441081454100350205142070b203a04c40002150300a03640b85071181d0a102c2075207510714151141c940452580e0702440d00d8540340c584d90f0300140c00ca100c0b441d03041c8810b002007a00400c106000900d81140700e28094004100b203c140880240001203283d620494801414000c03d60426075454101e49000b0342e02c0d44852403440000d00d480000d1495040303030f034104400040d020708160080c0c0342c2425030207404500040c1e1400c40c65440c0c000c03002c01418542c0600605004501800b00e0921819990314549151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 562651178 1250 562649928 562649933
    0x5071707020604020d142e0b180406110f0a09091a130506030a060219092106020708070614011403030f041a04050613030b0a09050d08071107060908160f03060b0607 72
    0x86201034a150387c1c40d42c2451440c072401320503a1192000010003120304100c0101c24002040102500a000400e920342c0c4030100e80704420f01c0002c0e03520011003240c400350740751f020040c0240204420310851071024242202c1000c0c5c401086000300d6402000303409180103a40c101a48805080083d000711b030140a00c8031404040386807400200034080807500c0401c01451300310b200400c1c00110f0340c04650500c45029040041c4000180420900c03900300601580f26000c50901d601c040c4202d0800520703491412100e9907206032480307040c1d4100c134004a40d248084200c2001e05803244542120f04c3d02c0341100700814031850400713a400c052a4104480c1c0c0900f8140c0300c8000c02c1c01d542c01054140125200c42c1c0f01002040a0850003030f40c00580c0c19001e00c100031095440c683d46401c1010400305204507100040c01d801d00c035002e4112080000e00031541040d0341e4810290030040c10f030207140c00502603a04001c80c840950700c141000c41d44be18200c4000c0b94a152507000092000b036144650015080180c40701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 562652428 1250 562651178 562651213
    0x6010309021903060219050702060406140912060405120f070b04050c06030c121015030c170c0901030e03090a03150204030c06030507020f150604020705010902030105071707020604020d14 82
    0x10310304ca258010b80d19000200c0442c0d10780d5406a03000104070007008240016151113081e10211a0f80f81882107400d03001031214101802007155407500007680c2c9544261020001030080d001d94010f0095501e900c040d4034544109206040c2070300c02c0380c03800700941c0c0700003109070f01341541c00b0707004106541c0301d030001400041032580140d40f18020010f020455280c225000c0c0050741c1c204040300f407410000717482e0142904002401440c010245940c8001c10f070306903400340510140f03800c0c036008000850f24103010f1101041d000304c1c0005000910f400c0071001b0201c000000c03078410301b80040030310f101c0340d1559640c00420602c0d216010040c680038440000024010030106011381030390349000c5000c7c0b81100e0024a454012400360000341e00c0a080c401d101242100c6803030b00b091040c0c40c090303501c0101c0d08020f400350030381400003505586084200801540c0c032025269801d580b00c0844000c9441e0504121b90303425040d540658482400078201c4005412000043d281b0742c1c141c410342d030110340714101a48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 562653678 1250 562652428 562652479
    0x1207080f060601020f0705010f03022a0609070e0f01141305010e010e1f0510111f110c19020d053f19050705030a09030620030601030902 60
    0x21440d81c030507418071801d9a0180140701c032160002000709040c03460417000900642c001014501810783c001800b0b00c1c20b004040c040700d00001209040455404421036135550748030221690041401004d1000c0b07220740300c3c0c06400b4041c1201d034400d01742c80d90a0181e1200c140e02034034103441d401030a90748140e070404a0744c02200d00811b54900341c00b842d50f160002c1c21b420100c0003000b080c84007441c11809024551210091700540e14103035040d046001a541e01a1001942c802c26511180720b050703440701c5100181c0c02c1c0d03c1d64050100e1003d02509540c0b14006285000d0340d10000315940201c16492040b200e000303050007000d0b00040000304083d0068036005e04120a0019800041c40b41c2c003005030b950b00c00f503401c116070080540e034019000400404549524000c03100311303140f588255031100134202c0c0b18009030340155400c042a40d90f2901c2c0010040c00000c12032004403440e6050482400c0f41b0006d6450500d41c0c4d8030b0000100c0c2c41d640c1c03880300440040c004d07803004981c800c00e11070302659003d55074004017 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 562654928 1250 562653678 562653703
    0x110909100302040b011b0b0405100f060807080a1e02060d0e030304050f1b060304020301060b0408030c0f010c050f030619120b0907152a0c030b090a02010e120708 71
    0x1a48100d0442c0180700944c2e41032440c19060109001c2c00454041511160040c1c69801410034112600c90740703049400c14920900c01980d80d814403c40c10340c040190340c0807008039140d1078100d80e411695000042d803154901600078299059045e105100d14880600b6100740ea880145800d1070990784080c0c14040381c52424116030300e54408030410040280c01c020010540001c00020700b0200481542a01d22900103d00355001e4240800814210340382508104007a28001802c01e4441c2e1b21543c0c42c1d41d0326001052000d00c03601c01d1804007042d241d810f00c9415405070042d501c091030180c0f0a02c00114682c00900001d41203242100c800d024400c40f00a1140601040481d1200b503912905007030f81c00380303400b41c400c0c003864010204c10030411031007081161411049060160205540c501100010580019244401145036025508000d400c0c040c440c2074a00c6840c2e103201e103842e0664002d0365041820402408644100380540d0b0600c0c1441105041e05004400c80301c1030394681103540c1c244100e00001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 562656178 1250 562654928 562654951
    0x50327060406260103080d0221040b07090b040e0604090809030d030f060e0c030f07091a030610020c0d0206160507090e010608060708072307030c0303050603030913110909 75
    0x80003c04998150048030510181031151070550460b120f1004620840011100a6a0004013041c00d41c0030310055440441080300c00c075042d40b400381403542e200b51040302c540f0001800400041245204c1d00306407000e40c0e141c4600020195a180180002092128803e40e5101800d0103080e0865402308810300c0d80400641c3e0215600307105070300310700a84180e40c2001d104071000c20308000c80b0b0003681c0c0503264003083e100c0710550f01d40c80f810b4041d0740f03c86181e081b620403017210300092403240c0040c04c0154060358060314072441041d050038080b40c0f1030000c17880b20340d407160754400d9070805498048042c00e5400341d814038482080003035075505c03460403145030311429600342c1780c8082e80d410680a210303900081664030003804281c070702500d00a01c0c514004080406200010a100d118040302d25040080030300301d041801e030390f11410709001e0304014081c00d00700c00280c20304000030a1402c01100b6100801d40103401140311030340450b50070024240d08600009428410f01404010b590340d002920300911400c6035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 562657428 1250 562656178 562656197
    0xa0506130503010506060702030a060c0507050d021506120c0d060609021b070501030c0c171611041b0f110c030109030c1704050904020d060617070504060e04050327060406 75
    0x502d0301391103000700850b105003414003044000d030f2030104100411941c810400940c2d10584c130015296130042c001c000e003080c4135080c50000c81e1030f0001055111400b850765400c81565955082010713618410f0b21204090b000b40c1568200d03405d2028003c4021445940080380e02505d5202400c1280c0100f11040c030a85203010682405034018041b51018007400e180074450301d00300070009090080b101000400d0442c440600d100c010126006035400140d030040751400810306030800b0580e402c41078100702d2045242514039090588101008148583c50380c480301600301031002c00343c032081300d1480031040f00e01907800a0203103942c1c20f02c90368144901c00d40b910120810315051800340c110001c40c1c01280310b00c08000c18489136a801e030550750f00590450b01c0349642541c40c500304011786019400240e07111054041c408407514081070713500c195482030740d080000c50b95800c00e02000060644000d0941d810410203041c1e0401c0845459000003001082044c02a0724000483d41a6000e54081c0000446071503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 562658678 1250 562657428 562657439
    0x1505180603091f0c08071404030615060324050f030c04180b010e0105010c1202030c0604061e050615130b0c07060f0f02151f2c070206060108060a050613 67
    0x91a008841c0c10f8001c00700400038510b42c000e440c550b00078012806200f514030321000c0406000e0b0880f00a19482071090100607108102400312140354080c0a000ca03050075070260300801c8440a012040b40c030600d595810919120500c460410080202c603094040c0080c2015151502d004060260b0b048035106403030001c0c00d060100354954103800071941c0311124001008181c0c1d106565004e92900140754151080040406034550f10a2400305c5545001c2c040800082c440198480304c1840d0030024100c4d100014090030408030703541158042e80c4014a070001546615900c0040e100940045090240c569102c100440c07087d0408030389910036030310015041c480684c0c40700401400041500b40184190030b0351030041d4880700605c101c8061201c1000c0003503400c00440d41e020701420042200341da10261240320252100d040ca0051541503d4501c001c9207100181d095518800d10165020b4842900c0702c400440f03c01c040509015032002c0014004240340c1e59110082159680c4414a00b404c580b521 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 562659928 1250 562658678 562658713
    0xa1a120307030e0d030807051b060711120f0f13050901080a0c21030c0c0510050d05010e190f0b04050903090405150a0b030c0f0c0f01050a06150518060309 68
    0x1054060701544903052084c0001c0c0d04090300541002007400e01684580121030441d40c1c90443c031000c4941c42c40b540d02030190454202d02c0c801136030084041034482040d201a043d416502c640c410a03040e840c010403541c80d01c4141c0c000500f540444866040c90075a64400000b0b100d11002e0704040101c2c1c0020700104100141c40a20710b0040084000b00703070301001010380c03036031201006241c0a410b11404a205604001c1c81004040c09444010100c1c4000d01c0300c448018500e8000210824045150500120307004094641c06803241ca00201c0c2d2483c032003209144040505080c1500d00051500c03650600199943e9014075441603003240b00450b1100160000c00003a40e9000d45441d440005090312a6603030380381c07180c4030402d903842080d80b60b54039213918040c6078941c450101c000c043d80d100851f801a00c4500415105000c0440d503000b0f210726201d00340d9500032542144601d07a01c80c559804d41134229405100a0b0028003c890144003454210801081140d8811103c2d0700041c0c200810513a8003800b032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 562661178 1250 562659928 562659947
    0x6030c0103051b281d04060b090d020a0906080709050c1e0c0307080a03050910110315030a0b0103030329030a020f0103150801020a020d0201092a03051209040c03140a1a12030703 78
    0x221b9050203410320b4540e41c44407611a04070600e0245d241c3d4041d440c19512041200c400800c03aa14080001036503440c0070307d80710581c078019440558101404100f50b10300800640711001c820075140c10b0001c8180f10070016990002041003003d0100b4803062002c902450003901c405290398070046441c2c0703080641c5508040c401d140400c1c41c00e1811964249032290130040e6580721004000760500c1001c0034001924001d25210001d08404c0004000720801d903164000030b4454078144107800c2406801d0380542ea480380f03101c103055003503402820f5110240c5003486034100c0d802d006040c0050003402c2c41e810031490070040e4101586a0303400040300c0b001d4a904004040c00b20081b88000c03c01c102465880c1c5001c500b09801c94140610741644017410184480781c8840210f920400310740c00f0a03908042d01410707030000700044e407142e840e007804c0d2010b0b540603026100494004032280f1041d950307004001c9000340f90b282d46209130401c0b00480d4030080c0c0c4400380701110a01510008544035a0700780740051010b4903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 562662428 1250 562661178 562661237
    0xb01060f031b0c1b0807091d12090118090504030e1009050a03020d021215040b130506041202010213080606031212010303110a12030506030c0103051b28 67
    0x2102c04450300d09903000669040c45a4442c0d04258411484c1d14100c03141041d60b0000003113800b03080c100103120342c0c4907072040c0d14a20a508050700c082c5220398645460301c00c40c800008a00700d0800294005600c103202d04000155902414080746441c1c407014411124111401c43c00320750900018000d5140010180c1c240c08920300d803102200d4100310215203c1c5e10703039220081c0203a15041c1301608650f205034004164000500c220750200600c044814540101035034156100e1584501090442003900f0307450303442640003001443e40f0b0700c6655a04d0008203403104103030219542484401446591003111200a260703510023001181064000c150402d454650021b01b031010800050243c48802220350781100d8042c14404c1c07540750721a1400b0b00388089010000d00381d100860300f40d40c23400d0701940903600640c03081d000c860b01c4283c6040107604407101034401503107001c400c1c00c882d55894900e5006203d032180e0111036510b815a409010024600c030300ca00b44012400c0314000820180c11407040111150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 562663678 1250 562662428 562662461
    0x1503010f240b04060e040f0902090f04140d050f1303080a020f01111911160e0708060301271a07030c18031e061b030c12060317070f0b01060f03 63
    0x18904036001e82240580c03600385003da031f29031214180c1e2054030f41c094003156801404041452600d80c9161142c020308481c1243d854400b4008508104030002d02a0ba41d00e01c55259070f80361414401e00350641c1d0b000341c07100500f1001145004400100c9a1002d001c605420b50000e107000406130301541e00b0f40da501c01400e00c0c1c80170180041411071004c140c030a2071141c00d90400c440d00d900d44075640b504101d144242007440793304501e0005088400c00030901d01c0380e1065510084180c0300c02040500f62440300314208034400b0f850714012400041c104807005818803801100e40d06080e0481c09030140301c01144d000c3e010a03694141441c1c015007003544074500300311082c440c00c241342c00c6a48104041c50428000c0d001201061050b83c00c21140707502000001400f00c0344c4100204039050010081c091615a041c0041c0d040c403541d840042090080d002900c1c0d00403410040110039000e1080346800044098900780003150141010400020780c00d0701070a4036035661001c0200844001c0d05444040c510903c0a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 562664928 1250 562663678 562663687
    0x102130b130512210c01050103080405100c0308041103150f0103061b23040b070b01050112090b04020409020415080114130302100e071a1b03090102061503010f240b 72
    0x181c041007009203402940b18801204610400c518150700501301034407886d40c80c110002c401c5c0032200c80500219041144d450500c6220148203e030601c4582000a020940c20000706001501c1c4442898201368068121910031a500f14607020060341690455100d086c060014414042e00380030340810090407003d1251000c80303581e8020010414184081808a0380c1d0700d0301c154036480702c401c0394010050340b400b040d04c5010505040381452030038801d0394042004039003404102c00d200d0049202c600c2d002984940643e449400b400f015101000c01280d0241e59540c1c40401140000d01150203403680500003d03000e0f007024510800d00c0300240c03042e00022078040340c0000099001800c5e0103403107034044000c10600c41c180e40052910580f5004074450380d10200c5180d01ca10b00407006002400102d507034111000440042042e00c91181c0c084460058101000090314001d0b0407281d9010990003034000101041890107060444145140070b000360034400103000350b8452248803840140000083c82480c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 562666178 1250 562664928 562664959
    0x1103061015050a0917010c0e030f150a14092113060e0310020301290903030406050a090e04060515010f020c0f011e02060405100504020913050102130b1305 68
    0x1141e0060480100100000c0d1150158803804107480109092140d400b110504021010b002e0a10141e002000401d58400c0c045286400100140c1c411610b0000d01a40c00c6403003460007411200610b41c001c0c1035107800344d000c01c001210104d1845103e04001404c010751003500c440750301040344403c40702ca40d103085c0068146800d01900074005c80f04a800c00348075505140d000702c4d040c11800c2c11903055007403010000203130650200540c0d40d20030300c000203403501c1c5141c0e034080c400d994041d0b03018141c1c041e482408180000303806000184941c0d205406c106040da03036115514101e0480495040f540c071a1940c0502140101c41100c0b800d14980c02d00b4016170303035980c008009659180c952142440360450181142040c3d003d14404280c9250703244c0300f44010a0401c0f00030b03603241000d40b0304a625218801d010210f906592040d02c1c069540104407400c10b443d000041060b224244c042074410795800c1001285c1d009160b00c042e0000e103a10074003941c403100303601101d81b22004240d10942c01040707a64881c401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 562667428 1250 562666178 562666199
    0x14160c1a010816090c0503190e010c050c010b060f0d05060d0f0c0f05010815060318030711030d02210f0f0d09061a01050304060c0917030c2a010c02031911030610 71
    0x3405140c0b000c070914592380130300142c0007a1180400790000355103014035000c0510b500c1710081a940c15980000d011060f14482070003140d11464250114224051195901c03000f0b05409c51078000c00b006082044209507505c40403024021000c1c00c607245015042c08105c0d4045008010300104000d081c48181490400220525980c07000441031244100000082050190300416131000c004901203c0d150040752030101d1141150b00880e91180c41a03d840c01080342c40007500800c41d000f58100111a5441c00c00b040a55411000f103003400d400c0d041c0400125010b6070340141290241001021420125904200d811118016210810000380c541000440c1c0d0b009003c0380d030415880030001801c40d002d078000701e40108081c0c10000c02c1803c11503141424003000806130500d0082401914100c480c4842c108640d003200c0001d208040ba05460301049a45c000d5000050301800a021341e03992090181c0380c08010420700c0d00460366441480182480390904010650f4015511031101c40380c0c504000342d649 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 562668678 1250 562667428 562667431
    0x180f0f0206041d0402030c03010e0d0e01021029040b061c0b0d0506041403070c0303082e14120705090406150306020d14160c1a010816090c0503 63
    0x8084814494045085495510480d401070507000c03050820540400b84014815405540c240c0c030a20420724900381624042c42024040b0105000034101c1240300c420642c4c01704140809581580680d528a01c96600c5900441001001c8002c840c100f00748844940d401443c2c00400e030302d00503031400041c120300d0380320882202e0354041e20580e400003403551034600314094800358840e40d030820003400204c010040c002130407500030307481011540900700030000c445660b8051040c02a0034140348400401c080390140b80000e4200c2c4140d0044100d03503036461507031503450050500c0c1909254061b02c01704038560f041c24140480d03183c100da240f07824030481644181e0f100860300032984240000300c0400c00700560751380101031841230030707030010203081c2d0301d0800c100290440f181521000d42040401070541205040b618804c15101c50742a03402040e43c00c08444c065031841040310302c0d04842c413591062401c5a4805402017103400003c046131130440480d803c100c5199440654082c2c109050442d200f904603040d01d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 562669928 1250 562668678 562668683
    0x20a0b0a0f0207050d17010b07050a03081905010816050a0e07030203180a050703020a09050f180f0601120309061803060207020f0423090721061b050d180f 68
    0x2240301007040a600000b8403038000c00809500c10140202c1601d500000b403448450b44000001d0b0306680d84513902c2080c1e12644078000c00d00c0e007240302000c0c00240103400194000c0c5100038451480d000080304281102c0c0281c000c1e00740c507845101c0d140001014901028003a040544410703452a01d030000d46204528050001002d040e0080002540295804040c2922584c0c0000b110301150443c00d01da0b8649003e8001a80510417840001c26101890701841d80258250a43c464256881c2012196004400110380d0850700800d091141e6007403040001070b000c0c01c416803a42d0500411440d014000552991108007840b850340b4403851b180000c0f071001c03c202d0790407600244e51040781d803001440c0d18603160180b83d406442c000c803186510318189035210000300100c00c9400c19450b008c000326a101054410140f0355140020071070f050802c401e01d50700099104000105212070300000c01350484104081e500c00040010911200b001514008c0a81003080702e80200010910f0b070319140780015500401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 562671178 1250 562669928 562669931
    0x1403070521030708040f090c05071b080d0819090f081612020109020103061a1b010f091202060a23040c0506030907180c0e10050903190b07020a0b0a 65
    0x140e500d1a441da41c000c08001e5505025240d44494515241c0401e40207801480c1044440040200d06480540306200e4510120744441c0d041010540d50055401081c0c1c00ba100019586c050000c0c0b011010880e03804003810544404e003c916040c00303001e20200c2c1c0d140050002c14100612000410030940c2d042015030b03001400c223541d44420140705072200424000040002c0078480741d01d4032003a07043d802102c50740d100b66414002075a07207003000040d403a039480c4199203141003085444000700e220440383d40112082e400101d00d80d2100d040d110103c0e1481c40c01070381c2d01c1230100048101658140811075005a034000f0812a0402010b039485044000d43d00c2402c00c413000c02d001c54244441080c14200410008142503640c4ca0b0400c0340a4495249204401d000710300c00c00c0c00408030045015001c00c0d03200d95940d044003184428108400740c400c403003010060000411101e651610140301440d030b0011700d046820706081d642c1c0740c09101200c0040404003150001d143d1480091000c803200c07908505035000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 562672428 1250 562671178 562671199
    0x3020418022214100501020f060708010524040e061201090506040303020c0313030507090f0b03030d02071e031805100819060806040b0108061008150c07080705150114030705 76
    0x2041c1e0060410458802d5003280b0b1804003c0c00d44404c0001c081034800a90a443e80d600840341c04558039035003503c80c0740100c1c004900610441c14661404d440d061810126624562031100441c3c100c0d91103a0404442e100c500b01c01c00215007000400c400b00c1000910013005003070310981300c1c10344500c00544010700309500018020004c075006c10556200c0441d800c0c25503e219581c0c035101e582e4501130311801d022182080503e2030350880c01d1084400c0c01c1d0014024615007100c0c00e030280e0095008010490300240314010340c01e000c03a0305180108900b4400e4407010204c0800d181c1030503848049900451280c030100c2400c2d94038680c422040f94010101380301c091b89050f80e1003111000303849140c11203505442600104010300010400040c101c3d100f0205030303800c5132034540048000d4440303030140402640c0400f030103a400034410781d4082c3e40070b402d41d150359040151690b500c1c00c0d01d81c003820043e41d1940c400f51040000e15520303000da40c010030350356a030748042c000d200c000b0039240d0180f032003414403075104403c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 562673678 1250 562672428 562672489
    0x1e05010309030c08030f012c040f050703120815150d09080d11090f0a08060103080a05040f03110906010503150402090d05010c0c03020601151715060409060302041802 73
    0xf0742d0f081c0341030f44000d0340d1341c5a1620400302180c260003440341240072908440103840d06030088041c00c0b458102d20f000e00d089580c5070744459401c40100c003001c80d0148142030000001c00c01544540c1038000095031903803400d003020088110300310078402d035044c82035800c00810380406044070101c811080304260041008003041c180340f5164061899280d0005040c4003240042d070035940d004001480046a03002c21480104050144080080c01044520750002e401400450515805025012840e103031003440c2545801c8201d1003250180d004039168007820b075170303400701d881c02160040c4d1040c020300e003460552511079070301c10000f03100700c500390b006a90000c1c4048040d2283d01e0b96020741a0060028402c5040902c8024134105031007509070014010600045a002c140aa4446540300b20742e9401c07284119001d501d1800c04800740030040b040e06075a0212480d40c40e180d010b08010a80d03c040020b000d851401440150b0b04030707043e0040002076420b218401030307450240c1c0140016000303403000ca0851445c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 562674928 1250 562673678 562673687
    0x906140d050a05070803040306050f0906070804141209120c10050a0212070803090f0a0819030b131a030109050d05130905090c010f030506010807140405120102040f1e0501030903 78
    0x31005440f5002c0e50001103940240000100300700c9201d000b007040a60754558902c1841760081d0b50750b2981350480808902a82e00c01c41010750028001c00306070144080421100307140030a40c82d00c080e01840089900301561500f030302c3c1030301070f0503001002c0c0072030402c00c60014424403140301c0d05500303000c0d001c143c0c5040c203482084034418000015100d86d581d00b01034203240f803c540044910b10910300c0b50542c138040030000420b108220a9004200300c0c10444400003e00c480100800700104040d500d202c248403a0381c402c480c464004108400010701003080192042145a421010a009a04241005002950000d241543d003030702490501e40701c40c2800501d41d00356481c1d52182080600f080d060009000300881d0710040c0401c240c80300381c100314506000760700340c0340e04440d590701040b0000b00007103445000311160703c814a840f1007a54075040c1c41e280020095a1521901c0800360b43c0403030144070031074800c0d0015002e04841824400c00007c1e07124000c02594580c05002e0405440e036044a0406024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 562676178 1250 562674928 562674943
    0x10c02210d0501090b040e071d04060b04090b0901050603070e0a0225050d020c01090b0d0504081908010503060906010f0b220b0901141303060b0612070f090906140d05 73
    0x2102070600255a4805240024014a42c078940c807032850005442c6104d8800106002110000003000000344903400f81000d80001c000d005407183c83e00c884c1109d0842c0e40740e215549500340b043c0546010307800d02035151800c40e00000d01c4e45009901c42c08003030003c0390b0001540ca920100f58500540e45061001406055000e82022840040c0e603c030340c0b0f4400c110700402c004082d41c0940c3d003200e4210340b1340c3e001105c03031940d9072050840d8100304000105c2100c1d6180c02c40d0394071a0098241e05c0c54610b0409048030504000124100041c2c0e08030010300c070b649010702412307400901007030003010300354107156060130510000e00c980043c0c5ca00c00551550042c1101100034a980d104415400c0043d0382e5045100e0141c1c0280c044c00c0c0020094010200e10a01a40a46a000c290908034890450955503800010001c441c880c6512072801c0c081d034000300310156480c900c281d0981c0e40ea40e0084050b4070000d00441e0141d00310180c80c0b170504e501031059a11031745884122070380c11100c3c00005a0b807400c0150900d02e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 562677428 1250 562676178 562676197
    0xd0c05030109210305060901090b0d05030406090806010503030406020c240d050108012a0309020a031704060908010b060d180209090106170a020d02010e1903061409010c0221 76
    0xd0a0b22401800116103101c0c042165204101c2005600d0240031005c407801151030b1644000c0500041c0610002d90b8030181b15010301030700b10380582036507480712451900103600c18000119081410b000c02442808039a0040505400031400c01d030509401035110544180c0b4540600c5950902c10b051200490210300411140d10100395591003010f0200d018007800d000b02c20703c0e9800d00c410119040140000d00c1c0c18582c4035184003000240050048021b4141c40e441a43e2081c40b18801001161141441401110b40100400e9070750f840d14902a0640b50240d00480c004d034034100f118003187c1c482d0070440e48034080b031807000a01200c02c1d444506075101c0781034002c3c1d0411000000c0003c4e21005601c910255403120030396011401820210715941d01c2c081100079002112143d20000650140300d40190108000742201c04081c041340020040240d03c4e84142e64007034944406c1d030500350352940c8141d0841c0840700244030004411a000e5910050801d119001203580c40910100c4404203003039801c60003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 562678678 1250 562677428 562677431
    0x705121b01030e100612022d04020319060902070c1a070b060105040b12221a0603120a0e01120204031e1518140a0b01090e01060902040303080406060807080c0d0c050301 74
    0x1512100c280c42c1584000740100e00440301c8c0100d0845e03038290011010a0005244103007a4400160018480650070160644002003c18035503414072113403d020742c1d4064074003d900140c0720703a05818110000500355014142c95019400503504001c11034044543c001d401c619140025129200101e55520481e801000c624001007100d45403100e4007101a40030310544000400306601c80401303441ca95542081c0102020410140300d0000c485105050390301c40d0004059170368401c0f2048001c140f5038481c01600340060440348a400056800c201d0a0311040a42c0c0b10850800342103550b440d00d90060080220f003591b50400c5508100b00505600084242e000e207801e203c1400440c0810f03002c00744844e02110051140f00700c0c040841d400246a56a80d600b0034500045a464511700d03c1c020000f11203903182e55502c3d440c000c101809640000d100640c8290740d050340038505410402c04485c50350304a502c01e500300a008010045000403c071565200880e81c2d0002c0d140c091400d084009007035070203203802d035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 562679928 1250 562678678 562678691
    0x100c05190c0f0f05120f0a0c0c080d0203030a050106052109120c0a0c150c0b04051c050c010c030c0e0f0609030d08160c0534080705121b01030e10 64
    0x3c0351007000350030114419401c80e00540800e071a441014082c040100d110b01e03105001441d506885800300100b424000e00181c01455140c4241c603040400c1d214001c4050303400042842094902c500c22140100801c0c03170075070f04142142c11548070002ea5021070000e000505008201e6428060107c094000b07018114103a40310403040c041510340b60321040c05c0d564204c0c428070005140c40940501c0c8a80c1c1c50380d540340c036a50091030b6119680c144000c1c01c155110300ca1485528120180401c440482845c42e490303154589440e40007290a40d203c3c17208500405060010980e44030750403159140c24401e08550000e48140700401068140c02030900c1c40c5c2d4140308800c0100100354124981e00e0103000038044827a031403409620280d0b200c0341d1500d4010500e502030540d074141002c9080e022050701805840105401070502c01c06108043c2c2c0b604407003101e810000d810000c6281c1401d245090804000191030080f50907402c9809581c0001001814035495090705c040d840c90a1142d0b0350a42c40303401e0108100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 562681178 1250 562679928 562679933
    0x9022103031810091101090801110d0903020a0609061b0e0109140f21161d070e060d1d120d020c0c0d0809010914030a060902011803050609100c05190c0f 67
    0x780c84101005c079021800e1010701081404d410300030800300c00041c0032120b251041c0a02040001c9c080000103400718000c28210f43d00049040c010385c4411030145002241e0305a01c0000d58200c0100421004280902c040b8034000c10b0742c0107007440044550b80c80c94a0011801c000c003068900384082c4c0c2032540808000741c01101d6001f028004200050204103e494403180110203001f60781041c000d0860403020140e00030042903c140885601a50178a4054000c1031014042045504280e00b02c55810b85c480c07000e1086400350081d0010050604001071040e48900400c00206210b4050141802500007862018a14041100e103205101c05006c6c0041a1040d042030b011b00e03044011400d00240a4010020302011041c01000d0302040080180450b01042d0391484c0c02410b16250803030600680f8445420407016425041c2c00039406200a08030620b010041e440c01c0c401d42d50100c1c0c400d0352400c4c000820071030340a000d03922030603902c603510307206030030f00b00d00907545a00204001000c1c0f030b910038910001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 562682428 1250 562681178 562681193
    0x617060406060b040f1403070f0909141906051f032a0b0f0315120d021203040309180e01020301090207061b020c0d06060305010509010902210303181009 67
    0x114034015101040290b8071103502071180e20139072081d1102150000014410181072002c031100034003005080310745150b035641c2c0004105040e584911045561035244030140800b090f461102000700034091309190602c9c00080303000307141081010309540c6c0e4541c0041c0b021072104100031080521008018031242e40c07403520229815424069030091110300003500590581d02440d102611001c0322100d003001c4115200c00320310303000101000b60b100b040105141c120340f00c45501625800e41c05005c1d20200f003440e0303c0a1700c6c050800c490724591010810412020070703484403840701a14000d4041d404520020303410719010b0480141082155480000001000e42055006041541c4144010301a05010040f41b80c01914a550380102581060380c3d10f100510b0441c4095090b684140b42c006070071501d03a160039084230300840d81e24185039940ca8046040d03203080880d0403400d4646481c5140e06247c4000c200392039000181c03603611100700480c0b42c0840b0300005c0c002038018100c82c03102007040c0c6070b541c2403028 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 562683678 1250 562682428 562682431
    0x9050a1a04031407020a0e070302190905031204050f01052a0d080106050304050d080a020c01020304050a0215031506161a0402010f02280507051809060a09030e04050604061706 77
    0x2d0200700c125010200410110f4182c620711900181101c0f660f07841d0406034440710394010942c00800d6401c20400a01070030306540d0703201010250f40d03180b90442c188070504d2328101841205420060051104004030f9580d00003031041180d0070311700952100c1208880c4004080c0c03089004002c91080052100091000a00c0c0c5036410002d47e40c40c2880d980c0c4150170f580038401650043d0945e044415454540c174004c0a01303a070012070268006141006201d0a20300326002510111003d130001c09103001075240c00036164504e13000950310310b813560520700b020352880604c040001d40206004a414074050040038400d0040c2c5800101d030580c61880203032242d18016080b5422800705422002c00c001030352000508141209841d200340801c862600701464079400740c5001110380d0302c58124041242d4460845c261401200202c1544681c10089411410700600400b485d124a00d80003120b00803c2d80400c01c44c3c2c580206550009841e02e50801040c007808694115241080d11800800740081c0001000c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 562684928 1250 562683678 562683683
    0x80609010605010503070e150c0d051c290105041208070b09010c02070b28020615030c0604090b13020f0d06080a170d0e07150f03110d09050a1a04 64
    0x20801d160b151070055405020958144001135007802c0210750505107041c0d1006080d0040504500300b81c04a00560f10388055075800748001900803e4211405001c07800020040c8110f00060000100c108081c04009803013a8042c50140c8041d52072540a9001d10220703409880c07800a040304016041c00c1401c80c50784070847c102c2d03030380c0541d00008080b00d0741072041d01d071101000d5001d40900c1e460080060103540011040c4903400b88208410301c100c20100e4404880302c00543c011b04514507045130075241051458000383c1c000d4001c000c27400e1103540c8080450301a56400da0b8005aa4812030001c07822454080f0112040d091001803e200301e10b544030050300310900005018040c0f15140d103c041c0e01d07442c141200070038007400c030340e01c62810811040c0a4552504403000c00221000000e0300c0c0b0780f5020117a80300300340418001c0040000b295002c0340c420804005401c09000d582d034100903a40783c1d03106000d083e44090382d64000d0313403040210502401d21041d80202c6007d100d04180584440001c405035002c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 562686178 1250 562684928 562684931
    0x905060a05060a05060f13060c15060312052a06220804030201080403020a06060608190c021216050a080d0501170d1b08030f1005010908030904090201031508060901 72
    0x14155489070050511032800901816000c500d80300500003142c04c80c0b0002d2180700410301100380841d171043c00317940c000d080ca5999528081c445041c841c0501d0110a945018507081c05424800b0481c02000e2112401e140c3c54074035030b190651035540007103a103010f09120160703508111416414900043c0d050140d01c604001402c1c50301047c4680c00180c821110003480c0c42000e0104001645c0280e070344a40c042d010f80182c8000034642c1e130320740b070858032150001c2000c512400d00740560014000c0e00210200a0600c08100e202d0040002954402c054030280190744c00000f0642d22440701d0100114400f6404012900c24420a191615881e007282284840131403074031000096041000d520f030891003071a1000f03882d407802030780740031904100e90107041c10080f1030540300003001941c0600114420503202020720b00b5418a59039858800806500560401003150f005000800c8080200c3e0303000c050841e400500261032348010b03005012800c651212881502c0800901110b01107000c5100d1140ba100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 562687428 1250 562686178 562686181
    0x12050d0f14090705031005060414280504030219030203130b041503060605040e0411061204060e0601050a0905190e0f0613030c060903020a12180b361003090506 70
    0x20382c640d03403451445200ea05a01950101c0b20340419a40b1050300180042c1000c51250031014103030340303140000e071500700e158001c000301c000c1c180c840201c152210403001c81062120307040649000b5500c003c040007407503011414400050405008004035052031001002404009a8905e100092a045413241c40d0324022520380816106200340705407030590b003044e00c60034185401c041d0302d4407140750010f10440714114100f021076810364440340549807454070180da10400b0300d820300d0440e040d00c010045510342c55100310010311035a9607549124040d602c6098002902e82e80742e4041c2c1d108171004e005144034240c070f0001c1c401c81415000c140e0325440f4482c0d0341140c0c80d5403181000d201c244040c0b000041c0c0082c41215010700000c545d90003419089009104075011021161240000f200e221204400072656080c03009081961100c900c0c002052a04055070504110528402c1c1140380c802c0a94a103a1004004402403a441110480b400b8409005d94540201e0700201034003e011104007521548507010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 562688678 1250 562687428 562687441
    0x1822050109140f1e0408090d06050402041a01090611010f1503022e031d120d110405090402040c0c0c08060a0501150906030510090e03070209060d0c0312050d0f14 71
    0x902241c0581360100922085030004a0a004500c002500c11203125408101d00f030310540e100441401c0c0903000d0340300061075080901c104800c840083c401007681101c4901d0f40001c61fa0050b901c4c404854140c100405590083c00c9518010544600f09405040c80c0402800c081300d05500d901094920a40d1003204000050f003400b40d000400000d040101000c07010041c0009110b6001500e20404012809030b860034024043d5060100d201444000c04c180403038403440071806030040008101505001c02e1070541420f010490f2802d004001134000d035110654a0800c501c943d12004035190400c0000741603a40f100001c80c2c85160946084507901d051500201d8101c858440c02c0400a0322601c0c0c500e4503c1c588001500a020001d2038069103050b221800100c241290040701a07c403154405107030354000c0ca1040080300c50016048a000c2d07002d80348294002041c940941c02134a4010004000502c2d0281c412181813049024803044a814640100b65802072900990410307107003410302800540c0c860f03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 562689928 1250 562688678 562688701
    0x60909022b080a05120702101805070e13140d0f09060203070303150b0c0304080d26190c050c010c11032703030a050c0105010b182205010914 62
    0x41410112100d00040c030030026014000508061141d030810071706003411344070001c003120780407207405001d60440882280310801a100d000003407400100e1100d003203c030315203038190340f41d0f41c9020b90516458950b0120365080103600b5400d00704c42e0700698110030020f03110705690b183c020104450011424104000380d0017402240d00c08103403401c6a0046003031002540f811000f600401544841d441948500494400c0302c40000f40001c0b00c2d200001d5603524600202107152031810304001003007005031000c0c03040315941c00310040502d2107542040f18a940b50901000c0f00c800e1071000742c0d01458a440bc8440c5215080b01c00703442907040c01d00c000c00850703c1d135900c03e03200041110580c0308243c004022403402d11048421030001110080c21190b0071a9005002c00d00e540c1c004503c0750040b030004181122240824058107001d0402d0302c01942c10b144d00c8a0074040b03000c2c00c00306040e00c80d80040c0f4032011541c2031a00c03500c2c1190104201400f06582d141103c100919028040103485000700f000a0a0318021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 562691178 1250 562689928 562689979
    0x60f05090a09021f020c150a0906050a1107030b0103120e060a1b0c121e03020a1103010b0904060501050a080a0507140d0506040c14040c1403060109080106090902 71
    0x15220380c40315507600108600804000000326402654540f1456042500d84408103900388582c005000c5451b81c0001c100b00c00e04e54511100c0322240400c80c111031240c1c0a80c001c01160303080c1c24003540300c0d0010481500d08174012000800c55200709070000060103069500103041701e0042508127501c0c052001d081b0f4100caa110070103034000000f0088500f01c1442004000303803504562000707640019199841c41c00c07480580d800700d0b0124040b083d001080c4103804070000c4484001d040b89040d401c6042c1e4010b0344901c04088043c02c841c0510f030340080d050314290840080c1c0c0345c0080c0301a000e440c042c80c4c010020300081c0689801420a504003044072440050740d402c01c150844010850035140480c1c84200007441e502d6a50005404c41c440701c000707041080182c0c0200d115030103031440306081441014000070010b044502c00e600b0040c500b00200c0c2c1011504081201e050702c015620383d903000050b1070150541e4064540c940c600b260028108085601181c0200d100302d0b407003100040c641c0d03400c2d1140e401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 562692428 1250 562691178 562691189
    0xa030f021215030106090e0604030206061002060402060a03020906070c03060c0e13020d02040b070c051c2a05150d0b220c121409060901060b0a03050606040506031603060f 75
    0x4201c0046460800b41c1c0c00703540c0140c00001c002240064480701400c040e83c0d12507035103010300e5011205104c10076030180300c0c0e15840681510100e030390b04e2140d480255a01400390000e8002c000000e1071000041c031940484a4036079019010958510340381c68031030310000081c4010b135013841c9000b913403101840c85844035658250006184a43c2c908035001050002d50241448602c442c0e8200300000708441090041c080850040160071866031500d810703c0302a28148400391a000e80808165000401100d1409081d071400c900e9401c0310424100c14500c00d10051f00920742c018a04400b680102e48810010000e0004201003444490741d01c0081c421040c1403c01c01c0441c0d004024080c4035408440d5102c6450481c19140c00302c0502081c606013011258040d1249514603002c00070003031404000c100d002c0e003103c1c2e154020044075140030300d4010709001d2045048209529680030601550f60301003079501030800200056034a0234086c07141c440b44a21b08001c0c402290901800203810361614814804944 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 562693678 1250 562692428 562692457
    0x30d110c010e121e0712050c0f060115030903021509030414060307170a06030c140f03120306040c0c08040605090307090c140706140c030105041116170d0c02030a030f02 74
    0x81501c0078603d40c064180c0502c030307013004003400044042600c1550f090040201078503031968400c1d0100c29503080c203143c4401c1c4202c5600807001000707000040ce221226041c01d602d40041e24440c145030480c00e08009100d000c41e02c901c040c090200310b030b80200040046800c5a01c40360341026131001070000794001200e0201c0490b108800801845402804080e0301007051000010729586950742c5d80040c8500e504207582c9188505072074541c0b03041011550034a00700480040141c07084106503442184001050540a00c0e1250107840c80c05001c0c2e103010b00c000b40d0106080d501c46860b91002081394110921040c42841029800941803130b0078413486c490600155116101040f448040c94080e40c0060003c482044d514a40c2c134060014801e000d0b80503401d03800481d6583e514000c20801504d6440c008010310000c10842c200c05030124108030b0800d5070340400c540c84c0800840311403540e24094603900c1341d2568240b5002450080e4040010454400c3c6a2810409208017002900880c01100540d5427840d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 562694928 1250 562693678 562693687
    0x20a09050307080a020d08040806070302040303090e060d061802040f020c01050717070302091f0309111c0b040503090613180c0509041a061218060402010c03030b03030d110c010e12 79
    0x1403d100c0056121a07009490440c54a90383e002e100f460510102c030414000381d0b00ec01c0030b204155110384005c004200781c000c05d0f42c182c108040024008498054014807060340d801548504107040c44404102c079030010800c00c69990b0403c0c0000203548040c01c1c2c003585519290000d004540100581041c040204024004954440a0030ba000b5401600b11540c81100c5070846070315214003000d2034404210b580d50100b10505a464981c0e52103490380203841c440c5111810b1480b40c45020b161803080c840c2c000030100044d860b2414424294030441001580000c1c000400b80070781c469840342c0c9001c0f200c007201c041140d105030320b416a0482d0760308a038120000b98200180040d03894903401c02100ba01d07000b20400c4900304910001b0307419500c1407400c074044800010401580040d4400c0070015610208081e000301d00e002e50008058624150740281415907441c4512000c4e02d04006a84144140403010403a808404c0c4120725181c00122041d907040d801c140c000c9165103800300d04c00708105803004130903041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 562696178 1250 562694928 562694933
    0x6010809030a1d1314152d121b190e070e04061403010b0a0e1605040b0723010603050c01051c062c0906071101090213020a09050307080a 60
    0x1015041422002d254080c442d4121640e4404c4144d1038031182500002a0150312419042044607000304003103c2c42c1000501d407012903c840389610041d220303a001b0540c0d25200100c0f40a580d4030100a20342d00595002519210070000141c1304402010b88100700102440c544100801e000724840040d80f99056050200501e00c410045d441d0440e1031402c1143d0501510b41c007003421600c9503130240e10121034a114106041c01c081c0724010314030409a481c011641c0c100440c2505d24203010303180c1410740070407600070301001e440760095a01805401c0e41e050340d121628201480c4200d025a038541c90008041d0502c0304592051140c20101c80d8001d0191030015800300056500da0003d860080e00d80b602c00c11903020084807842500d0143c104202031120740341003008030032002e011802190050b0300014007032080501000070100c0d844001c600e420300c82c445030307030f58260701600e1080c400a40181340324012106400e003603009003510016550b5506170b6107940300201030303882480b403080c00425004064203501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 562697428 1250 562696178 562696187
    0xe06010903200301050c0301090b06040b03181911040c110604080c0a062a05071703060d020d150f0c05190207120b061806010509010e0312040f0503010506010809030a 73
    0xa00156600110461810000440e007980d4041b1100d000c0c0c01d100000600041050348501440b000d0184d85850505003425038030b202c0c6210160945001a401851032012074004110200580c0d19483d50001c10160300d2614603861407440c407006100394100288000d04134810f8800c5613411010310028051616252109059503006914078842401110283c501168aa0003010716156203508846a100c0c003081010401844180381141040400c21000d00400c41c541c4071098000d5000c82d029175680c94010000f000183ca0020094000302c2b54800078007031012020304e80400c0c0082200c00c0c45101a07026111080b10100a895008660140300c0b41a100c029041607441c0360a40380111420301e9207820000c46500751100342180c0e181342500811005090400320140c042c0300c0804c2500706401c0010020f0018003c100e03806040002d000a40c0c1d40702d9508000802180c101658041d0b9296115104420307580d5142c00307568041d6080502241c07040d403042c1101d610600c06007002d58140340b1180c10444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 562698678 1250 562697428 562697453
    0x50a0902100e040617060a140412030506010c060504060b0f150a140909090307060c08130b070309081b0f0a0b01060530090606010e1c050f0601090e070e06010903 71
    0x1a001592001c02040d034000300084810030340c5c9400000c10f050304c0c1c8006140e05403050710000341600e00d02c40c000d010029507001c0b1200c1d00e030441e41c05d01103640d954403c0100c50b9408a414054562030400080c00103100d03080d1710a0865040c19204d40480c2e0b8640018801d640511800c03014921030100b102d88125445003454081c0000320304034951428848070001011090b003034a80400542000404004000740e520442400e40003500b800c0619191082112807810380d010310140610441c10001810a4070a6208100d456030040c05180c417610a900c096030442030034000c1103d980f140802d00d80c0c00c481c0c001016030009601449008080e800d10304210b429030060b4041c0750b28602181480407030307151440041c0c54688030510310001e05141c44411280781c03490140010b410f10191203c03904a80d100d016020b002e40120240002c400e410b140b4007586041d20088010035240501d0001003016451500b085024003c44000c840280b5124a460308081c541a01d4480c0800d00303d24003000018140d00390007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 562699928 1250 562698678 562698707
    0x708090d2109050a0506101a0d090602190e10021c1b051b0f241305030a0804030302070f06020d030c14030f042303030c030a06031a0a050a090210 64
    0x300b103202c407a03a1041d240c0703810410202c441c1d4120a04000c6080010181c140c01400c05072030710b0b50500118003881c881d901c10941080710b0741e502d900c0c03032109101c0c1c1c580403640d40c1100218407000246100500800540c00d52001c144540f11034074041c519035200290050041e410080780404140c5041000da442c0914086008040c208030031403840030800a000c14900c05466020b1052406184010004080e40000c0c2451045074071070302c801d8501c400800666000f102d84112596540d00c2c007031441491901e1030340084d51600c1844414401c0041034070140086034425021980e070541c49a110a2610080340507040040c2d000c81d0801014030700c02d070803425984105080048114480340000030035940101e500e1a1100e9000302407200f040b5290f40304000225030070101401440310542903079180c1c440a4041e11310b250300440802d0002c0580c2c2d000b02c005507031117010032082030752155050046840807100d20840394a4200004c180c0715040c040c1d116100d41c0184800344100152105840b540c0100010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 562701178 1250 562699928 562699931
    0x1208090d140303070509031e0a0b18010e0309031204050904031425020a061803030507081204031d0904170705010623030106080d0503221203050708090d21 68
    0x7035a003144070510046000c2e00c000e99845680701d04440506242400080701c02d030103002004200c82d600d01d008103041d01650350007852400c0da600c07203071000310b0308502c1d14142001380d51a109030f00d03205100000042500010680c2074a465030038120700000d880c01207120b07860300300c0d101c000024000391144038504130540030040c800d4200010341c4110110303100070070000801060792403207450035880d10440102c010721862410b03080b8011074a09084851a6520006090101c0030440c03404110070f02054030200d0142d50040c0341540f07840e00b80100034059500034034101550b992086103550070801d102c18032484d00034071a1002050744689080326a801510140c900e03558802c03001c03070b18001001c3d1029000c05640b074007018003440341041608489150340308176459408107454601c2c0c91b40200c10b0301da00907102440c0002210800c4080e823a0a100900010030420001000d009120b8042c0c0c0642c5c000c030882c3d0355000b00c90b512403003010b40d2411a1091400820815000c2d0007800181c40041091408403240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 562702428 1250 562701178 562701203
    0x1090b033d0911030105040c050114040801020a0201060f12050304060e030a120905190e0c070219030c03060c11100b031912020f121206010924091208090d 68
    0x380900c102004038a030740440340c4810900003809800110307400549804c500800450402c0e96482c604650305124650610a43d2140180c1c0300e081034041d500104000d00003550344003600c1c1c138001d000380007a014000f601e00c02d03c000407440104941c481d154159200c5c00551501c0d091800564044903a103900e03590621131013640c8000282c0c41b49801d21301d000742d81c0b00c4000c4541028104264056500400003640c41500d00812040c54469000741c2c001d170100f40007566411440c0003281c048144500c00302c2c484039140d0800020000350410f01c2d000ca034060070702000444a10402165140d0f803041c00622039a000c520603092804081c0d1140e8a80d03d0018126a400d0003004451400e010301032405032200c00c0d41448542c0311030340500610b075000310403c015060703021380c0f034242c1d5055010705680c440c0c5400e20b14001881f164000c1c4c0e0400b014010f002002c1400c0352560b14040e9031401094016000150307005000607103010001c5407210f00c15404003038103087c02c01e01414842c1100c1c08240688806821740d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 562703678 1250 562702428 562702513
    0xa0504051924110a020a05090402010504150804020f0604050102031c020d09050c090106111905120c0a110105090105070b0c071718270702010e030c0d0801090b03 71
    0x701d410580400000340140e03900c0c98028007908503001ca0007803010f10307044100802d005984242d03109050382d40c02c07950840280c4aa000484071400740350410705600d400024410001500020b03001d00c103902c01c558000f540342c1c82c2002c1c01854055031092901592040c00883c0d01000740300c4209502c0714070000018180303541032440d40103a400d05603095426420840402c1000d051100c4101d016002c0381c10040003400000f1102a034803421000340102002500e4850401c000d0107010034803000c2c0c1942d00d0b5030b031181c6c00d41002946944801d40200c5141140504180980d40a1010b603584204161500c500f0b090310764035440144c90000b00b18807410001041004c0014001c2c04000340c030364949005c1d99440d0010414038a540701c80d8011141d114500146030300d1005041c0c200050800a011000d0088545800006a001d0840c507a8041418003000c1446031240c1c2d0001740d90f2018034850b0b030b80d101c116662156040704444081103a03d8041e04042054000c10b2051024010006074601c0c0c0c1950362031240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 562704928 1250 562703678 562703699
    0x360f0902130c08150d0b040311011104151119140303010314060c0301030816110d0302032a0a06180605040606030303050c03070e040e03300c0a05040519 67
    0x40400d00040e40e032032060801c415070100302c036a4052407180c074040d042004d41c0c00080764010a41001040743c910a00000c04041c410650381c2108410b80d0b0007405403c100000207401a0400c0c01241c4000d101c9107510400e29102e43c03070010040b007001000e0b140720702d002920800c5042c8050380039a400d5441401c980f00d21303d01080110300030b5000d83c40d01c090060701811a181014000352a0f03013403500b01400148041510302003110028640b0a02c1400f105106140400310180780e840000d0340b000c4110b0401080c5034010000380008081a040c0740c41da4003100661840ca5118444c1c089400e1380449403040002d001c0d0790014600c507600303007903c40003540c07140d8864060340d034103c504031201c0e030303e8603002c008050b010701440e908141c1e4030036080d040d46040c00e001001c090201e5440741c072685e10b8200541d41d100c070a00407204a41d000075a4030300f55140410b0301ea06201d014400060b00344e18580001403d52586109650300d0742c6099664a103002d1900c01008017411800300380081041b1410800950600403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 562706178 1250 562704928 562704949
    0x30702120c070f080a3206090c0f03010c0203190201021903020a020601050f0f2e0203071202120f0c0715020a0302010c0806060a081e040309360f0902 66
    0x5020082060b40e0030500002e14410340360b4842c0702c2c81d44c45070b0070710400140b49090003141e203141d02c4c510381e1098440ca02ea80004500b1440c40b86880c1c01540c0501a10759001b10321701daa0854252003990b0030780c0c2c50b00305060807190200c44440041e0418040a003140c0c4800b807012411010510000d0301f00305030000c425858404106188012030340c006200800c01b9010b000305401032208491043c00c00d00c042022070301c41ca40700460148542040d03615840d40c000c0f01305950780c9105060440e981601c010305006566588044da0aa80d0200818060400e4a2000403546d0101c212882450b0800001d004800c1c5c1d44d4100065100c8240116000803031022000c0082c00310403200d80e4014a0080b45606019003181c120380b82c54410041c1c05001c010031515040210f035400c940d00c0c82d20500e650355070000e400e28100700d001e0b81c00541100c5401e120a0541c04000e8909580c40340800d01880c28807404e81c0780c6850070382030040c41c14100d050b08070b000030106580004c01c8032030203101c00704451116034009500d1459 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 562707428 1250 562706178 562706197
    0x7080c0313020f042406112e0608010c090509060901031208130506040c14010c2303120a06080f0606030c100e030f0609010606030608030f0a18120204180c0b03070212 73
    0x46450070440b00f98445800440d00443c00301a215601d590841403038001103104000794039480316601d02c40500c0082d40320800920360752003308056070b61508020500300080c1709192050390306002103421490a040c820741203d07401800404d01c821444c6041d036403280010903582c0400d070b034808204007043c001d000042c810f51250032190091410101000203241d0300701c00d0342c0c0c104000c0c201510002916022003030204413890802400d00540c441010b4078621807485000300e9000760b44140200b41c200b503040f00e0b05031440d607019241d540d40c101c2d040703999071601212500c1d816481811441143d08001c029881c01d11703100d2401410001340300300801d00c0c1c61402501c0e58555803203c0d00300015a0b2084c450107000e007105240600c892840c2c44c1959940c3c2c0281100e0200c080c0d030000f003085002d80100d0382946858003001c8160308040e541d03a40761825408800099008500b0b10085030718120440010388012544048004d0745203040c03e83c00c01e0759400081c0302d0020352086610050704c1490040c0900058034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 562708678 1250 562707428 562707491
    0x18150f03050106030b010f03050c1303060e010e030a090504110c031308010c18090b0118090504200d150e01090b041e26090a0b0307080c0313020f04 65
    0x129044018100d580503807050f81018035002c82049181c1c1c0c080412981e51219250200e000d03101d0850864103441800c03696001d0940709800001080015000450743c03588840c020401c030300800e24943d8803403082e4410000080c0c580b00092055141941c080581c0040e4042e000b0f0418000c01001880e5502071131000341074401400d001c12010009002e00101c01046150101d82c0d0143e030f0502c01c48001d054080d0314138007500c3d03045034071050341b0500000040203d0025990070441c0e5550650b4000d140a840660300c240300d40d01c803006000004501000049000b401046040c811511501c0c451000314104c1841c030340c0c5a146116034010240650b220842c06000c20300114105881e044013260554400c8550744500002d103200450004401c00785d544020074070394034682c2006090303541b842c07265100c03556101a414902255250018000e0f610504031038844000d039840d094070041c102d01048402c409082c1001c61076500608208080314592300c80908041103109040140d00c00e200b92912020b030041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 562709928 1250 562708678 562708697
    0x5010c151e050a0b0301060605091c050703030f081302060909070c1704091b05040314070306050705120604110301120804080111030f1302030c09040f1b06030c020105161815 76
    0x1aa081d1183c44c3c040b5404030001c1007410b141c0000a0068020a11100e11896181d048401421614031417604510741c0282603c90316a200c1c035000c0c100c0155010500001010100003074010203900800a903d550028481405c0150210400240c0380700284100e0030001d8001040c0009008048a0420b010080022540b11350520303003407104440346e6400c030342040103070049002c0c1e0150b044011202030f260403a107a045401c1c1d421100c5403802006078002002a0329107800c0180b030341d42c48405050104119050441d013529044c0c01c001c140c0c0d18101000c0e02104003000100542120114180403003880f40104600782643c1d44112401c4404100c4800f0444100204100740000021401948440204a0459401090b4001c60f81e50703a5a40d44480c000c404c0c0c20086806e0012202c440d002c03156108040c0d00c0c0f0021403030403001300031005105682c0400d0426500050390f5006010b030034400e000700c0c02c16140020811004451008249802e0542d4005010011901c02074a00044020004075140e22031030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 562711178 1250 562709928 562709941
    0xa0b15031b010e040b0616020303071b0509070e030607030f090828110307020d0602190309020f10020c24030702060601082202120f0d020a140705010c151e05 69
    0x2416490440e0303c02c9140020b42c41403946c4605c181c40c014403045442c002c0060b41032000c24a5407044a9010300030a1840040150310300b40756010109461098500c0040c64858100541e43d11900d03488241e410b80080c000925070905c00d03407180300d02d24591800400d050700c2d107454150030755001115203100e2000c1041840000811404034941024082c501116040c504d010010703240c3c0a05c02e030081c0304050a0000380d052141c82d80581e05000504844508400c05408029004202d111402ca014034091070a8020624080001040c408050b801403d003006040040020414200c18030b0303080d1406c0c400b03011800d062000069442024240c00408490816000250110100400c080e120423f6410503c0d115403402a20440640d816258001d04c070384001a0142000201c40c85151144074654800d03900d04e0380081c03c80700e00c0d8001e9200017251148411051344070007840c002d150114100a509800081c1d501500c0b07041c84640110004d100f135041444100d0000b0880d00604030035131500e0074000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 562712428 1250 562711178 562711187
    0x61404092f100903050c09070504030602090114180f09071b02130603030504170a030e01120b09090705010e0a08150c360301061a0c19061d010e0a0b15031b01 69
    0x41201b0120b80b60401890240c030010118803548c000100015000f0868140030303401901070103c2500380650082e100d100108025111130030340c0c040303244681e50300403000180d400e10044441c00b45003150b44401809070b5010030902c000c03928960032030b0400c1c4245080300c0d9462940c85600c014612a540c0d09507100d14000b1503030084041d4000005241c0c200c040d400b00080c1c0c00070300001070085c007820102c0045402d50b80420040046901050304412044200040e00f20003044140503aa02600c8004024001e407051210103c111301900d420340c3c7c0400f9101003c2041140140d1384a035650f01c03d10b01e0014800d901da150203031041100040080003c03506070000740107070880c40461006400811209140c581300c52069603500c4400c7d60741600005903052000d4080c0189988450b000c84030b910440071910303040c80180000135891800010141e409a00c0e1001805400403481c001c9000300039203052a01c40e0881d604018128035007514070484c0d880d00c82d4506100c5400a200c55030b840e210b0301d0003030000152 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 562713678 1250 562712428 562712443
    0x8030708100609031713060e0316050f0d15020a0804021008090d0807020f0f03040f08031e0a05041d01060207090c020709110913061404092f10090305 66
    0x2101d40302000301071150a920240003812242c1251403c02c48520400091020388196107400305000890b941c04203549800c03c01c082c042c02800d4088031031000c00c00040544010700350007101d81c0640c000b0100c000178038100318800907a6010f40c040100d5100d603144018103c0e400700d074800740403071843c0041105515044c05460300c3e82d05142000b003003d2030402403403a103407042e075002002801038190201e01150300c01c00c51200c845d282030b41101d5051201c1c030852a900d030030611039004038031070001001c2050740000c02541ca240c03c601d030074482400240307180811980c10405440c010040180400115010a0450480280c015807a00c2d00a5414810000d003402c605030880607086080c844041c50165000410348100c83c01c062000075003044103a581c100c0351285140140d401040354841e50000b554a5100c1c404a80700d00703140a0b042022402400305458202c5400b80c4542d60030a2540403000c003000e03480c44080510600f5050f404c034548001009000c0201c2d190340050500da8003842000b00c108002e8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 562714928 1250 562713678 562713691
    0x2041113080d2d141306050301170a0b07030207021f0c12020706021f022a07090504030903020105070c030501050903070b060a050d080f0c03211005092403030708030708 74
    0x10000b0454842d042140e00f160f60b012031080121004401484040075000e90300c42698218000780416911680248180c10138002d00704045080c5180d16184440000c402d000e69a0011414101c0c0e507a5246c20f40081d045024243e0700041101d62050700300c9001a80c008100b0f055403185640303800d0b0303410300071240c0038111003103000e65101c42420b024080e000920b945003460b2208170840346030031140422029015068400620160241c42403031490b00e44048507060042000c205d400c202ea8540c81d84003554800d55002d80482c1c94031b10140099403186000f00074080c05808034400c00c6581c0e070782d11401c4071421200f01039181c1010865000f04001c281e0b91541001e4211810012181400c000882c045142080200010f400140d01e80b14003100e24262003240030f062003a40e07262907036418100300e2070719101e0300340c02d060051700c000880b00c4184444041c20b03244081c299001942c0c80c101c1d6542009843e00c203000c00e142d200b196044c9203942c01c00041072400d1003181044d0300c0c0e04041c0400b61040c41c016003074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 562716178 1250 562714928 562714967
    0x13519030e04090b060618040609140903040e0703020702040207150506040f0b1f12050112020a08210a05040b04090207050606010f0c03030221040c08100c050702041113080d 76
    0x120000c68101c1c0f000c4c50300aa01150503555590445454002c0b442c00421a0758200e8180240020456800c2d07026000074a03107101c00c01d2103030791043c600c0c5889101e54064107140103407100206070428403a80c007401d061031019100624081280d260b0090384c2c0c0841001c2001151110100049414540030300c889100e00c0a40511400350b2410000d000040341010600168981e00d4038005524442e540080300418580c2080003156141c8017624810b003061181079009034003003000010842d00010b06892103200354044800e10024200001005a202c11503e000308902480081002c00c0648010710003030a044500607030700c85040c6800703800c007070004042c2814410804031900b4242c2d0001c913119030441c0e0500e00141e65900c46441c1c202d03d0202da2aa140300e02e8020000c000800401c0344416066031030310822505640710f031025540c2503503020b400080026405005450042c1001c2e0011490102d007145420f0902940240c0280e2200f07055215907156408550251500382c0c000e103140b104030703004444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 562717428 1250 562716178 562716191
    0xf0c043305040e01050d020d0803040803220317040c0b0a081501020106030804090f02161211010606020c01110309030102190908010203060a03080c070506030c12010e013519030e04 79
    0x400f0000010140f0400d4061750442180e40b08554900d8000c1c6103003540400b019072a420a820311039200d0b0801c031340c4503003d13203482030003000d4452000c01c4880d01e8a03803565601280c0600c884480a01d028084d204a810a40f000f401162022606c1d0191006041541d06d1f00340310302c2c200c1124500841540991415645056070a10210301d03a041150143c40780c500d00801e103003001c05200c80092140c0d40074604003e150b5041c0d20100300d007003410151404015034900e86880c0950034441e00f215581e21454000d41c1c0f01e004251001e501440a0203a01140f06c0250f03420719001002090a903403000030100301038035541e0100f40c1c0003078012074002c0c06082a68000c40c1540b4118001c503160399020f01010f400b0007808101902086030800c1460007a20018003850346a04105500c4540380e00039100c0d510f040c03007031100003003a41d242d94100301c0d0403225002c100002d172042c2804c1108002c1c0011001c0c80304940d042d0011550b04008114030440714128003250380542055080c02070020054415903131096045c0314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 562718678 1250 562717428 562717439
    0xa0b13021e03040314040e010e16050a030b0f15091008101403160608180a170c0708030301080a12080601021e03090d0507030b070c03080f0c04330504 66
    0x1019203141c5905981d035a02c2e15142001d4481800104145028000c00580441c800c0c0c0100d44207412038401000c0d0035000d032540c6140743d042a4940c42c0c41c200082d41400041807a61081d00706891001014040c02e82d031404250209104400783d0504006030080054174007490b003499000001e088040345007038210750070700d18804403c5800c10301c150344912100141f10b9007150f6080c0104a00319400d805100c5140707aa60f58007403d10b54040340ea0500e00f03403450002211200740032810341c41e0710750310035003181d8000c010303208040068000c2e800c8111180b10712900440c1c450300030801940130708503c40082c19494528a0400c0812562880040410403081d00380300642e600012211610b055101c0108030580e06888158514001d01000a52048443c900001480004190442070324011b0305032901d2956500e030103030b481960107140200022803441c005040c481404c6a20b80e00406048100e5280c542d44040000355501403181c0d17101030707050074140c02011940c0e600e06004040c040381001824940f919 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562719928 1250 562718678 562718707
    0x708160c02040e1005010f120b19090b0403020a0528230a1406090606060418200c061605040905180a050607090605030f1801140a0b1302 60
    0x620510144194406200c0c1159140d0b04030801154412040f07801500b01881e507900904002c3c0329032401040079105c04101000c4144c582841c05410003020320268881d444d120040e12010809a1501540d03060b04400152019180754040c90107039004004100007400d1050800c00741c034070030148070f0030002c0c8940c0078000071030130740b10110742c1002144a0101142c11441c00b060840908102c1c4c50040340e01110070420321080c0020355400201c1142c8060381e076145c0345a6540c1c0c06464196100760144000c020b07201081150700744145018170003080b114040840030840c1310b440800c0440143c400b040038200c516007006480d9105140b02111945060302c8003028080e48503c2c0504401c1c240c0320740001c0c540024505031058007002e00c41c11603589084909115441e11010303030380300000030910000020755501c50816039004411007030f1700e40700c0707515503820002820802c09000e441039502e0381c0c4050b20640030407108900c10342100300040740c040030520030000380103041404000424410300c2200d00d8400171 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562721178 1250 562719928 562719961
    0xd1104050a15113f070f0519031215230f09070519020c0a2d0e060f1507230714010914010e012616080708 47
    0x14a0702c1c40103540d80404089490090000450303405202d11203400c0c5024000000f0030604820700c2d0035015070803e84401629001501210440c20314000f400000040340500000c0070620f80f041e0125881070a003240e01b255003120000041d400b003401418031028200550044001400d00b40d1248040e80741040300c010344080c0c020100c0b2481c0100c0c9801e555440d00d4000285400b1f00c0000c1035541c66140c440f00043c4140d00c0943c0c550200341d07000c01e1012013240001250524250028070754501a8100295042c004d124020409800c030030004078202e00030313080e406400c042c1288034914042c500d44407052100790744840c56018007071076890f0b866080302d40b0b500003620703031495202c000c20303035402c0da541c0790020a000c1e40e02070340c0007500130402c0010346d2401349451101011003e80703800140c5580c2d070011031000c0d82c0c3d1000c00c030301190070404903404540c072949003211506036081b258065a4414141d8160284003110410440001d20f14070040c0c490700289043d034030001071b18151986241c00c05110061120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562722428 1250 562721178 562721189
    0xb07031b2301200903070510140a210905060c041d0709051c1109010501021e071802030906060a050d06020903010f0f0b100807050f090a08030309030d1104050a 70
    0x9241c025160310704402c1d08240d0307a02091104491241c186412180401d511821000d40b00c3d10038000006a681010107950f1503c404035264540315a61007103101c000c07541718503a02d200b0400c407009200e01c0384145402c111060407c004001800200ea45403035840e182000e01691030194041c801080740c544001105001604031804031340c025100d04906503021052a04220b40c411404402c0244900d4070740c0002020b0381c0503403012550000481b050107001c80084c01014010707000700030481044204030702070b40d19207285141102c414950b01d5481c80c0d04010308025240400d9000014000e4120080000301e4100760100e94900f40d05180c5000100c64881100000384010b03004141203c00356002c0d403102130800407040092100300640302c09800240400000b43c2e2060300c150114040d2184944a403d21030f4071107850b55072410a0440c1403603010782000403001c0d40103594020103c1c3c1c4040c140042c6018117180001143c40754400304044043c2e40d80994040407504087c8002c0202c4d58804804104031407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562723678 1250 562722428 562722473
    0x1308210408030904110c15040501060902030114010804111003021b01050618100302150c0609060705032a0d1d0318040504060e1b030114010518060a0f0b07031b 70
    0x1c92002e01c1c01c2585c0180584411b59004e01d00304004d03400079064847c0c0c480c51160008001c0c0c1601c8130360407001c1303010a000d8100c0d45220410b08581650280e8042d45e0418003034a844c04413000c000001030b0340649101d006400281d0081600c041c525440d1307140306030490704a0002d1050b4a44030002c94041080c4801c609500070312000800e210403114844070b000b640c0c02824040580c49100040310b0103600c480010000d51140b00001480e451003c100745000314030580d40c0c0ca04d981c8a54a001001c08200641c0d0140010f910118880d220030340b0f0010304803504c44960103c3c00e080011001c42d0b28030300304600c8001d0350700f04201c0307800d0502c0317101c6001e0012030b0100e0f00004d954a542c20720000030000d40740042d46a11078840a944094400946100100f004900900010102606038030b00c0000a109094100070403080c1c801e5007600108802e90310210140420300619a22104140c02d080303298000346820758001000380c00c0c10340c01b501d1141080c500103900556040e041da540f11003035510825403074040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562724928 1250 562723678 562723691
    0x5150408040f060302040f0504180b06010e031f0509070602030a0810081e07050607051002090415060c1e0b0604090312060803031e070206040803040204021308210408030904 76
    0x140000d5401030014207141100d540e844400284c001d6003e4000c3d010101c60015002950b0b282500402100309940e02c0341e141034850554172960700c6a0017401032810f1201c0e20200303891a4500b0804060070786a140d0b041385490f03840d00c501008444000d030949845400904062004d1900041265801c0c0c1d0f0f58501032020b1751703440c90030b40d0032612650072400450003030310307001800c28440b42c0440408814280c1910403c030341e075900700603040c411340030002c3c11600072010b4403103030031801d902030210000c0107480410600090322025000060b1034000c00c01048154642c1400c0c484c040b55680c1030140002c5503400d160389140c407400000700000f48803a01c40c541351b44000003018483c40c2c02019000c403c50007849150b4a60034040c2e20b94004a0340040403460840c90700d6510050640303001e00410b0b25401403c3c0c3c2e52900e0711651142e03440140241d80090b001c02840980243c891241c400030803102028010000501c40d500c000b07401081e0208140040c184014044500b01000b20340848404032000101c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562726178 1250 562724928 562724933
    0x110913080706110304050307051218060306060f030108060106021018142b180b0a0f0e100c120e100c020a090e0a0327030b0604020c0106080c030f060103051504 70
    0x307414102d0342c0f0000c02e1001302c24071040000000c080c040c000e1040082d02c0c078120914005030b007603029410320b0202010300380101349003e041440056412002c0035001501c0d05d0003d800103080c940c020703400900103510440040008580c180031588803007100c14418003001c641003202c2900e200c10028040d184000c000100e800a000800c04450701100740d503443c0c0b07400c8040055684179680841c200c171021510454903044103500b500205015508046061030502d035484004880d4000503584180510060000d1483c20790303101104a02c1d0540742d9070310303c0c001a9032403078030b02c80c0c005411020905002c6551460021507030380b0000050040001d1400c03062810361800010fa80050036808800003e146c80c0e0b1000c401d030000701c5c0302c80c026802500e8400341224800990401d000080a81c02c2101100820500000d42c10b4003800b034000c600140003500b4006000c0040c0c0c21126554054010b50344100a01086804e05110321811100040041c143c55890b5448581e203d2020140c4602d5400e07601c80007a04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562727428 1250 562726178 562726181
    0x908030f070213140c0912030306030706031d1f0b18040201030b01030b19150c05030d11040305061003020109090b1813120804150c02030a0e03240103110913080706 72
    0x51304522075510780c00da030074060860226030b0311440c1903034041d45500d00104000c14001044a02030513016009001300751800c41c0440051203001b6a60551240d4a000c1c140703103260420449941b021600f8001e851122502405c030100c405c038102c21401200d00c2c56680740d48054021802d540070342c0a09002c2550200500100c004003007a5090960160202241000040723510b01c05c0303002d03114030040e11040e5119075801903c1186480000400e41d43c42000b009883c9160760300050140c498002d00b1074101502d0340e40303560402d0b41c03c444085885050034420415583d005100304014143c2d4001001220180000f1801391400088050100d242007008150412542a402100541c22080140f91a40c42541c01003000d4029070301603840031500807002c1c8606c01035215441150209400031403a00c00311040039160a02006101949801100ea1a5100c2508410f6421031010707200180d440035811490010041c440012115000318141c008100140c004c3e007501240341c6070006071043e12058146041c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562728678 1250 562727428 562727441
    0x216170a031119060209090604050f010303030c0903141506060a0219020f040509030c06071701030b13171c09021503150a0306020a1101091104020a050d110a0908030f070213 76
    0xf028040b00d0391410140081d66000d00440c440440e0008031030345402081106440050783c20035071440c1d01d680104000b83c000e80c8a01c004203120309000c00d4281e034070345614072000c1603844c5d4285503403c0603181200350099610840d0f4031800c1140c4c0c0c181003840c00354000b907940400d515408006468004c580c4190741c0c0e0f0352254408040b0050050201d0719200c2841c13901c80e00310b05003580c035074824a004291030900503002d0101215413511300d0b5a1980c690b4954102100c400b600b11840c850409140e400030541c903000305911000c8406a80c0c3c0c9c0d48600c10182c0c004030310100d10b04410300c0d05d0202d4550040c0c0d91301c03030304003408014880913030740329250b0740040b01c215401c1c000c419601580e00c41340001084101c2c5c0103051001020b4440313030740d0001c0091003282070b9012002c000b401c4404440269030145810f03400381c01c07494820311f06070303050880056004088070f010016440c1c0c50f880201d100c0c801541c0c8440034102500303008014600341807054404a429005d800c4009200c1d0710010300c0c84820300256071044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562729928 1250 562728678 562728703
    0xd08042907060e060c0c0c0f060c0609160e0f0a0b060d0507020a060b030102311232060126011503050c0402040305120904110a0216170a0311 62
    0x115541d8030146040002044180408030103070007000002030640c8180340594031001c2c6107074045c050024291041091401d40242c1040e4450f03428851210220010032403507104d16032110040600b01c5401c40e50240036070855001c805072682013000c01c4100b089008800e50040c004800220320140401d00145450040c0030703040f11411710300300030002c04a500044a00c0c58901600040010300b00e140140340c240d1007001c4000d0746403024152044111240c50900500302c0000c03080d052003003621a1100040346801c11000d94610303c0084509403040348200d0000040a43c101d030701030349005500c104903101c0005128807504c48450a6013030300b44004142900500c04454002042110080b00d07051012400c00c1c0400e903058496000e004009062a2007102d0540360084010a14080e4a00a4110b241c1c031119440307800c1511841c010007808c00301001b8000b141e0164014081c41c10090312400c1840196500c803000804031703108032005080700810704615894242c6408820b419021115030324020610710b00c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562731178 1250 562729928 562730009
    0x1b08040806091507030b09160e06070f11010c03410d0b1207030b060406030501180b060102060606090103091110200105010e1603060305100e010b0d0804 67
    0x1000710201c000328203082d030f002180d40c40e00302a486040003181201c0060302d90a400508000c0890650200c0c0c40c2140030030082460429803c4581d000416119007141d2401c40c1c0c6034407000c458200300304851040b0040c1d10401e28000705001225100113041c1c2c1511401440c041581c41e440900108100e03038100b28000c800107005141e540f0505030740d1080e0307011005407800289845c5801819107004a01c0020700341c0000010440c1d1030071912841c0c00201c3c00b900e0503900a54509000002032028000c0040010000c41056100a0142010303844410300801d464119004141080001d58502060305c0f007074802860300051550041c40c24062128240c00142e611039441440c502d12203070702624603503281001101480003404404540740c26143c00703001d01004090302d60b000030003402d05545440741501781454041403540d0769807215420450070402d07100d2155120f05804074003101c2402000c0070030744255900d401105007604d800f1240d014a00131520350400302500e107942a101314260584d100b144101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562732428 1250 562731178 562731181
    0x210110a050c15070c21020616120e060f16021009060e120d0f0b030303060103020a09030803190606020d020618010e120c01150b1c110310061b031b08040806 69
    0x302400034550000200c55402407010201344050741c0150b030b001b85803d981c00401d055282c0028603030002e941d00c1501020030100700700d040400b507500d018202e03003c2000c00c050200c070b081062840c07180c04001003400030404071084410b03150560003d00701030141426000002c80041600c0c10750054040215125401c0c49000001d241c0c5c945c000c0000d0082445116040041d01002811a4195160b20b000c0941c1904140000b40855001342c00800001e8051b1412181c2281c880d911014180c1007a54410f13441285100b1462222840344100809004217000801c418220181d00a6491038001c2c03a4203080303191039a03a416803c00075000511040c03d01400d81e86a1298081c03651a03981001120210719030034411801400f805400c1c0e14400e460b52000181e02c1c140403824424040c4940201d101020307595602c0007000e04118402850003007007040000100c0500d0444c00902001c91001070001040519680800094216030402e2086580c48913805030101d40d410b11030050f01565202d0b40c601e000703080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562733678 1250 562732428 562732441
    0x10e04170c0f2404150e031204030f03050c07061515020a0506070e090c21070c021f0504030204110d02191407170c0703050d050a0210110a050c15 64
    0x9074500e0318035110003141e480031101c003800140070540340c108a030451055400304001c0b4070700d10854417140600032000301c1c102c15226811455644000b040189445030b902c00c0c003081540c00704408454000c1403501f48103a0822002e08083c6104046009040956480c282c2d849002e48120715070040c012075001c1d604100c010030020b919081d05800485141c0510307400a1003060052014030844403025055201e1a914240101d81d0b603846401e10001140c440065000580d62600b40e407481440c0942c0c5407007010005105101114005a400710904034400c480030a41c2644041541c080b00d404550205002e6074900c0c0d4194540301e0400451640d60000554040107074201c40d5086080c9a40e0b51900c0354122045042c00f01805440c0008007010319000180c00c114501c28060010a44a0303026500c49035983c0c0d0f921450155000e141e84040b503008544c40c1e16150301032041c2c17031181c5881304080c0112103d03a406126140b203103c544101340040454015020b41082010b00d108651100002c540c505022 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562734928 1250 562733678 562733683
    0x9130c09090303060503030406140307090509010b09040507020708120d0902041524120207060b090718090e0c0108040305120c0318190201110307060914010b030f06010e04170c 77
    0x100d01c254046420404006201c1c180042200c003210f10a40e254148440c414451006950000d402d440c20088035400201d00c44e941c5440d014000c3c266802d100d550303135030300100748402e0b510000e0a42096403c04801000754220104403c0301104403160506d58036114032800100070900500b010790068034102c0220517100150381400103550440c08648080e0202d090281240f0540280d01800a440403c1d9207080c076a842d0090b0850301c1c85100d0200c1d501c008600030840b0010110341c4040011103045d134004c02c2594041d04200a00001e0358180000e9030411251030303030b800788420078604105031a00094103061189090307030320004540790141040c0c10150341c41c174102c0c1c10940362200d00781d0b501685054103040c006080c50b2030209030072240c4403000903a0015940b0391220b500003003042c0401c02035000003541502c41c05918510890070030f0304e2014410601c908488102807024000d5120071040543c8140008689044485840d40d169080d92a8940040c110022111007000c1401c00b2901010b0342201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562736178 1250 562734928 562734941
    0x170105040201030e030c0c040207061e09030306290c031c0902030c01030618050403200f0105130206030c0c070308040e061005040b07080c1203090a21090509130c09 72
    0x740e80900100214400541c0c5034815881880d1a1b0303030011348000c41c02e0508c2c0e005408000d008078400a072011100e18414030a280e40c0c111a20b80c141c0d40c0c080441050b070140705200140070840d00c44c0c51941d5011091044a01410303c1d5074400c440c2c086950010700304100700702e404440c07401c2030610b500d141650000f0041c180341501240300303020300d110760540c651113445100c0440d1000d0707408483e0080c2c4003104900600001d401541080580030400000703403c03010f00d20141c0000540248058074440c01c13490308584020f8060162050508142c0b405aa2544c0649400c01c07a9554002d07560010fa010440c40d00c0240d6000070880c503c0402c2c000740c1500211801d07880b03250b00342c401108144000d8000c0783c2d2441513000e1205054000d02080d000301e900c003406090349152510864441c0114800d0030b4241b174004551084481e4806c0c0310000810208610307400440d081054800c2c4000d200741400341c004039031030054501484100f00050003078140e1000035081c850700850b030490b4880d180c0c014076020b0b181 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562737428 1250 562736178 562736183
    0x403031d0a060c0c0b03070804030e011116052106041b080a030504090b0d1707020109050d110315070f031a090f010504061e06140f04300302070501050901050417010504 74
    0x1130940c8001101808030003200e1203520710344d5030b08140345d503140d40949202d0070007003000781081411182e00090314020000405061780101c45051414682000c1008401c60000203010502c2001c1c1140c51150001400c00e03040b41d8480000408032880b01c107001755000e85640007565901c5502c1c010814550000c00400954035280810321101000b00c003440a0000740c064010030310944070704072264100c00b440180503c0340c814543740c100306d55200e00254440ca1480d02c00c0c0d8412080c1c601080e468502041480d040075101d0201462510b00004050458250344540000349030b03c8051403401c040080c1100601c103c2c0c0107119842a003482488000254000d0007058000c03440c1c042d002c20b410b2001003841e00b80d403031007008104e1201d003000c804035006165003018884100061080e180803a00d40c01c00380000e1304183e900c3c0769207018140228040c9000d55601d01c6201c01808900b580442d0f0f02090f003405030344080c00c200b03a03200c41c00c10040301c80b48125804503d0401810510f0b120120041d00010300460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562738678 1250 562737428 562737443
    0x4140109080a050705190f0b0406020d08041509060906051005010e0a0305121803030f031608011220040c021b0103020408210d0507020607031d030403031d0a060c 71
    0x16199041d90b80e03281000d68001c1e103103034403850041143c3d2a1404155412152401900403055584c408010300000d464010700640c1002007424410a40e04100c41c25540b0345c0c80c54000d403e41401e49a0346100030000450964150b01c1d50055401d002d01d940000a0700f82c1d028808000b24070340840d4600a01800c1e000f864009110054005418a071521001041d01e42007009003c803104010325a050f01d40c005800d02c0315100100415014607501400a032662414101140707a680c600041c0c001e000040e480003c0060041100062050000f441e00034442664002030070013441d2040030402409060740c0380402c0d481800c10b103e42d0002075012500d1010850703440300441c00c0c40100700043d000ea00481c0a2181d0340d921504000280341c83d020030514070410000f030700d54604000c0034002c9069403c00c440d40e2000d613001c2d4050160f480c0d0325208000d820080e0ba03e41402440002c1980c1d9142e10980c40044c003089405002a40c485041800e408048100185403003401d0341c1c2c401010741105081c100c207880c400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562739928 1250 562738678 562738697
    0xc18050106080106021005040f0f0b0f070f0e040b220c020613030507020108130b010330020627030d0b15040501020a03210c0905150c031b0a08041401 66
    0x8034001d0b20414142c83e03032078024084007014580080001c00e40204160b504403900c00705080401c5400600440b40350040300101442e20b85226008000300010305400c041069000c03415414503807056949030400400c86020828402100c006583d8031000480100c0d002c8119071503984600c0c8590000d0700d07203c3d076a000c0c1c07141a9100303848002c04d00c620a10160101d01d080115000661060010a50141c2c48041c00c0740381000540f2034402803c0c09030022124052083c124508240c40302c01500301c0e00c0c40c1042c44070552050a50029160784001d050000400d00b0311410b000600c0010f039010000c4401581200d0310b5a01c204201d1010780240740141c2e0080e095135400b044500342d100c081350182c0d0f074103800401c044a0075641c00c9901c011081300710385804010718482070f00001e4030300480c5d459640307590380c0702c0c003a0f8204400c11a400201b042d0f00c0e03020000400064205140100036505841c540c0007041480301c1c5603c500798207002c0c208200070154030001a0104905429441031a4400400e17a21003626 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562741178 1250 562739928 562739939
    0x10e010c0c0e191b03050f2a04030f0b070e1e220203040605040507051215070e0d0f0b150108130809040e0a05010509010213140a030c180501 62
    0x44140d91440a0000d100281081c800103060303505a81c2c01060300da40031482d40102d1041c01c400c8442a11400c40c6142000c440800e816a1500650340c20038448100c0035401c1c20700c403108605d500f138008411061200b1000c0c220800c00d850384140c500958000c401e00903034034860310308000b00c41e00c100c449d8030209070000710701e0959043c00110000403903401d8401002c1001e402042049011070301580004070421940c10400c43e000c0e50019500480c440d030760100711810640340840c101040794110034007818492000d036024a10014031500100c60149141c0c0268650318011640444080142c90b04030b10828000710801c04040751014500d80506e1240c403541c2c0760300d000a24050b00e4420054001000b400200b801256241c03004092140705011051a040c040c038040b9081ea02c64504500654201400d20001d0290038012140d118044000852900001020502070301202d030042414210000c4015400d03a22800d24181c0a142c124049a200d00c1d56880070b199480c13021841c9068071800d1400004a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562742428 1250 562741178 562741187
    0x8070905100e07140c0c04020c06190e0a1113020a02030c010b031f0c170717060f18040c03060f1a0906060d0b04060b0a050c1513020904050c03010515010e01 69
    0x40d5055642d00b40c4c90010300c4041e04030540101d0329810b240c0c05440b080b001c2641d03c80c40140301040252001e080c02d490024420500454110403003010f55060100d50484c0c040d0104030240d10a610a20507181d900d0080081041d6000b498030088080e8400210103481580010251203851551002445003c400702c003415203c851f132503080d9065403032000b043c001c4002c86400c100f9081c00c0d036141600760b0329151407850340300e4402074600401161580c2c5180307c540d21588615175100c40d080d2001d600100c0070102007080c2502c00010003081d07445840c04074080100d8005600019600300c44140700107200f0311415401040c0e04000071030b950301c800d0031141050600c9501d0324440c0e0300c0205421308005400e2031100251609590581d1300580c3c540000c16098240e50241041c0800c0d50786080e103826420850514040c101c161181d6a2027864080010b0980305c0300e0240c41d456415a4a985962100c0c074044d0f26040c123030b030b0240c4d43c15400c010421040010112086c800010240c1c0c03001000c0361082c0041d04c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562743678 1250 562742428 562742431
    0x2030f0a020117070201020c01110c0c0901030c061b0c15080702060717060a211b14010e0105070f030c200d021030111612020708070905100e 62
    0x901140300343e0a05545881580000c50340f02609000161403d031001400608660f110b04400c480030300003144131007042c1070030000820f840a00307440c4031441d541561200c0c0c40700b004922806040041991111010700101001c0d0460a50b00c6000c42e04560f496880304031f01c905441c045000041c40712000260700901c00100b4502800351030b22545034210360181d071003009001c0105415040609008001401c081c501c000012500140c81130407801e400340d1401426082204610501030010140140902c5603078640039540b01034242002c00d05107443d100141c07028042c8400140a403100c1440d240140344d00b0200e00000d9030320900b16400d020300040240e0b01c0791801290320070b81050b04400800d006043c40b022445040b01d442c00d0405000710940c840b0b481d00382902d851781348042080c88484072007020a0144035002d2030070603406410420241d000c0b883c4a115500c028009200d814840503030540207104800150500c401a109903d4546200201400c01a04c10742071041e140e41002421030a220940c0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562744928 1250 562743678 562743683
    0x70203011d06040b060609090a0b060c0a03030b04060603090b010b1c051e0603160b0309071e030c09050402010c020d02120d0f020c0405130206030a0b0603070e031903081303050c01090501060302030f0a 88
    0x14640314045440001c20384801030b560040070030031014003403660370824454214480d940206100c3e100b08180720555680e50312a07030615090600761000a0306230200b540c10b40320511060b03500d03224201c07410450303070341c10b110340d0b103502440c100034450300b10b00102e034442c4880040c130000e0f200c985950b001c1c10390b87c608603003280d5240200d0399824058045000001c580019003001250252034a4174690880c1185090404860465525041041103d0b40c6001401490740400401c150315180e000640b03403003c0680c000f4450035a90344107004550320010354900051114044646035803201c5005080c0840f0f0301904000b5225151210b447d0f80b40900880b0f201d04010240300b15000c0050b802d2018540020b0400003074207841d40c002103041d4840d0005148219042c0d920160124801c44c00e1605107a00d00031002552001a00004003298206000d40d030040c94040700700c2482a07076424112003d0251030700406140d428050f0741c201303001c07054000c2401c0c3c0780210705540011880050300341d942c01ca40e2800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562746178 1250 562744928 562744939
    0x5030307081c0f0b093405120106180801150b030a140403031d070515030408120f04031d0109150306030b040f11031b060d090209040501051609030507030206070203011d06040b060609 80
    0xc080b100c40c140c241b55100b06000c0c14464101305880c000520441d200760029000a42c447d85650b00000504d840900140300a000800011000728a00c040d40e00703081c000e03054000c1c03002006c10380c403240720340c0507020002c100240303001281054074008001d801d640ca0f919130b1a0480044600f010400469400c0445000906400034140d08440d04511504020002c0da03200c00c05100c8000c0e8005180151441011400200070182c42c25140152404801004103409410040119141e0382d801104490549202c000790f1481002e44090440c05003005810041c40407401030705000401c0340515070150380720b100b0a5000c442900b09003e0540c3d620f201403903da0314803694802c010450a024004000140c190780317003c903c0d0192038004c541a4613054030102d58680d0348404002082e1009244400151840e240c40702c2e103a03156845a503602c2c80607010181c80f869000035108119542507001122401e85400307241030340003820812039254007084a0954034a0003410000f0f01501d884021502a008010300707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562747428 1250 562746178 562746241
    0x4060f0e0609061206182b1103040f0609080c09070912020d0b090303151c031103121807060e18060315151905030307081c0f0b09 57
    0x2c01948003406010a504002e1908441241807002d11183d846140b030f0107600307400403403244509460400c0140b0748480c81179052281001814124030344d256641c809141c05501c804400305050300b54421075214207004c082c1140700242c82a002408001280d54103402d54401e5001407081c031682000442d02800000c018036000c2c854002c03003c4400c02013500140121f004248035503a1070707a18000a0380d2030981707548040100f10680aa249181c050741206560000280c5101003441141c4c0001d900c000f001c0c02010201406200070410542e071421349002d1041c00581410b010002d00500d00704400800e07030007000ca021500c6030040c5102c4c10314000103020602441c004515143c100d41c0701800e000c0d4540a048603e41d807000c0354003a41780c010303886409021148052401004100d6002030042070b00b140e03041c84104001d41d4040107480559800c600c105aa40c14060400c011080302e94021120041c581401d682d508107256208410340481900c141881c0d480d1040601c0100c2e10324000507221000210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562748678 1250 562747428 562747441
    0x4140f0d0c051c021005031503070b1602010e090c03010e0a02040803070f03020129040608010b100e010c050a050106032d1509020402040b07170a05162102060604060f0e 74
    0x104042c5581c0404503d04035854030a50005840d00114108000058804018060004c11031414a0103000048004048542c80c0c1640c0041901500d080040514100c4510340b0540e40255680500400010220903403403800c0c107425071382d42d00b0078018440c45c60306410001c3d5441c9004c3c07003100c054485141c020350914001d9070310014088042e4400301d046540320286145070324010394000800c00e0710402802c0d1105030348001d0108481c1542d10104250303042a41d402400d490300c11544210703040c5490441841d00710703900181c43c15581c20340c00620f03a108800c496410b0140642c0070f001540c0c81224035030102c20f8460000d800c50180b00c4018a40b8100e049800360008100f1403d5000c1c031440120040b50258183d0000f900700d8100394400003544200181080030403c44a0000781c00781e4504000c0d500703003c16100028011b0080300fa40c00000042c4074140030a21a20318125294149240744102c1119401040203440b0385055030414095030034800007240c1c0170442035003030050b994480c1003401c00b0390340c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562749928 1250 562748678 562748689
    0xd0807021c0c120804060b040209010503040609050304083f1204060e031c0f0507080c0315060a1211030712200403030504030c06080c0d020c0f010204140f0d0c05 71
    0xd10a0301800040d02c80c140c00902c0394403030080c24072115201d10941d49440d00300312080c0d403084041c40344240d104015030400c82c2e80010079a40c200e60852000500e9903ca03292203482c5100782e40103100644291001a4103809a40c0c154102c0d03102a448840e0b068441c20541c84840d01c00b0111005980c6000e00012490300e5502102c00d40c018010400460303600c4004490504651180da10810700c1d65006c10001d41005e07603801b51a0200c0c100c460100098a0642001030035054054002202500c000003c96050705000d101d2034820721004004594507c03490300082e03e070545000300c5d115041d042c02c42092954002909032032084c901d0303445030f00d2800e1a5101000051014409a8110070000c400034502d42d003070b02026201462082c5c6036140d0b00c90650038400c1802409601241c1003013400340400c840c1c1244503040c2c0c0c890f05031000d405070b103034007044900c281010340b0300b80000316543c80400c000590b90000000301e50800c4050b070300035071209055024403000342a10140078152400c2000204442d0030704 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562751178 1250 562749928 562749973
    0x201050702060c101104080f1605010c1a010605090f04090206030c13121208090304030f03050a0c021905210303060f0d060501060302030703050702030a0801030b0a09140106080d080702 81
    0x44a055070190590025070b9804c17140d1880d00302401a5000c502440003240c00c00a03080d20b041079800a10045048200440d02000907009050402210a421004200c0c010070708100c036030100100e0390015a15110f0050080e00110034041c0306003004809140181440c4c40b41900781c503006440645140d8882000f404036074031582405402c03201c54040001c0400060115408043c81802c92001030021200c0007020716801a00050850300104400c0000500a04078000349a50508042e920f03120381c803105640012001202179000b24500404050b00040320240e20140d8404607030091400000303078200e542d083c004111260305075100b0000f1500500c0e200b4400703000031200412425401251742e0b00d003425110b00ba030045000c00d4020040c85a07044d0507000351a0b001d85244025818a00301000c002d14281041c480603211142c40da010980c0f51840380c1100c6c14060700110100107030304c09180750500070501071242c00322134003504101c1104240724000b02c0d8010540d40c0d0040100410300a20070134034026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562752428 1250 562751178 562751197
    0x5041b0e030a08070605100e0906070f05040e0a060305011a010801030204200a08010503120c0604060b01140c0a1b051e04090c0306140105090c0412140303040b150a03020105070206 79
    0xe4280d0b500c0081c201c07400070030007148100e10208441c1003d0801289010664028000325003e500030400100e10006450b58408002d150005802c0c401c2a030550351485990070640d008104c82040010725003580d0800f20071a0303c10f000821a002e210342d041d0140e242a03901c4180001c04000041015140c281c000600f40007842001c958407441c14082611943d000184410209020000411540c9021300001100700c0f041e84043d46403806414085413256002040140f5642c3e6414541e01180d11031548007209540d1200d00c00e82c0ca0341c00c980c40700d5854180f00c90483da003841c40d01d141c1c01513a030820a01d60480e4006401411b0169900c0030095000d14018100c0d904166584840303c0424501d0016100950243c4000901e030040046000d40030a0140c0195000341510418800e41180001c0ac441c01c550030741c0b0b414040c0705114130344203400c0f45a00f9021401448044184024070817410045400780000040e61a1121080b00500c1008851484040c0c0420380c180260700140c00c098000b4501c2c0f40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562753678 1250 562752428 562752433
    0xf070602090301240e0603060705090603151315051f050c01111206041805030a180e150a0609050603040f0303020c070f080d0201022d250c05041b0e03 66
    0x141c1050304900180c108000781949451040c0104a001d0170619401c0d00140c003680134111624001c8000f034024481d8a12182c01400c002000460451000d1890b2108900050290b8405600340e010003029102048420000000f0100000780e10319081c6902d0361156860086000b4100790b0300401c1d00e0540202c40c2441065481c1c00c0d4500c680c2c200d110007050802c80702c01c40c1c0d0714103050007000c0c4001c071061901e03a45965044140d600e00070030703400800e951a20b078840c941649030f8100c00c00c43e081940c060343e02c140c9170002200140100e070060001c0c014800e00d01a036140301c0c0503981d0101116803070160311070603800c0a8200003003804a000e0720441040d99001c0d04026140c112404ca000d807a0074400e61081c6940c642030141030140510510503054400700510095007040d408044409000e41044065107465a15002100725090208181d44954490492080b03a503c0c10501c06070003815003041c115545011180041400c1c0b606206022852062854840a038502d00700240d50742c0394604a0140d051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562754928 1250 562753678 562753691
    0x111f0e1314061017041a010e060d02090a0e060a02030a0c05070c0e2d0f13170702030a12031b05121503030903010903171b0a050d2a140f070602090301 66
    0xc901d05a90707680580d11034612526800c2000701b5040b018541a0407a811800242060140d01d85d204001440c003c1c2d0101d85007000350710791382ca0107401461001d01d0365845014100c100002001c540c1e0185100700c8491009010a20381d15070b00320349500c200e900042141160000501c103009a00d04901e50000f404101c0e0300011034680c908152160611044003007103941082081004082449051307000340f551658002402c403183d4408200c82a900801a070000303000c2201419990100622503080c2c1d0040e50403042610082c100030003a002c080b20151812111400d485c94407032003042200c010034000810118203403250041740701d00e088020740c6a5811f00c0240000c1309588d8007031003801c0001d40300c3d4459400b0070300070040050b0f405000408a10010840948801040140b40c04071105803440d8504160384540402180d001045111a441003ca01c01e017011452000045ca1a042082c2a510f83c441c4d40d04004040c0c3c100e612403c64907190044081c007104c00060116000b409941c00003c0c0042000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562756178 1250 562754928 562754957
    0x180905251815021203090a0807110a0305060a0501080303070c03200105100e01090b011b0309030501180218010f05060a091725080703111f0e13140610 66
    0x1081c555030000c0c40740d240c054441d000d0054040202c14883c4044c0100355045241103c4c0c6543c581164400c090900e18000803d036080114101c056404188024082c01c0d80c1038403820100d544442c200c0e1b0800085e0324040010038907040000039644200c3c010713034070a410318003150b50860b04145845000c0c4c54207414114034514210081c002c481c4110b10a0303c0141055140c042301d5410040c0680c003140701140b074024003005a0742d01130102000b1703035002407020f45085854074003156000c50680c4040e00951030641154041c003600802c0000d21070080f90071690040c2c060600c042c002c0f200303102c6d186958541c180d0400542c20b0140107072504020754105400c001da941c001065869828411054403500001503040d07866200100b1502c0c03215402c01c101204c40e0034111019600c0e029400082d1911f115070001940913501c07181d0850300c3c0c440340e04180d406a5041d1078042c0040030000c0a051090700e1440d00a100b08010f40f003074007404884008410800e80700c81c001c0c8084021182d601604000b5124580b405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562757428 1250 562756178 562756217
    0x7020409020d080307030c0e03251a07030917070513090c030f020315280902030102070b07030608191e0c06081e01060507060b0604051018090525 64
    0x8540380074040360f0ba902c1c941498000e0440308803d81102c01d00c01b82090780842900c0c00250100c0000307000ca21050b8603007240e5410307540490164860340028a400e1305400a5035102c40c00341840da8401e44652a1507a01c1d501c0440c1c0e00ca00145004001d41c0c401001000f8629000c0349080f4030806000c00001d4840c415207407030814500980041d2005040d1403007040440c103082141c0c454500020360441014104440303178002107107401200c18582e10305c400704d0641120702c960150b0b0030540e0060086550318250318200c90f5003070040314400301003450403200050340b407404200510b4001e2600e02181500000350f0310000c802c942201c003400340031048004034001030700c0c3d0342c80c1c900038014644450308903250031504000c0c0c3d24510f01e500b245003011107004001194001c0240c03a50a035121002281c0350342d404000c40d039a80100d50000d580f100701607600909407074200103419083c541c403140c030004a82c0c45007007510036250242c03501410351803030792041d80c4032624414595400380c2c503525141850a0680d0952038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562758678 1250 562757428 562757449
    0x60501050a0315230907110607080c09060a08060405091b19120c0806060d0b0f18060112021801050a0501050d090510050601110615040903020c0406030309060807091a0702040902 78
    0x1380103031820740f1054a40703070003903203994072442c580340c006002d18481c0c644079101c2001802600900c1151030114500c1d25107403050300d00311140600400e4695110340303001001e5140545046000f10314010100300e50050100350f04144400e904506031a280000082c00b02c2c400c1c2d85030360a40ba403c40d81d54080748400424180c0c100c19400340380f40b0940b041c03d0003c8281881d401400051241d400304c8070b0940020045090903520611690703040101d0f555802c0f18070804002e490051171035010b402c00100f41ca448541310364135030600907600c001034040c0c04218044410300a0003015440a1920070401156200d82c009101601b04420041207504281e0349241c5041c42e51102402c00da5110400c101c603550380204445888140c0c00000d01013802e04688111407400000310081c02542c80310b00c200c0a240c0204502c80d0b00f8040600100312043c1d49007402042d00031a401030b50b0000e446072010130030352031141240205450403030300c40c40c140524486900b112607120b40c7c0d089030400d031034500c82c50140c0c0c0c4004254 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562759928 1250 562758678 562758719
    0x1f0906090204030c0906050307060c050a2307050d0506060906030a1505040212010b010c0611121305120a050a0c1109150406050102070803030609040501090f03051804060501050a0315 80
    0x1d0303150750562601e14a190b0440c1c1200c01400c0c0b0b00882003040c0d6400142c1e500841c0c1803428004240c0c3c100742081410308514080c05401c00d61403136500c04031070942c40b43d41c8800c0d00040056581c03464543d03081046504031414060b14903408640412941c0c6001207407583c00210003070490745840342980e540f00d8400c4418034150322465944040005508041d400c4402003500e2070000c10110007100e0018108000a060141c100c564460b400115241c5420880b008400307050f101c075031145003203521359034101503c090442e468021000001c2584404009688601103192251414480d4444040b1401c0107038000550307044080c5d0b00c002400f6112442c000340a103600ca03a406111103102010300003951841e61040741154044a02003121410100980f40c0081c0203c40c00305194465041003805440c1510300a42184404410f5030100750b000b600411420000040440d100220042003004a6605205080c041141040202c413950321950100d452000780c2240c0c204029202c00c0c0d1b080c0b4102c080d0001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562761178 1250 562759928 562759931
    0x10e2802041e06050a031512050c031209010206010b030c07080a02010e0d1d060c010902100512100608070507150c0906030e0115271404030305070e03061f090609 71
    0x2480901d00305020007221012071000c25880600c3d103480240a84034181e06401015915aa904003c8000c01100710051007a080c94203c2030b20142046c0380c0700c81ea440d043c80d1080c0b00300781e2496140d02114040d1008610140c01400c40d0368a00a011051503200400504440c1c3c000c01a05000032006070281a400030303541e000141c03501a030b58071140341c80e00031400801803140c543c03c121011950000381c20740880e0240c0b00d00d511120244100c2e409806c0b04070700258010301c03e403907429440d0350180c064602c000711048021001e84503014402d00701c000740e01400c80080e203044002184240500001c1c4526132107000c0038940030300c07814101411190952a1200041c00c1c1c85420481e6a515004030b48281d506c0ca0002c1062a144010740207084076180b0803441d9142e0004403400134841030318010078040204101c280410b4568031050a0340c074a0441d811800710b4505804250114071a81550000001c060700805841e200d0162811822103e80c4d4031110020120f40301054a4a050003a10001e0044000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562762428 1250 562761178 562761187
    0x20f010518060604050c1801031e09150c02060402120f0a110a0b130603150e0f0f090319050c010b0d0602070311030f040b030a020d02070c14010512010e2802 69
    0x200315003061000f81400e4842c0782000305100040342d81008407200341c01521030203000c40b0504d20040e03028102d003041c030b20303914510342400019030f040a41140c0c42c040e208100110140d0342d007114035012900303103107034600041c0c2c4448000340041c1001b04808200e0f05014003101c000c40b40f2801e0b00c91804010080840d01c50341d0300d17025603996081050582d8007401407000010704188951595004c180100e20800c01010f0b103400910300c485000030961406048000d003c0310941c40c2c1402e030414501c1d001d0b07444900c2418000c00249842d9004001d490740750b400c00d05038410003400e0200440ba5a0000640c0c10b03015540d65003c0e03a0ba40da201110000c20900c94030000d41c03141d00f1800c01801c4031440c01c0c20700005070001c000703a115000c20312040718181d03544009085d13241c2d103503c424070009001e041164038149200080c2841404003607980751003101d85150079100000c4945d401102d850085911040c8903d10780380062054820690034503030300c182c404c1c4400380403002588105002400c41c0820300d111507800103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562763678 1250 562762428 562762471
    0x10c14010e010f0c030c1e110f0a020a120206030708090715180501021c230715050703150909080c0105070c0c120210030f1b09081e030910020f0105 65
    0x140040c00b140360b040400c0903008511b03002c1c003111440d50305048031883d28003440101c3d90007a2005440f01d08940102c4d0071a189449016a4500c801c0c0d109a118502c80240015292400c10032040078a602800c098115110040107450018000d0143d400502450102140d00c02550f4414071514180b5558480400031034071100d8442e80c0306400650454201204034120480c540c251b004203844540381c08010301070246124100c040c024510141c145100003290782c1403000351135802d1161029038600704101e8803015006d81c2250b910f1b2141c0c400b02014994100104565a406182c0c4540111246482c1c000c58030780c05800c5407011624000407602ca48440001e00c9003006200d0041e0408950070100744505030001488203100b582c48200305a110746440516901c243c210340074528074081d449100060b400d5001e07000c840f2a002d0311800b440394507500c80d20344ad0039070a000e022602c40800303103240c0329804040c001040a21104442035120702c221203514030ba02481400c0c82500d00c0051000d0501001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562764928 1250 562763678 562763681
    0x1e1805010c050d0b0303040b0702120715050307080709060801120501060b340f062f0307021501050d08130e0c130905070909050612070b09042702010c14010e010f 71
    0x1a9105000303a001f880140602051074003192030b138503011910399000484140b0b02d6071400d010f541061604501d1000c00040e21030300600070714095005922500a29500c4800881d9008814401c210009546800400c0f220b5a100c0b03201c10882c2c05900041040794603a0191005903002044c91540e44500322854600b40601c05244844039076480f1a1807078603090340d15600b00e40404010007804881d0b50b82c2c2d098400900c544000e02d45d1030010326901c6540d82079008912001d0304101c40308400741c010703e19501c41d1010004c0d4410b06941008000861003802030f03c5c0c0c04a0b0790800f100803034040c260300502003034481328400800c3c45070407080d503d6580ca140c12444036414019a600806030142400244407400d90881c070b008058807200702d00011542e0301d45c0002200c0d001c00c002c003205e042c01001d0001c25008120401420071400c141d03418010010034400d040c003c80303a07021201054007403848440c801903100e0030740d080d0039a001e01c1d0026143c04684200b5401c482c5102c0080c0309981d5a1003181280300701c0b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562766178 1250 562764928 562764941
    0x1920030402040c02030705070612020d0f090506090106050a17010209031e0c180f0402030304120b0108150601090b030702030d020406031a1f08131a191e1805010c050d 73
    0x11413000e035040400540d40c09a41c0c0442e40a52000d20085241c0a4001401641036030b0f5103183c246400d0004e00580e00b2440020140030340d041c0da40d4002c500000e80820814000c000480381b01406456540b0718100500c040840008012200c55400700708050181d0b07010080303110502d4880d0302e400842e00291900f20b01d4400e085481c1401448030050003410090391a5050394031040c14081c1c801e1035900e502c002802c2d40b1480d0071044071000082c0a18061010000d0002d05071041ca500701c810f100f195603a440ca00c0340c0100e4a00740000c1d5000c0b014005074030840013941d0080c080d03004032410480701c40e5084041c2e8015401c8000040c1c1c1c4ca49002d640c10324414906140c0c44010703150488800d80860f445208900301d09002803d00082a002c46c182c0c6d5213038140c02c95140d8002494600004681c400c280340d1795010f503076041100d864000ca181e015840c8c0d01c0b456104040004c2041c0d0a800a0070164000d84084600314040c452400c10071804101d081c004c0200011450359030750b640c0c124410a43c8100c0f0072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562767428 1250 562766178 562766201
    0x10603060608190608190b0a14062b06020c0c010c08091002030702151e18040c0c05160f060c0f020105090607050d02070e0601020a0b192003040204 65
    0x2040c404015641e00508681c2c0c00081c040ca228610030795854001026101c2030b480510288108103041482c000d0046a144080e03120f141003020030389880d2448410350320300010302c2c81920305601c041407c41c6800043e1100070004044d02d0407501801d00031f0300320344602e040c60682d85290005040d0002500078040d00042180900f07100c421101c0c42c1e10b840f51351740500780d111070180c0901c02c4d0b0182e2450081065903041c0798001c00c0801901006030150f645604a01d48049495800d000d100703044640000645541c05014181d406014070010204400b400c50918207009000b190300a0f40c001c10b0080c80100c1810542750100c2c030b182450308004c2e250041555000344204045400642d000170341d51145d102051740c091910b1034032590a400001d1051141d00002071040c030404140025070f50f0041208811584e00511110743d07030780c8250041ea10f420402c40024042c1c00118000360000b194281c005080c8660302d0b1b40041d03401079451a07a0f412813181000351090040c084100405c40c60503003d07d404140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562768678 1250 562767428 562767431
    0x203060d05010207111c0b0f090102131206140c120613180308060a060210240e04030f0c0f03081b07030e0a090606090e0717010905040605101d04110a061205010603 72
    0x411a1203000d103d03000a44012060041040410366109c0250103442c1d0743c5903820b030715101c0d1039aa031161aa44028010b0100c4441c3e0030804406512084e0000f034510803034018458500c1d00f40c0001003441c01070340042515500c814254181400d5010a1240c134404941007151840260000d003405042c040004200a115201c00e90302400380d10b41c0031480144200004401141c48000c88034400c000309414403215264800c0f602c40041c80b016214251800390b4080c0c0c440440c42040d2800c101d0307284102d20406044030091010100c0002c3c86420f00d56880351540c1c075190001c0101c01c4600d5510382c0244010740014040c40050b0400d4940000c0040081c031a540701001458a40728000d82120882c0c0709520b000002c0e4000500c0040c002c042c9408420301d07a0034038003070075a19210503078010201075806030b841500d403c2c005044d000ca010041019907030040100001c00481c5d00160b0041d500082c02101d00d0a060800000a43c49441c041070151516450f01035144440002910440300705a11040815 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562769784 1106 562768678 562768729
    0x190e1203070f030b0a0b0405010c17130f1706011a040b0310171b040f09051207030215060a030206070201030228090b09130203060d0501020711 63
    0x500b190b031810060003c0590601c2549a07850199986039031041100f03024542c000d414480955200d000226050025150310350065042418245425900350009000a240c04007281002d010f11a003004c0307841c80311000b0300b41d07951810301c030340b40030018403601d86a540b0340c143d4101e40c05000301032240c80d52810f01811030008402c143c85282d000320000362400c0074603400414805c800d00c0b401144003a0040e90740e410403005200000382010260f40c5d403c0600001103050141c0056501c244540301e0300ca00d0315081c084d09020302083c7d81c41800700c400381000034541e01c02c124902502d4069584a44034500342c4016002840703000002c841c90581201c9000214007038603c1244001034590303c008803a985d41752584002d014051903030b80d006c6840400564512415405568030030402401140e020a403510b43c5400c980c4004020340c3c0390f603000780d190341c0b460070101c4183d003080000d9521081e08 = true := by decide +kernel

theorem cover : BRFrame.Cov 562589928 562769784 := by
  have h0 := BRFrame.cov_init 562589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562589928 ≤ n) (h2 : n < 562769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
