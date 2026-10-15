-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3906
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:01:13.201035+00:00
-- url     : https://prove2.me/submissions/2b0ed7eb-f597-470b-bb4b-2731dd866e6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 702338129 ≤ n < 702517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 702339379 1250 702338129 702338137
    0x150a140705060402011d0d060c02010f1b110102043501090803010608090f0d050a02151006020f12030417210405070801021615060e0c071e050a170d02 66
    0x2007203016280c0741c00d06100150583c010000d118051251a1290b4241901d800b0180c20b81d00b030f0464030100d803203085102d043c0d004103c03024100602e682081104c000a040002d8034107680c207900e683c0e140314503611110444c201e00030b60090704a1241c03d1090035018000b0790030001549150010b00c8180383c448591b4150031154006421906140f021004000b8a90000348082c2d0280d056800780000705d00200d4441d0b142e20b08c50b0760324024004085122042c583c420002c1c0f0300e0000c2c544000d042c09043c00e10034240b008030752744035110051003006c0e09144542c2011806071000d800b00107600341161a0707943c902400c0c001c4178900380303c0d02e0001d0104141116400440001c4007404404e025401c0c00d01e82030860505034140c00144044c1c0c0100700700e8034403074080540c21000d181c111425101c62070142d00c91a02412050340100d41b040100b00501c00407502040052044910034044005000b80441100c080344462840c080c0a80c0c0008a0340c1c1c021a200c400c400c117085200701c1d0b6581c035000c21130314444101d0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 702340629 1250 702339379 702339383
    0x212090622080d0e0f0409120c0309231009061d0103022b060603020301150e1804032012040b1803030d091430040506120402040b010905150a1407 64
    0xa0400d040c6410b418460803c145c41e12042d41c0c140588405a244c030817402003015000c1041110048050051501c1070b884a80a42508540c144c8200000761980041d070f00e18000180c4180461130b600e00d45540108a00411500c0a032900030f0f00340c0e1010541c0c15119041c01c0c1043c10b040d020480000d40e8070414103001224603c13920310000c075070725080078601180c07482d800c02014035104100601c80300000b4507520400c1c13242803034805101310408012850440d608815200d80c00c030342c0d1b0280400c0581140c0558020407440b000d52040d000503d440c0b035610040030381c8005054600300000d0100000b0030005060042840c90b5080b1410130307000100340381d0703480701f42015141036075016003104004080358400401e00c0002c008010306203000751441100d158810101001011082c40060400004c80985004050003400c464448021983d400c070000b104036801c9200f280f81c103103c0e07003281d809980343c4030560b13074080c2581400386400055071160f07a0251034640c2c1070001200b4102414030241c4001c00d4464 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 702341879 1250 702340629 702340637
    0xc0906160302061003260409060902030f150901030204020304080712082a030c1303050a061e05040b040308130b040c06080f1306020d1e0c0212090622080d 68
    0x20005040080c10318002811611500d0141380d0104041900610100242406802c0a040036080343c4800c412070300c100c0e4400c000c400d080540000342c0d0790716903001e58030594400c80206103a035156481c0401024444460704e91244c40b95005002505150707001d980c0c041c2c8901100361410b503094840c6020703402d26440290011742c800040060300c3e07205c1c0619098038814510200c0d180c1c0e0b0082070040c45404000c1c41130114400200d04261034003125500000115005000d80c0c40d6912241070001c0940f2a80400703503480c09110b00d00059200c12407041600c41c9800c0800000d0503283d565046034440310141281c403a0300c48003590b039401b043c828000302d40541d102e0316450710310f50310703044002c0d0010800400270f0402105580401c10110101c1e5201078507958000001a620700c0042c2004008207402a0600c403c00f680d0a913078411820990b00501141c0642c0c1c0843d102d41e191503009a89602c154014260080802d00c604401c200d1510716000c03400e05944c803039184440d140d81415240202c0400b05a00003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 702343129 1250 702341879 702341917
    0x1c020f0304050d0f020a0201080c09030703150203060a0e0106021f021c0e0c03010506010503010e09030d0c020309031501140409080f0a200c06040b1303020310060503070905100506030c0906 83
    0x410b0f0132036000e0110540304e001800344c505142d00068804a801060962040390010f8495055070f010b0110714081c2d030303100035072014100300c080301100203400440342c0c280074048915012a14032948080503048950581c0185075200100100c504207085041d04150f00507000e010a00d1600d58500510506c004070600010701c2901c00140c03185000c80554400340a071b4544010310180c2e03680103080780d041d200c0e02000f841d600e8440c0c100b0180703076110301d0b05007282c402e04d007120f107045d0b259000c402050300c2c2c0000c604036000c0e42c020701e860f42c400c1142031288101840f100e0310003a68030704007500040b079145d010304105400c10f8080c8900c0d140350f900c99205500007501421f055004075114003e43e031b0661502e0300c01000c02600e0000460324601c20b80c00b61050788103020810812000805e0b00c08800303158081c01b5a4104000301075840d0240820740176807817013400b03441d5000c6607414a51041c2449400c8001d10400c2c202c0c42d050034840d96074005041d41c1c20080e420007080000c1c1d01c0303e6000b02049a92000c40d8030762 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 702344379 1250 702343129 702343153
    0x10302070c090f0c140711211e1e030d150f2907030228021504230307050d15051f09051003021c1406010501030606050703051c020f030405 61
    0x4400c00160100c00c0310641400840003144658040e0b5100c4001528685840c99941461403007050703404034494482d104240b1401d4803030030303044c0310351084180d4001264200c3d144614201f1100e8200e80e04042b86a100b448550840d880d1a046580aa1360b0000005000c58940142c202c140380c05811a070b080b01c80b4800350400403d1200103035400e1020008419051880c0703030303038020f4903642029214000e10700580d014440750b001054803800d11550081c00d02c040d640000158048681083c4150004084070039000c107480f415078007590781d01420050161885500342820041043d801100584903440e0710082c04101d000e141c8100c2e4000c0e03001900c040c0076412401c10a06900000380c001403007403402c4c40140074940c4130f04418441502d50403035500080d00c16038501441d40d106615030107010305a18860b03940003002c01041c62410f80e90b080e40c0c10303c070142d01c4410588880c821600010001401004071031203c000700e00c1c03900c00b841210031016160480c040740c03403c0c1980083c1c07000e5031250012008241 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 702345629 1250 702344379 702344387
    0x1807050f070b0f04020f060a0804030810080a03080712090201020a021509030d09080d0c0308061e040212040209090d0c030516022e0810060e210f0c0a14010302070c090f0c 75
    0x1001b480d044851134a019a8501e000304500e2015100405010241021401d030881e6140e1034405007001c8400c0741c0420301c043c2002000707404191841c10103d207040314006403145040c00765108054068004200300411030b070901070f00241c41141e860703c2d500d090101c40d08540c3c0a000440700310b41c140e55080ca44034100882c40b81018a10404103007030180c46020480003a401c09400c680c400d00403070351010403100945c544241000244510b5611600c005850180c0c040703c8850540264000c0d5002c0c010780e40c503412001d941e004601d0748036000c252031404083c0041d22510090000d801091490080900958046100b0444408550b98403030103803441f444415451041d8038440082ca4500f40e000d0b03007014400494418828040c070000c2007400002d045454668103074204c40c0000740c4041006400b102c12078252108100034640d91107000d0850404030310728024008600f5103140c3d807107031107100d2030010042d002584007480031503403124a0080080d14103014030500c550007030121004680e001351070000030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 702346879 1250 702345629 702345649
    0x160f05070b0d140105100f021617060903070f0b1317030106030510051c02010207170604140102030f0f040212061008070605040e0121050105010906060e1807050f070b0f0402 76
    0x3d01c5003a540104050b90b11410504c21152160800d0043c1c4c0c0302201c0200d080c003d0b11900c600c0d0038002c1702d50004240b82c2d0300000722005680c0320269040c9d030b200c6198290700c920505501a1241000035041400700b8070000c015078120b25100e0000c10f0301030142d40c82090030f203a1940d205003070580c080010011389406001c4d541d4080b00d62484481c3d19401c0c0030004203014001e0714600c1c0244198856201107900800c061409403d0403645010380000790544503a80e2001218210b4030001503d0b50302070340800c1402500c0c0100e803c40312800040da00d0707072407244030140000c1c816030380710f031000600c013881110034400540a240144c416001c060b043c00b81d80c81c5405259400b44040040c00c2204024050302452602c0c103640c003203000f103190908480000c45910040b200043c2c02e41d485c0600004404915510681c00c448a54417000002034a640411006942001c2d807002c1c00c02c41580091f01451062000300041c0050102203800c2c030442e5250154140780850358404a214480148401d43c613244a40c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 702348129 1250 702346879 702346901
    0x1510031b0503090709020304060603060c02120405060d02071202160f03080f0912030d051f142b0507050a0902040b041e030f0305120906010803160f05070b0d 69
    0x921020445400ca0309280c0d0100080004014011001c03c00000d400d1041074020072914030150b480741080d0618900520151100b01d6185150018101180b400400c106880d4a411100c0e18181841e107400c0c001290b2000c800c0002540d820032034a000034120408481a034501d0383e0050801c0d8041075101208070744035400c08591088607039001c100080c40c11f01140d21501015460a89500092000c11490580b400720500315001c00b0900724454407140c0d100c148100d024030071100e0100c5c920240d5030001201e03030241c40720440005269180e2401c0c14450f610120f0103042d8884501420040042e01450002c54100d89640111100300079130700d000c408003405011101d001314506480d107074100c049482280b00e0841d404180600750103080c02e07003202a800458000711590205c00072490000e0059100351150740c0d010300f5000100f607038101e00142460580c0c0400d4001c52034600241e80c0307038060140c0e000e800c83c1c51b0450300081800042051002e240140884401c07180c5600c925030919090791000107034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 702349379 1250 702348129 702348131
    0x1518010509030307030302070609050304120c0501081015020a1e02040506120c0d03091206020c1905070b0f0c010e0d1b0b0402060d240503070f030b010506030907030605151003 77
    0x108006690040112401d1350b62506005a5a81c00382c6007460242c129041d000c0c0c030300d000c00700d4001054914909140c2c0340c54410403600000d60388406c01520301d00e1055444000f5416401018440c5071524203503000d5140440c01103407000803144d664001104071080d420400c403801219660b0450806001b02034003e20211412252001100ea005644107001c106003841200303080e22420905010389645c9000d00300704002b0400c40401814004003940c0700101843e0140301d078503003551003000d91080044a1940c800c0203006228074101d10602e045d000001039182e00481000340e4924070b4000d11460040041840280801f6800060054038101440d20811110310000c1095400113030003420980e8401d90450750140c40f4040603805200502030464002d1225011010080343d000d40d400306241220b00c1181106e210f5510340200b55004001440000c0c450550394005000c0e070324188014640c02001d600c122006590341ba114034090740c00c26a0a2072103181c0403100300480c0c0c1800c1710f40515000702410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 702350629 1250 702349379 702349387
    0xb090f0904020d0602160b0901060512030304240e0106140906090f0a090303110c150117030412061401090227030c0910090903120606020111030a0905070515180105 72
    0x71541c440c00c5071100500c4d040d80010000c0302c41c22405000d903c02c80c1c000139440c0312850040555030003880c080c09140e10a101c09000b0b441d0503800082124803450b030165181901034848c02c4c88400584010700c00b501141d8444d0101c50440c1424130500000f0b03c145840680781c501e075607050000701500036081500807040c070030410441034400d0900302e802002d010b000003880300c1c8904086006003c5404a54025000002c410210180010b83c0c0303984540001040041a681d503d400c00070103461030408161030704140420069210f890840c08503c03401060080782250380b4000e0204048004d81161251690104607645030403980168000d90a48070301d401c1080700c40800010766200c8541e51224030403070000b000a480580710a900a00a09503500140080004e0b8580900180807846840c02c0c02894030000140c0688140512592101031a4199180d900d6848140014092140f01664a80300d100000034aa4030350104a50f107000c5020700c04d0b45c036011030400000b1401c540c80101410884148 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 702351879 1250 702350629 702350633
    0xe150a0c1119030507020d05060a0e0c1003091e140106090c050d1d10020c06060f010c031101150f1409010303020c0f0a080318210a030819060b090f0904 67
    0x150044018001c2507a840303842d403070b40b600f00c40030b1190410080d00443d4810046042240001d201401208145014840e05164071021a0b030303024910902980051007070048448107000b0f6000441803070080020510302c04c20881c80c0c4110381c426000455040030074003e010a9040c0a102e143c001d441021024401421224402412070240070200c0c1e40403030340d130800405000b0801243d02002c0828001340e0340c050641595038002500442440c0407940601400502a40b5041803031280e1000161030703000900c5807548046075007803011a8000e00b40e40da9008245084c40b420340c001d200400c2c0342e031940603240d8104155880c41c1103c44070410300070f0980c000180b000036004190222600c0d0140ca00a42c10000c220000f0517a00c4581e010f0500c50000241000780480070040d944482082511410050b8507400c00524420502e02000001034200400840009200b8218241c10a400e906000000c481e19076440c021500c02c4e900004000724000b962a4881c04c00110112544004582400c9646041d17 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 702353129 1250 702351879 702351883
    0x12020d05010c1e022a0d0c030804050118051807050705070312140715050c090603011e24080c09100807140a09050d021513030c0504020a05120a0e150a0c11 68
    0xe006141c604240042425400707071500344d40049030942103010134187c1c0703581c0d0402104076030050140d6400180f038060403034200c0b1454101c513003c9490103420b090104602c5501c150703440b0310207064982082070800400d03001c82d208000140c044d602130040b0001c6060009000307084003000610b4018400004c1c032400001c42c0c01170441c1c0a05c01a247c00c0494940d84100d03600c14503120702c003000c2d0751107000800045182c1560503070b8091301101000c50020000d0b00d0303580900c03007515100ca802401d002241340c40900da9108294164101c0b07031544002d4202804000003a502922000810001622140410a6840d8030504000d00c0c00231a20b0424030300f080258004000b4111805840c4c012031460300c000c1700710744881c80200c8083c24a00701e4180c503908aa2410204800180700030313204001c0c54800071680b8074040c4200c40f981507454a906d4074189005c10060413040004200002c0c81d50f5548240c180138405214601e80c0360001d106070680f038680380d80403404803014401c1d60410010428150402d0380c0340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 702354379 1250 702353129 702353173
    0x7060204051e010f11100f29030604080a1806111605210709110406090807050105030708040f05071404050108160302060f040b0f070323030112020d05010c1e02 70
    0x140c1ca03180045c0315400c5552881d02400d01d01b00d80510b850300c101c0d4051440f1a500002c5003451031a414a880d00b1100d11543c10344000100c0d8a0785130b0092000304000441480c02800c0400441c1441c0101034000c0b8520200c42003542c0c80840450741c00403900c40401c4052015808204144583c507098500780008032b02c10090744101c4400300f05e01386500304610388042141c000104608182131140013099070040c0c1c03d40e0000e100c0d413400b080755050007058943c2d0200d4110142c4806a40b19800c43e81c0d00320781140c03c80340252041d140151158407900108005018020191121180c07080c3d240880c0010300084a005034002c0c0c103503400803107803041d0012103148203104403030301100d20356201e0781450050340c00d41c400c66201030301440000030060401640c0758040c240c9503009442c1d040035649c102e8107000c8035800c80c0300311390b91000003080107218100c111080310003064005401c04041440740d0b81c0352400c45016529400c0801d80c0400c01c0380e100384120100c158034051502c090020080d038440400664a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 702355629 1250 702354379 702354407
    0xc2c0109020c010b0604240314060f01110105090304140d05030306040e10051e0a0b090406150305100506030601121e1e1406010b070503160305070807060204051e01 72
    0x2400080e0b40b0b248050075042052441d03130040c0031035500e56035901017400442d010303100c03440445888424100098001d1107400c480014070410041d2980d2850304118840d0480d0f4a4a030510621802c042070000003446814440d82800c402190b0303441c20280c002c1e2911107440c0728184944005411036000800210503250011025900400d00015061882d4100803100c81c1c41800640b40a040020312682e440d80c0d422210300d180001441515003030640402e5418102c03001d0b800c20601c00c085800075642d0b60005d00516400ba191070f200c030380c0740c0d5101d074140400d505600d6001a200e100303001e810302e014070695004041c080c00c9a00b241c2030591347da18000010a0303007074400141c075000724800e10000c41035038500d80440040c0b030111141e403440d02c5040d00710399030401961482070400103d41c56120390211164550800e0085007029111448010308800c4540100c0400109101400000e0645000307071288a21403400541ca950412003408a0101c904240046141c5da070113244640d80d0300050760000c105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 702356879 1250 702355629 702355631
    0xe030c1011040509040b04120504031a07140c032703120c030906030108011406120a1b0f0303051209011118040605030d020a02190e0c0a14070c2c0109 66
    0x140e04010340e10700a01843d403000c1c0d0401c40d960200420041c4400d4100c0c4160321841d000d44100b6a01041118075004500000389210504103030007406240040300075034040c5051902c8220003000c4d200b07802043e00800211080e0f030340041a501c10620580360504c2099848942c1c0058080c2c0150001e03035611488007087e16408000203903290120740900031940c45031030103446c6c41e5807565031300723656802401e03001072058044103254046480c40c42c0120a018040480d00014003a000d520307180c50203d4440c00201e107040e10320b042c50000f444007849101074000c2d402603d03580c0c0c5840f4013a0191800e400010321008041c0d1411035058010548030054602d030524143d41081c0384a40f490103e80204000c0c1c116030340c184100c031502c000e01035000802440417031080d15a2070080c403603c81007203040c0160f8062400012050300c00101d04003554405403a0060701890310710f5003034a00382100003041d400140d040c0e80b11014a0b82c2441503203460007403141611032400c4411100b42e0386480520201006003e82c40c000d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 702358129 1250 702356879 702356891
    0x120f012f0a08010513142d240301060e040503070b100e13140106180b040b060904020c120a0c0b010602060402030d030f020409060f0321020309010c02061b0601090e030c10 75
    0x10107400c0d8040c420460107502100ba080c20048500200300b20103142c0c01c0c000f08280400320074401c1001c1035481c0516550223840081108007540c0c14807010150fa1115090340d80c9140000b40e0542e02100b0f5405540140c01860f990070745800c00420800c401008080b15120010007008100048168194050300d0400d40121940d928a000160408181204032066080040215400c1d02c1d40405244080b42040b04101c03001071401808103640500b0a03255016000f40f05442c01030070310307400801d1128030366020f481c4d040071000c40903200c640280070340c040000e008031001001c211415035034601400341c43c0000c0c00c280c9403a50019568905503c40d440c101a2280e80c00f446c955200e405075400340c84c0000c0103100c010340b103c080034001041c51000b5109086000d2030811803c40d074803134460f40d078004c542c0036501e06032041d4010344a81c3d141000c101d0300040704009403150a03200c2049d071489100b501025003801d524044411084c1c4000d600b1401c610f410030015191b0136080004d07020a508203006022400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 702359379 1250 702358129 702358159
    0x12a08040326010807120308040228080c0315010b030a091b0602100f02041d0417030f04020306090c01120e0a120c0b01140906120f012f0a080105 64
    0x2140b82842c00b01e2038510707489503000205040e5014505031044181100c160b1596800d21548201c3c2070075001c0d01155840020074094140241801f0010074200394900a40055010b5940101d4644e40300c0d00054100310004078403850148100d2104c00100d07060000c1a50401c116510381c0d02c1701508444149568401280400c90708000040c0c0030181c03403100c1c801d455a00c500280d120100011906a0649007081075a04000d042c800d940558500b40ca83c4428840e1046c0c2840000e00043c1066031201a85101c0103d25141c0030000d600c20904800545031508040c4145464400080c10380c0c45141c1181659081e03d0342e03c4611081c1c03544d8041404541a1465680c60342490b01840c00601900a40701003d20980e4201c0c5901100314407400c0c211105a0317840c0403130981c102103054210781c0041840302060286c03030300102c86103900c046ca40030382c0d0007808455081800c460160003481c84a40050001070036002e6044000d580c1000702208251500b150010001c202c1c1205009643c458000c510710029 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702360629 1250 702359379 702359387
    0x15030c051009030b07120e070803092b03030906050603011b120b0901060203220518070e130b030c060f160807060c0302030f0105030313050f120307060501050102012a080403 76
    0x100440d00130400b0622424820001052000342060700b020707403030a124441070500800201a0120307040c00001e107040a01c09001c024044890010304400703454220409000255044140d00425205c1e407800a040012840c0c1a016190000c050340c0c0310380d141213208441d8007003840706003d480340c2038500482c440c607078202980020801002e031503401810340c500114455030000024080c0c101e0000b12500c54002c2060000c0210381036001d05074200d0002041c41c0300c0210746d484026000b0310203090101e01640d000c40450159100c46006480d07054580c4e03045078050505000d013000c00c10098480501c3c161100580e60300511804000f00c070310401c580501c00504c10500252050035a010303805101059102c18000d02070340059031031500215178000009018540001142c0c46181c2c00d00c503451029207040100005041d0100e1030070780211001100d608614403d0004101d158421800040d02e54140000242181d0325410000092800c00040e041e61280030000302005807007a24100c40c5580e01c81c0b400719 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702361879 1250 702360629 702360647
    0xc0506040b1312030c1b05100209060f040b12010f1404020a0e27100308030402060d1d0c0315060108040b0c0d0c020318010c0203061b070b01030b0402011403190203040501090206070c0915030c0510 86
    0x1411840c03705001c6000c100002c0201111038240c0c1d04c22001382d80360f10030504070b10707001c1c4940e6540042c00c1340d8134003090500b81c01801100c145414071a1070100080c0c0450808040b060101801c0e40b080484080310010048800d0f0704002c0000b8070759aa00e09507514104544405030020f442a003000c9100c0411000700d402214400c440b4002100350007030f0000c003003544d440d208042284030b4020101514040c0701c0a140c45803246c001651110002c0e203c6485900e0700d6403024000c05200b54040058040401460160910301d0724950300844d036502c00c120760074002c0d90450144504204660481c00c0140e6400102540c000108403500340040c004180030250343e1048050041440300a600000180120035450511a500070388a01c40d0300b040d40d51880765a8801100d6080301d900d00c014205202c2c0c0d0280c1d000e5070384940704400000791551700d40c0029405400048086800c0c1801020038082c80000340544100071090001900150307095640e07400030300080d03000c1c20340151444001d040250b0301c039410030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702363129 1250 702361879 702361897
    0x6210320191511250f060e0a0c0b040611011a010807050405130608010507020109150b030c031222050d020f040f0e010e0d0c0506040b1312030c1b0510020906 69
    0x4000050f88503c0089040e04043d401641c440b45000c02181c16059800c200d481e403590012030b243d406901c1d503450500400c141074040c12948100c0f120200003424611141010700f40420f02151558648200100074035141c80074030f40b803039040084021102e14001c0c2154152542400c1000302c60740c915904858034001c035407055030f006101710300e04e100d5000b103517000741d05440b41100203008594800f44164280d4002c08002407901c0361100360280e1600c1154043c41d174000e0024241d0350107012a5001a2900c120010785a03503100f03000594139030500101d0031a003960081900782e110b84c60318100018202045003100039018800c1354550f20416551607114240c1c6001d0081c0402c055100981c249000341003000820703101c1c0c450f840442ca11540602102d0b0f40702588580140788980c0c1e1556a05121140903200c81b402e19400044c400000b821440b9424440e011075900144905860f00010f280003540801246614605101314003c9031002c29910f90419001c0340c0541d4a002040c0031031100d120741684 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702364379 1250 702363129 702363131
    0x3130510090c060906030510140406080111030a1803050d0b060d1a030c01050c061803120115141213051606120e0606060304110103062103201915 64
    0x7807000c120010610609440d1107039610a55030340c48a4046c2d040314400da0b101c3d040380b06580c504000141115400c554062400740000c190305582c0c4042d1420740d40044501c000301d160100070403100e2115403103512841c0e03040514401c078142e641d4401a0161064201c0000342607201c0c190308071a074031008202d60f404034024500304001443d900c5c444010809642e013513840b0b4014010840305542c81a8103a9107080448006054161980c80301d0300c0d4400c0b2042000b5a1b5400248002c401d0341c40c07414440c0e4003c0103600380f00b080d441911000141243c203124500d207040301c0c1c10b00482c1840070fa00d0b101d165100c0a030541d0441e42c4041c41c1071a504d000702d500d29074170060649020104180b07600c001900e406401a00c010b0290b0325240b080e49445086c1100e4940c0c1001050001070301048100da01100c8070303c4107050006146444a200305000640c588c03031101e0200914102404040c2d02400369146000003a19000309001601c51282d205c1c03144268690b441da1f0401c1d030b8030040c4801907840c01181410f01c24 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702365629 1250 702364379 702364391
    0xf0f03090c0e07080f1b1806160c05060a050d0b210c0111120306130b0306070512070804050c060f04080f0115080c0f0d05031e0d06080a0803130510 65
    0x410901e80000458402d0005044c50f4013040c5070794020707280e15001d0440e22111204005051484094a800010084031007002c007044d100415101e05005000071741c1c80081881808882d07080490040542d680960b0241d041000048402c540c42000e6616016200314041049040d5500094802c1181401104081001d00110810034000108400c3c18503081e01c0d400c089001c40c0807000c1e01e80d20014130402ca0054200700140701441e0018640140304a0100001a0307580c402002c01e1034a4800c88109010800000d1951840c40c01101c0c40350703002249180c031001c0c41c601a0303252903c2e0500e140205000b060b000c904507542c21800c20594029000c200120303840f00349043c0c0124040c0840494080c500800b911010035464030210f8541c00f00f09020380882d00100d9514240403401c0c624040c00d40360307070209200c064100c0c0c1c0c07400c0400200700d100380040c940b071f01e20000d040c4048903200d80c8401c0c60365018000c1a40060440c0c81581c0e4030000c81002e0006440301424240c0c102540520300400883c030b080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702366879 1250 702365629 702365639
    0x1305010f020c070f08100c120207030e010e06070c030308071202120709050910120809120610050301090f0602071a07050705160b180316171006060f0f03090c 69
    0x50702a1405102c0001142c410700d94070a80001c90402e1805161402c0d0400c0301090b0391050f0a811a001d0320b006881c020440a1001c2000e60890b08201800c5002440c4568680d55540c0d000030210041081142c00c1071030301c0b4450340d401302a40040e00c4001c0500012030001112075001c7c1c00403030300c0e00e490710b0700965860180810403440034008070307007600114440d44c1000c219410400e107081e118414130703c1e0040c0035030b080c00d0741201c9560300d01c10708803280b550400c5400d155458088089208880341c2000b8181030800300c20380c0095002e9904000d001e43e24121121000c501c07a003900555141d04410016580c00d002d0920601640240c120b0300d0500c2d140200b88640646d100c0002d14050340280b0544444103501600712980310b600d44150668281d05210002449034046104540404001d0403a039503095450480c0020301d0301a80305440b099064010366015000611041d0180800003a040001c00c1c101140a815094402c03036040401048880388410140240c1c45032104507040b00d20703060a503542d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702368129 1250 702366879 702366881
    0x170a06051207030b070e01023c060612011806020702060c01020301170c010e010827010f02130504150b0310030b04150b040e07152d0206010b0a0c0b1305010f 69
    0x52204a44521328000050301c0c1c40c3c1700b00d4213581c0e0280305034060700302801140d50980c200c12802c0c41d4000107903010b0021000d1011108105d01035404804040c00c80752600204002c68031b520b110884e54240d04101040d030b04410806507007c200c96104c540103841da0380a00114085000d4540f40031000c0d88004004101000c03056034a4021900180844410925640045482c1d03400c03210f07080e021541032404540302c2c4000c0e240c003440c4034a03502c1c0f5081540e00001c61850950b8145070036641080d600042c0911030012024000b805444141c1e030a000500301c8800000d050152889902c203501c0c0d0110124280406004c00c8034000c5801a8258900341000e041c11107003e440078800140003450410012201c2c02c15003d49554120a035000c0c4c50360318903001342c00380e004049410400811403592003a011501070100030520540c0c03800245590380c0a2402c0103840c000040c2c0200c0c2d0081000c0c404404800e60040c0d050746c5072a4003419514140c2c4803101e2186108240f801c004001d5401c1100d124050401d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702369379 1250 702368129 702368143
    0x2b0c050903101103070e060c060103060b01091a1e0d05010b18090402011218050a0b06091b16021219050d0306080a0b100b0403050106150f170a060512 66
    0x100301e00342c596642c02401110304442003034001d55443e036424400a20302d140119100000900090540751800c101d0300130150511009030011a1110303a5203603000c4035940d0240859025150b00c0500846c0002c4a0404041c5400f500c1c000d4400e440c01102210f5446098006841c5030740f05d038500501a039615a083c000c5a9004101c018500c000c40890b8003c540c5400c0247d14011038042c0c40d10758010021210900203880001004060714082242c3c45000076130030080894480e009a05011a60070200304001201d01c010389414408207007421850400e004040885003501c1d040c10b0b01e080000001c0c808200d0904e0303d091800954000c1e00d40b0241030b6001002124512031144040d01ea015103100e1080d8111041c40c0a242026840340c030141c800114418049600680a601803441050b84d40c5036901e21a44a504111440d94481404101d00500704925140e00855414090b40c6038140100042c40d86031061015152840003030082050401c55500182c00780002400100e0800c0c1d00901040e40c40a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702370629 1250 702369379 702369397
    0x813060806010c12180513091e021021020a030b10050313060f091416080a0f0b07030b040e0d140403031704050304120b04031b03052b0c05 61
    0x801880003074402c1d803080003481c1c2041c4c0d2243c0c0781d40603040941030868807060425098041c0412072280810541d9802c0350f100344e482640034000c0781d584011310b40000b10b00030711035032817821251200303005d40141e07036414101061030420715004000703021010740d18103100c9500b5894198288000784407202c04e541600503c00c0c0740e13015905803a10300102c0000f228284411540a842a9501c00d816800503059030040c40505082100105038a0142e4442c0c400c6a0b010608401c2d4907484448415000204412048000c0810340e0203003d0b482440e07260071100754110306004008031070342c2c800203075010700991100c044004064030802220380040c03116603a501c44025030a0120300d4071540344078440c90200846080d00d505594812120720191342603046038502a000704c859010030b00c0045030040700d10400004690162080715000c0c01c00b420050840645001e01c5406810b003030701d60a0109400804540c01c00b00d008004081704022625605480000340030784405150400b008650b42c69440b90280440f40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702371879 1250 702370629 702370637
    0x3040e0a02090a12140f060604020d1407170f01030b0403080603101104051203041a0c0708010f061401030509150702240901110304050a020f06041e060905120721081306 74
    0x4048413200d40d9481091b40b8880a80354881800250306003816005440380014042d004284481c0e003003410481201c04a0b844130000703007241003201c02c0f040609001a0032001462000e0501c0d415a19004110300000300050284102a002720340c4540301001113a81c000c00049082008152864110b55150300522030a07124002c801034010b421040802240c2c200c0d81085100d40c00107641410080c40707908500b2a4004030f004e503800000d1100000c0c01070020484115000003401810403000c0b040b15030020f404641050300c0c1800b044549072000a480b20807030012084c20789150b80711b0b08103d00d802d0b11010007000000c01c80115031411710403500018010201c600080c005400d5a070104400360000f160060b001e5400200110b01505100d008898441000380c5068607082d25a8400765001540c016a0310106a10b030200300000c40c0e0240e450000f9020480c0c0c1031409070030201c8141e42d28419405107180820f0761489480300419205080c810329948184056200d010442100030500860711602002c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702373129 1250 702371879 702371903
    0xc020102010b0612040f1722060c05100e010216060e0c030c0913080d1a03070e0105153106090602070317030712020408101d03040e0a02090a12 63
    0xa00c2d100c01982c1040044600c42c84e0385541d0f9881d240c900016140f41560a0b040c2e28248a0190101300000e08182e19228028440030f4500c01c0c0c079220400840d80080c0070441200180320001d13002084c9042d84109844021a900d0030501c1041c0c0284114402c007842d6003c03841c0c40000b0001c0c19001210051400015507621042c0701c0c090540716201c03050220390080030200021000b8650411808210380981e21103810041004048400ca03600f14841c07100c50880036081c51081c0c6020031081000d4001020280c04552518001c1303802c91007451025452442c0200d50f20721104190260720b6101002c02c0821a281601400481010140b0380039010004180c8800807800303900014001c0100ca6124800c03560a05454282100c2504083c0c42d600070400d00e18001c8146c22b1960002d40040c180e0366000d0300c5a03143d8112448122510443c0030030300d0043c1050446599603000c01a10211030340c94851074499a11000420000e2003840d0b10103030310091144000c1024091080c02c501028440c07882c501107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702374379 1250 702373129 702373151
    0x80d03110306030d050a09050d0308061e0a0501050d0f0626060411090601032c0712050c0f010c0b01031b05060304022d040609020a0207050d05030d1e0c0c02010201 72
    0x1a844100c2d00543c040d88449a02c4407114424001040d030360f869440c01c0c8040ea91280001682e8000303519003500094a00c1c000e20900d407804034084001d0002c5500c21511544080011034a560600d10a6506004002ca002c90500b2500d4000d24194600314408100e00d0340c0b180d0282009103214070151002000f0b000609402e44800108503001ba0780010315010080c40d80b101b0445030751001071913a810561100c48020700d50103000000f1181c0d02d041c62070510310b1950106041e00d00b06540c0c6c00203006c00e842141540c00f1441c042042e408003601a80d01054080030840140c880041840000b862040c070700c000013080c042a0141742d18404111003030102031300e5858080210b1400240c5029620000c044005040c066040b00128070030400340c2d5500107007445400000707040781d02e19402088101e40000346409802d5042c01711001504048030441031103003454640682d00d02505143c40d00d9580d940e103d400943c01c0d006001000071910f10001d222451721001c000b440002d007042e049003d5800c040e45099 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702375629 1250 702374379 702374411
    0xa02030a0c1403010306050c0d0504050d180b0d020a030b19060201050703020702220608010905031806070c0918080c010c0f081501360e09072d0f080d03 67
    0x101c51100490541564210b1b100d85008140c06040070500b0b0104000710400c1d0841401001d200e18007e001401080700402d402130304001d0301160500400002c09424000311520300281e40089400400040c2c4070030720200241d0003412070000035a401164204d0903407240c000041600c09483c40c6900a110940707660f0402e45c00e0740030f54031b402940700702040e1100700c503e4084403404920f901884c03004504555a2201c10f400c4886003401a1b03996080060701c2155031620a94100c0400b80560346903190000d00d8035421610002c0d070291a2a0b41d480c0c0344a05182e0140c02880c64005800150303480e0784ea551544268000e207464000200802c0301d4541c00818035024a07000b51242c0d2a80c2c81ca0141da111070401100e00707a801a101421410107080d510001c0305510500c040b000403642104030056007800c8a41500120040958000342d00050003404070703110307044040007034000488046403030b41a00d004c0300100500716004454404a41c01002448001c00118250b002d44140c408002c1d10031401410382c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702376879 1250 702375629 702375647
    0xf06170f01052e03020d20070b1b030109060e0a0b010f051e0f0c0f0a050a1103030d2a110d0e18010e070813050705060d090503030a02030a0c 62
    0x90030402011004110030f00f01200ba42050480d010004201d0380c0c1c08610030662165180f803032900095000c0f030400d03808044c902c40c3c0d6040284080a01000344103d5204002506c50024014002e030a0000856900f02c01d00c64504c0061a100030320940360342e1240c1c881001840c003031080c900404051404611302e600d880c0324046c0c1400040e076a160307400c02501810380351a40880300400c2152014030460901090031800b60003102880c0c07014582e0703010035580092034100e595464071920b0304015901c100007040050080300307450f0b00c42c940001c03030221200001c0c00c0d8040e188012a410342004500007210101000407800841074200241e94407400700405c8819071014001340500c0d0b4001d88002c600103014004c2000760410040805118225188000c00001400ea004640c03464060040c0445103400c420081d0744480001c02100c8415815181e003a65400700e40300380d9001f030a0004401a90041c60b8010f20300c140d4201e02201e03528102101440000d600482e040303001e040ca00f41d0f070100b10503c110444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702378129 1250 702376879 702376891
    0x20d080609090c01180509160f1b110a0b030f0f0c0702010801091109100c020f0108040f060b120102041d10150503131202010902040e010501050105040909020d0203070f0617 76
    0x140800c05443c40150358402401c45800300100504a0005140e40d40c00c00c554400d0200c000d10718200001ca48002c1d0202408000361001d006a10301c094030448483e14810080e02c1c4c1006001481248600c041501180b158010b038002c62000020807a4403100c0600301406400c1c036429441c807030b640304507054645009000c0024009541d11004003c03419a40c0c10468403030071550b041503d80700c400000150074028202e442408541eaa056031019890b04040c40b540091080c00c01c003200385003594489102503018603008020a50b1102540750549685415000000091000710350320f6894407001d580055904444141d42d101c80300004040007107444490007211164028520700101d61034040e50150802086072802602100c00000840c4808150600c4107103140c00000b50558140140001e0b00c02070345000c0382980c104001000706991050071581110b884002c00181e0030740a10000c3c0c80002d007624080c0d4140304000020682c16010001003040b00c841c4d484440b42002d1030500660038040450f08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702379379 1250 702378129 702378133
    0xd02031606060b0a020a0c091e0203040317010f080f0109440301090b03011413060605030616120606020604120c0c09020a020f0c060405010315090c020d08060909 71
    0xc5a4000c0c0449888012010310900700819210303203412440c40260020444c450050380310402c00300a01c090301038060b004e004000c0e42404460002c010005c130142800ba401c04200380c1c008001410306101d82100d103070700621030380046030a507560700e505543c00c2102c0c02044d80754025649d1401c0c03804014862011600d40c080807064a420080b120b000200344071007500881c01c020302081500c141c0e0b04214606e4407403442120a07840794104140b01b02221000c410b41c5000e0780c0f405d6035a030008440c0b00083d5a1040c0010242c00704001c4a03d0601c0180c201d0741d20098043c03050400b0300a07001e0907001800c103d080e541d84d0703d003101d00f0000007071010780314107224910141e0844000308020421580314520030080d1401c000240c034480d59100481a2020760094201950100b04140c05940c103102607140e181c81c803402404220780700390025129100c0e52061506160b65400a812000b01400020000f85042582002003000036140a500d420384207929100040350b040006a6600e001403c0302d01412850300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702380629 1250 702379379 702379387
    0x2090901030602070f060f02030703180b0a0e0c1809190c12060209060a03050108061303020c060c0f06100302090a0603030503071d041e110a080403030b06040306140610020d0203 78
    0x10b900e4000d500592065480e400079120010110f8401d0040d200001089100140c0d20320b41a9001801c6505e1401c8a42007440f03845007081c04a28201d0086401a00d0800001120704c00e4501c0359113002c0040e42c07e03e404c01d8113000d020414901d0140050300c0350003020261001ca071524483c00d9140203504a0080504208070810b108540c404101800401e11801c0010301d0440b00c4400207029800030464a80000e80304c0b401484854000c4c0161504503e00e401c803a00c401d80260f4000c0d45070401c0c01246c600520340480c0070b00c040502003101107200b10303c903002c3d644030741450004036100f01c419010590080b04988082050400a8403801e41100d8240d035406007940c032111421034806611a901c0808043c003605a03092541d228807031001c0903180c00c1c03020040120a00103000940c1c00c2045010702c03141080c868407500f50f402200d26a881075042c50005080c030311380000658140600d810107401c0910300b800000300000c01c22002d0303019280840e80c0184000029008996800d2200c84800c0141c00c180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702381879 1250 702380629 702380633
    0x3190513060504050705061b010609150e0910090311010c05040e0c0703030b030610050f030a020a0e09101a030f070f091a090a0506010f020a020906121c030b03010b040209090103 78
    0x342c403103a0054812001e807100b5a55a03800107400f90080b0703543d26044001201d01d00381220003403280000400c0704500c14002001e03c01082d100e202090710130384203468140d100190410009121031035102121603020020f03540c26040c0108800b88180310350f806503280000c605102c81c005d405039000c84607803406400169540c400280000d03045031f0003c40905844400c400c0c042c2d1b40c103001281c8a45d00c18281d400b40680f418081140c8401c200302000c0c0650040040100035840781c4100e1003d4907003827480b003003068032612040da240c80042c500701c180c218948065a00c100f10058000442c8840880865503480e02840001ea12005e40c0c0c81426414030307101104018094050b080a4220340100c00d51200500010020819451080fa030144030603603a001001625a0003047e4422410740c1480101030321403050b0b02281c151034010385202d2154182c1010720809c1d010402c00c10baa221900200a0900e01481c07001501070490320841511035401c0c04000d00c00c81c1444d100740c8200500003418070040f40d01e19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702383129 1250 702381879 702381881
    0x209090c190f1b08030a060e0402060723030a0f0e040e210c060f07090f081504151a0109080f030304020402090105120103110406230f0103060503120319051306 70
    0x803540301020310002c24802d4400c0203221083c2c102460003007500d640c2d2443c00d404400308540340b98000e804000980410b000150311080155807007140d005070812154281881e03600e9044055100180c070138130000a015450942c170110f10308098200c0c0e250450110f0500d81048103a5007020400304a960051800005000028414051451105180900e0640490a6141804403c64060031042000d00a2002c1c076035102c5081c00080c0340c140424840241040da1803921540a19500400580e0120118050007a1080390200034400e07200301b088842c49001d440b95407004030b8000d0303034045014041d002035901401f00e00b0181000600d4080c624550301daa0030040203400c100c40c0e02d81042028804e0788003926034007107200d006e1402550324004284a02c800c00003941c0d02504100060440c080301d4800054400c1e003a2049420300315840e0340c1032049100100c0040505920007503240c401c90002602c5c0d0b144081c0110b0140c91074018103140060064155419140150791450700c998105a20001003412 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702384379 1250 702383129 702383147
    0xc0813021005160b10080304030b070e010e0d0303051501110705060c0f0601060c1e03080402010503090a0b01060c03020f19121b0c060e031b0f010e03100209090c19 72
    0x160a020f0b043c0030a00211880c0a4600b481c100d5141c3c80ca02d081c401c5080d26044400300420015008510b0a81560f0300d03182c54030343c00f5059000344500a02c054620768007603084100c034030001520811200d07001e0300f001006440c041c0c4140f10360800585149201e544540440d0010101d01801081e900d0325240c2809841d038407003001c10000380035081c0743c1c003030306501489070741d000701410390340d0390001d180d242030062006040041100c8a40c0b150a00304d000242c0020304658002d8090804d2502d80e61550b40c41810030802c6c03c0c000b000b55403c80004035000c0d411038861030390329001e07030b00f1544800101d103d541e582e000b121500b1001c4100c094a80000103444200c803e180020600c0c2c142c00707100069840602c8000c5003c03044a503080a50014840903034891070030000303803004a00809441003041004800321540039094ad0040941c1b0725070503c03a034001d41b02000c40e0303030380602280c4902690016400081d04a07c3c152031003020540d0110f0748264103601a03c07030030f9920200d08101c0190094060381e82d044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702385629 1250 702384379 702384409
    0x30c0702130c0809070906150c02060910030203180303040519020303071202070603050c09010c060b04020c0a060603141203070305071704060905120c03070b0603120408010f0c081302 80
    0x195031025501c800594068111840c080b40c42e400007508007802280e040c4035143d045024003902e00241000400f840d5882200c0d0090a400e02d0611000c40b170000c0740e914413400d544980c201d16140003800e021503040c0d004520850301d0200da410001e240401e0b180e120b10050300c0c080c100364880041070141d048409940b48500344002c040740d2521425a81d55150604c4503024000507810100cc2041069058001c003039000c20307030315441d030324003041e0100181481d03e21690141009547c1d01400c149030308c0300ea046500316a030382e00c21540701c845186013140140c8030324081140c0111182d1490741001c0300c0002c41c100c1c514442d02c400c60440d03481e80412001031000070003440401902082804450340f400c03c269000754001d04000c50303240c855040141c640094016481c0740780c2420000e62541a901105407000b42c0d6020010010f6600c80d803000034a803000080e041d8100d03800010313001580d0b05056000d00c01e5032504200030300031085098004d483e4410112070302540c1160460725100103107844100248040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702386879 1250 702385629 702385639
    0x70f060c05070b280b013e010218040b18090f1509070b0703090608041a1e06030f030d021c18060e0115150908060c0405030f0c180901110f040509060f06030c0702 71
    0x989101f07803886042148006101c642c1d60004820111103004501c05040c0042650184407150340c80020901030340914038190a000b1414021400c0c41205001d8881e1090f9840112040e6198903407a09041030000d603130002c10303423051801c00101c1100500548076000e0b016242e50481d149040380945a8480051040350100e40c0c5c411031001d000f400c0310509000309410900711081c52640110103c5840001d411070744070b60310000980c0c00100f8004111000030a02d40c0c4003580b04c170800101c1401e0021075514986601d824490072000354003004030480c03042c42c09100c3c113010720718080e40d8041c02c03034a00360700380d82c05a62410030034058481d2560b4401075504613443d00494042d5504840d40c180342c415178801c0c04420000408000c6031800300821102d98207080c000d0010380116000189002d6020b05d03000506096000000314128000e5000840d224500101aa074450070413403c440701d40e1190042520580700540401d0440c01c0031440d003908250302418440c0b65403034038104501c407034000300012070b840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702388129 1250 702386879 702386957
    0x150e07201216062d020d1803081902030f2715090c090f0403030c090e040303091203020c0a0222091208010b070f060c05070b280b01 58
    0x10303038440090006010003901c8101c0c0218900d8484180c5114550001c0c02c882a0b00c218015066014018422452038a1300180d494540354103d0000d00080000c0c46191800700d87c1c51410315401c80480f078400d04400900345800c100d00c0840104900040e50b0900c2810b80c074000041d280c0c000c551441c3e04003c640c1c1a04003840805d40006450a1612009500e16007611001c3c03200e0000700300207441e400e10080781c10780c00500d8801600c1860940050002e07040680351105020380720b0044106401078403250302440722600c1c240c20301031b016001340281110341c01381306820f068003036100b403095030900c0340c0100103003240d60426001c01240402602c0713071260406107a46010302100c00d034424101118400c542110601944c09070151441c40168041c501e00e2000f0403068002611204110599640c08a00040e440c0000703c411581c50040c001c0003004441110180002420300d14240f0803007510300e0700c1c6246981c944000110a030740041035030030b0200d21204c000290203990000c001c7e103048000d036603005030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702389379 1250 702388129 702388153
    0xe0609040309170c1207230d02030d0c030f090510030903020c10020c040507020606061e0f0304080c010c02030f040b032e060801050d1e2103150e0720 66
    0x70702c0b090011400b43c02d500c0070310388841c00e040101d840310b00610301030f024100f500e00e0801003c80a40b42c01d030380c02210016140b0140d00d240e860240c900441034014040383c0000c81d141c0c101801d031500c1050151301044040101d5000740707203d4490b000030f80d90043c042d02040d440076102a0301502c0501d0703089081d4000c08070144800e07240d158a540488681e82d00904400f4200814881212800b42c00007045402c16400c2124685445081b10030314202c411440401c140445803219a5028010580c030b1040800014403003885a03c1001d40943c4180708000c00c1501d524290580c0d8030310909104070074410b0281b000700b002032581c00246502080c84040316203c0e0480d41d91210001000e2110107003800c682190031b10410b86d20003625809440281d800e0742440ca40307501c599045000300c101d400e842135031410400080080090640d44400b103d0f40701c0a4140404103030290140044856001d109042400001144034894003000c1c024511900d50300010070716070010607102108485441c103107104005442003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702390629 1250 702389379 702389399
    0x209101115070f120e060c130905070e030c0906031c180602010203090609010c050f0306040b0a0b0a020114060603010e1e04060c320307030e070b030402030c0102070e0609040309 78
    0x4070600040c0c2e24007848403d2100d010341100c50318485518101c0c41d012420034240030004407560048503400c640ca0f00c580c0b120b050300c0210095600000c484034106014031045581058044441000403800e81d1030b41080c00c0140551507104544d0315903d9030200140b41e81e503d000c1b1034a000300800c0c910740200000050754207143c00383d107164420710050b940003080203210103040c40a260000e441388004e02c80d540901200400300c1c010300050050310000003000c210207030744070781c031011307508001500140d900755a80c0c18413041500a8959a0095400c0800e0b001c000c04400e08043d02c100001407030745041d43d00300ba070030307041a507002022102102d07040c508040e521b40c0417a85482c4903900c514004500e0300c005180003000a2041960107c40d4443c02c03c07007900081d462820450020b2050703101d1a00c075910350604401038000090b040c8094020b400001c501c460884005512aa00a404450141010100491340c0d04420701c0f5400c0c240c1e1580002c40d0381c0c0c0c43c0c6280c40540050203403601500040d00c4d441a01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702391879 1250 702390629 702390631
    0x90c120f03030115021e1c050c060702210405010801030f0602091801050301060e0c07150b1915090e0705070f20030c04061809151b030608010209101115 67
    0x3000203000c13241c5081038550411410b4070520844440280c104008004a940c8201410840c800d86c1c02100348085c1b49485141514440c040c90780c119501814400c030080e48440b076001c005070100c0c0ba443c6030000b880d20713000100d400b182c0d8180e60303d8107168a543c4038080780300801d9000711181502008a240655946006000760500d031aa0b21080395140504050843d1020340c0311a10b42840c0d10108100890314200703403080e0700e03044001e0400302e140151506004040889030700b45d20442d040c43d180c0003101c2c5e074600907081c1c646015162803080142c6001740c0e078080c0b90788100c840e880303d0000001d545511680151800310b1161781900030035102c0f036654611b500304510304ca03905003840c1c01c110780c0b03145001c01c1214601c101c10303a0100902410003108140110204908220664998002c0d03020000c250f07441c2c01c000d0002020400c4501501c5207880074220a0a180100090a024021900701018800c50754910320041c46500b00050a0000341e80d912048120a4401d01442400d01c41c49018031082c0d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702393129 1250 702391879 702391889
    0x207060b060714061e06121f060303090905010b0901050703020a290a151e030506071107170d0c0303090b04031e02070f0b090a0803040e011706090c120f030301 70
    0x140f1616036041c95854070340742d0000d1004401012a0f411707401004048820542c100c041919180494080100160302c0c000d210443c0f82d03aa08204024581c80060550241094031b200f80e030340c1141c0075540c0c500c800941d40203000c0c0500301d64041050384100d40c010801096030904c45d0040d508140666140e401282c0d448501000045445c02046022a06c54452147c2d1203280102c0070000c80b14010b001c81d4001e4000c0c01080303a1000a4402940786071902c0c1d002ca001107602c0021503c681c41d008034010486403c2c8910030555102d021008100d905100309800c4481e03400310b00070f1540c2e0300c10107001c0f00c0d20101560250207169640700300d480411303403802c411480350303020b9282c1d100300c0c50394141440800d02c0685000c0d03045411826040c0090022070b54490201da5901c40c420b615000b4500004003c7c8101d9803050580b4400050002403544850f94031504070b45c007280402480c010828070140c0c4900088640d050b0300d801a00c259086071600410001a12440c041282c1880100e8500340746580d0003a048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702394379 1250 702393129 702393143
    0x20c070b0d1d1902040e03041a0901020c0d0b04060b0f0315010312110601090e010b0a030b0601080c0a1e02011d060f131e02061e0304031206180207060b0607 69
    0x1071100d03012070b5104400c119070725802400682e40190460904142000c8000d100e02d031202d61007200004100141c0300603141e1040004030400481e010b126003984200d4059015000b900002021840c01d0610311415030b401514484407599039a40c4c140007051511350040d4007100050070080c5548042086441003140c010000c1c1d15941182059210000b48000b50700070807900034180c0c81000b102041c114111031850102295000c064880c1c180900400701c809504041180070000134400155051400740900b03032209006a20340290400007840341c04400d902040100180849400b26441000ca02214600c00010075103200d98603148d001944c540346106950100b418048030010080503d038200344c01603050a001c401564a11f41e52602c080640e0a42d0400448450295200c41c0c048803260041c04130740009000320410031080a40007918180c000441c1c2000030207040e0802e124000696480e114580401c082c0f205003180654808a41211410340f02c6118030141d850389801740c04040e200e050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702395629 1250 702394379 702394391
    0xa060312030c020601080d020d110111030408041406090a050f03070b030c0a02070f0602211303080403060f051b0d0e070f05030d1d0405042405190b060a03020c070b0d 73
    0x800901d81001070700710703112a81180440011f841e4002940d41c06c03030205401c5c09802d041d588080d49006110f0408403134190040001000100860b00740180b0030350f03101c2604420345a40e0101030210502404181c240c0066044e082449145400c000103480b00c0c0c0c008049981c62030300c2c1c2d4480740c9260016034126841e120b020403080c84054050040d03402401180d401e0401e030354030300348001b0755420f401d10424400780c20101c80c9070080e519100441b00340ca181c2d0504072582680e03a20300301002d644180700944400d1b01d00100c18103000e26031b0056500a022000c0714454542c05124890840d922806160b450b0550f594803007043c0707000c00c0c40840e0080000703440f45448a440c000c01d05041000f03003200c0270100449904101e410400c00e01c000d80b440307001500d001990703684a18090912081051043c00b1030408a0220141e000a90308010f101d0702d0728400060038180b45401000075905c0404281d13501503414801081840d00c00d601804442040070700703d80c08980d50f4501c2c0303101907000d85070740c400381c644800b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702396879 1250 702395629 702395651
    0xe0105100506030c04060f090f0b090f06120a1d06010f0e0f07020d2f0a0611072402040e09030304170f070611190c050d0302120f0a06031203 62
    0x10350128001c08041d16682c0c51442d12410402d01ea11850140000780000002c8414480e0b102d041c424014140c0080c1900da520f80310311065a69803c803256481c07040b04010400b0394981001000e44040001c82d83e8030000507145c3c0842e030030141c88c0f2690131002c041880726000508402c100701e07180c000c0202003140c9009034207080c0c04101c5424000d0001c01184c0855081c40881540007400303004c001d2240c41c14882001c1e0140c01c1c498222807881e06460110b0801136110404800850b0f03000366103110b400d040006441d05642d440d41801084000703420300c0c000d10009100c0315810380c0060600e024410006107000d4589030115540c00c5c05568001a84c4e20100c100000c206003400304170703031128280c03512904002c0c0280044509125004000b800c4a8541c030307000c020242c02c001a81c00094241500144c2d110a00100600c220b04a541c10b403400d102e0a048540300c940248200c1c0d45100c00c00484012558918640303404240018280c101d8440d030780c0b200040421041c41040040c00303495500464444a8a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702398129 1250 702396879 702396901
    0x120e030d0f0f050601112802060c030d0608010c210f1b0f0e0906012033040c060c0804050603071e110303011e080303090a0201110106060507020d060b03010e0105 71
    0x208405c1c1401807040e10755050804c0040e0540d00b6001076004281d0359000713140c104024001060340290081e0000c69030488500000c4094805079040030b80c1001500d907141015800e88080c2034207880031071440402c840b50620800305860342c01841d16008146900c00c0400c0c0c404680711001c04042c400d440e01e40c00140940d20044190621560b40b41041c1d81416010018a4810014102a0621410f0100a05210045081e0128441e0810143c540015030700804a00f0074154001841601c8045501000407195066205000e181c020f4000d40201e030800c0c5054070300009081094070422028440090b865a0381030003503109219982e80c8034503428200080344100c00420382c030321091103041106184038280006c1542d0442d49070701414035802c00517944160416240d60805001da01001041002e0114002424000c10340700303170b803290b1090304480186402c0b500e8034000c40c00020010800d6001624128109445490040d500044c102c80c1c01c100080c21203106294840441e511a801c1100c140e1103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702399379 1250 702398129 702398131
    0xe15010c020310150906180c020c090405010b0307170d030c090f1805061c060b01200c0108010b040e010603091403120103050712080708250503041410120e030d0f0f05 73
    0x280481030003054101969104400c424451f4100303840e50725802c900340f2910800c40011000d1014040c2d10030b82c2418200315004c1c240c500e005502a12a01d0340016180c00d0182c184440a440f01000c0c000014500900302e01421088450b0000c00c007400201007103028092420b0f10003846640e41d0100316403103540e01541620001004148513202d411101070004464240101440b98070200c0082c44c00d401a00599100d4258860001c0800c1036561529004400040d120280e09090701c0c0c2c0c1185a9035012200c0e80b034810b9000340c8c2115182c0340010404036010b034200e841d41c0c1e44501c02c12001c541040100300d280d5003090400d1070001a2100040060040038408400070b843e2006050740c1c164865150b11016202d400b000030040c0c2800540400c4808000e9400c2c00030380d19106007038050212600b041a60783d0090300481c00541000301c240ca025180c90000300d0f106210503102d00c0c45040c540c044038401002081ca0301502d80c001001040ca40300c11905c61003042e11034001c00001c107a041d12000740d0840300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702400629 1250 702399379 702399389
    0xf1e0a0222050604020c0a0f030908100f14090d080702101803121a0f0f09010e100e15190504050108070306110304020d2004020708041706010e15010c02031015 70
    0x210401c6142401d000114000800a070024524186da81231f0345030071035102c83c00e58001e00013405056a251414000b58000010f0718028800a001c0c050100001421440003954549920340c40900b000002600881d0019440549401921020a00c2c60944010b5542c3d403c0340981485121480d01c0406400800f602c0b601070040d00c00701328002d05860100e41c152440b00d42140300e0140445400c4803035a03403200446c1d5000025088402c5540d441ca509041d244c01501e03514a8101420b101140286000d03c03101e1080c1079a5000740f82c0d58251500b401101c1006054010450161800c01700c1c023600c03540121b0f40200f800400400000385141012411950001d00410b002c07481003090001582d2410903841b1210307040401c000d03424945005903a044018040025081800402d01500f0b05c6611302c09030040b41c4c21382d03101d0301d091a40022030548440d02400780c601501d04050104003a11910500002e5072441810003a12100103500000e00d4915403d500050107900c03554684550840810b6500c003c03c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702401879 1250 702400629 702400631
    0xf1115010314010c080a020f160b01170d02030405040f02090d0b07030c0201110405060a260f060d0b040305130f09060321020318041805010c030c020f1e0a0222050604 73
    0x41c0b13101002020319001800740440d16801040d101110761000040b14107c0c1c20100d102d06600107946000307149130b0424419007040300c01c1c0501c011007026011408092000340780e4059417600303080104004c010f02130140032a44840c0c0c04d000b0920035468001e011304105010b01070b0381c041407401001c0101a101e029408a045904001080c2100010700c4190740640d075003200c0341c50300e541d104c1008480c4410200d0055178007500205008001c0c800041c0c0e511700883c4101c0b801500d540d01c031030500c0408004100001c100340b6038480024086403046000e0100c01c94002c100c02a6103541c0c0210f090480003580001040c1070b6144802c00400003900394400188600362599400041c07840ea020b0340760301450920000d1041c00c0781c80f070840c0f5955580b0048440385c50480d0116484002d003070440c000d0501d200042c01191501014403549400028000c40b4139000300020480c2c4049640540c222071840c01040800e8032030001610010b131786100c01ea18081c2c04100d05034a048840007403040030740d04060b00140c02a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702403129 1250 702401879 702401891
    0xc020f0105040302180703091b060905040e061911040305010e06070309051005040515040f0501051f23031207050c0a050120120f0c0c0f0d030f111501031401 69
    0x5803075102030105e1002c500004c50080c1d588002d001c1d00940b6500301c3c01050950306640c02da2110411184603001e88103141d8030f401125441c1c40501048807480038008000e640508002680f580c1e40106034088014000e40120310701030022107070071072a0495002128140d4440c1000c034000002004800d1380a9414070f8244103041d8a034950715200c40c0002c00b005803441c2c03035038001014020100724404910007003400440043c03410b0300b000001000741d070741c1c04c55181d400c080106600441036075083d0300d0400c14207000d401f0b5900c1d220212504010a1416503d070a0f1902000d00c0340741c0e0280b105e01c5400344090600c6694228a280450404800b40720362031044003108030901c09a42d02075180800c00d88400301c418200550401c02a01d440c0f502c0010f4040c14900148001c4030310031440150404d51701140484078030040440030801615100342219821511188541010078460032802308040c0d0103060800d800c00c0c09801981c1495007641d0721120444d4500010000c00000a903102a0f101d0110020004d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702404379 1250 702403129 702403133
    0x31501020a0510060e0f0c0919030c06260f06060a0c08280915050c010b12070617150121051006090b030708070e13020423060f1210030506070c020f01050403 69
    0x28038048c44c82d00714000e29450007a204194003000320304000e10341100d01d5499645c0e036604000d2906402c0c1580b42020561903905400c170341141c000843c001c550324000e04017513036180414425107800c58030000b0200031040142401188140c8001c01801068680d1680c0a0103c050000980c801411100c410032030006810440f89402d1940344841e0701c0b01e0301c0c0c0740d5680c045842860f400360240b07454280c0e201c501503428441d4404c0c005101421520240c54400800031900d1032141c0700c40084402d88514200900c1070b024540c07092071208510102620f15220100302d421800e022074030125200e640307031b00901405001554001e5030400040440b140a180382d407400c81d100510394000600b0700414401c29071946000c42d503030304815511900218074115155651071001c021005191410641d1102c40c24110303a403981024000c03a088503001c90f001c83c0c646413600d4281e0110803401442c0000d6075001d030602200298007400801d004161950b18075014660b107004203c8404464490941440f03010441000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702405629 1250 702404379 702404401
    0x190809010c060615020c010207060201180803040c0e01030620070807060506030705060a0e09060a0608150301090609031e0306050d030c1a04050a1214031501020a0510060e0f 76
    0x90480001c0c80c20200342a29440c080c1c1c0a044150065090304103890141050a40c0c002518080c2e00300036801c403903105030750b5003050b4202e40410902143c0d0078084000318001c21281c030700958002d88a20316030802d4a039901c16031200c025080e0000c65450f03880c0c0c0124074540d04201540310b041c040030044d55190511f17603070700c18805102d000001010350b91070b500040e24070f58003806040000c29020b010b1503a034618031070300208950307415084244038501b1003001c030b00d00f8203113176001c003080d00c11380c0c2c032203e85035180c440c4068180c1c00070180325603240d900ea00500c000510310f4040c4001086c0309481c1c0800d400f01c2801181118160b44855104240c0b070041c0070000c0d55030b232351003440c0c240c0e0301420819890000e90511045d81802040b401c005001900140010000d00044483d1454011503008205082140342181d0748520020018101e070340600108600b440005200d65981c4014011140e07034858070303550181821000542c0b542510f175611010409101c0c548221980110b0410503400340c0d20309186800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702406879 1250 702405629 702405637
    0x70207180b1f0909110c011811011808030708190206160311250b010e09030702040e03131e050105160b0712090609140d0c02090903130e06031908 64
    0x140407000552410b00902d0b018102c5400540a918401d02c19070103c105c020f0860b42c00252401000d40c6464050007810060002e29617a06903c005901c0e0203031112401140c0c0342084c10410307403e1364400d80000404801c1000140a00c62240e404140c407450390305171860031802d400d0080ca007990410b6081041c50803105280c15041400c1e0b041c00190040104440c45e240c0c06481030340316070b0440d8000c4455894491440902c100d0f803103201004e02c00c3e0307200d559003a2030070f106690b910082d90050004100515064120006034240181200d040c07007c460280c0202c1500c680c040b041d43e01004c0c4084d10210070440821000e000301307080a6207020603001c2c002c01c030b540c15039802410941c21500032410381072060048d24080c00809105020035522803c1200003811460400c988110540640c1d12064401260002c82c41100e91200507120400750240034401c000204900740c1400704008400200c0f14054030200906290000c11916180c501d082c10b20308442c1007248607240d46d40c0150070f0000742c020412a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702408129 1250 702406879 702406909
    0x5011205060c1b011a0a06090b2b02030406050a0509160e1506040303080106031503210519080105030c042a02150a050402130204080703020f030a0b070207180b 70
    0x70301da81e000b5107001c8583c01c0301000c03c3c40c0c24650130220501a80d508112500c40c10001c101c5660040c01c1d03450b01c0039a06d64855200d001c00d0150280300c1c02c1d0141d50f884050804030030000d40c0d440c4c251801a15140200c3e8400c45017141d100d5039440600501052500c1041c2c0d1040c0e40c00000d00c001c00c5a0605903001284c00e00c1001382d0a400300001403140b8901210500342e13408058100c0742c90300c1d02c130f140c0505084024011180064908128160b0030750072100f185007107913080300c050280801f1840d0408a081c4008240300280306041110005842d40c03070541e51500b074070301d5403200b641d5410a02010305008650700558429410084100440120610b2a25048800100101120703d18000030307400c041003400d20040310100001004584c0c4c1c07490700f01da88103030302c01c490510158000788049000c90140d40510f0007950f000580074001400c220000380c2c0e07140030090807201c817160260b1791030585100c11207201d001a00a20401c0080d00039160715440000601002800203602440108065107210390003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702409379 1250 702408129 702408151
    0xe19020607050f120307020c15251b05041d0606011d040507050a1116060c06090804080d1101090f0b06060d0e0102130801110f0c03190309060501120506 67
    0x481c4007006810031801c07018081180075510040c0c441408158250012121200580a0504030b01510301c0d0041070b0110701541c1000190404001044903050f51003451000d6501c50591113440010a842c0b1040018041ca0001e02d8002c0c5406c01e018007041d2515441c04043e1000d44040b0405001801305140d9444002882e000d81203e00e0603c0c0710381c80c0741031020a103400c00e203040c2c28042101d074440d00400320b1803466124440314140548003166200f2100d01300c00c20a180250061041c40d11034824504494021200030650086903181c501d260791281c0d12514080c0c0c010b110101d007641d0010007849200010700020424a0b446468008010300d004c04000c1101219a00107401503481500381d8040d002e24001c100000000114440d000b9446448190032603031b50040001140401406800484081c2c00c0d40c1504003521280104503c0d005902680520f00090011001100d480b13680d03054002196600856001103608100c4211038060b0020000810017241c4400480e038005402070b008060401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702410629 1250 702409379 702409387
    0x90b1c050147360a02070c080d1d010e060c0f0601050d050a060209010318110f10020304090203040c030f06060317030c090904060605030a1a0c270a090603150e190206 73
    0xd50b050440301c10000f8292120f0b201c1041c0504000294060300c4840d03c50780410320f129489400c50f030340e00d000300c010182c0054070500d001c00c00d4540401030130910a806052540307596081c000001c45540055049a9250b880150084a1039030308110f400e0040c01c09548551815505441d0180c4448400c500504065000070355601145d210740e0101090102144943c140080f031483d10400060540b6a490b204080c242c007207810780e123404540303a029180103400440c6403a02e000800310103908020002e58100c4103400c40000480c100e54a085c01140c4aa1400105d0504503e824100d5041c0102c0c9485081014020000c2d2254907004039800c0035401c46404100d980e481c079042014100c3c940049030503004043c404010403440020f203248032500036185154a0b07403211000302d01805001003254001c203803000300c0101140c0b20401d0409205000d003460381d03501e88401c081d0341512220b6100315111032604191403518441480b03031007543c10a03075001d04200e0b0303508040103104c4074130b260019208043c005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702411879 1250 702410629 702410689
    0x3020a020a0b01090b090a0b101d03030a08160207052d0307080a053a11030310050102100b030303072a05060601020601090b1c050147 59
    0x2000900442c0e100d240324040e584c543d002d00e8090401c143d8440d000b00c0c544004901d44040d01d01621000045c06000004d08148420007101c079070f4000c2d90307140c0c0844c0c12128083d541c0d44081c4002c0810301c0d0192a83d850500700103840c0c8013180d1010108030304540140034284155914039013489090005030906409100c0d000c2403d444414000480300c1e8503100e02840000c034210b0100b4480c11170b6001e5000d5a0f6101c46031f031074482101403132821810b0f0350b245200204402803650003141c13900000f0761030a074500321040d218492440c0e109981c0080c1c220003070a070801166904220002668208103820300840284401180d0b6a0101030890024807150700d0810517440303131804945900d10700b41890014014554100380d62210300c00e94041e40140509800071618201d940211020303405c01500d104c86600c035448c0c48952918504404440d80e540f07410700707030242080343d4440304007103101c026403882e251101580807031060341c442c4c0c1101a0005ca03020645441da1702e80c04144106001c822040e07010140007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702413129 1250 702411879 702411883
    0x40b0319142a040b0a17010b01051914070503041e1d07050f28090b03040b07051c140603010510061d0d0b0c07050618061512070b07050c090403050a03020a02 69
    0x3920505170132080281d0005070b4011000700540c41d01400e64004c100d0b94040c1401100c05100e0401c091201c002080d100d4905244151030203510307484040b84c041d0904103503546050456000364054803500c1418a0152a05a0344040342e1001309224524841e043c5940c01c02c800c50030500920300700901078042030301e90f8040d0890b4103e4200701007008600c0007113107588491800c0404ca42c007440000a034103000c0400d0080000040300c2c001e94001d415a0003565031204115081e600600101c030403035025114903c44d1190702c1c001c0d6800100f5201c071000340c515000b8241401c46000070b0086009264402c010080203400c0300200c1d000a090021401d080f0010b40041030407056016001418101031008120650710440054281340b4400e0040e686140c0390407a401d9454420455a0465504103c010440725003404407801240d000180400d900e00044044950a01615500c4044421780006011381000424401d0b00b044030300c201c80c04070850610740c40040087c0070381142c40e000d040c0e00160450500e402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702414379 1250 702413129 702413141
    0x121b051b0f060c15010902040302090a020a140a120f0b0a12060608031201060306060e13050405010f2c0f1c031427060f0a0b040b0319142a04 62
    0x40c1c0b22569038010201c0856884042400c07009001440c0030010440909500889044a4008200c0e6020380c1310800184020b51010f907094045c4214070700201544200e4101400c0c1f801600d80300d09011440702000b4000762000750316080d1030980b43c82c070441404d0391401d040d8070230b43d012000c0d080b201550a2410070024002904126800d11021445a0b5000480c042050594496a40c1440041d5441e031b42918910700d0b60325001e03400683d030a5019880e06107684859880346c028000418090074207401003040704e034503c00490603007240b0308400d41c4040c0070790b20590074400c906d8001e21320040c030711200a45800550010581d4011b03000c06810f0300c0c83c429001980b20400703042c003100306030400c4e55408003480000700315482400c9400884030403041011521600c140c1d00c00f0107000150341d881401600402c2ca0400c9264402e076254504030403030310104500001d0030f000c1c81c0041c440e05603605103a0019001c803044c05003136902c515005442d24000c140018003928100d0301c18022500b0b030b84001006040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702415629 1250 702414379 702414409
    0x3010e0304080f0f0604050706050f0d0e0304050411091e0102070312080615091e0102010908120603070b03280605030312010603060f0f0e090304030f121b051b 70
    0x40080360220351110042507589038a10002e041310b00c065408074000c1e8840740115000b0b8890f4010284c200800c0d030052008145005007641100c8c5031070409200035044807040c154555540d4000b02d07040c80581000d20505041c4426021140d05044d040400981c05042d0401010ac8011a01d2884100340c0d00070850b24020b1079000c030300028200300d0864028070150301181c0c40b5205070800c54118a006020b28201c0710240c2c405030801d21408001c842d001180300711070070010f04540d60b5000c064007040c1c0c40d0b0050700c040c00c01d41500c91060700b0a84109480d20741d180d0000d4500200410600c0020030503100c041c00601c2010440e505290b601e464101d0040400703600454243c0000101c0e64080980c4524040c141c0341c05880c2007116545a18060322244494064803014088041302031296030400302105034464045000c60740f505440f42d07641c04204c1205a0202d034032000b0402c110001a8000400b4600401e4203003507800b020b07445440c0c0954455a4084040034020000b49a4801d80c4030401d501c241c2c84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702416879 1250 702415629 702415633
    0x90f05060a020904051012021002030c0d090f08160608280906050a061202090a2d0b09100302061b0d050403021206090d27060f0206280b03010e 63
    0x86004401603002c1e50080740c41d40d2245180000007101880d0086000341528125102980c00817040ea007445243d000c3e020360682944000d0004202d004403c1094042549039552200402440c021098810800540022400703400c0381ca11001801000d40f912001c0301e0891500b80c034103403034141c5844c2c00b1162031080199407940054480100c03001d1134000300b40c25071040c003081200c1d41d1102014011610300f40580c1ca03000509240420161511a05564100c0b000e414001074040000304c2d001c2e074103020007810494003d5217070740803070f9068014400e40c141007405840725103442c90492104a0a01c080d404020301c04c05005c40c54a00d002e061911100302410464211101040c90341d4003c0e01941251000301c1c400c914034465000502c80105802e401812040c005010403202c1d0760050b5036101059007590400d000c025518141c0c41a40700c100001446141c60304040d14220b5030000781010390042043c41c001d11034489604840807004039242c030440d5400000100b011030300d40024090150310001c070880b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702418129 1250 702416879 702416881
    0x605031b0906071a0f15010509060409060e060a0e0c19030b0a23041e05040201022b1119110307050a0f05210a0605040f082b090b01030204090f0506 65
    0x30160140a00c50080c400c400305803107070350f0179240004401c1d044a0b04000c00c04003800100c1d0650044001e0001d1080052a950800e5100c142c014101c4405520100c0501000380500445060500d0040b025098403110f030700c001e1410145145003445035182501101c0c0740302c20b00c1d01215203e80e2011581c402c008040090711a038400020080d1035200c3d6082e605400000080c00161401c0e10500c80c9000d28071100c94403044103100403600801c0010020307419400707400b842c041030701031002d072001c03888c034200c4141d0501c5a4104001046580c8c080d41107075860b4400c024001440c241015498841039000e081203240d0124280030a0400c011640076941101c8185404282c01c0c5101e000407081d1034042c0c2d070f408201012842441401252500d809200d40c0003941c103003010601030341000b075005000b21810401c10207190350ba030826071f000c01c11030420040e80301389040111401c0b45c046a82c4014001c0203002d4845d56131290340c00700c0b1043c070009125986e04d61100301000385510450101030340200503520a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702419379 1250 702418129 702418133
    0x30c07080c011a040605090f0a06080607030e07050909060a09030210061403150f01030807020d2a0f0f0e06030a05010c0503070306091104030b060f1918060605031b090607 75
    0x7030b041840b222121843c5000c26015103040038451081145c2c802442962191035059124100c40c4020b800322803415115a0041112101080801e00030300ca165000204d101d8516a0b141c14080c0c40e4022070303c00c143c540d00740610700000060301a080341103d4070018400c5150315040c0c1c90014501001e001180c14402c002402413005507090301250300503015a07525030640b000711407100b42c00715024504052458014000301d26140301425407248084c00d0110310003007680360550652050142e00707503800e0003010b00e603107a8503c412940e001000382051580406c0d04045100201c0c0c0c40b14043c00d001e072441040010754641c1d0401c0310b070300141d8004000300100c40c1000001851640300319842400710741843c40c0042c900d410381c80f031000e01400f1000558285819565020030404014140684c0612465412101681c0c1c2c0140000e1109010030354140700740c0381c03e0b880488010100301d148000f03858003008200c020380100c21650320002c4062002244076803400c01c0051805a2550950814400314000d42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702420629 1250 702419379 702419381
    0x180f090c080f122802012306030c04050402030322051f1106040519051509060a1a0a061107031a010e0903070317150310020a0e190605030c07080c01 65
    0x540100c0300342c280e0b082031402098100703561141300d0030440d40c0c0e1101043c0103200034000e00301c200060700301e100106004044441208441d0305042c11403000b41810414840b03545070410208008010aaa0030f21661034160000f0740c40340503c1d42c0d00c82c250f03081d0040e08601e2515407411325001c0c020040c19108060340100106498120442c0b80e1404502c2e90503140c007003400c0005449215a41c448010146181c6003416000d101d055000700703c615200e0810301c00315030b50030a03506502ca01e02e00c400500c2c4030710302541158255040030784c42401940700400e82c521241c0302c20904d8003d82c0c0f101d040440b202d8101003c16864030b10030340c0c40036204002c40c01001100c5111044410704a554114414080da240c0741903950f201e200f0114000c0105009010308290400d06100d96680f044600742d4042c2c940c40600c01180c00d050325075215112690703000412f10300554006580e103200d1903013036070203003000302686880c6808004103002d51414018084001b4140c074800300d044440440e400440140c844290700c081d58 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702421879 1250 702420629 702420643
    0xf040e031210080604080d0c090e0414010c030618020f09030a0809010e06030c031602100e01060f0b03010e150301020d0207030c0b0612031204060905070305150a06180f090c08 77
    0x109410b141e0300c4001041c0300c00080c00f501407604402c41e01e2400c0e002110b004000c10700c115154041c420003400008950128461980c411809894122000e1125200306421070b0450f40707040050601d005000e0110050220a02012403000000140c0e114040c4810b904140a040311040d8036102d07010b0100c0800401b9005030100010a89a14641c80a42030401070203010440750b0300d40a00e000d00014141e40c0c4200d05001c041420f50041c0c440d0000dd40c402e81c42680d1502c484094203039141c0c64100f000e60102040b04d001820b540300164115410a91502c56250b8040c168914400b003030103088405603000e50456660081e041c070115601d100303500d40035140c8070980c001907070550f4a8500060b000d0400304a42c01c00351208001552400200280880c5440b5020340203459140c0d4a043d11b01c0091010050200a580140020090022990342c084414000109403c6020341822003c00410760307051100d02c40100441000300d620003034509110018805403038040d00302040c5c0300000907a00380110701c203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702423129 1250 702421879 702421891
    0x614061c092604120605130c1203180321030222051c05060610020f071e14060301090218130606020f072409080f0c100c110f040e0312 59
    0x840805050b50800c031100d070081c0d10909005800440c0e030240014040d07031105501100448004681c8942c80e101e0340c0c22161079400030500050100b00820070326410402d14541d10412004010901d4190b0752514201103480d4003d80094044004503505c0f140241c041e10f0307482103401900c051014014401000c01000d4ac4103060081e01001d4000b1881c4501c80c0095a040381c1110041c00c0d41c1d142c50044c040d030240303107a00110850040580355150a002481744100402e50308503800701100e03010800c10411040e55204c40700c180b082900e02d913010f4030b0700c1050720b04681c0500310040e02c4c0c00c84110a0030b554402801400d030b100c0c003920070a07580b24041e0fa0007181070300d0480c1c4c00c0b550681040408695201501d010b0b42c001d10802d4160003408540c5420312000004035480c0824810f507941d202079190004460700c01080d81c0209035640700a050200781003000d62030340d14100d01c100195445200308000300c0e0950030301410400d81d80d126191100d4018011000c020401c40e951802c121b02400f040490984e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702424379 1250 702423129 702423173
    0xc011814060601080c092805010f2c0d02130603050106090603380f1b040323120d060911190507030e0409050307060608010614061c09 59
    0x4140222200040d44610441043c0c481088913142c00000d03440706d402c2042582e80c014050904001c03404c0401e030b01c070394000b260003106180441c101070000d0324070480c0d0701411b400c006490078101503802c9140842c682d000f58084c1104e0b0b48004490200b4440103208002a4100500228940201e5142d6200f0400c80b1f00940081040544a9041000369520341c4005441c075000c4400705040301c60b028002c08803000403550810742c2845030310b07031178070780d030441242d17800300707040381102086900104201500038a68102c101e0924041c107542ea03000031080003010301118201e0202503000245402c001680c01c0029420f280e0b600c03101c8016014019041c6801800c41080c100044e91003804807040c16200b41c040e84440756024a10a54012695074011f00419003c110017404401da045d00e46108a200c25030017003014681c1c5d5817040c00c108090342e460781d00400d02e903850300d030081104075461401810140c208540d050f40d00e40d078501815002400101c8245920b52800380004100400410b000304008101c1c25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702425629 1250 702424379 702424403
    0xb030708060111030904022d07201305150603090f1b220b06030c07031116260708010606090b16230a03081905040206070b0c0c0118 58
    0x1151114180c43e000c0043da40140002101882c0c50740140440308440d6802c0c4c100701241d135400205800c040b401c0e0100043e00020000c0501241d550000c0381180c0f5001c0c034000010f0041c0114004440e0b4120034240d4590380c0d00456088402d00e2400456654000c04058490400c00005070300e418202c6183d074514844d50030000001a18100307038441d00c8400601d00c40c96514040c46c40160110611494241181d0b038500045170750e0b90300c03409907000e0250100160f4490b201850081c141c3d44041d041011298041c07904010001340848100f000e5440b00d0154084031480c00b504045200a0082181100e004c2e503140810b031a00c055005a04880d60b541e10b000d4015900d19490109224102031004401d0780703205078602242c001e203411100314030310f46241045400d444482a05004010350102c00140020040c03001d80d06c1000600e03028580318a0040045040641c0050b070f0610403824001c00c0c0b40c4841e8002010351000341d00355050b10552074002d0104c501c021400c2008141c03070841c00c450b1004013034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702426879 1250 702425629 702425641
    0x80d14010603150f17031b0c0103050c07171e070605041122021b010c030b0a050307291207020604020a0605030f150a0b0703090e0a09050d0e03070506040b030708 71
    0x1842d544200c4910300c100320444c3c2d007403400c00c0b641c0345400501000d044c032080180007541e141e0000d1030000003800c40041d02c0c2005c0309000040550780060203a01010750188155000700e12603016850500c001210160703074403c1909842442c1e03511701d095045241c2c1007c50208244003980e00158400e5106054804450844400f00401d5083e4202511410300181d051203550041c4e50340240480000014004a05007039843c50a084d0368107041c2c1721001030307185e00c03208099040024456020308011405481c00d607080605150450b92100c40d43c580c54080300100040181c003420440d03088402904a00000e440c1005000c1d41d90b41c026a400c90280d40c80070b100040c0c041c031800a6a001e5205042c0c1041d050320703100941c002100080e03491030340c40700225100164a001088c01020010310035240d1010007803034902005409040186403101250031b20590b0b100113100490125001603d6003410741010b1100c0c00441d00e0a1000e4204540141c0001004150402c000f4042c600c118516034829625a40d54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702428129 1250 702426879 702426911
    0x509010608130b0601050910170c090d11040212040b070206070e0d1128141009050607061433100507050c040f0c02060c030f010e04080d14010603 64
    0xb210703410030907451a4224000100054100f503004101450554100852240040c983e020b281c00d21501142150040c0310107400140c880320307030181c07410b4800390800351f540011800d44064400300400e01030540c0d903000520366071641607800e803600d0720034000c040c1d1903d031801507034000041d106000507100e030b0000194000d1043c40d10240701170016260300440145555004000464070385c045512802d1500040c581044000e17144c2c000c80701c000c01c0034030610715052201441c00080e80d00b05010f14640c442c2804010781003002c1c00e00b229001e94502c0c0d69680300c2c0c01e246d001003e12480f82c0ca10000f1070010321904130703d0484242d001c01854504403010503400049014454000d54450742c01c00303d82c0440c100b145000b0400380094034012006c0e210440e81080006080700c1d10381290303062030b9540c0d400c280311140d41000b5003540032840810700c0389035042c4020b20b07480c1084144200b460520290340001d0420000344243c54003450503a46c06d010701080e0800491040d042401401d0000389090408801034202e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702429379 1250 702428129 702428131
    0x3090b0906130e310b0603010b10031b050c03030f18030a030903030b090f0105040f09050a0b01031703070e06130e0f160201060311040207060e060108030c06130201020d0c0c1205070509010608 84
    0x4c59a42e415098150380d0f03e0311050b0020001641550703100184950b0380c071140000072900c046a50005002d0540302000ba5404075801541c000f0844140180441a00008200d0340c02c209001c00500e0a03079074810781c184d609070688800b80740c14000400c0404445405400480034588a501c007480b4030104107080c40a6920203d404800c0c510010004000509250303115072207000030020041440e060a4640078035010078103030101c510050f290010010700041e0100d511070385207880d80c0c80e8507506042000600c851400e000c40703489680c00040d01c007030b0309035020310f504000d00c3d00c2c0f148009145000140d8083c0a0b40881e40105810300c2c014109102500c18820401070b6580150041c200150103070521000303400400e01110280c1d84c40c0741580007288200944d600070100300c4004d55032400042d400f64100781d400350189030002560044d260041c0c0c0c0101d81203150410364642416680024100b81281c4d4503c0d41c070284642a0340440308042c0000890b10b08103507002580d1400c2640d0383c40f0411650100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702430629 1250 702429379 702429451
    0x140307050429060f0a0c21021203100f0801020c1606050a1d04061205010b0d0309152307051b010503010302060703030209090c030405061303090b0906130e 68
    0x12100d000407454140c0d240d44090040040c20503820400282c904000d0343e0312400c00d0a012038150481081004a1110380540754410005c2c040007c0d443d404000c0c2d5200826a04011345503408030024440c0c611511503c0002c0040904941e502690b40302554001c2d8410f1545072068058004250000449203a1002c02c0310160782d0707943c0c6800d81d2a01d0032985502c039001100300c50b4801d0b114903821643d55010703010150001c03144400e424822031406a00315054120120300800c1240c400e07002007a00300c503080080740e228180f403400d950581c080496a00034501b641007402c42941e0070707119101c1a028064004c440c800c030111514508014990001c81c2c120212603800210208014401401d040000d4602e840c400e007405070070b11601000040131b2000448081401d240b0100801c8103111040012b150450490101d020b5000721503280201a8282406442c401ca030000403c0c0d6496200c07c82100c00001244200d5000f04e07443e0312034120703804001d1702c400040b54100c0c2c1c5603640c1e00c420218071204240c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702431879 1250 702430629 702430661
    0x105010f050f0102010f020a030b09090c060d02070f020a0f06090807050a09021b0732010f0509031504060207050d080c0d090317042102030a080a09020d05071403070504 74
    0x185064200184440342d8600207045540b074080d00c0e0400240c0d800505a0a49151008507440121206011000c07200411181c0c0651002f07502c83d84603141c2104076410140141c0c000f44c0d69100c0b41c280114070040001d4001d400c070070544000a16144002c4d001c90666200e55078001d10284d450b03203500d54420340c5001d0a0b51000641004102c145410360080c9210402d211401207945ca412170040c2c00c0040d26031060340300c078482003056100a82003c0095014003482c11000408200c0500000d00d1030402d4807004090140004844402da6001c100405110350b98101d000f24920301407a0820282d0400c0b18100c441d40f09082c07072000454020403416110304a000515410100800883d80280100e54001d40a20410034110381c841c1d02c00c0700380a4807441c05402103031600a03045090103620b849002c51201150824851003445503400300207950020301101001c10021410b00024102c08407104006049100341d40b0005400100b41e1180c60038114201c042e04c0d007955951061105550740614881401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702433129 1250 702431879 702431909
    0x304060504050d2a05010908030a1509060e0402010e03120f1201080a020108161713030e192303030a27240225140a080304060507052401030b0702010501 67
    0x3045a4180d13210109005a002081c10a03841c3c0351918254401c1e100c615466403603404020760480300840c2c240c014108550100552490301a08125104001e40028104580f02c081102540c3e420440c0510380e2040011050342d030801120040950b9001c241c100c0000400034000007090040410009030b05038040c3c54501803a620461490f101d00c042c01c0441051250700918176001440340345480340308044085248580e2600c505007c0d0841e640303003038041d100e0502005034a100d14400d0070742d1012203110411441a02150080210fa0003484070780007505840041190140e1680c80410007240c0100b41d0410300c1810130980341180441c80c280108501c000d1205082038111144001131040c0016a1040c3c3d540e18003488051080740c041900030943c1034001403404c0c06010890707011081c25042c11115100307410b1400d1074081d241e0055100d071005111001c100c0c00d05211060000501100c04100b0f0080325058410004e0300c443c0c0c0a001c1500e07010740e818000b465442c014402c0b10b05032102c0c0d401c1c004413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702434379 1250 702433129 702433187
    0x705070b0a1107030c031a0106091823101203050f18211501140108040503041e091109010e22060e061f230f0304060504050d 55
    0x31640620300c00320401082d011a54000700c014440d4001451107504402c0c0302d245181810400211104540c1504050b042c00412205410005500890f000000802e40301c80d007182c0810024102c1008040803000300c602c18a200041d07289040d0f204d0000c03c0c01c042c5240c4e48404034034050044460005012403020040b031035401844002901944941251010014050b800800c649151000c030802802d01c40302210b107880c640a000390f081c8450800003403601589883c10b14400d40f00d0740c60516040c01114408201031002c18011100a0602c8020706031200d00b00c4101800303140c0040c481c44030303610701e41143c40354050329070021036800e00c50507500d00703140c2d002e482c00304071018030f50072014802c1d0140001c4202541d84207005600080071386040c11022841c04005220264181d1921207200b800d040400c1c065182d0400d90344502c02c03407000310007a401c03c4010365843c1148590360401400d01c002104020800000790000380c4510f1090090b200740028480003a100c141e00c5031130b0341090940011640c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702435629 1250 702434379 702434399
    0x20307020103023a0b10020304030b0403090b16030905180a0b012c1011030406030c0c0c032001110a020d05012a080105010513060c02011206230303070507 68
    0x109013181d400c0301105441000c80b40200c0480414807003944207000c0d040f1320031000c0a440b5a00c3c0421054410f00f22240306010000d480c3d100340e010083c131100c068030208082c1449041504050011544901d9484100e1038001500301079003032045002a021403030100c1c0300d042101122100301c0814501c0006074490760082d074040c10b490303e0031754100b03e64003100c41000189800c80341c2c0d60401e20400100101c004009201d1060174440c01c00040c011201002c1d40383d000f0000c1124115886441c000540c40c8a01c4030172034928050301400350118041d20000710a208520810200c16000d0072843c0e070141c22414015541403074042d00d110b070079070405600c15015042a00110154034854400000c0c01003a04000c02c1c0c101d1480442d00c480009540482d10915401c100e030306000d0482401d03d6410501800d035020100c9089008160030800c5070402c400031640240703032820f50b050b00f0080500c403564450001100300e50342002150a07182400e0104c152905000c0304581c1840c3c0c1020150240c542400b500792 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702436879 1250 702435629 702435637
    0x3050c0f1605010c0620040e1605030f04170f030f0906010321030f020c010504030f2c01050909070201020904150e01050d0c030803010b040e0c180f0a17060711030a02030702010302 79
    0x140d045d60b245c4107414207000306460380760482c254440e64241c407142440080d100300c00008200d07000010304000380350105500032050300c0d84032203800c00d900d1555850380781ca18486100c09410340284140816004d481500765006140314480b131008030b1a203951940446039450340c0a200180c8030301c21100c81840384c58260b4529882164503030401040f0141c0c183d01400c101e90100c001a2001d9640e041030104165010211039002400340c5400700344e5403000c0341a002e45100603140060044d919541511443e4000c0099030112131008200c3d03041d03450801c00c064041d5001c420130600c110314214514860942142d0808182c0300c14003204003281c0e0030030041c810805103000f003c0e1003079180c03088000b0000d20f5440040d800b0381103600e040c940396441c061421030350700780c080c144121605040c004d401c1c2d43e040c101410700c807940c421290200c050000102240d05100b003500440c10302c43d21100c01d004d1600d000103919016801540d100d01404802442e801d450317026000304203006803c10400c040240d842900a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702438129 1250 702436879 702436883
    0x2060d021308010f0506010c15020d09080c0a02010305090a0b010e0709050303040311013005282720040f02030405160b0a091701061203050c0f1605010c 67
    0x51030002502000784400d14580d00000c1c41d40c0d100d002411424549025890b0000310a007080c11100c0d0310303036075900d403146009001c0c0803001c0c0d40441e0354401082244c000700320080d0012941650790301c0b5031040780e1325000c420206a010900740303c007003080d0031400140f0940898009544040590810904401328640a0701040401c02d24000c0403e8695062004000452203103210f01e810305182800500040081c1c0c6019a1a400c14650380801c00a00d01500001d00003464000072541e507000703031407206803e51010781e8288072a5030805000c00310b1213500c00f400010396603400340c40608070748050101d003600d207a2000301200d010501c007d42c643d110700c001681341c81c4020000300b5240c641c454540d0882c0c108480075203c0fa0700641030001100340c0c000e0442c02170010f05924503e00341454001910002d0305102d035180380c0c0c4400c09011a01d802c29804900a480350040914003c002e905009015401400728012107004480400540b500f00203031030009400c56044410f038151030600103444805c607100d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702439379 1250 702438129 702438131
    0x80303060d0b100e0c0a140f04051909020c0a03081803120709083c0304050f040615090e090d020d0c02030f06010e070e04050402130902030703050a122a02060d 70
    0xc640c40c000307405014800d07500d001e119626646d11100041500d0030b01c215640303990104010000100c51040c0899055072019501003d600c08003c44081456941e81d0264140f41c0c4003081c40901024081680e41006000e9920501035840b030304412a0343c07040401d028081c9920400c039215403e5840850280e0008280c189130008564a03212281400c0381008002c4032030683c1c6440741e920000018201c90340702ca1400123501240c0f04414035543d00d08c10b0380101441a000841251407039a15500880c02a0038011050303c0c000301000405025010b00d400340640c00c1c2802c000140c124400025151484042c039030040103040a240003e4681440d59003081e0b8040c064890107180754502001000d0080480f8040c000300e07498100402001c0c003a422050600c103501300030510015030b4a0222121200c21201c03c0099130180510020b0b1810700140d00050103406010001020f12030480c1803030030900d11584540517800c1c644080800e0451328881e9242c1c001c44040c00300d802505100010f400300e0803640f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702440629 1250 702439379 702439411
    0x70f05370e2409210a050a4b0219081e060403050d0f0212010503120705070b03060307050d060b0a090504031205072a02040e01051603020a020c1c0b01080303060d0b 72
    0x19080e81440001799094841d64072540c2d81c0d0b81000240250740d000600810380d07002800b03922100102d64601d1501a00040030207111105216001088206032078940c0100b00e041e901c600c1b83e00c01170040345503110304c803503174000c01d1000c4840305828003000511070001c00103800165910754040c0c17040d400c407030521554039030741c4d0507121040405c910042c8481b04812000eaa050b40c9048101480d10f0100c0b1641c0205040c2030001100181c00003881500342c90000460340c0c0c8a13594400482d10b41095640401c1c0d0008150301080c1c2030100d039601110b22542c00b61208110b00b81c4483d01c6c0010f031901602c000f0700084000180d43c010307a1041c0d000b40d8002115190000715816920302e545482040e608a1440e03079a03002805004600e01449501c01203807100c8001d0100d4a000602c40ca48440720072440790034150000390201e0f9640c801d020507219280000d14001c01c0310203c08bc2d40d103440b20002d00494001e0590800400e1100e0000b0980c0c1c46010010000020701d8107a60b142038070311601a00100c81025050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702441879 1250 702440629 702440689
    0x1905040b0708190f0f082a03090d0f080106050a1e0509040510030b0103031101110a03051609030c0b0c030702090c0909070f05370e2409 60
    0x40100100c0380900078090b2200030800948003034005080c000410b0000381540e0039010f035005810111321180c5ca051041090f901d00c06082141070060f032541004031040a55910080100d102a50140c001c2e801120702c560365100d03080e20780c1e00303071349400501191700e1200400c145031003880101100c841a241c41519600140d030300307850000511211101007a130200f0083d40508041c0b0405070702c01c002c0d14882c44e0480c5107448204403034006010240410458150069007844250040740c00d03c030001900e070340c1d200030314140100204000d0b102c01002900340602000301c940300311085025260450401014a4a4885044020f0384100d61114083c001809101c0140e40d901002d5842842e00903030340d640c1d17821801c00300104403e0040442d824418800c40c8515110351210948540e000685540383c115190000031030781420000d030108505404201c19213403031a510030744540300d07035400341d4215290320580350200091500c44480c01c0c50034a000d0082400d18079150100041d400c40c03088a200760b031200a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702443129 1250 702441879 702441899
    0x6020c01020717012c12091302490207150f0b0301141f0e0604050a020c0616080c0903250b03070e030c041413021906020106080d03020f190504 63
    0xf45100311505c030390010a03160004040c0509103170441c00404041c134056030f21000441c800c0d110004e4650b6503902041d0440c07103011416140c01c810000003618030420500c940300c1d086402d000007041340904480c3d20900c0080b0740600130307a08403c0e13009590103d0186259008001000310720841030545469135508101070301d0a1003401c40f5202000a1091107240507a0468020042c0d101540840714103031008205800c100503506030450401c645c041801c1d254845101c5c041c1c0580c4140180740d008103014010800840c16171244070500c6a01d9400040e0b0f1444030883c03585c00340f2181d591b016000310480044016000c01e10103a07500327000406201080e2070f54403100068000b03c3d20503002c1154450a0b141920f410000c802d02c0d01d008440a001d001c0751309524000025016000d56007550071100820219900e1500843c12140b03818500c2c21120f613600d100a020b07220510605401d8041c040c20f00291912074002c0314050a0150130841c034081901c0111000725000c03405210411509020104d00c010b41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702444379 1250 702443129 702443171
    0x6050405071502030c0c0102120304110105070605090109050d08130221030301060206241e1815090a14071d0307030f060b031f112206020706020c0102071701 69
    0x402c3d4010743d25140c0905101e4079050030400013038150350011815407219901c80c0c007260362150b0321001c03100c42c40e26154010f0790b660046190003002c1078108820016071990560100005900413011161354001b8800305a480701420f481030410480c4003200d0341c016080002c04030001400e00301d110349840031071a102c581160020382049005070001800c3c49a80c0390038803002601a040c0007c0707003c0c00446078000640c55030301e040072201c04802c3d0140d049583d958000c4800740b0750280840612080c9880644003000304110762596110b50350704008140d0340b442d20310500d81c40e111101c010310815241c40c441035031104408002e0314950b04412007049103e4030203000141c003d43c8a1071081c440e28900d032074485c05a034081c1007070f03a0281d40080c406211082c0c10704103a4100084801c40000e0010062031454a903201d218a030b02040318080c4200d48000b0580ca614108a901d603609030b0f1902511540100d840394142c480c0e803030060b40b02e0751040c0000b0350380d00003c6c2d40001100d0700000d08000c000ca42c8801d5040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702445629 1250 702444379 702444419
    0x12102090a090b070311030609061c030f1d0a03080c030c070b070b07050306030705010e03031204150b0319031209050d020109030e030a151104180e0d08040803040605040507 76
    0x51901d00701010001c120f180b0300d0b0000524141800391065107180300c0e400d400000c0016200e246800081400d5850b00c42016800001100f0118141030850038060003a104135080740000507202c0c207000c1c410a0583c00c0804c1d0004005040d08459407441d211100d09410004c1e4601d8140001c00c40400d01c0102000348100404038030301003580382e01d00b5013000070403a10002e08041c10b1060810420929a074046149001e907907090070004009081c1101081c43c50080c1c1c10315188c07007104003041c0070074825482c5020302803403800035040c1f01d1208003034240750300d4514190316202082c4400c0390201c00240a0500010001c417655800940600e203603d400c4e03d8401c801c2201c90150f5941d441314401d1540c40141011140e0064000709190b00040e41d03004c09029035000c007130307991940d54042d07480300c0508681100c1c000d0800303c28030035101c0d04440c04c180003000680d08003625131181980d000b05c01401140268450340e000a036943c103690b6a1344840020385801001141c480c0a5218042480c0e0281000c541b90301c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702446879 1250 702445629 702445631
    0x8010302010f030e1f150f15020f0d0302030c090a030b060108161220030c0c010e0105010f170c030d020c01090b0306030d140d0903031b030b09012102090a 68
    0x152440c00003400810041c00785004041c03c2c25402c90280c400024810400c5025402091090000348160380040084404000c22005174502c001070301c00803280c550042e07500c0040002860550000c0a9a40d07141402101c01580c02003440303a2078160203a40655480216031041038a80303240311000520035a62a04119088500d1405010712542d000f4920396124800799507100c2d4001404c00050300720061802c2654100352601e280c407458000408054419084d0260081c3d00e81c105154606110781000428128961a00102002960050155504031055810004c01c020f04015445c0c800101414090005214501c0d8070780340f0f41c40801c02c2002140b42c50740078144450801c0c0005040342d007580c0c06003206610907c1804816a80401c048a409216082ca06604038031040c1c1c05085014000756031461a01c0d020041d424560550090002c6c0c80f108040e80c11688100e001c250104d43c40c800c501d50f0058242401440440d0403041d502e16500c0c00c0c1c0c0e41c020b01c080603a81c0028020f8400b140e0b40c021007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702448129 1250 702446879 702446881
    0xd050307060603032105010317160204050c030105030d02010209130b04140106211e02070201021e01051605070f02010e0103110705012f090f0a0308280c05070302040b06040e010608 79
    0x41d00005c8104684210b0300188805d501d540c5801900007403040300601d45080010b94043c900d40403207220a9010b0f8050014061031511209015954009110760b500a006846031191881d04c12b10803500d441400030b010400780a40d01401200030041107003041e401039601e0950203500101a04664002d11690780c40c43d08009915000c86400c0ca0000c018034a924108030a441d00246103a420401c1c403810404010b07115403c0d0b00040707182c0740b2031841d05220a0703205000101d8540381034200d07500c81c00034000c4044099000810440b40d6200e520750203032081080002c1c1c200198840e481100c40c1d15014034000c02c101c0c051490000035076004080845240e0b65603114121a081142420b45501606c1410310b039408024143c80b150a00c10038900741d118000340e00001c0c2d640d07910400600080e54000701440d4503000c0c440c078100d021855494558020040c0d855000d10800e2059088060066200c805420300c1440c3da42803001524031f86151582c0805e0503c07011401404421100e4001c02c4d10743c0d211012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702449379 1250 702448129 702448157
    0xc060a0b0102120f0409090813090912110a03030f06050616020906090c040e1e0a090b0c0309070902030c0f07050a170304080702120a05370b060d05030706060303 71
    0xd0280c0525091105250038401003289031a2103080c0c4044408000001c41c1e030147c1403030051407038410182c05401402031840c011580d00350300d610080300c0500c10901428171a140080548820b004032030340754581c2c0d200d828803400080c802e400c00b0b0510403000d0008070b00d83c0d454800044054001e00005450480c0c80101a0158602100d56907000481070740c4120050420400504151045004980c2c075800840003190364040c2002e10820b6a881215a07801141864103441d0040c1070003030b205850b84440c440101e00c1d24003419045a0007200600c0042c400036182440d028065000108400f62066080c8070295500750104001c11480384150090074070111240b8095007031540444a05004240900400c000103e01070103c500700394040f15000036902d290324149280c02d101200040890180218040c490081e40e07003001048034514804568031070074031000313009410307a0030300180c02800440040740003405d020078003246003402081034910b0884240c5606040d0fa142c0d80c0110001109a498010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702450629 1250 702449379 702449383
    0xc0801110c0601092a0c0804030c150e010503130302120406050301062c1e04090c090f1503030e01052218020703020a1509021302090f121209060c060a0b0102 69
    0x10142885003c201320300324007010301400320b020343d810032401c05d030720000201d802c1c1c0d004112956070a98080d10490351291a49040d400c081018485c003101d40c480442503856582c0102c000601d40c90301a55024203580d2000500001d0f03149111013601540620f132104021449a030300240042e00080d2074440d540d503d0980014a00c0c0d1440100300c0a2005a40c90880300e0240d0101030401d101c0c08880a1451240c44007400704142080c1c10015401444c00f200740d01081440005941102c0c221181000f41024154605055501c0c80302002003103100800d050001030f01403003101c0140300043c500305003800700102082074600c18040e02c0c2d9842200e40e4a08002c04038886042450b1847c5043d820b5040c20030070780d07020755100d000200c01840c4007000040e803440c0083c00d9001010b002d030020015201c460070303090100025031082c02d8a9000b119030704000140750800f4000d2940f11072104005001c01c81e021548580d0325089407041c1c030f074010410030807070381c0d1310008110083c0900c4071083c000070002918400a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702451879 1250 702450629 702450631
    0x260c0313151d0609072304090609050f070501050301050d06140a02041a043f0303150608010b07060207060b06032e0602070e0c0c0105010308040f0905040c120c0801110c06 75
    0x40142d8041c0d03080109240005c14020229600c65813190032506d038180d400f030820700500504c0d940140c503041c005014072110350032011b4201e000314140c0e40b480c0c10215446031034541d2030040502140c420001042141032101003003a016010342800101260043d441c02c40d0444140c40c0030200603008282404403410030510b0103001c00e10384210600c2c191804c0e00701201c403921940c409c010b8410b451060b58412000303814448a410061010785085020351a001d0006c1615045c65144912512400300f12503008600e0a416a080c00000d1400c194603075807424041d42c00000111a56034803100602101c1e11008003960041100000101120752404051003001c0e01c014140c45a00c002c9689c10040240c000c50010141c40713107100c55801b070760380300c80a0703c03420700c200003a007069980381c407000000780120702e4050030a859441c0700100405d940c40c441d5006440c802d580240c04040c1c1d194040200802c03503c02c416031503105d140840800c90f60746601e1400c40c0c11030614044a510000340903907003410184041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702453129 1250 702451879 702451931
    0x1112070503040b0402010c020f032d0304061e0e091e06010305060a060f050405030709051b2701030f050708070e1206132102030a260c031315 62
    0x1030442c5415141e80d56584030192020381444800d69802080d074480040f06243d181029003213807060032b00034911010720840034141c40118240c1d500841d0080e007000c401c4070212551507a8600e06032250f1501003195504070045c0d0b81c240219001621115100d01d49854030980410300310503100790204201d255940f000600450416280404102195480782000c0d0140e886500e03241d4214140810140e506124580181e0f03418400d0100004110481d60007440c821443d203600c0d101e1b91744650201403a20f01035682c0e65032580c0500444d00301079900c659141300d04981d0500d40806e403005048480000c40e642621600300182c2c150b4208109140c102600c84040c03841611944000a84842065240c11014002d882d401d00340076514811310940d0081c3c0314144079511050700c07200c0300c00f5101a42d01c1d84400c60210201d286808098220091450009040d000c00900204150344840362441c803540002c0032a05a00404c001101c00700e910001c1d0140e24080c0c440d4002007041c1803065640480c118082c2ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702454379 1250 702453129 702453137
    0x40e07090608150d12090305100506120a1502090f040905060103020103111c05071403010e09150106020613050f01060e0a0b040b06040b0c0717060a2022050301111207 73
    0x9540b6211224a844ea65400000d480291a50368808880808866002620920941c40c00b585400b0356980701d00d006441c201c644280022000e001c9507100c441b503039005010480700c0c50018107401d0b000c2c0c000f0070b000c2c0001810b4200903044500003600b12208500280d50b1644090014004c558142c450460f0300c84c1c2c804991800c100f89000011440d4141001c008403807034940c00032815141c090462004540b000c40b100c00d8407582c451100c0260014100d0704800d4138824116100340c26401081c0c800c0c165031103a806010559101044078001648007941150030348115009184c1424081c4210310280441038200c9103e810902c01400c152449000810b1045103061120070050b52004111012280072001c0680c8880603c0d46e101c2c241011a884040c1030000f8110303d02e120715020840500c01c00000314100403039000190400c041d60b6034a071400d9414001040105903ea42c07135005c1102c2c2c0c1c031402d24a110125100da000c03a080d20282c540d080c0c4590000701e0740c580b45803441c0104560100c12450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702455629 1250 702454379 702454411
    0xf1803080a0e01020f1803070906120c0608040309060c0c0315020c010f06060e37050301050a200c0115060906020d03050606031801020705150a0c1b0314040e07090608 73
    0x340d01c9a06109018501c803050712214000001507c00388041d00040600ca5000c1020039a10081c044500c28450003ca400d07a02181d0003285890041050794052174165803440401d030700313055041c2c3d81200241010b0700c3c200c1c0c202d6000000180c2401c080e49140b00d17200e20151310b45046104840c01d4a6440400b14007a9082500c00c0c01030396131141c45520705490032504600c00b404410b4102c40c2d4100e441d000302440c1c1816a100162078220000b0200c101c1d0000c0c0d00820056403800e080e401102c68124081020300d030303030b03019010340303502c0b400701401060b414a0000904140000002e11440d001540b101011a0081e8410032149406008000100c01241403e101c00c3c6050400120640700041c60348040c00c3c403802403c009030b0f00940c15a4205580f080c222407a865000f10300701d08808040711005040c03800c280302200e401c9c0c8140300528114a0100945240c0051590159900c1c0c0d068041e24881090503c00040d5a08130441040e020300d28603150491a07a080c070700f008016410081640d103007031100318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702456879 1250 702455629 702455647
    0x71401050c0406030c0c0b0f0c19030501150302030613110c0709060602060105151c06031406150f01021902030c0a0e072c010f030b10030b040c02060610030f1803080a0e0102 76
    0x103080340d0320900a4100308ca140e07a405404008500503106143d07210045802c0c80c13240160141d1100b4140c0700e05035075400781e0306040401102a44012190160007003100c0106400c004000c2e041081449000e03040c01781428420b981c41c0c0e25155880c1e00c540309076030701d070381080003840c0d01801102e002d044182d5806e2401c010f4190144154444c2010f1004c200049a961640304416a4001e03000b07198410200d075078060800c60003958035981030b2801c40c0c1e41000321046041074500856141d05290041c0c0203004100a00c2c0c5806014210800c0182d8042c0a0b000b0328001e40c0e40c035540036001918440b0708070742950a1400c0002c051070042075502c1503400d034000b1992070440d00794000240c014002d103030455440d01e44440c200c0c05050405003058011200c80d01610445800d03411580c0407482c156820026001c144104076500c004c160750498002c1d0402220f80f4400748250001445400703202c0d00466920090880b070a16088101c0054001480c2d0340c0500c1440c91480c0a0400303100c980800950070140a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702458129 1250 702456879 702456893
    0x203041203050d05070f030608030a1713020406030f050105090102070c030f03090308030c0705010b0402040302150c070302030601030f0209060f0622080609011d07030b0a02071401050c0406030c0c 86
    0x290186518240041040d0020148501d0803512181c1400506014a040c040b0300a42042e10f10111500400d08006010038400c00c000150b5205c81007955031544500351900095a1115028041c00baa4111142003803001d43c85600490009510500411400c40b000c2c0c03d200d405c4443c00750610049900420812000c50f0303e20105ca0180e91b0842c0d60000c2c072035a245800e07206520342ea480100084000b01c02c00c0246c1403a04040d0280074018402400030400c4501008128400d502000354460196030341161580180405804041030040c200d56481d0344071340010345490403d0340200c0c0e03036113031401c407002c214142607052580041080c1c401c02504194000050114010040c092a403a1804015010a506507890310780003030aa400594900d2309100490501a1811b0382c01011000702428960000400004140b011642c002c2c00b544800c0d210302c060500654441842541e009400b51205100050284a02403746818241c516500c40c03a0aa0280c150303800040d40030107200c1c1180105c0081140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702459379 1250 702458129 702458137
    0x11060c1204030819060314070905010e150a1e030309090c02070e06010512130201080702070806060d11131b05120606090a0305070b04030b1b0a08070e0d0606240203 72
    0x702d4184580190b503194210350260026900d4298035500f088000000d11032a51500392200d0200c1e41030700e20942d2600c21041c00d070391007842020703e060321a8000179075a813124451143e82c510700400782c900c1c0305c0c0d49900040558600f104038030303070309c24100e58100101904005150001c1c03014403401e003c000c0c01c9440107521082c05124520888402c41c00051140e8882e00880c0d402c0b01c103111203120507003810030040980c0e100c4014100d0208104c00040744840d4000641202151002001008243e84d624144805a0300440781280e585d46150202907442d907640b2500035180140d05c00001c1c440c000390f900c58108440e0441020300307020042208901c66040007840c00e0307210b0301c1651001d80ea9030803100810a000700760341c07010b001802409d10229a43c11810000c0c8200c078020b9801c01c03c03d499010501d070404140d503030903455030340c0e080140040081c081c1f90f40d198814182d0624015420b40d16001c61711004911070122116550307554280603500d0307544101450100501d1403952503290701f030006035417849 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 702460629 1250 702459379 702459383
    0x1020901120627020c190b090609063601020307090609230f06190f02070b1b0f0316140a020d0b0c0424030c080408040902090f0402070311060c1204 65
    0x244000040424540307404494503205c1d6130085884e01e081004a0f0b080700f400050040310007000e0b8074007141c1901f00000343c16001e800d102d4043e01c8240c40d21003500140108882182d80294070182d0a03070700014160260f03c0d40000da06d000507030345c2c0c600b0410041c80c04145030041c0b03042c4500c01c80c0a010a842c0408000a142d8284440c60380c548014800920000c005041b080e81c02180019400841d01d0700000d84100000c2e42e49501e51010b501c140142e884400600680c1c502490034400401048004d101a403107000600d000d40e034554061028550455200c02c10f841c04081c90380301b46004009001400403c0c411314600130301104289540000c110041c0004040c10140b420380104808c0b85e0fa100866004120766050200740300142d081c980c20032480d800850f8003281c0380c80b1001d19118007607003042c2e1041c0c0d400104140381600340f03075040c2d0017500300f1b440058109103850f00318075440e00e461000b08041c80c0a91030b00d200201c3c19490042c50304500601580c0804400e00211040345404c904281d0860703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 702461879 1250 702460629 702460679
    0x320060c0d020702060f04030215030411062a03040807060311030601050a110706080604050604090b06090711060103050318010c05120304083015010c021c080408010209011206 77
    0x1c0c0d500d80258040d0048441c069400300700000c071996042c0c02400148101e0b4400d880d9070f904800302d0321648680780022100509070030910440f00c4224509000103100350005580d076418180180d4041c0441c811015014107501e6000240c188414082041860002c1009240c1480341500f140c07102c07001804090180b0741070020210b80e4950041c0a0031840400381d091104980031360b45c0c1c0d02001000c849086e036072180500c0ca884007294260519005110391a0f4000640b140541c4620040c00500d180c001d003c4404c12801d842884500b4400b0b1119a00840c020301c019525202d0f080a504418009003074400d0600882050020000f0030110b040e12122051017082600c03642c640c14400301c90f1040fa260104032040081c1e06c640104c035202500c02401904003260555a99a041c2d600383c07081d46181c80e540458400105503005141ca9411045179511143d89034401c15200d51380c009140d0060380200d08141d4000c24016955680802e150780c40024401003400258a00905884020342c0c0c2c1c030a81e0012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 702463129 1250 702461879 702461887
    0x20a02120d1d0105070e061204111516020a0f0e0a02071719121503020d0213090f060b010503011d15100207030203010f061401050d1b03090320060c 65
    0x1d004590b120212030950601903840c5040a604400c1c002c0c1402c030303408004100081c60381c100c141400001c5d60190f15030307902c060005445680321115051441160154070180790f04550070443d00c41c00c0030701a400004c2d41000d180104910400c0011440c60b00520300c8401070443c00c000401190307180d2508440034480050780c6080e1800c040d1200e4000e060b201c41c580d20002544001c1c2684580c3c0956a000030381e8801d440c0b0745803010741c0700c10749d0f0f40b240449454013030552040c405454103a0700c2510703071840189000010700c00c00c00498243d0f0684502641c2607405c0803803250501c050760141b49440b030307000d181440c0303158108000c24070a044940e41c00f9071503030000000500800c03800d440d1200c408400130180d81c0c03191015074009545088a0004074002d5090003110b6030399080d5802680c06940300040e2020640910500440301c1d50004640b08030714903140e90101000c2c015138189078501c00350540d00445c0e081501e0601800740311098960f01c240c001241c4100c0c0500002240c0142c01c181840c003140d40d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 702464379 1250 702463129 702463147
    0x4060b031308031302090c120702010c080a020d022101170307030c0f1a1807140a21061a0405060102191b05090a060f080d020309010c0c09020a0e010210020a0212 71
    0x302013039089000350040010800d2022590030300c0c0c061305100c02290105801c41c0d580010407803d031001d0300380007000700b00380070042002d043c16500503042c080e80c03408005003468000110059000c21158040c2c0014441c0c50040c440c0d49140c2144100500c0341100440c80c0180659008181c7e90040401401d003408651041042107106040c01c00e030b400d00c00364800040d0400c00c0d81902d4001191694628511407508001041400780d520300e500800c0080038003100d04c0c9000800046003085002402002e2800ca00c02400201544034040d405208103468071003a80360207041c00100c0b200900030f541954014520391b503800d18451303a41481c0c140d2180040803141d4100b0b551604081c1c0b10b07080103510110300000c11107141c01c0e81d488101111848010010300c9039a400b513094440800214800c01604200070040b00c42d4003072910100d44522810022a1440d03660201e401260810341404000551040001d82c0640c1e041000c1000105112021440c050030035401a55038401705418000004011514402d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 702465629 1250 702464379 702464401
    0x90603050612030c0c01080112030e091f031a100b0d0c02010b061809070c05060f06210d030609060b07061e06030309031202031c022206050904060b03130803 69
    0x203082c1040c48100d0b600e850071403080584603084c0c90301d0180000e20003800010300701c4e0700d40c0c00f203c400b603016290780c1e0124640806100c09140003c001d070380d200720500121605d02d0418038803440154082c1c4038213018410121051500884081c00d0745401610080d404d1284541d03000480b490b076a61f4500000e038190035a002a80548a00071000340c1c04000459031040403687c8111075485010200c0d2407550b02d071744400003501d15074a003450180981d40715100081c03c98046c480d103a900f04034010261400700d07101044541880100c4412028a41c0203060340c8400c050305801014060030349460140031060420004812501a06030040d08080d241c8034900d00d011507003039501a9580700c000c81406229100d0402500c242c5440c80111a0420701210740c90420b44044140d41c08400c0c4184001000da4508600c58041e4126100c002d13102d1003901e0200428104400202c0014201a1034460312002c41030100812035029a0101800c0c030002c108000e02007401e0524000000d80c080c01194407501c880d84011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 702466879 1250 702465629 702465649
    0x10509120a06060617010905010303021c0201060510050d0e0a030e04090303090204050f07080915040311102d090b0109091b0602010516020307050a15020f041206060b0a0906030506 79
    0x703442c40385401000300e40715a11850882503c8030b411a1281346980c0d650014040768403d202c064016040100e6004842000d8841c81c0c2d00028540300106005888000203030b075503078680282e11f02080c0d00207508011341c0d02a018003503840303c03000090180742c116603c2c0900021201c414140c4100d59805079001014000e078440d24441d0703000f400421881c035200c0e50403c16640192425404182464001003466400061540c18904403080740d040c1c3e5100c80d81c0a07100c1c2c2a946421800c6030082201300320382450548185801b4010a0f001e01840106051044d0040b03410341600d0388041d0b061804400208030145c20250440703900d803400140040719400d101c00da00c03242162230b4001e01280400084d00c2031381504254041c0300800e051714132b503413049070717013a6500d10840d0703401040b9800045184001c55420380c0b00400e8208054000341c0740850348226034201c0c2c0e01c503400c83c2c0d090601d000c411100707121445c403a01000d850901d0340c0c0d80ca00307075007580003404195881c0309401c2015116000940f80b500c441ea440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 702468129 1250 702466879 702466883
    0x181205031e09150c07081c0605030f06040c05010c02061b0f07170607030912030c0302091c121106010905040501110307120b0406050a03230d020d02011109010509120a 73
    0x16140710304007401c00a40794000e400803100002e0410000c030360800800c03021201c1842d0301000a5141410000e404182c02c614030b218002225a20800004c554070140f040c0541c072003d450103480b0515207440d091038004020b8106034108020a0070040058807090b045910132400d00c404603a5030380ba00c2028910700b8031180c0c0c001000380500c10f0000780340d010900804000d81e00c8002921015910214110200c56035924080e100010214039607501c180a03034043d804d00d201c2c0713281c094500300201c000300d111500f185041c4990200300c180d001051140280708494980014906030300d050240d40c0c419980c8000600a103180d0799515404a000c100d02503120041c4aa0b2000c032290301c0780780c443c1003d410030400c60b40b143d1416044c45600300084ca001c3c400c01c42500c0000b49138003481c03401c0d9102c6520042200c4c201081d2181ea180e080341c0085420480e004044042e5402071085c5002048003c2c20348015070314218008906120907500f0384e802c03d041d2007455506580c8080d00c81c4100d00324a14002c004400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 702469379 1250 702468129 702468181
    0x5061905010203090613240207080c060403080901020a0b15030f011125050d11213010150206010e01060804060915020c0d1d0d0c0f060305070318120503 67
    0x103d26100c41c2d0761040d40351987e0280d001d407034060360303140c00c00b980300c50203085016803100c0104410b00000368000085d003200d0b001803044400010301070b500d07120290300503034161f401441c0b0508a802d00c1d15080000c5c46100d69850000e00580d034014021040c40e000f001107030034010007900801c0900340c00c4d03e01c0100d6141d40040403a021094600c0000c2c1c140c0844000000c118060212040a020f051110390884480c030100b40f50701d01258224004078002041e01c40003042c90301c0300c03642031901407481e0005014245c84000c824030760307141100800312424841c0c980810764010400411810818603c042d0440d0900d05008150707031b80f00e00d06400107200301040100071480840841400a2940d809006000c0d100c9040340c500c80d03c000000e0390081920442c0b5600d08111000c0c180c01070401540349521381c0c0c0b1458085801d00c1d11691100d2050040d50031000000e50794004000c40c05505000d481c840242203100c98810b01c0341501c461b08141c000160000130710100001103003011546680d00807a1018041c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 702470629 1250 702469379 702469409
    0x10c0203120f06221406031603061e0603120806011806050a110a05010507260117010209060c16051804020108150a08060604061d04240f05061905010203090613 70
    0x4031381303002002008140035400c0410300001d03200341800030700b4803450f0004040061829241d0360301c480292002010950400d00301d01291214101140150405144120f6480342c2c441402c0300c00801002004048504000f0501c06200d0f00b00100003050050315443d00c0c085540700c03c0d0a1080e00c041c6441226040300703210780c054560501c141036001500170002e0795601180c00d8800094001d4001c600100c99040301883d50042102c40c0c9600f0800e88628580000035050404c4100058065001103821090030303002001c01000403800845440701030401101d49481c001000828040040c0707004000a0600078804040340003a92009101e180c0c2010080014910549409400d9140c03403003500c07120b00940c00c20f4404500a25880d00000b20a4440c1c2c4590b0302c1995107868200c800ca0466000e000c001c41c5440d41005a041d4901030080d42e0b00c100040800c550074180300b4803029805400b00f40b9070010000e0410b0010340c0c1e0120849421a108944845d11400e07000344030040152964000d0900d641210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 702471879 1250 702470629 702470689
    0x60a1407020a0314010e0c01050a050a11070e090601080f070b0d1a03100603060e06040b0c13030602040e1617061219060e1615080406022a010c0203120f06 68
    0x14100300031b84204d240503260001c010b58015103030340c001d0640c440e02080040c09184d6105200300700e85103a416085c030440721080e548103000c01c4030b190b042d16115440e40115005000c3c4410402c01e81c13003001120700c01810079626241c4480a14015140740e240304540718142082d02000320010860781503402029a807929040c401018010460380c031013211140e0030003100c1c80d26107030041001d51090360000d00581032335650854038421940014050400c19042c2d0001001043da0762005c0d001605000c000d0030424207040203000e41104041c181d100070014181040300500d41505086a0084030a903084249101c88071050ba081407400c0040c0b583c0c074529043e40e9001d0248035000041010b000d401906d0899024039008050140e680c00b5142030f192210303004a400f9440b608030302e80e00500800d030040c01e0448002c0d10342140043c4440c01e24400980c403424411061003032050300b20780e49150008600d400c0200c0340c00202100010078070001a0140c20000784c0b161962104100e0044072146c0d000b5440140c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 702473129 1250 702471879 702471881
    0xc1709040606032c0a02040e03070f030905120109031d1201090503030f1e0103020108040809030f0c03070603060e0a1a030303011e090b03150402040605060c030304050c060a1407020a031401 83
    0x209212200c04800d00041150fa9841e19040e80311100e0307010301600c5400705e507800b404050080001400c80510003082030b5004502401c040c0240107220340c1d00c8090301468441003010a070024480314040764581601d03000002d0f040314240c002411003014246d0100704c00c0c400146442e50300b2102400d030303509200c0e0b04410460040001c502c1200320026038241030f103401101100144070102c4184482c0b565030700603c01740d800b07141000e6000d4072441300d10707140200032300100741842020340f840401503010f452000480e14041c0034400c058800381c0784c100010f501c0d0980c0310725a03400c081c00940d042580d0f0a1005140d4081e04240ca88400e8040d04596403945d541c0301c04124074440908050310f000010f0000b080f0304d0b0841c043c0030781810b8028020518100d00c0f040e01008904080c204a80c065a84c45002800380c54050103000710300d0b4140d0145849280c2401c1c968140b0010034809842002c08002204a90b0b402c444410b4034001001005c5e034a840039480841d0b01c0f901150000360000c2050041d6842107041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 702474379 1250 702473129 702473141
    0x1050405031e0f0705090106030230190203090d051c15080f0102360301180b010e090d140f030109020403050c100815010905100203071e030c170904060603 68
    0x1c82c804840003c0e42001c0d59545610040c016140c0c40403525004025051081d00648a00ba41009000401d841058030300400d1000b0410345944d591084810000b50111b007401d42c80308114410340640c510b1030f05070150358461914010035000c0c81804120301c02001c0d03000384074099007a986031080214014a20010035900818400d800041c814080c2c0f5a4800310306000340c3d8200701c1c0200507010281c0814003000b41003115160303000d107101c60051003403050f940d0034003a2848100c0c0007406101065014180700b4a104416009104980c154500b4050f81e5030300081d4034680c0c0d904c03e1034060440400140c4a0341144505105030400d048044000711b44100d0650040007101e00c01c0040760700700040701c0306100f0101c102e411654041002c40000890345403441d80d888445202c149080300f001c03611030b0005841007440e1400c10006130310200d40301c010810316034010307600000029001c5800d002d41d9507000b01090000c0000a00c0e43c50100c00a400e104480000d80d403100303800820a0081923101c603801401400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 702475629 1250 702474379 702474433
    0x170c03010c1e0f1409040e1f0e03040e0609071107060f032904021e070b0406060f0e0c0a0c1410060605040506070605040507030f201c0b060105040503 66
    0x2e140801030603124040c100342041d120180e224210780d01e00c003822024458115a0040d0340007038441d01006020342040c40000b050b40c643c01c401050509440d00300c002100c10050910750242e20400080c04982d41480c103c960100040311034507071541e54000129008080c0268148280c400c409003c1159600301ca5154600c0020340d40c204580311a80c1401d0108140b003481164105010701001c07c03031402d042c0c0040508200e138204c4030711041036043d0b0061566200c5030007030700e003080210107200401c0f405004103402082c0480c0c042619904100c602c1c402d00e0006001c52085000c00910116083d0041088a80042d0007100703075102e44842c5184140c45004401c995401d241c44d1550220b03030a0b025000391010360324054181401c10b070440c2e84a400410024100342c40601c19014000002201207510086d00c510500e1765803507207505036085c1044000090043c5114609100341400e4a42d80351103054900d0707030041d1003110191034480050b280c1e4804c40d00704542500880c010031100b818801142e5031568 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 702476879 1250 702475629 702475667
    0x170106060f091508061f0206041a010302210c0603180d1d040f0f15030302070501141215040c03060e06090c07080a2c13090c170c03010c 60
    0x441014000c40d9620741c2030083c1d801d00c0c40c042e404401035901c20369100354003a40141400f0040e4611a80c00b07a080074500c4050300050b40100708100c00c0200e800da840107003614000200c00b965045500040441e40000310b0300000c108200e100707048090b420080445440e01c0070740015030303a0404a03813a1815806080002c5003d1041d070081000c0184102c4100b59549032200e1969000354140d0104005005030404011200782c40d0302041000110324890405003411440380200400d02e50b28001c0c1c145240c682c0498103011850010b15203900c8030b44200d52428540c4440404e03140c2c1c03005c02000c1c0f40500302144c150001d207010394010103e90564041c606444590084250f6a80c40300108072400c0e208550540007010184100c400042d1481c02030131550100b030030328024003080410b82e81014000a0600700070340300c500c00d00c000d1500b003a90400b581c860b0b0b040000d0000d11681d03250100075003080c2c80390072140c003069000642000d905114106006000500a0010405d2500700924140341090f0351a45d007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 702478129 1250 702476879 702476897
    0x2030f0a050d05130c060c03030b0a080f2404060c1b0b010504060e09030909070c0b0c04170102071101050f0d0501080105040204060b0319090f14010c0210180b1017010606 75
    0x3134203440c018070920f5032000b00c0f844520b042c81c0382110480c0a00004030107168840346070114951300d0441c0c0e18064020040240f550400c00d040c030a10700310103e2914048806c1e80c102d0000202d007600e0401d40d0158001102240707040c1c1e011004c0f583c0117001512003100010b030341d4038a401c104031401aa0304072502160b05000454032291490781e032000030340302c008556004000d810881c0c10030b071007959486107150900d861500903e41762420300203021248103901c0000017030b080c408480801c011120007180301c8021418000e1660302c91025240400b4424144200415440c1919049000f103605800824109103c40d5a6034031009018203400d0350101e210718100000494421400030a0ba48149480d41c0c455203a044d100c00e42c0801824400c1068848840c008401000b007000d400c0e00f0310128403540c0001806085840303000b4208034694030f03000a194242022009002e414655454016030031200c440c07610b80f2a038892242240c2650302034040c040309400b81d0608042c065108408036900c0b80c8a00c286 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 702479379 1250 702478129 702478141
    0xb090f070b04060903140a080d020d20071506091a03010b041e021c020c030717160b06030106240e0103020313061a0301020d1d0a0c120302030f0a050d05 67
    0x1590155000f0318002414028040010035600016030a4860818090b6000b5100c951211079031a444a54049441d039000182d01c0602c4600d4030a44007800c00081d84041c0b000300110086010b4495204041c0c0358544810303815540901e96881640200f03100a4100b1414102020744240401048686482946440740551050070f081c0188484001d1100c8030404044200795081d0080d0418841c0d2035808078110403800741e4000610062040c2d108400c02503441d16400d103859003a0502011602200c0081440266460800e000300c03000709580c40300c9140350036521003002c00e0061815074001c60ba41c81d500b0a00345d03041c4030051584080000c4d5070b540d01c0380d01ea04450042d4103034881034803010f20a082c881d5004000c45d2403a403103170408410705102d19508a841c0304c002401c0e41c104041d00140c150303580782c0e54040f0020310114030b1100812038001d0220030b00c481e114100300502c14402c80ca048400020f0b10000c2610038801c94a003940d440240e25107400b04a80c3c0101143c000354180541c903480c090110350307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 702480629 1250 702479379 702479399
    0x140619050a11091e030312060f0a03080d0902030f060a020304120c020f06030c0909010e16020a08040608070c0b040c052b0204021305220510060206061009030b090f07 73
    0x2030740d42054414a40b83c4140321051150855010201c2e02e80d01c8a451441003003550306000400c1400f01102040c41c4a0900d01c00b005050400100702e148240724004080001802c030105a8429120f49a00042d0800541c0007190034140301181511032806004204024500603501850040340a0911034590000011054540b09002140694010504001032945181941c000c42e4840003081c00c080c180303c101004120680c2d000e030060315a52402c203080050001c1510142d4014075810300c0145250002c50b240c0e04c00c14851030203010100910100000d130100e0140c2507840d40342c0d074810045007040c6020b080a64408615000d50340c41100440352620b080400080451403074550808e11800001c40c603800c00009500502110899051a0400080681d2952034011410305d030050122440000302c5401c0041f0b400007003004c824000c02440c1400781903400078000d0350040094a4107081c0488440054640412507130004001254000410040240200e8190b4800e02c28070210303007a83c0c2d101d5007020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 702481879 1250 702480629 702480641
    0x7030908060906010312090b07050f060c120c07020f120a030e18360c03241b0708040611120a020c0d08040e130b01140f010c140619050a 60
    0x3d52090b0010700c0456803000e090141c89003e410301048144e038030003810500d90001001510540c015100000345114103100d41f0764810b40f00c0e40f9081c50412414690081500060211400702030003281c01003c6403501c0d60710070681c07036004015000041848050640d00c6011020031800a01c0c880e200c00c2440c00c0c11881d0401121142042504598981d000201030740303260202102a030001d00c084084900800d80c0c2d59891701d42d04000780c8142c0c04d003030301803601d0441041c02481c030301540340218126a0354401c1496400200346404d500d11380c0f02c8242400300f00d016009014003040000100050055000005011080d6400094410002e03504c0950280e0307014a0301038034003503002006802101c3ca0022072140c0114031642000b400c181c1c6404542c0d407a2042218201e2905604c2c160001c00d016900110900501c0c0d08541c2c00035158840380031401182040c42442d05020840c0803000c200000c000d40d20403c905c03d203049946902d4000e01d5000302c03161003400d901c0c40c00c1c50003000c508000007a0081c0c0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 702483129 1250 702481879 702481891
    0x1b0a030b060d0501121101080c1801090521150912130f0e0402120d091202060d0603030509030f0703050d121404110f030102070b161202040801091106180f04060504110703090806 78
    0x3401c2290081030f20b4609010ac5090300e04019010801007400d0f038038115610210440441d41e07083c80342c5880826807403d05182804070551503a1010011201c4000230701c01e050045092246846400340d1814428241198002c909084400c260108a000441e011548141d000300c41074106003500703014150f102c904800031200041c54104045c80708200e000ca00c8613507503101034507492502c2c520511080032030b10310b07410480000d0b00001c0c0740c040c00c1c5410030130080c1e8400301001812446103903a0b240395039894540004070602420150002c85a2261762107801030001c16104242240381503e841ca80204460079070511030301c003410584140e4101442640c9801da84201903a87c10386502c950000c0340560a4600800c020102d40f14080302480c0d40058801001100c002181d116140d1501311020701c4000c139200c1c05994288a000722420789038803003a2170444d0079a6517098401006000c1005080290499500036007440c095520700740c091070041841034041c1c1e464902403070b12600400e031a13500650748 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 702484379 1250 702483129 702483151
    0x303180f020f03031c0905010b1f1d040e010509060106090b070b31020f0607050d1107170a1112060a110706050702030705061b0a030b060d050112110108 67
    0x18400050034011540c1c900b00200404481c1050346580c442176281c6805800c001030701d5205e90401c030070401d0074003412040000c11510058000080d00c16142841d0350005a50b00300702225001c1c80340a68250203130340403808050801d0181100ca0300c0c07040e01904045d02c0d517412510414000046442c86000344000340ca072071410441c903201494951400c1c0b4140034010b803410f030b55011034080c1860310301c4044444840341004c0f9501d8030411801045820703080d0704000c5024074003c001c004005407001c40e4254859003103040000018561035145860403040303070000304480f800c9810907031501400007445852548a00b40441031008500c06100c440015008480a142d1166010944050303a6812241074418000421410a211034a03030000b51441a0352000158200141004c140a02801143c3e030280a81c084414138004c0c2d011151441d00c5854545000c0507983d20800400350f444400b2110101d00380c0400744810b5031142020710700b894a074102100d0741c000c0b01240401d19400703000d90a115580c1192 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 702485629 1250 702484379 702484403
    0x150102101509020301080708120f0d090f0b27030702060304120c080304032105071b0212100c020d14030109050402030c0d080a2d0f020313080a030318 66
    0x9a0000c0e002070012010981081c50300801e21820300e10155000342500001050075929150149050200b44042007000c00010014a0701e0080716404441890303c2c3c1c0240000d10625038104004414142e100090414801d24148112111081c3e20080000e000c2c0890f00c1111240d80303180c503920302c038180c0002e4200c2d0042c00050003081a50f154400e118180341400759074100603030f4480c000c540c0102c07070403004240c0c40c12956996808004c140c80546404410401050070007681c0988245180c48064840c500c07c840400115111b010300d14404042c0c2504844003540d5820894000d0321000704058010b04c41c0c40703090720459210b6006204171388858086589180d0a2243c50b0700640001403050360103105800f6011690740302d210707004000300e004030100d5460710b000c404c00811030701c04c01401000058401082c4050412011488003160696042200d60b940818000fa811030003001e0300f000c00a41051000200703000042600d0307000301d20aa504021210000c04141905c1740f14030000740844e403444da = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 702486879 1250 702485629 702485653
    0x5150316230307030c0e1608040c09020d111305090708040b31060f050c070218060d020a0803091311160501110a170109050402130b010e0d06050708150102 68
    0x4490149540150a8403c40d58490700c1d0850740c209503038084e07101c1d4503049041048802150000b940d4014451410200702d04240e160340c000d514840c007801510f65030000b6408040041a4403102561065984564480002c403418200d051282e12910380622203420000701c400d4030480710075100d01c0d03000941352070a480c2d500f04420300c0c40f0000c0c0d1400d001c002040a000010f0851411703104103902ca6800410400941d07003004050340c0b0040c00310307100164140412401a6550084200c2100801900d0b07125546c641000503000f00191002a4000030b81c54404130320741c80c0203c010010b404081c0c1e21000358421400211089070b000b031418044070607042c441112004038035106254058092000421404030318800c0c0c82860b407003031484901040d50b010449200711000c900090043c94001800c20082ca8650040751a503a41300c50f00648035039980c031000700c8607800382e480d0701c606800c0a0004501c484851400000602040d6a0030010460f4440060a89004a160860540c00690203010802085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 702488129 1250 702486879 702486929
    0x3050702150c0f030a0f1d07060815150705060f060a050f0a08030a021e030a0c02060f2104030206090a0804060c0812040606030c090b0105120703090605150316 70
    0x10704600700b051030030010700701078001242c007440c0281144170000442030000c00c0403c040b142422844208905201070b991060301002c0345040403100c1e18200851581d84070b03543c565425001b11080782d4041140a100289200000041c000301c2d0f12801c11101592116400401c034484101c5800380d01c42040c0d0818001802e00c08440d044030350740074041c0c01003681c42c4d50000e03003540c000b5031405c3c00590001c0100902c400c03200c0c202176054200760300507500d07060804000400f5001c2d805030103405000c0c00031b00c5403540030400084660209a201c034120603079604044010250006640590040c030801000c01c4c94400081000240c16501030744551502d46000b40550301c80d80104000c1d1000f01003440b0b130004070300145c801e96104912030480002d043d07045103071031520340300c0e25001502440d10744691220b8a982140885244402d01c000c22862555002401c40107851000002001c042c02d00741442256003c840040210784422016502010120f40005a0380d900d14401d0081c0c45c110b090310003c2409007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 702489379 1250 702488129 702488131
    0x91703030c07140709151a0301140d060f05010e010509060109051905150a080906010e01030f060905100f0f0e0a080a02070305030703110106090911130b220b010305070215 75
    0xca4070608000c0070640b0f4405041100035400940304c0c030740711500081c0d0081c81500c84405000741400401c290032134180303881c5040c0014080c8241d02003810500c0b90041c3e48203400035103516032181051004c3c2c13490885040c0988021700c00c9656100080b0008200340c0340000e95903104100c180d40e5030384a41d1504081000390301e001800850036004541c070126840d00e036401908030840e1005181c941da0007003040010720305000101019081c2d000000144055200c4001d5281182d4200c40000c001858908010b0f000b071211807401401c03403003010320724000b04010350080e041c581e40482c1e003000b0912002030820140c446650101c820354000101900c0044c01310000b404540c40355204030340c0d505480355100d07031566021307082c150081005692001d00004c0d0900400300900031000c41171041050b985d5038a5220a01304101c10311441015a0000e0300030b2007503102030f0901c4401860349144011a180d040e4071140b5121103445000c0c02d0075030b80c13030495003c1e020f00c50040c10303154010a58810a10115100408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 702490629 1250 702489379 702489383
    0x51206220507180e1f030302070311010201110d0f0609060602100513020423131e031418040630030e0405041118040804090216080408030a091703030c07 67
    0x640304440038070103d0701c0500714090141849220701340d003001c21a034842e6a0000e4203010f0400d030240f60500006c2d5000c01c6080803030b94050781c109856481c82006030b0141a000612041c85800484c0100d500120782e081202003020b559000c0210640390f04140c0141ca030355010741d001603841003001696010075076020582c4051034103091685180030341d00103016602403c0901c15101d101080040402c541c103103540d908a40c04451a2030b10179110782d544030b903045802e6500c0c984a40c01382018418980243c00060002c1031100c641940e5a180380004162101401c0e143c9010b03502c1c4c144e010521841c800c0b03600000903a000a0008a1204607c03000095005400e0407420070a01d420800d4454070345009031070059120b404c060507180b003000103000b1001501d540705060414030f00305203c0800c04580c11a030070780c0c050f401c0151b0b07500c1003818268408ca01d841001040c01000041c0055581000b0010304003600c240d6841d02a4195070707856180b0280d50100c40101503800405c0420b00c07202c168001400068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 702491879 1250 702490629 702490637
    0x300b041a071706011103070804260604050709020a030b0a0e01061701051e010c050601030b040605061f030c0201200a1106070f08151906030c03140103020904081603051206220507 78
    0x21a00c4c2d4410000c9d401c1580160031001c201da044600c000c0002412182200e040c900424440c5829190207998010510402500a90028840038054480c0d04041401e81d0007070224030a8950342d00840008070001d03c00c080015038602c409030440c8042e0718071035040f02d00040820b4400003054066460b42a40012000d041c4414000010001001808003a00842c003a140c82c8115183c241030620503143c0007401b00e4451440c015a04400c0d2109040ba00031030811440c0004001c000b00b20281c2c01042d07031031032516080c0b00d9445c01911044c414001055070304496503840707400b0800101e0284c4e45940645030440440c400e000310a40e160f10401d4003542c080710903a5035082140c080008101c080703803100710750842c21040140610002c4d03014020081c1060041c40e00300005041c42c8543d00c428a01804020f00c600700001c0402d0a004e214003d440007061402ca03c0e8100c0c68040c81c0c060700a40c00344100300e617400c0b1940c0009129103043c1c0d9030060901c1078001941d66594144200f1402440c0044c00d0100f40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 702493129 1250 702491879 702491887
    0x3041a030702031b03030126030706051005030f030d0e0c0a03060905010f020f0d2d1517070905070206130602030a091e03080a06300b041a071706011103 67
    0x9140aa041840039548041c5d0b07a00d504100e03a40e03498800070500010700c007040b610500d69244000040301c0205410800025131034507440d902414002442d0301c0707030b07a01d4412118000700b41007001c00107059242290208001d0301204d0008a1b8840c00845401a80000300c90420004246035030000301c0401d20031400012445da11800d078000301c2e04000c199410034440414800091100d038441d01840f00c1c0040810314044443c01c1003101d40000c0401c02840440c0c8803d488040c032421000f129000e490310011264618900c0e81200d6503d40003441048200c600b404081a01c042c000320751b85006400c80c203a10315092110340c6502d4081c1d40003a00c00300c00c00790350300d07013002c045243d55403030342038116110140d840301d4100303420010000d00d405009070031340c0c3d45070200410ad80c000420400c0070001810108074400f0b0a0b40c00c0c07004940c03404103406428003600d0402c001c00c008c0c000103e00e00d0301c0d9803103c41443c07585036032808030390700d96818152441c64980103012415543c041c1401280c1c15215800f16490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 702494379 1250 702493129 702493147
    0x3010c02011e140417070f0c1701140714040b030106030209031504080a0c1110050309070506090307060309030c0f05010203060a15020a020f0d051b0a060f08010909030509030a031d010203041a03070203 88
    0x7d941e1019064464001070b44050007506d100280c40b10f0ba80404c03c000f070088961001c9016801000034201e04203004030481e140b0104d4541300f06441c0101440032919413a50380d140c070090043e5100403929131107030042c030301a8800c246841d030300940620b400000050500c00c00c6101910000d403464410703213042c456280d14404035680c0700000c0a041c01d80e0b9403526103030706042130518500045900414403e88081c0a40082e035240022030004940c0709150208815816043c1a10380003200c00b0040e00001900010206000c0150010360141c9810340b441128180c1e155040303030b5041c0d203140340c1e0401038000d035100002516000d0184000e00030024600320381c0212503690586003104e0003200b182e04041418580280340740184400c00100b20a080181000001100040040b5414040c403070b042d56a03801d101090500c62016500307030b418041d08071070040c640e90501421210784600d48a0203007851020040d2254408400d0328100e61081074480d44612001c154030000b50401403649045110a10107c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 702495629 1250 702494379 702494393
    0x100e0703021801180203330f0420070809060f0406080f0c09120118050106090b010504240c080c0c040b040615120f060312020609160b0310030203010c02011e14041707 73
    0x4507c1951032a07000c1303104021003440010130034040b440d44694a003911204801d101c0d681d06c610800c040c044d0181c0d45a64500d065451405074804c41500481c000c94403800f200130803030041040c0c03070f203030349072608280c0d0b42d121003054030141207640c1100c001060007564a24141060b960300d01e0307100d8000101e40302c2c01d40207401e1404c01c810305003a0794903034480c1002c000c00400340c0314100b0100401e20b00103150074203103c00d158045030304104403610b0300c61503040d49130701c9403254450282040d0301090903562000c0d050070301940c4040014102e482a032070a180001e0b603191a1003120220b8610f50620203401050070300036151000701c00c000c0003009440b1090807410001500c01e040c040c5120b135950b285902c2460000a183c140018a101c00d20703485011146801524507000c042111125103d00d981ca643d1b8212148040120381d00080d095802d1081c500110741c1c041d00903000381d17560300c00f02d108c4018880f2160010b84070100c0c560300301d04149030003040c01f18400318a0300b250041c100306014075000e070b50b0b540c40d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 702496879 1250 702495629 702495691
    0xd05030a0302090f0f010e100e03240f0108120705070512150c070b011a0d0c030501090b01020109110d170703020d0e060c0d05030603100e0703021801180203 69
    0x3100095001451400780d01c1e00c1080d142c0244016202c51540e02c1192001810814070302c1c2030240b040100a05400c0028880d600072405100050140d448000c940f00c054410001150041c0452031586c000185180c807007201c50750304a6a8070001050f0300c094040e441d03085ca0f480b070002a03d080c05031000214854030b640000c0e142340000040105502d00f404138445480c2d002c0582400c0700200c0400030b200104e0303000e98400717054400041708503500b05403044803455a845000300c0c03046650309044450380392580607440103049800002040c0550000140120300700e030118a4000c14241c4c0c43c1800002c541000f00025248500c5620030154003030004180c6c0c0b8035038010100440041c0d001e41c0103040c0b44e07940300c254005843d905413089030410340018107141c0c81c3c44e2880c2c940300c10018003000244450b41c08010100c0b04500a813020040c2906800f489a240c542c0d6020036802501e003800c0811403590700204241c122a01c0320300c504600717403070443c403d800313541b004e028611900b40b548601c810f079070300b418489 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 702498129 1250 702496879 702496897
    0x512070915080610030303050c180f040f090606030606060e1509041d0303160908060703110904021b1e15090309150a08010803030606090904060f06081f060b07020f0d0503 75
    0x441100f0380356107030003000d84600a0210902c0c4606100158501340104ae411805060840b0301c0f044003421340303010600410ad52400410442d081c141120301348620340d1300040940e0301034042800400c0e115803050b140d07240000042d5400c580100d10f200c613a000c0d40e40203400080300060000c142e2503004155075111170910059418103400c000b0a20070000508003844d61120120f0400c4440c0d2813034a1829a20b1f814002e00e004182b545a20a00b82c428880104882d840c0200070011902c2d121821071507400080036001104091144900c3c841c94110000b16849803000a40010801040119503c059800c0c014050b0913007031005201655441c6e8528903050344514003400120b484440780c040003042c4140680c00b202990b00700300b0510003540c50f060200e54ac14042507030400104d445614002c0e005241ca5040c0d0b107000d6290200102e031602c80841c10014040e80340480e02c0c54446100c034640b0440b4110b07c511400341e1010041d00005040002c540c09080c0d00081c4640715241d2117440701c908541c0100b0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 702499379 1250 702498129 702498151
    0x1a090408120906060105120718120606050603090606120f010f0c0e100509010f1b12080f0106081605270114030412030504050703080f070b0105120709150806 69
    0x882240c1041d0030340159800200702005044a04102001030818458000d4450048003502c0c000b401c040e00441c1c02e004044203110007202003035511900642c075400d908004441d0356041c2a80000c4628103001520302070410b1502603e0691105010040c00000754030240e00315000740c11410707100d0b034401c0c418400106101c07200030545d03129004004060007810003807603110b202e8041c40407007500e40c04015185400c4007030134124203404034000c059030720918014030080600c0e00c1c5100d110420140b111180d1070032946440301030850b19a403011425580b0309005200014058600061a120b0140403080709404c0c0c034203102d4a09041203100d121349003046043e0380c1e0900e04600d284003203540e12a20b500450100314640e9800d5051940d00e41b17001412500390f80701010f40321f50108003405010700000c80115070052480c0c2c1c0e00c0000400b8900d250f017104005403100da031136800020345818402c0384142c0c40401e40000e0300c4510308005480c401010390b10400f0b45984032140c40480c0207402048041d0140c0300c07602c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702500629 1250 702499379 702499387
    0x80309011a030d090b030a0e0f0106080114010b0901050d110307020601050f120322050a0e04210e010c0c051507050709061511010b130504050105070519031a090408 72
    0x181401c0e900d0342030050703503000750f200c480e040b840c56a0060251040d10302c00408207a807500c592042078064400741240807a1800798810380320b44448154011070840b40814024401c6202070740041c0c0380c0c0b81c001d116414540d0300030484031000d036100300c00400a00e0144a00024050b044400700000c3c4c4e0011540c03070340507a100100501c01494040b41c0510104021a142960005682e80441d200e0003070304441ea6198050265864680c80e020640c14060710010b020008995911006402c2408040d0380641e2069104074000150b50500c40390009078040685440344001507030780c0112201141c0301340c2a030f11190600008a17032a90351448800f5205614060b06807200320b9401c25504148460348490310b000c1c60711f6020001d104000400506040c91400c01c00961302890342058050000410b040e80d2003110b08a6a110916242d84018040ea015030001c11155840c0001511240300b502c1003280c0249031725104070324281c800e0304404c1d00031070f1039030201e199070f068040030a0101ca829101141c45050100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 702501879 1250 702500629 702500651
    0xb0112060b2802030a0e0d0219091107030509010507060f050c07020301150e0f0703020408011d0f01060b030a09020f10111c093003030c030606020102040302210a08030901 75
    0x74240c40a40c07601c030042c910900424060180d0303248a1150301c60f00303100340201d82000c141da40b03003600341400d03030052321640e0710001c00d04540080d40031074001d486589103410000b145842a107819034106940c141c0758035151040d61801980c075504660402c0310b60381c0d220144101e40c20381da0300400c0c2c00340c00c0300034115271104010f00c105400d40c1d84007141e03150010350f098010000040071072544c5410030007407500e4802d030b51102c02d004c50180c4525007188508d0b6003072105064603482c0001c8403190400700c0380250741143c0b6600e1440c1e8282c80c0c1c24411203030410010300c00310715840c006900c0030446a20080045280400080c045140e40c50b884410201103680c3c0005c6520b40e0304240035103a00707900003408090a4010803000078041c009203010b4002c2000a440d030740f6144407000c1c00800160110011001e240c000c85140c001c0140c0888402c1780300103410880005540c600500079607066a81c02001c1c0401280380b0300154a82c81c1c11b10300f40d03030b030303030f403041484200c00b0400c170600840c006c9034a0320000c203210b074102c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 702503129 1250 702501879 702501907
    0x607150501090606032318010203100509010608070816091d06012709020f04121101030e0304051507020109120305041e0513050925030c120309090b0112060b 69
    0x541c0c00442450f0405400c41503880446e510342400518045c1c1c501d03003545543e1030500400400d401420520340c40001400340b00e6240180409c121003040703581c404d142c2c1c0c85100c200c1e102c1c0c00c1543c420000c1000c030b002090160380440845840c404491621007034440d540c1a246014086905010b001981c5190501c030440d41d1103607180c0c1c54250881c000e504020a007080d500302c0e01909203c7d600c2d400d0740c003040c10b00301080c000d002c49004102c80b0a9039011405282060015907440c08002400f2910b01000c24041e00d001000791403c54100400c8040480d42c6a40800c181d41e120721422810405001d00201c5c0c581b1a2203190300c0014040d9a800b5299400d003400489039100c10000c41f00d0f9100d410b981000156140d000045500090302d40228161710341c80c00062070210b0b032680100240c0003010f00e0588420200d021902161301440c10300c1104ca2362420501803c109649025000848081041c42201010b03040030010180600d000154102c000c0d82c0700040711440c0e0420300700324200240343d04200d114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 702504379 1250 702503129 702503141
    0x30b0a0c0e03070b031306060603020307030506040509211b03070c05030102130b070606030206041e12120807110a060c080906010f140303040914090d050705060a0b060715050109 78
    0x40350601c00c035078081400000e030342d9000034420703c4442c810002c001581c0c0f042051083c80394686c03102e070910280d511500c000d0301035001280c1280c0002c1c86c00000403c40d282c61b0007542e0052070644040c0250040002580816180207900030b480b001d004c1103403400410000840c800395024070405151a40924508602c58903080c2d4001c0f40300e42c0c014000d51810084001000b8111405140b80c1d5544201134038282000d00030315440658404008140000c6004440612002c12910500e1803140703d41c45d91001c1d22403411601028108030381a43c4003020440c02441030941081d00c50602da0111450078601c24500062481d04540e13407602c2c0d2801030f5000340c0144084e9044038844025280c5981862920100100700e486030b11041c440d10a070700704164030b00f802180d002d05541c2e4800d011688403455501c4001e0400c2d1071880041c4500014840405d100d501a030305a141d1040141140d40c449915610240003040b244a41c424020009400000c500000ea800c1503d4a000701252940c5841014411600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 702505629 1250 702504379 702504401
    0x6250303051902070809040203070c0f0605011a13120f0f080901120c0804031209060908040e07050c03090402031816030308071d100c080c100c2a050f0304030b0a 71
    0x40141302c46070008041c181030780c0031a00c0c1a03500503100e80d9504000c03034040c2180351014144011040c143c4050200a42140307059900b0401c0c401801b2905030b4821006e8864489a440d58040c40401880403510300090211500d0089114503004a03175520384004881c85554225406080007900c00243d58015020341600382000f6402c10025400610241030100011720003801c0101d40034170040d40030613070b50100c0704040d0441c004020400c0130340343c9041d880d842401008405142d000000348a00d00c0f1300100c50f0307151110400356041000c180c9c10700010350400740c10000141500d50b03100c040c0e86820803d10000e002221898644585142800f500b0194054512001c100604141d600c40c2d0300000300f00c00f09c41c48191142800f5004541c01103403246c1c05034600500c0d946000403041104100002e14030308802c1d1908003040210880d00c1d095852001807580e580c00340303581000c2017001030f122240e542a001c1c081e0302983c1c12503414014140c00d40c1c0c4290000c440481040090280f000d11a114401102c0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 702506879 1250 702505629 702505631
    0x7090e060105040509041202030c030f0904180503040306150b0c150708101a042117090a09090f0b0a0f0e030702031c111f0c0c0b06062503030519 64
    0x3c2d0424002c0740202a0040c8060030700c44400d50565000e6100300121381d030f00c1c1071440c1500d45414600711030200700c1d44210314441c495400d214400c40702d08692040c0000c1c00e41d0140055260501d156500c0c00a4a110030710b18034020303443c0b440050540040d038010b051300c115503405130403180318040010602a1001d0045402c2002000c10030200740902c190610541e407866421003078609950305070000e540b140d9002400000707990300d110b40e01c0340b0450311824a0544980031070700d0189039070480d0340042c0c000c15029070791009000700c00b0800b850007a444542c141d40116926405c00d10162100c100c050030a41c0c101103107030740e84c01c50380c04d5446107403003142d03081c22a000c0a54502006600000d684070021500715810403010070b02c000c41c15018180306c019400c024015115850b8004001014042ca801c08400d405800c102601c3d841c3e502c204058080d40d54014200507143e01c601c824000c558101068010310005640880e0000685d041a01501c09100303540c04240380c6400c0040b40f094420780b1518406031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 702508129 1250 702506879 702506887
    0x18050f01180b0d02120304080706030e06040201050a0e21011d0307060b1915120504030906050a030906050906041703070219021c0c05043606060e07090e060105 70
    0x820311400c404a4003849100114030560b4034000541044443c910003940821041c9a6010b024008005030085070a400c060b500c0d02540c0e2401501950b00c103442058050b0401c2001600541c00703000035110307411503440c01184520340d00002c10b001c000c0c4c04482c2c00405d5040c0c440d1090394502405000202200d01ca54000850400c0b04101ea42e40a000b4000340681d88501c02c6003020744078888075144051121601c004015a00c9030584070022400030b00324005021854200d003420014040d107801264107a0b954900303d450000300322555080511791508058507401c80101041c1c0c18022907002c1c241c0c213405045e2038101807620300110000c2040d01107404406208002000350003007440714103168190003c104004007840068500c412412540f10302e0110034a0500034440c08101540c140d40c2c0c29202003241c1035031101e00704060b403005d418140340300c44180b544480708403000c209460141e10a50703001c583e603a1200000c0d224403004882d40c100080c080c2c00200030b12011160030640006007800d009140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 702509379 1250 702508129 702508139
    0x603110d02011202031e010b09030601090c0804031202040f030302010605120105071704081e09181006030b040b04090b1f030206030c0a1404140112050c0412170418050f01 75
    0x3644401c0010f107191181c2c00b2001404986054004050003410700ca42c8603120f60312010101f9980e0000c0741160302034800c8400100b5400b40c01e200d030603104056070300e424078181e0b51960111078400e00d106100116580030711000801004160316000510301c29000410202d050000784079001e4203003140b01101d42e0506080c003841c05d80080001a000d5800500c081c0c45551701e090540b0300e407050311696000d07140226210301c1144e1100000d00100c19003100c1604914456080744030f1520000d990b8890226030611081240c3c074003d80c09071860f03200c09840480e41e01c84600001e0120b840044063300e00340619001c02c02c041003c808a000c01405a00907a1802800e540200d042c81c00020800760418200194031602e081c01a0034805034041c0e50140386554540740d669046035284240f00d8540803e80c0201d12640520590140c01d10600d1600112800d00d494698074440410144d18251200500c41c0c0e207000d40048200000d00c0030344901c0861003030100e488008241100d00091015031001501d00050003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 702510629 1250 702509379 702509387
    0x709050f0c03010b0c120f0c0c04050621010902060d1d190609030c0605090f0717060a200a0806090a150302060a03021216111603330603110d0201 64
    0x1c15a03541d000101d48031248800307414608050200381106d510000314651f440032002400405d820f805030801c1d1000020000c040c03100b0781c1c8080e40d410b03503c041c1090f100c1d40d624a40a880741a40d045174030021860303800a40204145620003e003131009641c0710b402c0203100301001100400d2464003480100840d258840840000110740740000b0f00301070300e80c08450b05252190007100368168009000304164105000303150f940305141c43c0300000900540000040001d00d610b0311510219002c80980101c0e5110b20b01040100f00b144401140284010300f00042c0740160800f4020301340441e202c1820310b0410000700050a200100303044412400c0100d02007a0b0200661032000300c0ea415a04540c903203201180035400707802040005805000c169003040340b06031603080e2151420003c0d46904001400a07440b10b42c03241030b03900d151640368403182d40030800540503e41921751401000c280410541d5065129180c042c1044810501d00b51241c03c1801400381e0340504890310141210307056500c00040d0b002030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 702511879 1250 702510629 702510631
    0x9030b04031805040c02010b1009060c0b060604030f03030c0813050a14190501140c091e0114070b0601020f010e0c0103020c0a02060a0503070905041406040b03011d0709050f0c03 78
    0x1000c20410440d5581c880e05602d1110001c1c200c010030a00c030350303074030380c2c2d0b009000301000d116003441500c400c170100039528041c80020050311019a90341250701450b844503400c54001602590708003008102c00404030300f825501f81400c40c404d5034023150302d0300606002440c9010143c1200501265a0810000250000743c00c90b2102c1d481440c10100c44000c0e10300d6802c1c18031801c1141c08040c80d104e0300302c04010065000041d180e203003600c00762440c2c642c040030045070b00490349802d82010031040c60b001c1751065401564010001494a00c020503080386601c441500041d900722000a100401e0000c0c56030140034450203031740200000c018646110314031507503960a008605050590000e41c0d00c11008062012240300da030003400960751007800366001040c41d4812074040b00003a86220b004503581c5454003610304030070349a2035580040d8440b20104001405545030495240d96904143e8800d61070083c640311002c80d0306000341101c5071070b00e2101c40580b9801800001145a170721b00b0080c4000128003a2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 702513129 1250 702511879 702511883
    0x30606010c0609170318060f090d08151c020f0306101703130f1802041208160c0b03010815100e04240c09061b080319050906060109050109030b04 64
    0xc03c00c04024203003180720035401010788482040c00010844405410507500901d51001800c6031490b55a001c100781c403201c019107542103182c00c45000700038241d1083c60920b801038240184447c0b100d440d81c000840d1a0480381040c2c4c02020701c00c11000642c501100d0051031000c0c150003070503480ca0301c03460503050007899000d025140d02e4070803c0043c034020104299000002c07840400000d5544450395652604031030f00c09d400400c0184400c1080c14001340c000e81c2c08840f98010544c1d80410280e5419a030b94001407800415058480021310108a003540c5070b00c01001c005003400e0303595042a032540d0600e40c0d2402440c0d1112500810300002420440d42d003411104400400c8415403600d107400c01200c906070781c006c10411213001200c800131080303a2180c1600002c03a10385403104da40d0b441c010786008041000403490100c1c0c0541120201d48200c00440d444404070183c000e2940350010905c00711502641c0009640c0c0c03120b000c00a080d608000403e010300024204004541e2450351803c29003d401400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 702514379 1250 702513129 702513131
    0x3210a0507140a0311070f02040b0d0c0603200a080f060406121203023117030d0c031803090f0e060d060e0102040509040b04031409030c01051c141005030606010c06 72
    0x1d400d03c464425441401c0441900048035038440b1b1a040c455000d0160f01c10681c841e83c40c2440d1120240352000e50750780c80343d40c48207034144000d14000040d001080c00c51813014510742d00e00b46d00f0704844c0d8410014130340c42c4201c3d118164a0b040c200700c00c060300c0500420042c051841c0c10b900b440b603407602c2544032580e16880401c003c007a80780038408138081d0103447d071003046d41c084403a03010b107903154101512030f41607025042180900703a54803040401c0d506402038a1119802c100b000040d026001e800640000841c6d080c04100c6681d91003400c1c0700c000c082e9001350005007504000740318158040000b80d00400c9800c0c81110a801c0880010f600000780c1e0070005c001c6a80c0e600d40a5a511080d01034600400000300b980720580b40c10b092818154104440071400100b9440d001c1150020032000e5969840c0040c00034619001b58000544032075001c404c0d0302585800006007890000c10798010741820740c0f550303040e40c0d211781840700b000602080c050300100d200b500320a04002490740c7c06007804140c140c005c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 702515629 1250 702514379 702514387
    0x120b01350106030b0f1801050f07030905070503030d0213051905101b030807120c0e060d09080c01090309060306050d060203180f03090a05040501080601090c1103210a050714 76
    0xc40c010040b60348014541d9618004010600c0e108550962007a40c1c0b01d162043e12100301c40c1140d080748c0044440904140782c1c0c8002c100114803e520051305e061084003143d02090f11031703000901d10740107036040e070704425000240e010601040d114000024007003503c04420040040144050110041c00341c04d01491a111405001034401e000c10215418031030744000843d211414024046071044407c4004944070016041070020948249540310049903240201100c2142c108080c60b030180002c041300b2074940c4050008544030b00002c010711140034000050b856500d24010b0820820b42e4400414540b8040c02005152a26220505c0d2694000001a541d0342ca4600c2c0d08409400a0100c2e4414446d000c6003030008480000109004103084501429899031441003200741c9809020348111900b051004100400742ca0700202e41c03440150501800d00010f50540ba4616000f500380100881040c01c011096000200c40350354020003810030900c0246421403029081d650320156114804000103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 702516879 1250 702515629 702515729
    0x140703030209060f0a0c023606061b010c0f020a0510020d0e0f0109061a0f0f03010209100207060306150c0f0206040f032402031b22120b01 61
    0x9021520000d0b01d44c2149a100c003c100b04c020134044000310103d001e043d1800090503010000740750400b06d542d0050014002014101a0048510003c0c0c465070300000144030025624406138200100e441d1b581c4000110709500c0c0e8001000c0d00c1c02c0380c0001095400c03620a8502160b0085404100b400e02180090f0703540f14501802c0004280643d40310025008080f085681c011045d0408950303130740030390828400200d212514130324085030710510303d074002810b5480204905280c02402c0c2c89400090005040002030700106600742040b100540060304841170a1050b00c1d01481010b01500b103510011800070a035403405408140034a101601350340301d080281c02156508802c0b03a001d00803e480c0840401c2d40c0b45003c40c0d0f40d000c604030f1000f51140c80c107030419900c0755038400c0d64031030b40d5400ca032a0007800204140b0342503580100302000500c010300380c1c4c01982d1a040000d02c0000c0c4040c6500209041c140c5c01d1032a806c0c9010382208a40000440b070f423030050408240842c3d541e40c01e800040208034084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 702517985 1106 702516879 702516889
    0xd1409010f0c060f0e060f0906040c12020a0f15090e040507051311070f020102011a061b07170a0b15011709010902090a0c090501140703030209 63
    0x503004035111070b00c54508880500c1c01424005a44040c81c201c407015036803481038011042c0d00c840107108400c250410410b44c080c04a201402607801c0a548410b90240c0750f12820340c0100d40724000c0010b40d600c0201010061200305101c0e80881d43d01c2c100d51000c0090b0f854003074040b511542c4000741c191800c400f103910441d80500a0900b0b10b0404c800c108000010707166440d450b50351016003440303ca50010051070009d0099200074040502d520009003991a032012843c1c4155201d1400ba141d515580e064030490029800802d802c000c0c004100e82c0f901c81030b07500c00c40b40340e88081c20708400c0714004101400c0a502650742c4907451b0340c41500030010b00300100001400260407030101d5402c52000d000d4070b83c00001803c00424100015000988011425100c40c0d2605c2c1e03a508014040540000c031410003400c0a007054680c0803444101480301740224440a0145500016007038815514 = true := by decide +kernel

theorem cover : BRFrame.Cov 702338129 702517985 := by
  have h0 := BRFrame.cov_init 702338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 702338129 ≤ n) (h2 : n < 702517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
